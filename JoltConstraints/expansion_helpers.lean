/-
Plumbing between the bytecode project's expansion programs and the final Jolt rows
that `program.lean` stamps. The programs themselves are the bytecode project's:
the generated `JoltISA.*ProgramAuto` (from Rust's `expand_instruction`) and the
hand-written ones in `JoltBytecode/JoltISA/Expansions/`.
-/
import JoltBytecode.RiscvInstruction
import JoltBytecode.Inlines.Keys

open LeanRV64D

set_option autoImplicit false

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail LeanRV64D LeanRV64D.Functions

-- Jolt's own source instructions: custom opcode 0x5B, decoded alongside RISC-V.
-- Registered inlines (opcode 0x0B) are `SourceInstruction.inline`.
-- See : jolt/crates/jolt-program/src/image/decode.rs:71-72, 192-210 at 5def437f (decode_custom)
--       jolt/tracer/src/instruction/format/ (operand formats)
inductive JoltCustomInstruction where
  | AdviceLB (rd : regidx)                                -- FormatAdviceLoadI
  | AdviceLH (rd : regidx)
  | AdviceLW (rd : regidx)
  | AdviceLD (rd : regidx)
  | VirtualRev8W (rd rs1 : regidx)                        -- FormatT
  | VirtualAssertEQ (rs1 rs2 : regidx) (imm : BitVec 13)  -- FormatB
  /-- A successfully decoded host call, with no normalized operands.
  For example, nonzero encoded rs1 and immediate fields are ignored; nonzero rd
  is rejected before constructing this instruction.
  See jolt/crates/jolt-program/src/image/decode.rs:204-209,335-339 at 5def437f. -/
  | VirtualHostIO

-- An expandable instruction: one instruction of the guest program, RISC-V, one of
-- Jolt's custom instructions, or a call of a supported registered inline.
-- See : jolt/crates/jolt-riscv/src/kind.rs:20 (SourceInstructionKind)
inductive SourceInstruction where
  | riscv (instruction : RiscvInstruction)
  | jolt (instruction : JoltCustomInstruction)
  /-- A call of the registered inline `key`: `.insn r 0x0B, funct3, funct7, rd, rs1, rs2`.
  Jolt's decoder stores `rd` in the `rs3` slot, so `rs3` is the source `rd`.
  For example, the SDK calls `KECCAK256_ABSORB_PERMUTE` with `rs3 = x0`.
  See jolt/crates/jolt-program/src/image/decode.rs (`decode_instruction`, opcodes
  0x0B and 0x2B) at a6b6dc717. -/
  | inline (key : JoltISA.Inlines.InlineKey) (rs1 rs2 rs3 : regidx)

/-- The fields of a raw inline encoding, `.insn r opcode, funct3, funct7, rd, rs1, rs2`,
before the registry lookup. Jolt's decoder produces one for opcodes 0x0B and 0x2B
with any `funct3` and `funct7`.
For example, `KECCAK256_ABSORB_PERMUTE` with `rd = x0` is opcode 0x0B, funct3 1,
funct7 1, rd x0.
See jolt/crates/jolt-program/src/image/decode.rs (`decode_instruction`) at a6b6dc717. -/
structure InlineEncoding where
  opcode : BitVec 7
  funct3 : BitVec 3
  funct7 : BitVec 7
  rd : regidx
  rs1 : regidx
  rs2 : regidx

/-- The registration check: a supported key becomes `.inline`, and every other
encoding is rejected. An `rd = x0` encoding of a key whose rows read `rd` is also
rejected: Rust would substitute an uninitialised instruction temporary for `rd`.
None of the five hash keys reads `rd`, so their `rd = x0` encodings pass.
For example, opcode 0x0B, funct3 1, funct7 1 with `rd = x0` registers as
`.inline .keccak256AbsorbPermute rs1 rs2 x0`, and opcode 0x0B, funct3 3, funct7 0
is rejected.
See jolt/tracer/src/instruction/inline.rs (registry lookup) at a6b6dc717, and
a16z/jolt#2414 for the `rd = x0` rejection. -/
def InlineEncoding.register (encoding : InlineEncoding) : Option SourceInstruction :=
  match JoltISA.Inlines.InlineKey.ofEncoding encoding.opcode encoding.funct3
      encoding.funct7 with
  | none => none
  | some key =>
      if JoltISA.isX0 encoding.rd && key.readsRd then none
      else some (.inline key encoding.rs1 encoding.rs2 encoding.rd)

/-- A supported key's own encoding registers as that key, with any registers, unless
`rd = x0` and the key's rows read `rd`. For example, every hash key registers with
`rd = x0`, since none of them reads `rd`. -/
theorem InlineEncoding.register_key (key : JoltISA.Inlines.InlineKey) (rd rs1 rs2 : regidx)
    (usable : (JoltISA.isX0 rd && key.readsRd) = false) :
    InlineEncoding.register ⟨key.opcode, key.funct3, key.funct7, rd, rs1, rs2⟩ =
      some (.inline key rs1 rs2 rd) := by
  simp only [InlineEncoding.register, JoltISA.Inlines.InlineKey.ofEncoding_self, usable,
    Bool.false_eq_true, ↓reduceIte]

/-- An encoding that matches no supported key is rejected. For example, opcode 0x0B
with funct3 3 and funct7 0 is rejected. -/
theorem InlineEncoding.register_unsupported (encoding : InlineEncoding)
    (unsupported : JoltISA.Inlines.InlineKey.ofEncoding encoding.opcode encoding.funct3
      encoding.funct7 = none) :
    encoding.register = none := by
  simp only [InlineEncoding.register, unsupported]

-- What Rust's dispatch_source returns for one source instruction.
-- See : jolt/crates/jolt-program/src/expand/materialize.rs:71-101 (dispatch_source)
inductive ExpandedSource where
  -- A native row, or the no-op for rd = x0: one row, not stamped.
  | native (instruction : JoltISA.Instr)
  -- A built-in expansion: stamped as one sequence.
  | sequence (instructions : List JoltISA.Instr)

-- The instructions of a straight-line program, in order.
def JoltISA.Program.instrs : JoltISA.Program → List JoltISA.Instr
  | .done _ => []
  | .instr instruction next => instruction :: next.instrs

namespace ExpandedSource

-- A native instruction: one row, after Rust's rd = x0 rewrite.
-- See : jolt/crates/jolt-program/src/expand/mod.rs:126-170
def ofNative (instruction : JoltISA.Instr) : ExpandedSource :=
  .native instruction.rewriteNative

-- A source-only instruction: the rows of its expansion, stamped as one sequence.
-- Programs for instructions with side effects already contain Rust's rd = x0 case.
def ofProgram (program : JoltISA.Program) : ExpandedSource :=
  .sequence program.instrs

-- A source-only instruction with no side effects (shifts, MULH, MULHSU, division).
-- With rd = x0 Rust emits one unstamped no-op instead of the expansion.
-- See : jolt/crates/jolt-program/src/expand/mod.rs:126-170
def ofPureProgram (rd : regidx) (program : JoltISA.Program) : ExpandedSource :=
  if JoltISA.isX0 rd then .native JoltISA.Instr.canonicalNoOp else .sequence program.instrs

end ExpandedSource
