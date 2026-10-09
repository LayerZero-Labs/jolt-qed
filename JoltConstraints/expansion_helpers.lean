/-
Plumbing between the bytecode project's expansion programs and the final Jolt rows
that `program.lean` stamps. The programs themselves are the bytecode project's:
the generated `JoltISA.*ProgramAuto` (from Rust's `expand_instruction`) and the
hand-written ones in `JoltBytecode/JoltISA/Expansions/`.
-/
import JoltBytecode.RiscvInstruction

set_option autoImplicit false

open Sail PreSail LeanRV64D.Functions

-- Jolt's own source instructions: custom opcode 0x5B, decoded alongside RISC-V.
-- Inline (opcodes 0x0B and 0x2B) is out of scope.
-- See : jolt/crates/jolt-program/src/image/decode.rs:71-72, 192-212 (decode_custom)
--       jolt/tracer/src/instruction/format/ (operand formats)
inductive JoltCustomInstruction where
  | AdviceLB (rd : regidx)                                -- FormatAdviceLoadI
  | AdviceLH (rd : regidx)
  | AdviceLW (rd : regidx)
  | AdviceLD (rd : regidx)
  | VirtualAdviceLen (rd rs1 : regidx) (imm : BitVec 12)  -- FormatI
  | VirtualRev8W (rd rs1 : regidx)                        -- FormatT
  | VirtualAssertEQ (rs1 rs2 : regidx) (imm : BitVec 13)  -- FormatB
  | VirtualHostIO (rd rs1 : regidx) (imm : BitVec 12)     -- FormatI

-- An expandable instruction: one instruction of the guest program, RISC-V or one of
-- Jolt's custom instructions.
-- See : jolt/crates/jolt-riscv/src/kind.rs:20 (SourceInstructionKind)
inductive SourceInstruction where
  | riscv (instruction : RiscvInstruction)
  | jolt (instruction : JoltCustomInstruction)

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
