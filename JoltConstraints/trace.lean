import JoltBytecode.JoltISA.Instruction
import JoltConstraints.register_encoding
import JoltBytecode.JoltISA.Semantics
import JoltBytecode.JoltISA.DeviceMemory
import Mathlib.Tactic.DeriveFintype

set_option autoImplicit false

-- Rust paths are relative to /Users/ari.biswas/Work-with-A16z/jolt.

-- Derive the enumeration of all Sail registers and its completeness proofs.
-- Generating these proofs exceeds Lean's default elaboration recursion depth.
-- `in` raises the depth limit only for this declaration; runtime execution and
-- proof checking are unchanged, and the heartbeat limit still applies.
set_option maxRecDepth 4096 in
deriving instance Fintype for Register

-- Rust: [Cpu::new](/Users/ari.biswas/Work-with-A16z/jolt/tracer/src/emulator/cpu.rs:516).
-- Integer/FP registers and CSRs start at zero, except misa; privilege is Machine.
-- Sail-only registers use their type's default (zero, false, empty, or inactive).
private def initialRegisterValue (entryAddress : BitVec 64)
    (r : Register) : RegisterType r :=
  match r with
  | .PC | .nextPC => entryAddress
  | .misa => 0x800000008014312f
  | .cur_privilege => .Machine
  | .hart_state => .HART_ACTIVE ()
  | r => by cases r <;> exact default

/-- Assemble the initial ISA state from Rust's loaded RAM, entry address, device
and advice tape. `ram` includes every allocated byte, including zero-filled bytes.

Rust sources:
* [loaded RAM and entry PC](/Users/ari.biswas/Work-with-A16z/jolt/tracer/src/emulator/mod.rs:219)
* [RAM base](/Users/ari.biswas/Work-with-A16z/jolt/common/src/constants.rs:21)
* [device inputs and advice](/Users/ari.biswas/Work-with-A16z/jolt/tracer/src/lib.rs:366)
* [initial device](/Users/ari.biswas/Work-with-A16z/jolt/common/src/jolt_device.rs:110)
* [advice tape and cursor](/Users/ari.biswas/Work-with-A16z/jolt/tracer/src/emulator/cpu.rs:20)

Sail's `nextPC` has no separate Rust field; it starts at the entry address here.
The Sail bookkeeping fields below have no Rust architectural counterpart.
-/
noncomputable def init_state (entryAddress : BitVec 64)
    (ram : Array (BitVec 8)) (io : JoltIOState)
    (adviceTape : JoltAdviceTape) : SailJoltState :=
  { sail :=
      { regs := (Finset.univ.toList : List Register).foldl
          (fun regs r => regs.insert r (initialRegisterValue entryAddress r)) {}
        mem := ram.toList.zipIdx.foldl
          (fun mem (byte, offset) => mem.insert (0x80000000 + offset) byte) {}
        choiceState := ()
        tags := ()
        cycleCount := 0
        sailOutput := #[] }
    vregs := fun _ => 0
    io := io
    adviceTape := adviceTape }

namespace JoltISA.Instr

/-- Only VirtualAdvice receives a per-execution payload. Other instructions
carry no extra input; their operands and immediates come entirely from bytecode.
Rust: https://github.com/abiswas3/jolt/tree/main/tracer/src/instruction/mod.rs#L207-L233 -/
def RuntimeAdvice : JoltISA.Instr → Type
  | .VirtualAdvice .. => BitVec 64
  | _ => Unit

/-- Fill a copy of the bytecode template with this execution's advice value.
This only assembles an instruction; execInstr remains the instruction interpreter.
The destination and immediate are preserved, as are all non-advice instructions. -/
def withRuntimeAdvice (instruction : JoltISA.Instr)
    (advice : instruction.RuntimeAdvice) : JoltISA.Instr :=
  match instruction with
  | .VirtualAdvice dst _ imm => .VirtualAdvice dst advice imm
  | instruction => instruction

/-- Rust initializes the advice slot to zero when converting fixed bytecode
into an executable template. The actual payload belongs to a trace row.
Rust: https://github.com/abiswas3/jolt/tree/main/tracer/src/instruction/virtual_advice.rs#L79-L89 -/
def IsBytecodeTemplate : JoltISA.Instr → Prop
  | .VirtualAdvice _ value _ => value = 0
  | _ => True

end JoltISA.Instr

-- Rust: crates/jolt-riscv/src/row.rs::JoltInstructionRow.
structure JoltProgramRow where
  -- Rust: JoltInstructionRow::instruction_kind and operands; ISA: JoltBytecode/JoltISA/Instruction.lean::Instr.
  instruction : JoltISA.Instr
  -- Register constructors must follow the ISA's existing Rust address map.
  -- This prevents a raw .vreg 0..31 from bypassing the architectural register file.
  registerOperandsCanonical : JoltRegisterEncoding.instructionIsCanonical instruction = true
  -- A VirtualAdvice template contains no execution-specific value.
  isBytecodeTemplate : instruction.IsBytecodeTemplate
  -- Final helper operands must fit Rust's runtime instruction format.
  operandsRepresentable : instruction.OperandsRepresentable := by exact True.intro
  -- Rust: JoltInstructionRow::address (RV64 instruction byte address).
  address : BitVec 64
  -- Rust: JoltInstructionRow::virtual_sequence_remaining.
  virtualSequenceRemaining : Option (BitVec 16)
  -- Rust: JoltInstructionRow::is_first_in_sequence.
  isFirstInSequence : Bool
  -- Rust: JoltInstructionRow::is_compressed.
  isCompressed : Bool

/-- Static bytecode and the complete initial state for one execution.
Rust stores the [program image](/Users/ari.biswas/Work-with-A16z/jolt/crates/jolt-program/src/execution/trace.rs:17)
and [execution inputs](/Users/ari.biswas/Work-with-A16z/jolt/crates/jolt-program/src/execution/trace.rs:129)
separately; Lean packages the bytecode with the resulting initial ISA state.
-/
structure JoltProgram where
  -- Rust: JoltProgram::expanded_bytecode.
  expandedBytecode : Array JoltProgramRow
  -- Rust: [create_emulator](/Users/ari.biswas/Work-with-A16z/jolt/tracer/src/lib.rs:366).
  initialState : SailJoltState

namespace JoltProgramRow

/-- A row followed by another row in the same source-instruction expansion. -/
def continues (row : JoltProgramRow) : Bool :=
  row.virtualSequenceRemaining.getD 0 != 0

/-- Rust fetches an ordinary instruction or the first row of its expansion. -/
def isEntry (row : JoltProgramRow) : Prop :=
  row.virtualSequenceRemaining = none ∨ row.isFirstInSequence = true

end JoltProgramRow

namespace JoltProgram

/-- Position metadata produced by Rust's expansion pass. This describes static
rows, independently of the witness or its constraints.
Rust: https://github.com/abiswas3/jolt/tree/main/crates/jolt-program/src/expand/metadata.rs#L25-L54 -/
-- MODEL GAP (trace review): this checks local sequence metadata only. It does
-- not enforce Rust BytecodePCMapper's unique address runs, address range, or
-- alignment. Two ordinary rows at the same address currently satisfy it.
-- See model_review.md, "Follow-up trace audit".
structure SequenceLayout (program : JoltProgram) : Prop where
  endInBounds : ∀ i : Fin program.expandedBytecode.size,
    i.val + (program.expandedBytecode[i].virtualSequenceRemaining.getD 0).toNat <
      program.expandedBytecode.size
  ordinary : ∀ i : Fin program.expandedBytecode.size,
    program.expandedBytecode[i].virtualSequenceRemaining = none →
      program.expandedBytecode[i].isFirstInSequence = false
  next : ∀ i j : Fin program.expandedBytecode.size,
    j.val = i.val + 1 → program.expandedBytecode[i].continues = true →
      program.expandedBytecode[j].address = program.expandedBytecode[i].address ∧
      program.expandedBytecode[j].virtualSequenceRemaining =
        some (program.expandedBytecode[i].virtualSequenceRemaining.getD 0 - 1) ∧
      program.expandedBytecode[j].isFirstInSequence = false ∧
      program.expandedBytecode[i].isCompressed = false

/-- The source instruction's byte length is stamped on the last expanded row.
Rust clears IsCompressed on every preceding row, even for a compressed source. -/
def sourceLength (program : JoltProgram) (layout : program.SequenceLayout)
    (i : Fin program.expandedBytecode.size) : Nat :=
  let last := i.val + (program.expandedBytecode[i].virtualSequenceRemaining.getD 0).toNat
  if (program.expandedBytecode[last]'(layout.endInBounds i)).isCompressed then 2 else 4

/-- Prepare Sail's two PC registers at a source-instruction boundary.
PC holds the instruction address; nextPC holds Rust's pre-incremented cpu.pc.
Within an expansion the post-state is passed through unchanged. Branches and
jumps still execute exclusively through JoltISA.execInstr, which updates nextPC.
Rust: https://github.com/abiswas3/jolt/tree/main/tracer/src/emulator/cpu.rs#L654-L692 -/
noncomputable def prepareSource (program : JoltProgram) (layout : program.SequenceLayout)
    (i : Fin program.expandedBytecode.size) (state : SailJoltState) : SailJoltState :=
  let address := program.expandedBytecode[i].address
  let regs := (state.sail.regs.insert Register.PC address).insert Register.nextPC
    (address + BitVec.ofNat 64 (program.sourceLength layout i))
  { state with sail := { state.sail with regs := regs } }

end JoltProgram

-- Rust: tracer/src/instruction/format/format_r.rs::{capture_pre_execution_state,
-- capture_post_execution_state}; Lean retains full ISA states, not just captured operands.
structure JoltTraceRow (program : JoltProgram) where
  rowIndex : Fin program.expandedBytecode.size
  -- Rust patches VirtualAdvice.advice on a per-execution copy of the row.
  -- Repeated visits to this bytecode slot may supply different values.
  runtimeAdvice : program.expandedBytecode[rowIndex].instruction.RuntimeAdvice
  -- Rust checks the signed immediate's magnitude during proof-trace conversion.
  compactImmediateFits : program.expandedBytecode[rowIndex].instruction.CompactImmediateFits := by exact True.intro
  preState : SailJoltState
  postState : SailJoltState
  -- Execute the bytecode instruction with this row's runtime payload.
  -- ISA: JoltBytecode/JoltISA/Semantics.lean::execInstr; this certificate is Lean-only.
  executes : JoltISA.execInstr
      (program.expandedBytecode[rowIndex].instruction.withRuntimeAdvice runtimeAdvice) preState =
    .ok (.Retire_Success ()) postState
  -- Rust reads the old word before every store; successful Sail writes alone
  -- do not certify that all eight pre-access bytes are present.
  storeMemoryPresent :
    match program.expandedBytecode[rowIndex].instruction with
    | .SD base _ imm =>
        (JoltISA.memoryWord? preState
          (((JoltISA.sourceValue base preState) + imm))).isSome = true
    | _ => True

/-- Successful ISA rows with Rust's fetch and source-instruction boundaries.
An expansion executes consecutively without incrementing the PC between its
rows. At its end, the next source is fetched at the ISA-produced nextPC.
The trace may be a prefix; completeness claims needing termination must say so.
Rust: https://github.com/abiswas3/jolt/tree/main/tracer/src/emulator/cpu.rs#L654-L692 -/
structure JoltTrace (program : JoltProgram) where
  rows : Array (JoltTraceRow program)
  sequenceLayout : program.SequenceLayout
  startsAtEntry : ∀ h : 0 < rows.size,
    let first := getElem rows 0 h
    program.expandedBytecode[first.rowIndex].isEntry ∧
      program.initialState.sail.regs.get? Register.PC =
        some program.expandedBytecode[first.rowIndex].address
  startsAtInitial : ∀ h : 0 < rows.size,
    let first := getElem rows 0 h
    first.preState = program.prepareSource sequenceLayout first.rowIndex program.initialState
  -- PC preparation changes only Sail PC/nextPC; registers, memory, I/O, and
  -- advice are linked unchanged across source-instruction boundaries.
  linked : ∀ (i : Nat) (currentExists : i < rows.size) (nextExists : i + 1 < rows.size),
    let current := getElem rows i currentExists
    let next := getElem rows (i + 1) nextExists
    next.preState = if program.expandedBytecode[current.rowIndex].continues then
      current.postState
    else program.prepareSource sequenceLayout next.rowIndex current.postState
  successor : ∀ (i : Nat) (currentExists : i < rows.size) (nextExists : i + 1 < rows.size),
    let current := getElem rows i currentExists
    let next := getElem rows (i + 1) nextExists
    if program.expandedBytecode[current.rowIndex].continues then
      next.rowIndex.val = current.rowIndex.val + 1
    else
      current.postState.sail.regs.get? Register.nextPC =
        some program.expandedBytecode[next.rowIndex].address ∧
      program.expandedBytecode[next.rowIndex].isEntry ∧
      -- Rust stops when a source instruction jumps to its own address.
      program.expandedBytecode[next.rowIndex].address ≠
        program.expandedBytecode[current.rowIndex].address
