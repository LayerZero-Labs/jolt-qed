import JoltConstraints.program
import JoltConstraints.witness_helpers.destination_capture
import JoltBytecode.Bundles

set_option autoImplicit false

/-- Rust's proof-trace conversion accepts a load only when the RAM value read
by the tracer equals the destination value captured after execution. A load
into x0 captures the rewritten temporary destination.
Rust: tracer/src/trace_row.rs::captured_state. -/
def JoltISA.Instr.LoadCaptureMatches (instruction : JoltISA.Instr)
    (preState postState : SailJoltState) : Prop :=
  match instruction with
  | .LD _ dst base imm =>
      let capturedDst := HonestWitness.capturedDestinationValue instruction dst postState
      JoltISA.memoryWord? preState (JoltISA.sourceValue base preState + imm) =
        some capturedDst
  | _ => True

/-- A live HostIO row may read memory and append advice, but it leaves the
instruction address unchanged. Keep this frame fact explicit on trace rows
until the Sail byte-read frame theorem discharges it from `execInstr`. -/
def JoltISA.Instr.HostIOPCFrame (instruction : JoltISA.Instr)
    (preState postState : SailJoltState) : Prop :=
  match instruction with
  | .VirtualHostIO .. =>
      postState.sail.regs.get? Register.PC = preState.sail.regs.get? Register.PC
  | _ => True

-- Rust: tracer/src/instruction/format/format_r.rs::{capture_pre_execution_state,
-- capture_post_execution_state}; Lean retains full ISA states, not just captured operands.
structure JoltTraceRow (program : JoltProgram) where
  rowIndex : Fin program.expandedBytecode.size
  -- Includes the requirement that a JAL/JALR inside an expansion is its last row.
  -- The deferred source-to-row proof is `JoltProgram.rowValid` in `JoltConstraints/program.lean`.
  validProgramRow : program.expandedBytecode[rowIndex].Valid :=
    program.rowValid rowIndex
  -- Rust patches VirtualAdvice.advice on a per-execution copy of the row.
  -- Repeated visits to this bytecode slot may supply different values.
  runtimeAdvice : program.expandedBytecode[rowIndex].expandedInstruction.RuntimeAdvice
  -- Rust checks the signed immediate's magnitude during proof-trace conversion.
  compactImmediateFits : program.expandedBytecode[rowIndex].expandedInstruction.CompactImmediateFits := by exact True.intro
  preState : SailJoltState
  postState : SailJoltState
  -- Execute the bytecode instruction with this row's runtime payload.
  -- ISA: JoltBytecode/JoltISA/Semantics.lean::execInstr; this certificate is Lean-only.
  -- NOTE: Trace execution uses expanded instructions, including rewritten native instructions.
  executes : JoltISA.execInstr
      (program.expandedBytecode[rowIndex].expandedInstruction.withRuntimeAdvice runtimeAdvice) preState =
    .ok (.Retire_Success ()) postState
  -- FIXME: Derive this from `executes` after proving that Sail byte reads
  -- preserve PC. Live HostIO remains fully modeled by `execInstr`.
  hostIOPreservesPC :
    program.expandedBytecode[rowIndex].expandedInstruction.HostIOPCFrame preState postState := by
      exact True.intro
  -- Rust reads the old word before every store; successful Sail writes alone
  -- do not certify that all eight pre-access bytes are present.
  storeMemoryPresent :
    match program.expandedBytecode[rowIndex].expandedInstruction with
    | .SD base _ imm =>
        (JoltISA.memoryWord? preState
          (((JoltISA.sourceValue base preState) + imm))).isSome = true
    | _ => True
  -- The load's captured RAM value must agree with its captured destination.
  loadCaptureMatches :
    program.expandedBytecode[rowIndex].expandedInstruction.LoadCaptureMatches preState postState := by
      exact True.intro

/-- Successful ISA rows with Rust's fetch and source-instruction boundaries.
An expansion executes consecutively without incrementing the PC between its
rows. At its end, the next source is fetched at the ISA-produced nextPC.
The trace may be a prefix; completeness claims needing termination must say so.
Rust: https://github.com/abiswas3/jolt/tree/main/tracer/src/emulator/cpu.rs#L654-L692 -/
structure JoltTrace (program : JoltProgram) where
  rows : Array (JoltTraceRow program)
  assumptionOperands : Fin rows.size → AssumptionOperands
  allAssumptions : ∀ i : Fin rows.size,
    all_assumptions rows[i].preState (assumptionOperands i)
  /-- Every ordinary RAM access uses a window covered by the assumption bundle.
  Device accesses use the separate Jolt I/O semantics. -/
  ramAccessAssumed : ∀ i : Fin rows.size,
    match program.expandedBytecode[rows[i].rowIndex].expandedInstruction with
    | .LD _ _ base imm | .SD base _ imm =>
      let addr := JoltISA.sourceValue base rows[i].preState + imm
      JoltISA.ramStartAddress ≤ addr.toNat →
        (assumptionOperands i).memoryWindows addr
    | _ => True
  sequenceLayout : program.SequenceLayout
  initialized : ∃ entry ram io tape hostIO,
    program.initialState = init_state entry ram io tape hostIO
  noEarlyNextPCChange : program.NoEarlyNextPCChange :=
    JoltProgram.noEarlyNextPCChange program
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

/-- Every trace carries the initializer requirement, so register completeness
does not need a separate zero-register assumption. -/
theorem JoltTrace.initialRegistersZero {program : JoltProgram}
    (trace : JoltTrace program) (src : JoltISA.Src) :
    JoltISA.sourceValue src program.initialState = 0 := by
  obtain ⟨entry, ram, io, tape, hostIO, h⟩ := trace.initialized
  rw [h]
  exact sourceValue_init_state entry ram io tape hostIO src
