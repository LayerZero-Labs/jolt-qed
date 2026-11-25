import JoltConstraints.theorems.Completeness.Helpers.TracePCProofHelpers

open LeanRV64D
open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail
  LeanRV64D.Functions JoltISA

set_option autoImplicit false

namespace JoltConstraints

/-- A retiring halt returns nextPC to its source PC and records its kind and claim.
For example, Panic records `some panic` and a true panic claim without a memory store.
Jolt at `ff6fc6568`: `tracer/src/emulator/cpu.rs` (`Cpu::halt`).
This primitive execution fact is a candidate to move into JoltBytecode. -/
theorem execHalt_end (kind : JoltHaltKind) (dst : Dst) (pre post : SailJoltState)
    (address : BitVec 64) (pc : pre.sail.regs.get? Register.PC = some address)
    (runs : execHalt kind dst pre = .ok RETIRE_SUCCESS post) :
    post.sail.regs.get? Register.nextPC = some address ∧
      post.halted = some kind ∧ post.jolt_device.panic = (kind == JoltHaltKind.panic) := by
  obtain ⟨link, source, middle, _, sourceIs, _, shape⟩ :=
    execHalt_shape kind dst pre post runs
  have sourceEq : source = address := Option.some.inj (sourceIs.symm.trans pc)
  rw [shape, sourceEq]
  simp [recordHalt]

end JoltConstraints

/-- Every halting row of an honest trace ends its source and records its halt kind.
For example, an EBREAK contributes one terminal panic row.
Jolt at `ff6fc6568`: `Cpu::halt` and `BytecodePCMapper::try_new`. -/
theorem HonestTrace.halt_row {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (i : Nat) (inside : i < trace.rows.size) (halt : (trace.rows[i]'inside).Halts) :
    let row := trace.rows[i]'inside
    trace.bytecode[row.rowIndex].virtual_sequence_remaining.getD 0 = 0 ∧
      row.postState.sail.regs.get? Register.nextPC = some trace.bytecode[row.rowIndex].address ∧
      ∃ kind, trace.bytecode[row.rowIndex].instruction.haltKind? = some kind ∧
        row.postState.halted = some kind ∧ row.postState.jolt_device.panic = (kind == JoltHaltKind.panic) := by
  dsimp only
  have terminal := pc_map_ok_halt_terminal trace.bytecode
    (accepted_pc_map_ok joltInstance trace.bytecode trace.expands trace.accepted)
    _ (Array.getElem_mem _) halt
  refine ⟨terminal, ?_⟩
  have pc := lookup_trace_PC trace i inside
  have executed : ∃ advice : trace.bytecode[(trace.rows[i]'inside).rowIndex].instruction.RuntimeAdvice,
      execInstr (trace.bytecode[(trace.rows[i]'inside).rowIndex].instruction.withRuntimeAdvice advice)
        (trace.rows[i]'inside).preState = .ok RETIRE_SUCCESS (trace.rows[i]'inside).postState :=
    ⟨(trace.row i inside).runtimeAdvice, (trace.row i inside).executes⟩
  unfold TraceRow.Halts Instr.haltKind? at halt
  split at halt
  · rename_i dst selected
    rw [selected] at executed
    obtain ⟨advice, executed⟩ := executed
    simp only [Instr.withRuntimeAdvice, execInstr] at executed
    obtain ⟨next, recorded, claim⟩ := JoltConstraints.execHalt_end .success dst _ _ _ pc executed
    exact ⟨next, .success, by rw [selected]; rfl, recorded, claim⟩
  · rename_i dst selected
    rw [selected] at executed
    obtain ⟨advice, executed⟩ := executed
    simp only [Instr.withRuntimeAdvice, execInstr] at executed
    obtain ⟨next, recorded, claim⟩ := JoltConstraints.execHalt_end .panic dst _ _ _ pc executed
    exact ⟨next, .panic, by rw [selected]; rfl, recorded, claim⟩
  · cases halt

/-- The completed trace ends at an explicit halt, on a source boundary.
For example, a success trace records the success halt kind and a false panic claim.
Jolt at `ff6fc6568`: `tracer/src/emulator/cpu.rs` (`Cpu::halt`, `Cpu::tick`). -/
structure HonestTrace.Terminated {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs) : Prop where
  nonempty : 0 < trace.rows.size
  atSourceEnd : trace.bytecode[
    (trace.rows[trace.rows.size - 1]'(by omega)).rowIndex].continues = false
  repeatedPC : (trace.rows[trace.rows.size - 1]'(by omega)).postState.sail.regs.get?
      Register.nextPC =
    some trace.bytecode[(trace.rows[trace.rows.size - 1]'(by omega)).rowIndex].address
  halt : ∃ kind,
    trace.bytecode[(trace.rows[trace.rows.size - 1]'(by omega)).rowIndex].instruction.haltKind? = some kind ∧
      (trace.rows[trace.rows.size - 1]'(by omega)).postState.halted = some kind ∧
      (trace.rows[trace.rows.size - 1]'(by omega)).postState.jolt_device.panic = (kind == JoltHaltKind.panic)

/-- An honest trace has the terminal-halt certificate supplied by its final row.
For example, the certificate applies to both success and panic traces. -/
theorem HonestTrace.terminated {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (nonempty : 0 < trace.rows.size) : trace.Terminated := by
  have lastIsBack : trace.rows.back? = some (trace.rows[trace.rows.size - 1]'(by omega)) := by
    rw [Array.back?_eq_getElem?, Array.getElem?_eq_getElem (by omega)]
  obtain ⟨atEnd, samePC, halt⟩ := trace.halt_row (trace.rows.size - 1) (by omega)
    (trace.stops _ lastIsBack)
  refine ⟨nonempty, ?_, samePC, halt⟩
  simp only [JoltInstructionRow.continues, atEnd]
  rfl
