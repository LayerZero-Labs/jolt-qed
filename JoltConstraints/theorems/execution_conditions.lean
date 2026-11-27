import JoltConstraints.theorems.Completeness.Helpers.TracePCProofHelpers

open LeanRV64D
open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail
  LeanRV64D.Functions JoltISA

set_option autoImplicit false

namespace JoltConstraints

/-- A retiring halt returns nextPC to its source PC and records its kind.
For example, JoltPanic records `some panic` without a memory store; Jolt copies the
kind into the device's panic claim only at the end of the run (`take_jolt_device`).
Jolt at `504dd78a2`: `tracer/src/emulator/cpu.rs` (`Cpu::halt`).
Adapted from Quang Dao's version in PR #73. -/
theorem execHalt_end (kind : JoltHaltKind) (dst : Dst) (src : Src) (imm : BitVec 12)
    (pre post : SailJoltState)
    (address : BitVec 64) (pc : pre.sail.regs.get? Register.PC = some address)
    (runs : execInstr (haltRow kind dst src imm) pre = .ok RETIRE_SUCCESS post) :
    post.sail.regs.get? Register.nextPC = some address ∧ post.halted = some kind := by
  obtain ⟨link, source, middle, _, sourceIs, _, shape⟩ :=
    execHalt_shape kind dst src imm pre post runs
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
        row.postState.halted = some kind := by
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
  · rename_i dst src imm selected
    rw [selected] at executed
    obtain ⟨advice, executed⟩ := executed
    simp only [Instr.withRuntimeAdvice] at executed
    obtain ⟨next, recorded⟩ :=
      JoltConstraints.execHalt_end .success dst src imm _ _ _ pc executed
    exact ⟨next, .success, by rw [selected]; rfl, recorded⟩
  · rename_i dst src imm selected
    rw [selected] at executed
    obtain ⟨advice, executed⟩ := executed
    simp only [Instr.withRuntimeAdvice] at executed
    obtain ⟨next, recorded⟩ :=
      JoltConstraints.execHalt_end .panic dst src imm _ _ _ pc executed
    exact ⟨next, .panic, by rw [selected]; rfl, recorded⟩
  · cases halt

/-- The completed trace ends at an explicit halt, on a source boundary.
For example, a success trace records the success halt kind.
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
      (trace.rows[trace.rows.size - 1]'(by omega)).postState.halted = some kind

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
