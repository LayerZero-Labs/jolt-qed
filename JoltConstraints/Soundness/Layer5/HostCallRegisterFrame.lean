import JoltConstraints.Soundness.Layer5.HostCallRestriction
import JoltConstraints.Soundness.Layer5.Registers

/-! A successful operandless HostIO row preserves Sail state and virtual
registers. Its absent destination leaves the witness register table unchanged,
so the local step preserves full register agreement. -/

set_option autoImplicit false

namespace JoltConstraints.Soundness

open Sail PreSail LeanRV64D.Functions JoltISA

/-- Keeping Sail state and virtual registers keeps every source value.
For example, changing only an output buffer keeps x1 and temporary 40.
See jolt/tracer/src/instruction/virtual_host_io.rs (`VirtualHostIO::exec`)
at 5def437f. -/
theorem sourceValue_of_host_frame (source : Src)
    (pre post : SailJoltState) (sail : post.sail = pre.sail)
    (vregs : post.vregs = pre.vregs) :
    sourceValue source post = sourceValue source pre := by
  cases source <;> simp only [sourceValue, sail, vregs]

/-- A selected operandless HostIO row executes and preserves full register
agreement: every register-table value still matches the execution state.
For example, an advice-write call may append to the tape without changing any
register. The slot equation links the selected witness slot to the next
expanded row. See jolt/tracer/src/instruction/virtual_host_io.rs:9-38 and
jolt/crates/jolt-witness/src/backend/trace/registers.rs:26-57 at 5def437f. -/
theorem host_call_selected_step
    {F : Type} [Field F] {params : WitnessParams} {witness : WitnessType F params}
    {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs}
    (charAbove2pow128 : 2 ^ 128 < ringChar F)
    (context : ConstraintContext joltInstance privateInputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam
      context.io context.entry witness)
    (restricted : joltInstance.HostCallsSucceed)
    (run : UntrustedAnswerRun joltInstance privateInputs)
    (nextRow : Fin run.bytecode.size) (pre : SailJoltState)
    (ready : run.NextStep nextRow pre)
    {t : Fin params.traceLength} (nextCycle : t.val + 1 < params.traceLength)
    (slot : Fin (2 ^ params.logBytecodeK))
    (slotPosition : slot.val = nextRow.val + 1)
    (selected : bytecodeRa witness slot t = 1)
    {row : JoltInstructionRow}
    (rowIs : bytecodeRow context.bytecode slot.val = some row)
    (instruction : row.instruction = .VirtualHostIO)
    (agrees : RegisterAgreement witness t pre)
    (advice : run.bytecode[nextRow].instruction.RuntimeAdvice) (answer : BitVec 64) :
    ∃ post, execWithTapeAnswer
        (run.bytecode[nextRow].instruction.withRuntimeAdvice advice) answer pre =
        .ok RETIRE_SUCCESS post ∧
      RegisterAgreement witness ⟨t.val + 1, nextCycle⟩ post := by
  have sameBytecode : run.bytecode = context.bytecode :=
    Option.some.inj (run.expands.symm.trans context.expands)
  have rowAt : bytecodeRow run.bytecode slot.val = some row := by
    simpa only [sameBytecode] using rowIs
  rw [slotPosition] at rowAt
  have runRow : bytecodeRow run.bytecode (nextRow.val + 1) =
      some run.bytecode[nextRow] := by
    simp only [bytecodeRow, Array.getElem?_eq_getElem nextRow.isLt, Fin.getElem_fin]
  have rowEq : run.bytecode[nextRow] = row :=
    Option.some.inj (runRow.symm.trans rowAt)
  have instructionRun : run.bytecode[nextRow].instruction = .VirtualHostIO := by
    rw [rowEq]
    exact instruction
  obtain ⟨post, executes, sail, vregs⟩ := host_call_exec_sail_frame
    restricted run nextRow pre ready answer instructionRun advice
  have nextAgrees := agrees.noWrite (two_pow_127_lt_char charAbove2pow128)
    context equations nextCycle slot selected rowIs (by rw [instruction]; rfl)
  refine ⟨post, executes, sail ▸ nextAgrees.present, ?_⟩
  intro register
  rw [sourceValue_of_host_frame _ pre post sail vregs]
  exact nextAgrees.values register

end JoltConstraints.Soundness
