import JoltConstraints.theorems.Soundness.Layer5.TapeTrace
import JoltConstraints.theorems.Soundness.Layer5.RuntimeAdvice
import JoltConstraints.theorems.execution_facts
import JoltConstraints.theorems.Soundness.Layer5.Registers

open LeanRV64D

/-! Every operandless HostIO row retires and preserves Sail state and virtual
registers. Its absent destination leaves the witness register table unchanged,
so the local step preserves live-register agreement.

VirtualHostIO has no opcode circuit flags or lookup table, and selects no register
read or write, so its local constraints say nothing about host-side effects.
None are needed: at Jolt `ff6fc6568` the tracer logs and ignores rejected host
calls, and the bytecode model's `JoltISA.execHostIO_result` states that every
host call retires and at most appends bytes to the advice tape.
Jolt: `tracer/src/instruction/virtual_host_io.rs` (`VirtualHostIO::exec`) and
`tracer/src/emulator/host_io.rs` (`read_host_bytes`) at `ff6fc6568`. -/

set_option autoImplicit false

namespace JoltConstraints.Soundness

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail LeanRV64D LeanRV64D.Functions JoltISA

/-- Keeping Sail state and virtual registers keeps every source value.
For example, changing only an output buffer keeps x1 and temporary 40.
See jolt/tracer/src/instruction/virtual_host_io.rs (`VirtualHostIO::exec`)
at ff6fc6568. -/
theorem sourceValue_of_host_frame (source : Src)
    (pre post : SailJoltState) (sail : post.sail = pre.sail)
    (vregs : post.vregs = pre.vregs) :
    sourceValue source post = sourceValue source pre := by
  cases source <;> simp only [sourceValue, sail, vregs]

/-- Every attempted HostIO row retires. HostIO can append to the advice tape, but
cannot change Sail registers, RAM bytes or virtual registers. The register-table
increment still needs a separate argument. For example, an advice-write call may
append bytes while preserving every register. -/
theorem host_call_exec_sail_frame
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (run : UntrustedAnswerRun joltInstance privateInputs)
    (next : Fin run.bytecode.size) (pre : SailJoltState)
    (answer : BitVec 64)
    (instruction : run.bytecode[next].instruction = .VirtualHostIO)
    (advice : run.bytecode[next].instruction.RuntimeAdvice) :
    ∃ post, execWithTapeAnswer
        (run.bytecode[next].instruction.withRuntimeAdvice advice) answer pre =
        .ok RETIRE_SUCCESS post ∧ post.sail = pre.sail ∧
        post.vregs = pre.vregs := by
  obtain ⟨post, executes⟩ := execHostIO_succeeds pre
  have frame := execHostIO_keeps_state pre post _ executes
  refine ⟨post, ?_, frame.1, frame.2⟩
  rw [withRuntimeAdvice_eq_of_noAdvice _ advice (by rw [instruction]; rfl),
    instruction]
  simpa only [execWithTapeAnswer, execInstr] using executes

/-- A selected operandless HostIO row executes and preserves live-register
agreement: every live register-table value still matches the execution state.
For example, an advice-write call may append to the tape without changing any
register. The slot equation links the selected witness slot to the next
expanded row. See jolt/tracer/src/instruction/virtual_host_io.rs:9-38 and
jolt/crates/jolt-witness/src/backend/trace/registers.rs:26-57 at ff6fc6568. -/
theorem host_call_selected_step
    {F : Type} [Field F] {params : WitnessParams} {witness : WitnessType F params}
    {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs}
    (charAbove2pow128Minus2pow64 : 2 ^ 128 - 2 ^ 64 < ringChar F)
    (context : ConstraintContext joltInstance privateInputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam
      context.io context.entry witness)
    (run : UntrustedAnswerRun joltInstance privateInputs)
    (nextRow : Fin run.bytecode.size) (pre : SailJoltState)
    {t : Fin params.traceLength} (nextCycle : t.val + 1 < params.traceLength)
    (slot : Fin (2 ^ params.logBytecodeK))
    (slotPosition : slot.val = nextRow.val + 1)
    (selected : bytecodeRa witness slot t = 1)
    {row : JoltInstructionRow}
    (rowIs : bytecodeRow context.bytecode slot.val = some row)
    (instruction : row.instruction = .VirtualHostIO)
    {live : Fin 128 → Prop} (agrees : RegisterAgreementOn live witness t pre)
    (advice : run.bytecode[nextRow].instruction.RuntimeAdvice) (answer : BitVec 64) :
    ∃ post, execWithTapeAnswer
        (run.bytecode[nextRow].instruction.withRuntimeAdvice advice) answer pre =
        .ok RETIRE_SUCCESS post ∧
      RegisterAgreementOn live witness ⟨t.val + 1, nextCycle⟩ post := by
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
    run nextRow pre answer instructionRun advice
  have nextAgrees := agrees.noWrite (two_pow_127_lt_char charAbove2pow128Minus2pow64)
    context equations nextCycle slot selected rowIs (by rw [instruction]; rfl)
  refine ⟨post, executes, sail ▸ nextAgrees.present, ?_⟩
  intro register
  rw [sourceValue_of_host_frame _ pre post sail vregs]
  exact nextAgrees.values register

end JoltConstraints.Soundness
