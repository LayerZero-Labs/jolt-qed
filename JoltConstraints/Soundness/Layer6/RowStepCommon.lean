import JoltConstraints.Soundness.Layer6.PlainRow
import JoltConstraints.Completeness.Helpers.RegistersReadProofHelpers

/-! Shared selection and observation facts for individual row extensions. -/
set_option autoImplicit false
namespace JoltInstance
open JoltConstraints JoltConstraints.Soundness
open Sail PreSail LeanRV64D.Functions JoltISA

/-- The next row of an unfinished expansion occupies its selected witness slot.
For example, bytecode row 3 is selected in slot 4. -/
theorem ExpansionState.selectedRow
    {F : Type} [Field F] {inst : JoltInstance SourceInstruction} {inputs : JoltPrivateInputs}
    {params : WitnessParams} {witness : WitnessType F params}
    {context : ConstraintContext inst inputs params} {run : UntrustedAnswerRun inst inputs}
    {first : Fin context.bytecode.size} {done : Nat}
    (state : ExpansionState witness context run first done)
    (unfinished : done < expansionRowCount context.bytecode first)
    (bound : run.rows.size < params.traceLength) (next : Fin run.bytecode.size)
    (indexIs : next.val = first.val + done) :
    context.bytecode[first.val + done]? = some run.bytecode[next] ∧
    ∃ slot : Fin (2 ^ params.logBytecodeK),
      bytecodeRa witness slot ⟨run.rows.size, bound⟩ = 1 ∧ slot.val = next.val + 1 ∧
      bytecodeRow context.bytecode slot.val = some run.bytecode[next] := by
  have bytecodeEq : run.bytecode = context.bytecode :=
    Option.some.inj (run.expands.symm.trans context.expands)
  have atRow : context.bytecode[first.val + done]? = some run.bytecode[next] := by
    rw [← indexIs, ← bytecodeEq]
    exact Array.getElem?_eq_getElem next.isLt
  obtain ⟨_, _, _, _, slot, _, selected, slotIs, _⟩ := state.next unfinished
  refine ⟨atRow, slot, selected, by omega, ?_⟩
  rw [show slot.val = next.val + 1 by omega, bytecodeRow]
  simpa only [indexIs] using atRow

/-- Selection supplies the PC observation, so operand and RAM observations suffice
to extend represented rows; for example, an LD supplies its base and address. -/
theorem representsRows_push_selected
    {F : Type} [Field F] (joltField : JoltField F) {params : WitnessParams}
    (witness : WitnessType F params) {inst : JoltInstance SourceInstruction} {inputs : JoltPrivateInputs}
    (context : ConstraintContext inst inputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
    (trace : Trace) (step : TraceRow trace.bytecode)
    (old : RepresentsRows witness trace) (bound : trace.rows.size < params.traceLength)
    (slot : Fin (2 ^ params.logBytecodeK))
    (selected : bytecodeRa witness slot ⟨trace.rows.size, bound⟩ = 1)
    (slotIs : slot.val = step.rowIndex.val + 1)
    (rs1 : witness.Rs1Value ⟨trace.rows.size, bound⟩ =
      TraceWitness.Rs1Value params {trace with rows := trace.rows.push step} ⟨trace.rows.size, bound⟩)
    (rs2 : witness.Rs2Value ⟨trace.rows.size, bound⟩ =
      TraceWitness.Rs2Value params {trace with rows := trace.rows.push step} ⟨trace.rows.size, bound⟩)
    (ram : witness.RamAddress ⟨trace.rows.size, bound⟩ =
      TraceWitness.RamAddress params {trace with rows := trace.rows.push step} ⟨trace.rows.size, bound⟩) :
    RepresentsRows witness {trace with rows := trace.rows.push step} := by
  apply representsRows_push witness trace step old bound ?_ rs1 rs2 ram
  rw [pc_of_selected_bytecode (two_pow_127_lt_char joltField) context equations _ slot selected]
  simp only [TraceWitness.PC, TraceWitness.bytecodePc, Array.size_push, Nat.lt_add_one,
    ↓reduceDIte, Array.getElem_push_eq, slotIs]

/-- The selected row's two operand values and raw memory address supply all
append observations; for example, LD has a first operand, no second operand,
and an effective memory address, while JALR has no memory address. -/
theorem representsRows_push_operands
    {F : Type} [Field F] (joltField : JoltField F) {params : WitnessParams}
    (witness : WitnessType F params) {inst : JoltInstance SourceInstruction} {inputs : JoltPrivateInputs}
    (context : ConstraintContext inst inputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
    (trace : Trace) (step : TraceRow trace.bytecode)
    (old : RepresentsRows witness trace) (bound : trace.rows.size < params.traceLength)
    (slot : Fin (2 ^ params.logBytecodeK))
    (selected : bytecodeRa witness slot ⟨trace.rows.size, bound⟩ = 1)
    (slotIs : slot.val = step.rowIndex.val + 1)
    (rs1 : witness.Rs1Value ⟨trace.rows.size, bound⟩ =
      match rs1Operand? trace.bytecode[step.rowIndex].instruction with
      | some src => ((sourceValue src step.preState).toNat : F) | none => 0)
    (rs2 : witness.Rs2Value ⟨trace.rows.size, bound⟩ =
      match rs2Operand? trace.bytecode[step.rowIndex].instruction with
      | some src => ((sourceValue src step.preState).toNat : F) | none => 0)
    (ram : witness.RamAddress ⟨trace.rows.size, bound⟩ =
      match TraceWitness.ramAccessAddress trace.bytecode[step.rowIndex].instruction step.preState with
      | some address => (address.toNat : F) | none => 0) :
    RepresentsRows witness {trace with rows := trace.rows.push step} := by
  apply representsRows_push_selected joltField witness context equations trace step old bound slot selected slotIs
  · rw [rs1Value_real params _ _ (by simp only [Array.size_push]; exact Nat.lt_succ_self _)]
    simpa only [Array.getElem_push_eq] using rs1
  · rw [rs2Value_real params _ _ (by simp only [Array.size_push]; exact Nat.lt_succ_self _)]
    simpa only [Array.getElem_push_eq] using rs2
  · simpa only [TraceWitness.RamAddress, Array.size_push, Nat.lt_add_one,
      ↓reduceDIte, Array.getElem_push_eq] using ram

end JoltInstance
