import JoltConstraints.theorems.Completeness.Helpers.RamHistoryReplay
import JoltConstraints.translation.honest_witness_helpers.ram_val

open LeanRV64D JoltISA

set_option autoImplicit false

namespace JoltConstraints

/-- A selected captured read agrees with the shared word at that boundary;
unselected rows contribute zero.
For example, a store at index three does not constrain a captured read at index four. -/
private theorem ramHistoryReadAgreement
    {F : Type} [Field F] (params : WitnessParams)
    {inst : JoltInstance SourceInstruction} {inputs : JoltPrivateInputs}
    (trace : HonestTrace inst inputs) (valid : ramAccessesValid trace)
    (index : Fin params.ramSize) (cycle : Fin params.traceLength) :
    TraceWitness.RamRa (F := F) params trace index cycle *
      (HonestWitness.RamReadValue params trace cycle -
        ((ramHistoryWord trace index.val cycle.val).toNat : F)) = 0 := by
  cases selected : TraceWitness.remappedRamAddress trace cycle.val with
  | none => simp only [TraceWitness.RamRa, selected, reduceCtorEq, ite_false, zero_mul]
  | some chosen =>
    by_cases same : chosen = index.val
    · have inside : cycle.val < trace.rows.size := by
        by_contra outside
        simp only [TraceWitness.remappedRamAddress, dite_eq_right outside] at selected
        cases selected
      have read := ram_history_read_word (F := F) params trace valid cycle inside chosen selected
      rw [same] at read
      have agrees : HonestWitness.RamReadValue (F := F) params trace cycle =
          ((ramHistoryWord trace index.val cycle.val).toNat : F) := by
        simpa only [ramHistoryWord, dite_eq_left inside] using read
      rw [agrees, sub_self, mul_zero]
    · simp only [TraceWitness.RamRa, selected,
        show ¬ some chosen = some index.val from fun equal => same (Option.some.inj equal),
        ite_false, zero_mul]

/-- The replacement update used in witness materialization equals the selected
increment at the shared-memory boundary.
For example, a store replacing seven by five contributes minus two in the field. -/
private theorem ramHistoryReplacementDelta
    {F : Type} [Field F] (params : WitnessParams)
    {inst : JoltInstance SourceInstruction} {inputs : JoltPrivateInputs}
    (trace : HonestTrace inst inputs) (valid : ramAccessesValid trace)
    (index : Fin params.ramSize) (cycle : Fin params.traceLength) :
    TraceWitness.OpFlags (F := F) params trace .Store cycle *
        TraceWitness.RamRa params trace index cycle *
        (TraceWitness.RamWriteValue params trace cycle -
          ((ramHistoryWord trace index.val cycle.val).toNat : F)) =
      TraceWitness.RamRa params trace index cycle * HonestWitness.RamInc params trace cycle := by
  have increment : HonestWitness.RamInc (F := F) params trace cycle =
      TraceWitness.OpFlags params trace .Store cycle *
        (TraceWitness.RamWriteValue params trace cycle - HonestWitness.RamReadValue params trace cycle) := by
    by_cases inside : cycle.val < trace.rows.size
    · simp only [HonestWitness.RamInc, TraceWitness.OpFlags, dite_eq_left inside]
      split <;> simp only [ite_true, ite_false, one_mul, zero_mul]
    · simp only [HonestWitness.RamInc, TraceWitness.OpFlags, dite_eq_right inside, zero_mul]
  have read := ramHistoryReadAgreement (F := F) params trace valid index cycle
  rw [increment]
  calc
    _ = TraceWitness.RamRa params trace index cycle *
        (TraceWitness.OpFlags params trace .Store cycle *
          (TraceWitness.RamWriteValue params trace cycle - HonestWitness.RamReadValue params trace cycle)) +
        TraceWitness.OpFlags params trace .Store cycle *
          (TraceWitness.RamRa params trace index cycle *
            (HonestWitness.RamReadValue params trace cycle -
              ((ramHistoryWord trace index.val cycle.val).toNat : F))) := by ring
    _ = _ := by rw [read, mul_zero, add_zero]

/-- The honest RAM value column is exactly the word in shared memory before
that cycle, including padding.
For example, a load after an output store reads its stored word without an overlay exception. -/
theorem honestRamVal_eq_shared_word
    {F : Type} [Field F] (params : WitnessParams)
    {inst : JoltInstance SourceInstruction} {inputs : JoltPrivateInputs}
    (trace : HonestTrace inst inputs) (fits : params.RamFits trace)
    (valid : ramAccessesValid trace) (index : Fin params.ramSize) (cycle : Fin params.traceLength) :
    HonestWitness.RamVal (F := F) params trace index cycle =
      ((ramHistoryWord trace index.val cycle.val).toNat : F) := by
  let step (before : F) (current : Fin params.traceLength) : F :=
    before + TraceWitness.OpFlags params trace .Store current *
      TraceWitness.RamRa params trace index current *
        (TraceWitness.RamWriteValue params trace current - before)
  let state (n : Nat) : F := ((ramHistoryWord trace index.val n).toNat : F)
  have transition (current : Fin params.traceLength) :
      step (state current.val) current = state (current.val + 1) := by
    dsimp only [step, state]
    rw [ramHistoryReplacementDelta params trace valid index current]
    exact (ramHistoryWord_step params trace fits valid index current).symm
  have replay := prefix_foldl_eq_sequence step state transition cycle.val (le_of_lt cycle.isLt)
  dsimp only [state, step] at replay
  rw [ramHistoryWord_zero] at replay
  unfold HonestWitness.RamVal
  dsimp only
  rw [replay]
  rw [ramHistoryReadAgreement params trace valid index cycle, add_zero]

end JoltConstraints
