import JoltConstraints.theorems.Completeness.Helpers.RamHistoryProofHelpers

open LeanRV64D JoltISA

set_option autoImplicit false

namespace JoltConstraints

open scoped BigOperators

/-- The shared word before cycle `n`, or the final word after the real rows end.
For example, padding after a one-row panic trace observes its final memory. -/
noncomputable def ramHistoryWord (trace : Trace) (index n : Nat) : BitVec 64 :=
  let mem := if inside : n < trace.rows.size then (trace.rows[n]'inside).preState.sail.mem
    else (TraceWitness.finalTraceState trace).sail.mem
  Mmu.ram_doubleword mem
    (ramLowestAddress trace.initialState.jolt_device.memory_layout + 8 * index)

/-- The first pre-state uses the initialized shared byte map.
For example, preparing the entry PC changes no input or RAM byte. -/
theorem ramHistoryWord_zero
    {inst : JoltInstance SourceInstruction} {inputs : JoltPrivateInputs}
    (trace : HonestTrace inst inputs) (index : Nat) :
    ramHistoryWord trace index 0 = TraceWitness.initialRamWord trace index := by
  have start := trace.startsAtInitial trace.nonempty
  simp only [ramHistoryWord, dite_eq_left trace.nonempty]
  rw [start]
  simp only [TraceWitness.initialRamWord, TraceWitness.initialRamWordFromState,
    MemoryLayout.get_lowest_address_toNat]
  rfl

/-- The next pre-state and the final snapshot use the preceding post-state's
shared memory; for example, preparing the next source PC preserves stored bytes. -/
theorem ramHistoryWord_next
    {inst : JoltInstance SourceInstruction} {inputs : JoltPrivateInputs}
    (trace : HonestTrace inst inputs) (index n : Nat) (inside : n < trace.rows.size) :
    ramHistoryWord trace index (n + 1) =
      Mmu.ram_doubleword (trace.rows[n]'inside).postState.sail.mem
        (ramLowestAddress trace.initialState.jolt_device.memory_layout + 8 * index) := by
  by_cases nextInside : n + 1 < trace.rows.size
  · have linked := trace.linkedState n inside nextInside
    simp only [ramHistoryWord, dite_eq_left nextInside]
    rw [linked]
    split <;> rfl
  · have last : trace.rows.size - 1 = n := by omega
    simp only [ramHistoryWord, dite_eq_right nextInside, TraceWitness.finalTraceState,
      dite_eq_left trace.nonempty, last]

/-- The shared word has its final snapshot value after the real rows end.
For example, every padding cycle sees the same final output bytes. -/
theorem ramHistoryWord_final (trace : Trace) (index n : Nat)
    (finished : trace.rows.size ≤ n) :
    ramHistoryWord trace index n = TraceWitness.finalRamWord trace index := by
  simp only [ramHistoryWord, dite_eq_right (Nat.not_lt.mpr finished), TraceWitness.finalRamWord,
    MemoryLayout.get_lowest_address_toNat]
  rfl

/-- The shared word advances by the selected RAM increment at every witness
cycle, including padding with increment zero. -/
theorem ramHistoryWord_step
    {F : Type} [Field F] (params : WitnessParams)
    {inst : JoltInstance SourceInstruction} {inputs : JoltPrivateInputs}
    (trace : HonestTrace inst inputs) (fits : params.RamFits trace)
    (valid : ramAccessesValid trace) (index : Fin params.ramSize)
    (cycle : Fin params.traceLength) :
    ((ramHistoryWord trace index.val (cycle.val + 1)).toNat : F) =
      ((ramHistoryWord trace index.val cycle.val).toNat : F) +
        TraceWitness.RamRa params trace index cycle * HonestWitness.RamInc params trace cycle := by
  by_cases inside : cycle.val < trace.rows.size
  · rw [ramHistoryWord_next trace index.val cycle.val inside]
    simpa only [ramHistoryWord, dite_eq_left inside] using
      ram_history_word_step (F := F) params trace fits valid cycle inside index
  · rw [ramHistoryWord_final trace index.val _ (by omega),
      ramHistoryWord_final trace index.val _ (by omega)]
    simp only [HonestWitness.RamInc, dite_eq_right inside, mul_zero, add_zero]

/-- The shared memory at any witness boundary is the initial image plus all
strictly preceding selected increments, including the final boundary. -/
theorem ramHistoryWord_eq_prefix
    {F : Type} [Field F] (params : WitnessParams)
    {inst : JoltInstance SourceInstruction} {inputs : JoltPrivateInputs}
    (trace : HonestTrace inst inputs) (fits : params.RamFits trace)
    (valid : ramAccessesValid trace) (index : Fin params.ramSize)
    (n : Nat) (bound : n ≤ params.traceLength) :
    ((ramHistoryWord trace index.val n).toNat : F) =
      ((TraceWitness.initialRamWord trace index.val).toNat : F) +
        ∑ cycle : Fin params.traceLength, if cycle.val < n then
          TraceWitness.RamRa params trace index cycle * HonestWitness.RamInc params trace cycle else 0 := by
  have summed := sequence_eq_prefix_sum
    (fun n => ((ramHistoryWord trace index.val n).toNat : F))
    (fun cycle => TraceWitness.RamRa params trace index cycle * HonestWitness.RamInc params trace cycle)
    (ramHistoryWord_step params trace fits valid index) n bound
  simpa only [ramHistoryWord_zero] using summed

end JoltConstraints
