import JoltConstraints.translation.honest_trace

open LeanRV64D
set_option autoImplicit false
namespace JoltConstraints.Soundness

/-- Reading row `k` before the cut gives the same optional row in the prefix.
For example, row 1 is unchanged by a cut after row 3. -/
private theorem extract_getElem?_before {α : Type} (rows : Array α)
    (n k : Nat) (within : n ≤ rows.size) (before : k < n) :
    (rows.extract 0 n)[k]? = rows[k]? := by
  simp only [Array.getElem?_extract, Nat.min_eq_left within, Nat.sub_zero,
    Nat.zero_add, ite_eq_left before]

/-- The flag that row `k` starts an expansion is unchanged before a cut.
For example, an ECALL expansion start at row 2 remains a start after row 3. -/
private theorem stepNOfTraceIsStartOfNewExpansion_extract
    {bytecode : Array JoltInstructionRow} (rows : Array (TraceRow bytecode))
    (n k : Nat) (within : n ≤ rows.size) (before : k < n) :
    stepNOfTraceIsStartOfNewExpansion (rows.extract 0 n) k =
      stepNOfTraceIsStartOfNewExpansion rows k := by
  simp only [stepNOfTraceIsStartOfNewExpansion,
    extract_getElem?_before rows n k within before]

/-- The expansion containing row `k` begins at the same row in a prefix.
For example, the start of a DIV expansion at row 2 remains row 2 after a later cut. -/
private theorem startOfExpansionContainingStepN_extract
    {bytecode : Array JoltInstructionRow} (rows : Array (TraceRow bytecode))
    (n k : Nat) (within : n ≤ rows.size) (before : k < n) :
    startOfExpansionContainingStepN (rows.extract 0 n) k =
      startOfExpansionContainingStepN rows k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [startOfExpansionContainingStepN,
        stepNOfTraceIsStartOfNewExpansion_extract rows n (k + 1) within before]
      by_cases h : stepNOfTraceIsStartOfNewExpansion rows (k + 1)
      · simp [h]
      · simp [h, ih (by omega)]

/-- The VirtualAdvice flag at row `k` is unchanged before a cut.
For example, row 2 remains an advice row in a prefix ending after row 3. -/
private theorem stepNOfTraceIsAdvice_extract
    {bytecode : Array JoltInstructionRow} (rows : Array (TraceRow bytecode))
    (n k : Nat) (within : n ≤ rows.size) (before : k < n) :
    stepNOfTraceIsAdvice (rows.extract 0 n) k = stepNOfTraceIsAdvice rows k := by
  simp only [stepNOfTraceIsAdvice, extract_getElem?_before rows n k within before]

/-- The number of earlier advice rows in an expansion is unchanged by a later cut.
For example, a DIV advice row still sees the same earlier advice count. -/
private theorem adviceStepsBeforeStepN_extract
    {bytecode : Array JoltInstructionRow} (rows : Array (TraceRow bytecode))
    (n i : Nat) (within : n ≤ rows.size) (earlier : i < n) :
    adviceStepsBeforeStepN (rows.extract 0 n) i = adviceStepsBeforeStepN rows i := by
  simp only [adviceStepsBeforeStepN,
    startOfExpansionContainingStepN_extract rows n i within earlier]
  congr 1
  apply List.filter_congr
  intro k hk
  have hk' : k < i := by
    rw [List.mem_range'] at hk
    obtain ⟨j, hj, rfl⟩ := hk
    omega
  exact stepNOfTraceIsAdvice_extract rows n k within (by omega)

/-- Honest tracer advice at row `i` depends only on rows through `i`.
For example, truncating a five-row DIV trace after row 3 preserves row 2's advice. -/
theorem honestTracerAdviceAtStepN_extract
    (program : Rv64ProgramImage SourceInstruction)
    {bytecode : Array JoltInstructionRow} (rows : Array (TraceRow bytecode))
    (n i : Nat) (within : n ≤ rows.size) (earlier : i < n) :
    honestTracerAdviceAtStepN program (rows.extract 0 n) i =
      honestTracerAdviceAtStepN program rows i := by
  simp only [honestTracerAdviceAtStepN,
    extract_getElem?_before rows n i within earlier,
    startOfExpansionContainingStepN_extract rows n i within earlier,
    adviceStepsBeforeStepN_extract rows n i within earlier]
  have hstart : startOfExpansionContainingStepN rows i ≤ i := by
    induction i with
    | zero => simp [startOfExpansionContainingStepN]
    | succ i ih =>
        simp only [startOfExpansionContainingStepN]
        split
        · omega
        · omega
  rw [extract_getElem?_before rows n (startOfExpansionContainingStepN rows i)
    within (by omega)]

end JoltConstraints.Soundness
