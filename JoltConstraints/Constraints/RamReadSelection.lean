import JoltConstraints.Constraints.RamReadData

set_option autoImplicit false

namespace JoltConstraints

open scoped BigOperators

/-- A missing RAM address has no hot selector. -/
theorem ramRa_sum_none {F : Type} [Field F] (params : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program)
    (ramFits : params.RamFits trace)
    (t : Fin params.traceLength)
    (hnone : HonestWitness.remappedRamAddress trace t.val = none)
    (value : Fin params.ramSize → F) :
    (∑ address : Fin params.ramSize,
      HonestWitness.RamRa params trace ramFits address t * value address) = 0 := by
  simp [HonestWitness.RamRa, hnone]

/-- A present RAM address selects precisely its remapped word. -/
theorem ramRa_sum_some {F : Type} [Field F] (params : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program)
    (ramFits : params.RamFits trace)
    (t : Fin params.traceLength) (b : Nat)
    (hsome : HonestWitness.remappedRamAddress trace t.val = some b)
    (value : Fin params.ramSize → F) :
    (∑ address : Fin params.ramSize,
      HonestWitness.RamRa params trace ramFits address t * value address) =
      value ⟨b, params.remappedRamAddress_lt trace ramFits t b hsome⟩ := by
  let selected : Fin params.ramSize :=
    ⟨b, params.remappedRamAddress_lt trace ramFits t b hsome⟩
  have hsel : ∀ address : Fin params.ramSize,
      (some b = some address.val) ↔ address = selected := by
    intro address
    simp [selected, Fin.ext_iff, eq_comm]
  simp_rw [HonestWitness.RamRa, hsome, hsel]
  simp [Finset.sum_ite_eq', selected]

/-- A recorded memory access has a hot RAM selector in a valid trace. -/
theorem ramAccess_remapped_some (params : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program)
    (ramFits : params.RamFits trace)
    (validAccesses : ramAccessesValid trace)
    (t : Fin params.traceLength) (ht : t.val < trace.rows.size)
    (raw : BitVec 64)
    (hraw : HonestWitness.ramAccessAddress
      (getElem program.expandedBytecode (getElem trace.rows t.val ht).rowIndex.val
        (getElem trace.rows t.val ht).rowIndex.isLt).instruction
      (getElem trace.rows t.val ht).preState = some raw) :
    ∃ b, HonestWitness.remappedRamAddress trace t.val = some b := by
  have hf := ramFits ⟨t.val, ht⟩
  have hv := validAccesses ⟨t.val, ht⟩
  have hf' : raw = 0 ∨ ∃ b : Nat,
      HonestWitness.remapRamAddress program.initialState.io.layout raw = some b ∧
      b < params.ramSize := by
    simpa only [hraw] using hf
  have hv' : raw.toNat ≠ 0 ∧
      (raw.toNat - ramLowestAddress program.initialState.io.layout) % 8 = 0 := by
    change (match HonestWitness.ramAccessAddress
      (getElem program.expandedBytecode (getElem trace.rows t.val ht).rowIndex.val
        (getElem trace.rows t.val ht).rowIndex.isLt).instruction
      (getElem trace.rows t.val ht).preState with
      | none => True
      | some address => address.toNat ≠ 0 ∧
          (address.toNat - ramLowestAddress program.initialState.io.layout) % 8 = 0) at hv
    simpa only [hraw] using hv
  rcases hf' with hz | ⟨b, hremap, _⟩
  · exact False.elim (hv'.1 (by simp [hz]))
  · refine ⟨b, ?_⟩
    simp [HonestWitness.remappedRamAddress, ht, hraw, hremap]

theorem ramReadValue_zero_of_noaccess {F : Type} [Field F]
    (params : WitnessParams) {program : JoltProgram}
    (trace : JoltTrace program) (t : Fin params.traceLength)
    (ht : t.val < trace.rows.size)
    (hnoaccess : HonestWitness.ramAccessAddress
      (getElem program.expandedBytecode (getElem trace.rows t.val ht).rowIndex.val
        (getElem trace.rows t.val ht).rowIndex.isLt).instruction
      (getElem trace.rows t.val ht).preState = none) :
    HonestWitness.RamReadValue (F := F) params trace t = 0 := by
  cases hi : (getElem program.expandedBytecode (getElem trace.rows t.val ht).rowIndex.val
    (getElem trace.rows t.val ht).rowIndex.isLt).instruction <;>
    simp [HonestWitness.ramAccessAddress, hi] at hnoaccess
  all_goals simp [HonestWitness.RamReadValue, ht, hi]

theorem ramWriteValue_zero_of_noaccess {F : Type} [Field F]
    (params : WitnessParams) {program : JoltProgram}
    (trace : JoltTrace program) (t : Fin params.traceLength)
    (ht : t.val < trace.rows.size)
    (hnoaccess : HonestWitness.ramAccessAddress
      (getElem program.expandedBytecode (getElem trace.rows t.val ht).rowIndex.val
        (getElem trace.rows t.val ht).rowIndex.isLt).instruction
      (getElem trace.rows t.val ht).preState = none) :
    HonestWitness.RamWriteValue (F := F) params trace t = 0 := by
  cases hi : (getElem program.expandedBytecode (getElem trace.rows t.val ht).rowIndex.val
    (getElem trace.rows t.val ht).rowIndex.isLt).instruction <;>
    simp [HonestWitness.ramAccessAddress, hi] at hnoaccess
  all_goals simp [HonestWitness.RamWriteValue, ht, hi]

theorem ramReadValue_zero_of_remapped_none {F : Type} [Field F]
    (params : WitnessParams) {program : JoltProgram}
    (trace : JoltTrace program) (ramFits : params.RamFits trace)
    (validAccesses : ramAccessesValid trace) (t : Fin params.traceLength)
    (hnone : HonestWitness.remappedRamAddress trace t.val = none) :
    HonestWitness.RamReadValue (F := F) params trace t = 0 := by
  by_cases ht : t.val < trace.rows.size
  · cases ha : HonestWitness.ramAccessAddress
      (getElem program.expandedBytecode (getElem trace.rows t.val ht).rowIndex.val
        (getElem trace.rows t.val ht).rowIndex.isLt).instruction
      (getElem trace.rows t.val ht).preState with
    | none => exact ramReadValue_zero_of_noaccess params trace t ht ha
    | some raw =>
        obtain ⟨b, hb⟩ := ramAccess_remapped_some params trace ramFits
          validAccesses t ht raw ha
        rw [hnone] at hb
        contradiction
  · simp [HonestWitness.RamReadValue, ht]

theorem ramWriteValue_zero_of_remapped_none {F : Type} [Field F]
    (params : WitnessParams) {program : JoltProgram}
    (trace : JoltTrace program) (ramFits : params.RamFits trace)
    (validAccesses : ramAccessesValid trace) (t : Fin params.traceLength)
    (hnone : HonestWitness.remappedRamAddress trace t.val = none) :
    HonestWitness.RamWriteValue (F := F) params trace t = 0 := by
  by_cases ht : t.val < trace.rows.size
  · cases ha : HonestWitness.ramAccessAddress
      (getElem program.expandedBytecode (getElem trace.rows t.val ht).rowIndex.val
        (getElem trace.rows t.val ht).rowIndex.isLt).instruction
      (getElem trace.rows t.val ht).preState with
    | none => exact ramWriteValue_zero_of_noaccess params trace t ht ha
    | some raw =>
        obtain ⟨b, hb⟩ := ramAccess_remapped_some params trace ramFits
          validAccesses t ht raw ha
        rw [hnone] at hb
        contradiction
  · simp [HonestWitness.RamWriteValue, ht]

/-- The captured write value differs from the read value only on stores. -/
theorem ramWriteValue_eq_read_add_inc {F : Type} [Field F]
    (params : WitnessParams) {program : JoltProgram}
    (trace : JoltTrace program) (t : Fin params.traceLength) :
    HonestWitness.RamWriteValue (F := F) params trace t =
      HonestWitness.RamReadValue params trace t +
        HonestWitness.RamInc params trace t := by
  by_cases ht : t.val < trace.rows.size
  · cases hi : (getElem program.expandedBytecode (getElem trace.rows t.val ht).rowIndex.val
      (getElem trace.rows t.val ht).rowIndex.isLt).instruction
    all_goals simp [HonestWitness.RamWriteValue, HonestWitness.RamReadValue,
      HonestWitness.RamInc, JoltMetadata.circuitFlag, hi, ht]
    all_goals split <;> simp_all [JoltMetadata.opcodeFlag]
    case h_3 =>
      rename_i bad
      exact False.elim (bad _ _ _ _ rfl rfl rfl rfl)
  · simp [HonestWitness.RamWriteValue, HonestWitness.RamReadValue,
      HonestWitness.RamInc, ht]

end JoltConstraints
