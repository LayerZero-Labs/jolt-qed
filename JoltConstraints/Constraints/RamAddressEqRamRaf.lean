import JoltConstraints.Constraints.RamReadSelection

set_option autoImplicit false

namespace JoltConstraints

open scoped BigOperators

/-- Constraint (25) in `constraints.md`:
Recover the raw byte address from the selected remapped word address.
Rust: https://github.com/abiswas3/jolt/tree/main/crates/jolt-verifier/src/stages/stage2/ram_raf_evaluation.rs#L133-L151 -/
def ramAddressEqRamRaf {F : Type} [Field F] {params : WitnessParams}
    (layout : JoltIOLayout) (witness : WitnessType F params) : Prop :=
  ∀ t : Fin params.traceLength,
    witness.RamAddress t =
      ∑ address : Fin params.ramSize,
        ((ramLowestAddress layout + 8 * address.val : Nat) : F) * witness.RamRa address t

/-- Completeness target for the honest witness.
Alignment is required because Rust remaps byte addresses by integer division by eight. -/
theorem honestWitness_ramAddressEqRamRaf
    {F : Type} [Field F] (params : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program)
    (ramFits : params.RamFits trace)
    (traceFits : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor program.expandedBytecode.size)
    (validAccesses : ramAccessesValid trace)
    : ramAddressEqRamRaf program.initialState.io.layout
      (JoltProgram.honestWitness (F := F) params trace ramFits traceFits bytecodeDomain) := by
  intro t
  change HonestWitness.RamAddress (F := F) params trace t =
    ∑ address : Fin params.ramSize,
      ((ramLowestAddress program.initialState.io.layout + 8 * address.val : Nat) : F) *
        HonestWitness.RamRa params trace ramFits address t
  have hswap :
      (∑ address : Fin params.ramSize,
        ((ramLowestAddress program.initialState.io.layout + 8 * address.val : Nat) : F) *
          HonestWitness.RamRa params trace ramFits address t) =
      ∑ address : Fin params.ramSize,
        HonestWitness.RamRa params trace ramFits address t *
          ((ramLowestAddress program.initialState.io.layout + 8 * address.val : Nat) : F) := by
    apply Finset.sum_congr rfl
    intro address _
    ring
  rw [hswap]
  cases hr : HonestWitness.remappedRamAddress trace t.val with
  | none =>
      rw [ramRa_sum_none params trace ramFits t hr]
      by_cases ht : t.val < trace.rows.size
      · cases ha : HonestWitness.ramAccessAddress
          (getElem program.expandedBytecode (getElem trace.rows t.val ht).rowIndex.val
            (getElem trace.rows t.val ht).rowIndex.isLt).instruction
          (getElem trace.rows t.val ht).preState with
        | none => simp [HonestWitness.RamAddress, ht, ha]
        | some raw =>
            obtain ⟨b, hb⟩ := ramAccess_remapped_some params trace ramFits
              validAccesses t ht raw ha
            rw [hr] at hb
            contradiction
      · simp [HonestWitness.RamAddress, ht]
  | some b =>
      rw [ramRa_sum_some params trace ramFits t b hr]
      by_cases ht : t.val < trace.rows.size
      · cases ha : HonestWitness.ramAccessAddress
          (getElem program.expandedBytecode (getElem trace.rows t.val ht).rowIndex.val
            (getElem trace.rows t.val ht).rowIndex.isLt).instruction
          (getElem trace.rows t.val ht).preState with
        | none =>
            simp [HonestWitness.remappedRamAddress, ht, ha] at hr
        | some raw =>
            have hremap : HonestWitness.remapRamAddress
                program.initialState.io.layout raw = some b := by
              simpa [HonestWitness.remappedRamAddress, ht, ha] using hr
            have hv := validAccesses ⟨t.val, ht⟩
            change (match HonestWitness.ramAccessAddress
              (getElem program.expandedBytecode (getElem trace.rows t.val ht).rowIndex.val
                (getElem trace.rows t.val ht).rowIndex.isLt).instruction
              (getElem trace.rows t.val ht).preState with
              | none => True
              | some address => address.toNat ≠ 0 ∧
                  (address.toNat - ramLowestAddress program.initialState.io.layout) % 8 = 0) at hv
            simp only [ha] at hv
            unfold HonestWitness.remapRamAddress at hremap
            dsimp at hremap
            split_ifs at hremap with hfail
            have hb : (raw.toNat - ramLowestAddress program.initialState.io.layout) / 8 = b :=
              Option.some.inj hremap
            have hraw : raw.toNat =
                ramLowestAddress program.initialState.io.layout + 8 * b := by
              dsimp [ramLowestAddress] at hb hv hfail ⊢
              omega
            simp [HonestWitness.RamAddress, ht, ha, hraw]
      · simp [HonestWitness.remappedRamAddress, ht] at hr

end JoltConstraints
