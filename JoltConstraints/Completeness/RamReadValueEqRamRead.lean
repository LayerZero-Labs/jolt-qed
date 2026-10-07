import JoltConstraints.Constraints.RamReadValueEqRamRead
import JoltConstraints.Constraints.RamReadSelection

set_option autoImplicit false

namespace JoltConstraints

open scoped BigOperators

/-- Completeness target for the honest witness.
Nonzero accessed addresses and RamFits exclude cold selectors on real memory accesses. -/
theorem honestWitness_ramReadValueEqRamRead
    {F : Type} [Field F] (params : WitnessParams)
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (ramFits : params.RamFits trace)
    (traceFits : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor trace.bytecode.size)
    (validAccesses : ramAccessesValid trace)
    : ramReadValueEqRamRead
      (HonestTrace.honestWitness (F := F) params trace) := by
  intro t
  change HonestWitness.RamReadValue (F := F) params trace t =
    ∑ address : Fin params.ramSize,
      HonestWitness.RamRa params trace address t *
        HonestWitness.RamVal params trace address t
  cases hr : HonestWitness.remappedRamAddress trace t.val with
  | none =>
      rw [ramRa_sum_none params trace ramFits t hr]
      exact ramReadValue_zero_of_remapped_none params trace ramFits validAccesses t hr
  | some b =>
      rw [ramRa_sum_some params trace ramFits t b hr]
      dsimp [HonestWitness.RamVal]
      simp [HonestWitness.RamRa, hr]

end JoltConstraints
