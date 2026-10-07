import JoltConstraints.Constraints.RamWriteValueEqRamReadWrite
import JoltConstraints.Constraints.RamReadSelection

set_option autoImplicit false

namespace JoltConstraints

open scoped BigOperators

/-- Completeness target for the honest witness.
Nonzero accessed addresses and RamFits exclude cold selectors on real memory accesses. -/
theorem honestWitness_ramWriteValueEqRamReadWrite
    {F : Type} [Field F] (params : WitnessParams)
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (ramFits : params.RamFits trace)
    (traceFits : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor trace.bytecode.size)
    (validAccesses : ramAccessesValid trace)
    : ramWriteValueEqRamReadWrite
      (HonestTrace.honestWitness (F := F) params trace) := by
  intro t
  change HonestWitness.RamWriteValue (F := F) params trace t =
    ∑ address : Fin params.ramSize,
      HonestWitness.RamRa params trace address t *
        (HonestWitness.RamVal params trace address t +
          HonestWitness.RamInc params trace t)
  cases hr : HonestWitness.remappedRamAddress trace t.val with
  | none =>
      rw [ramRa_sum_none params trace ramFits t hr]
      exact ramWriteValue_zero_of_remapped_none params trace ramFits validAccesses t hr
  | some b =>
      rw [ramRa_sum_some params trace ramFits t b hr]
      dsimp [HonestWitness.RamVal]
      simp [HonestWitness.RamRa, hr]
      exact ramWriteValue_eq_read_add_inc params trace t

end JoltConstraints
