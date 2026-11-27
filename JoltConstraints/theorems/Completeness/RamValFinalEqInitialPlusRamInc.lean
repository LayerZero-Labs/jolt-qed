import JoltConstraints.translation.honest_witness
import JoltConstraints.translation.Constraints.RamValFinalEqInitialPlusRamInc
import JoltConstraints.theorems.Completeness.Helpers.RamHistoryReplay

open LeanRV64D

set_option autoImplicit false

namespace JoltConstraints

open scoped BigOperators

/-- Every final shared-memory word equals its initial image plus the selected
write increments of the honest witness.
For example, a value-preserving protected store contributes zero, and an I/O
gap store contributes its actual new word minus its old word.
Jolt at `ff6fc6568`: `crates/jolt-claims/src/protocols/jolt/relations/ram/val_check.rs`
(`RamValCheck`). -/
theorem honestWitness_ramValFinalEqInitialPlusRamInc
    {F : Type} [Field F] (params : WitnessParams)
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (ramFits : params.RamFits trace)
    (validAccesses : ramAccessesValid trace)
    (traceFits : params.ProverPaddedFor trace.rows.size)
    (_bytecodeDomain : params.BytecodeDomainFor trace.bytecode.size)
    : ramValFinalEqInitialPlusRamInc (TraceWitness.initialRamWord trace)
      (HonestTrace.honestWitness (F := F) params trace) := by
  intro address
  change ((TraceWitness.finalRamWord trace address.val).toNat : F) =
    ((TraceWitness.initialRamWord trace address.val).toNat : F) +
      ∑ cycle : Fin params.traceLength,
        TraceWitness.RamRa params trace address cycle * HonestWitness.RamInc params trace cycle
  have summed := ramHistoryWord_eq_prefix (F := F) params trace ramFits validAccesses
    address params.traceLength (le_refl _)
  rw [ramHistoryWord_final trace address.val params.traceLength traceFits.traceFits] at summed
  simpa only [Fin.isLt, ite_true] using summed

end JoltConstraints
