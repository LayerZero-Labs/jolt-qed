import JoltConstraints.translation.honest_witness
import JoltConstraints.translation.Constraints.RamValEqInitialPlusPrefixRamInc
import JoltConstraints.theorems.Completeness.Helpers.RamValReplay

open LeanRV64D

set_option autoImplicit false

namespace JoltConstraints

open scoped BigOperators

/-- Every honest pre-cycle RAM word equals its initial image plus the strictly
earlier selected store increments.
For example, a load after a store reads the stored shared word in both I/O and RAM.
Jolt at `ff6fc6568`: `crates/jolt-claims/src/protocols/jolt/relations/ram/val_check.rs`
(`RamValCheck`). -/
theorem honestWitness_ramValEqInitialPlusPrefixRamInc
    {F : Type} [Field F] (params : WitnessParams)
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (ramFits : params.RamFits trace)
    (traceFits : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor trace.bytecode.size)
    (validAccesses : ramAccessesValid trace)
    : ramValEqInitialPlusPrefixRamInc (ramInitialValue (TraceWitness.initialRamWord trace))
      (HonestTrace.honestWitness (F := F) params trace) := by
  intro address cycle
  change HonestWitness.RamVal (F := F) params trace address cycle =
    ((TraceWitness.initialRamWord trace address.val).toNat : F) +
      ∑ current : Fin params.traceLength, if current.val < cycle.val then
        TraceWitness.RamRa params trace address current * HonestWitness.RamInc params trace current else 0
  rw [honestRamVal_eq_shared_word params trace ramFits validAccesses address cycle]
  exact ramHistoryWord_eq_prefix params trace ramFits validAccesses address cycle.val (le_of_lt cycle.isLt)

end JoltConstraints
