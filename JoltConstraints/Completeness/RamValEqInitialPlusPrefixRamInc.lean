import JoltConstraints.honest_witness
import JoltConstraints.Constraints.RamValEqInitialPlusPrefixRamInc
import JoltConstraints.Constraints.RamReadData
import JoltConstraints.Completeness.Helpers.RamAccesses

set_option autoImplicit false

namespace JoltConstraints

open scoped BigOperators

/-- Completeness target for the honest witness; blocked by a Rust completeness
counterexample. A store to the termination word records an increment of one,
but the device ignores that write and a later load reads zero. The Rust witness
sets `RamVal` to that captured zero, violating the strict prefix sum. See
`bug-report/ram-val-termination/README.md`. The Lean model preserves the same
device behavior; do not narrow the theorem to exclude this Rust-accepted trace. -/
theorem honestWitness_ramValEqInitialPlusPrefixRamInc
    {F : Type} [Field F] (params : WitnessParams)
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (ramFits : params.RamFits trace)
    (traceFits : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor trace.bytecode.size)
    (validAccesses : ramAccessesValid trace)
    : ramValEqInitialPlusPrefixRamInc (TraceWitness.initialRamWord trace)
      (HonestTrace.honestWitness (F := F) params trace) := by
  sorry

end JoltConstraints
