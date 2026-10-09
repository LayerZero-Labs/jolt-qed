import JoltConstraints.honest_witness
import JoltConstraints.Constraints.RamValFinalEqInitialPlusRamInc
import JoltConstraints.Constraints.RamReadData
import JoltConstraints.Completeness.Helpers.RamAccesses

set_option autoImplicit false

namespace JoltConstraints

open scoped BigOperators

/-- Completeness target for the honest witness.
FIXME: false until a16z/jolt#1951 item 1 is fixed. When a run does not panic and
never stores to the termination word (e.g. a program that is just `j .`), the
tracer records no write to it, but witness generation (jolt-witness's
final_ram_state, not the tracer) sets that word to 1 from the panic flag alone.
Initial RAM holds 0 there and no row adds an increment, so this constraint reads
1 = 0. Lean's witness does the same.
Also check #1951 item 2 (other stores to the panic or termination words) before
attempting this theorem. -/
theorem honestWitness_ramValFinalEqInitialPlusRamInc
    {F : Type} [Field F] (params : WitnessParams)
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (ramFits : params.RamFits trace)
    (validAccesses : ramAccessesValid trace)
    (traceFits : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor trace.bytecode.size)
    : ramValFinalEqInitialPlusRamInc (TraceWitness.initialRamWord trace)
      (HonestTrace.honestWitness (F := F) params trace) := by
  sorry

end JoltConstraints
