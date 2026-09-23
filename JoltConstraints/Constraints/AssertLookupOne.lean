import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.honest_witness

set_option autoImplicit false

namespace JoltConstraints

/-- Constraint (12) in `constraints.md` (stage 1):
assertion rows require lookup output one.
Rust: https://github.com/abiswas3/jolt/tree/main/crates/jolt-r1cs/src/constraints/rv64.rs -/
def assertLookupOne {F : Type} [Field F] {params : WitnessParams}
    (witness : WitnessType F params) : Prop :=
  ∀ t : Fin params.traceLength,
    witness.OpFlags .Assert t * (witness.LookupOutput t - 1) = 0

/-- Unrestricted completeness statement to investigate, not an admitted theorem.
Rust's intentional VirtualAssertEQ spoil mode can violate this claim.
The original constraint is retained, with no assumption excluding the example. -/
def honestWitness_assertLookupOneStatement
    {F : Type} [Field F] (params : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program)
    (ramFits : params.RamFits trace)
    (traceFits : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor program.expandedBytecode.size) : Prop :=
    assertLookupOne
      (JoltProgram.honestWitness (F := F) params trace ramFits traceFits bytecodeDomain)

end JoltConstraints
