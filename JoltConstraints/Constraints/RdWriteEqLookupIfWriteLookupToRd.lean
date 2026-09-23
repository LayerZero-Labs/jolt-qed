import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.honest_witness

set_option autoImplicit false

namespace JoltConstraints

/-- Constraint (13) in `constraints.md` (stage 1):
rows with WriteLookupOutputToRD copy the lookup output to the destination.
Rust: https://github.com/abiswas3/jolt/tree/main/crates/jolt-r1cs/src/constraints/rv64.rs -/
def rdWriteEqLookupIfWriteLookupToRd {F : Type} [Field F] {params : WitnessParams}
    (witness : WitnessType F params) : Prop :=
  ∀ t : Fin params.traceLength,
    witness.OpFlags .WriteLookupOutputToRD t *
      (witness.RdWriteValue t - witness.LookupOutput t) = 0

/-- Unrestricted completeness statement to investigate, not an admitted theorem.
Rust's CSRRS x0,mstatus,x0 expansion can violate this claim.
The original constraint is retained, with no assumption excluding the example. -/
def honestWitness_rdWriteEqLookupIfWriteLookupToRdStatement
    {F : Type} [Field F] (params : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program)
    (ramFits : params.RamFits trace)
    (traceFits : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor program.expandedBytecode.size) : Prop :=
    rdWriteEqLookupIfWriteLookupToRd
      (JoltProgram.honestWitness (F := F) params trace ramFits traceFits bytecodeDomain)

end JoltConstraints
