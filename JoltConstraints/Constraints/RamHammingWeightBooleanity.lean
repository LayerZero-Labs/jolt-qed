import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.honest_witness

set_option autoImplicit false

namespace JoltConstraints

/-- Constraint (57) in `constraints.md` (stage 6b):
the RAM hamming-weight flag is Boolean at every padded cycle.
Rust: https://github.com/abiswas3/jolt/tree/main/crates/jolt-claims/src/protocols/jolt/relations/ram/hamming_booleanity.rs#L89-L93 -/
def ramHammingWeightBooleanity {F : Type} [Field F] {params : WitnessParams}
    (witness : WitnessType F params) : Prop :=
  ∀ t : Fin params.traceLength,
    witness.RamHammingWeight t * (witness.RamHammingWeight t - 1) = 0

/-- The honest witness satisfies constraint (57); proof pending. -/
theorem honestWitness_ramHammingWeightBooleanity
    {F : Type} [Field F] (params : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program)
    (ramFits : params.RamFits trace)
    (traceFits : trace.rows.size ≤ params.traceLength) :
    ramHammingWeightBooleanity
      (JoltProgram.honestWitness (F := F) params trace ramFits traceFits) := by
  sorry

end JoltConstraints
