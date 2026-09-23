import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.honest_witness
import JoltConstraints.execution_conditions

set_option autoImplicit false

namespace JoltConstraints

/-- Constraint (19) in `constraints.md` (stage 1):
entering an interior virtual-sequence row requires preserving the unexpanded PC.
Rust: https://github.com/abiswas3/jolt/tree/main/crates/jolt-r1cs/src/constraints/rv64.rs -/
def mustStartSequenceFromBeginning {F : Type} [Field F] {params : WitnessParams}
    (witness : WitnessType F params) : Prop :=
  ∀ t : Fin params.traceLength,
    (witness.NextIsVirtual t - witness.NextIsFirstInSequence t) *
      (1 - witness.OpFlags .DoNotUpdateUnexpandedPC t) = 0

/-- Completeness under the explicit execution conditions below.
The trace type supplies fetched addresses and source/virtual sequence boundaries;
termination and arithmetic bounds are required separately where used. -/
theorem honestWitness_mustStartSequenceFromBeginning
    {F : Type} [Field F] (params : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program)
    (ramFits : params.RamFits trace)
    (tracePadded : params.ProverPaddedFor trace.rows.size) :
    mustStartSequenceFromBeginning
      (JoltProgram.honestWitness (F := F) params trace ramFits tracePadded) := by
  sorry

end JoltConstraints
