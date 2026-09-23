import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.honest_witness

set_option autoImplicit false

namespace JoltConstraints

/-- Constraint (07) in `constraints.md` (stage 1):
the other operand modes preserve the left instruction input.
Rust: https://github.com/abiswas3/jolt/tree/main/crates/jolt-r1cs/src/constraints/rv64.rs -/
def leftLookupEqLeftInputOtherwise {F : Type} [Field F] {params : WitnessParams}
    (witness : WitnessType F params) : Prop :=
  ∀ t : Fin params.traceLength,
    (1 - witness.OpFlags .AddOperands t - witness.OpFlags .SubtractOperands t -
      witness.OpFlags .MultiplyOperands t) *
      (witness.LeftLookupOperand t - witness.LeftInstructionInput t) = 0

/-- Completeness target for the honest witness; proof pending. -/
theorem honestWitness_leftLookupEqLeftInputOtherwise
    {F : Type} [Field F] (params : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program)
    (ramFits : params.RamFits trace)
    (traceFits : params.ProverPaddedFor trace.rows.size) :
    leftLookupEqLeftInputOtherwise
      (JoltProgram.honestWitness (F := F) params trace ramFits traceFits) := by
  sorry

end JoltConstraints
