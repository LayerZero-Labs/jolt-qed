import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.honest_witness

set_option autoImplicit false

namespace JoltConstraints

/-- Constraint (06) in `constraints.md` (stage 1):
addition, subtraction and multiplication use zero as their left lookup operand.
Rust: https://github.com/abiswas3/jolt/tree/main/crates/jolt-r1cs/src/constraints/rv64.rs -/
def leftLookupZeroIfAddSubMul {F : Type} [Field F] {params : WitnessParams}
    (witness : WitnessType F params) : Prop :=
  ∀ t : Fin params.traceLength,
    (witness.OpFlags .AddOperands t + witness.OpFlags .SubtractOperands t +
      witness.OpFlags .MultiplyOperands t) * witness.LeftLookupOperand t = 0

/-- Completeness target for the honest witness; proof pending. -/
theorem honestWitness_leftLookupZeroIfAddSubMul
    {F : Type} [Field F] (params : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program)
    (ramFits : params.RamFits trace)
    (traceFits : trace.rows.size ≤ params.traceLength) :
    leftLookupZeroIfAddSubMul
      (JoltProgram.honestWitness (F := F) params trace ramFits traceFits) := by
  sorry

end JoltConstraints
