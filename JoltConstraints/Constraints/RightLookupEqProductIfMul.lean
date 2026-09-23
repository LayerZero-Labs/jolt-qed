import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.honest_witness

set_option autoImplicit false

namespace JoltConstraints

/-- Constraint (10) in `constraints.md` (stage 1):
multiplication places Product in the right lookup operand.
Rust: https://github.com/abiswas3/jolt/tree/main/crates/jolt-r1cs/src/constraints/rv64.rs -/
def rightLookupEqProductIfMul {F : Type} [Field F] {params : WitnessParams}
    (witness : WitnessType F params) : Prop :=
  ∀ t : Fin params.traceLength,
    witness.OpFlags .MultiplyOperands t *
      (witness.RightLookupOperand t - witness.Product t) = 0

/-- Completeness target for the honest witness; proof pending. -/
theorem honestWitness_rightLookupEqProductIfMul
    {F : Type} [Field F] (params : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program)
    (ramFits : params.RamFits trace)
    (traceFits : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor program.expandedBytecode.size) :
    rightLookupEqProductIfMul
      (JoltProgram.honestWitness (F := F) params trace ramFits traceFits bytecodeDomain) := by
  sorry

end JoltConstraints
