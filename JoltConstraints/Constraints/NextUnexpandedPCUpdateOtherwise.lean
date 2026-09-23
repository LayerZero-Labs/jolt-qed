import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.honest_witness
import JoltConstraints.execution_conditions

set_option autoImplicit false

namespace JoltConstraints

/-- Constraint (17) in `constraints.md` (stage 1):
the remaining rows advance or preserve the unexpanded PC according to their flags.
Rust: https://github.com/abiswas3/jolt/tree/main/crates/jolt-r1cs/src/constraints/rv64.rs -/
def nextUnexpandedPCUpdateOtherwise {F : Type} [Field F] {params : WitnessParams}
    (witness : WitnessType F params) : Prop :=
  ∀ t : Fin params.traceLength,
    (1 - witness.ShouldBranch t - witness.OpFlags .Jump t) *
      (witness.NextUnexpandedPC t - witness.UnexpandedPC t - 4 +
        4 * witness.OpFlags .DoNotUpdateUnexpandedPC t +
        2 * witness.OpFlags .IsCompressed t) = 0

/-- Completeness target for a complete Rust trace, with its mandatory padding.
`Terminated` includes every opcode allowed by Rust's repeated-PC stopping rule.
There is no jump-only or nonwrapping-arithmetic assumption. Proof pending. -/
theorem honestWitness_nextUnexpandedPCUpdateOtherwise
    {F : Type} [Field F] (params : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program)
    (ramFits : params.RamFits trace)
    (terminated : trace.Terminated)
    (tracePadded : trace.rows.size < params.traceLength) :
    nextUnexpandedPCUpdateOtherwise
      (JoltProgram.honestWitness (F := F) params trace ramFits (Nat.le_of_lt tracePadded)) := by
  sorry

end JoltConstraints
