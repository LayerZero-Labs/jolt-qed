import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.honest_witness
import JoltConstraints.execution_conditions

set_option autoImplicit false

namespace JoltConstraints

/-- Constraint (15) in `constraints.md` (stage 1):
a taken jump selects the lookup output as the next unexpanded PC.
Rust: https://github.com/abiswas3/jolt/tree/main/crates/jolt-r1cs/src/constraints/rv64.rs -/
def nextUnexpandedPCEqLookupIfShouldJump {F : Type} [Field F] {params : WitnessParams}
    (witness : WitnessType F params) : Prop :=
  ∀ t : Fin params.traceLength,
    witness.ShouldJump t * (witness.NextUnexpandedPC t - witness.LookupOutput t) = 0

/-- Completeness target for a complete Rust trace, with its mandatory padding.
`Terminated` includes every opcode allowed by Rust's repeated-PC stopping rule.
There is no jump-only or nonwrapping-arithmetic assumption. Proof pending. -/
theorem honestWitness_nextUnexpandedPCEqLookupIfShouldJump
    {F : Type} [Field F] (params : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program)
    (ramFits : params.RamFits trace)
    (terminated : trace.Terminated)
    (tracePadded : trace.rows.size < params.traceLength) :
    nextUnexpandedPCEqLookupIfShouldJump
      (JoltProgram.honestWitness (F := F) params trace ramFits (Nat.le_of_lt tracePadded)) := by
  sorry

end JoltConstraints
