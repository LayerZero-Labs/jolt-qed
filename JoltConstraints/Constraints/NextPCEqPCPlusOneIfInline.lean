import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.honest_witness
import JoltConstraints.execution_conditions

set_option autoImplicit false

namespace JoltConstraints

/-- Constraint (18) in `constraints.md` (stage 1):
nonterminal virtual-sequence rows advance the expanded PC by one.
Rust: https://github.com/abiswas3/jolt/tree/main/crates/jolt-r1cs/src/constraints/rv64.rs -/
def nextPCEqPCPlusOneIfInline {F : Type} [Field F] {params : WitnessParams}
    (witness : WitnessType F params) : Prop :=
  ∀ t : Fin params.traceLength,
    (witness.OpFlags .VirtualInstruction t - witness.OpFlags .IsLastInSequence t) *
      (witness.NextPC t - witness.PC t - 1) = 0

/-- Completeness target for a complete Rust trace, with its mandatory padding.
`Terminated` includes every opcode allowed by Rust's repeated-PC stopping rule.
There is no jump-only or nonwrapping-arithmetic assumption. Proof pending. -/
theorem honestWitness_nextPCEqPCPlusOneIfInline
    {F : Type} [Field F] (params : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program)
    (ramFits : params.RamFits trace)
    (terminated : trace.Terminated)
    (tracePadded : params.ProverPaddedFor trace.rows.size) :
    nextPCEqPCPlusOneIfInline
      (JoltProgram.honestWitness (F := F) params trace ramFits tracePadded) := by
  sorry

end JoltConstraints
