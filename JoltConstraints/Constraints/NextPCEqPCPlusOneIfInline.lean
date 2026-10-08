import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.witness_helpers

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

end JoltConstraints
