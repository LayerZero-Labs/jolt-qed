import Mathlib.Algebra.Field.Defs
import JoltConstraints.translation.witness
import JoltConstraints.translation.witness_helpers

open LeanRV64D

set_option autoImplicit false

namespace JoltConstraints

/-- Constraint (18) in `constraints.md` (stage 1):
nonterminal virtual-sequence rows advance the expanded PC by one.
Rust: https://github.com/a16z/jolt/blob/ff6fc656813d950565c9f6e1258b78bdaf0e60e8/crates/jolt-claims/src/protocols/composed/r1cs/rv64.rs -/
def nextPCEqPCPlusOneIfInline {F : Type} [Field F] {params : WitnessParams}
    (witness : WitnessType F params) : Prop :=
  ∀ t : Fin params.traceLength,
    (witness.OpFlags .VirtualInstruction t - witness.OpFlags .IsLastInSequence t) *
      (witness.NextPC t - witness.PC t - 1) = 0

end JoltConstraints
