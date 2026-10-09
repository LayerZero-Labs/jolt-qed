import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.witness_helpers

set_option autoImplicit false

namespace JoltConstraints

/-- Constraint (01) in `constraints.md` (stage 1):
loads and stores use the base register plus the immediate as their RAM address.
Rust: https://github.com/abiswas3/jolt/tree/main/crates/jolt-r1cs/src/constraints/rv64.rs -/
def ramAddrEqRs1PlusImmIfLoadStore {F : Type} [Field F] {params : WitnessParams}
    (witness : WitnessType F params) : Prop :=
  ∀ t : Fin params.traceLength,
    (witness.OpFlags .Load t + witness.OpFlags .Store t) *
      (witness.RamAddress t - witness.Rs1Value t - witness.Imm t) = 0

end JoltConstraints
