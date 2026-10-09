import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.witness_helpers

set_option autoImplicit false

namespace JoltConstraints

/-- Constraint (05) in `constraints.md` (stage 1):
a store writes its second source register value to RAM.
Rust: https://github.com/abiswas3/jolt/tree/main/crates/jolt-r1cs/src/constraints/rv64.rs -/
def rs2EqRamWriteIfStore {F : Type} [Field F] {params : WitnessParams}
    (witness : WitnessType F params) : Prop :=
  ∀ t : Fin params.traceLength,
    witness.OpFlags .Store t * (witness.Rs2Value t - witness.RamWriteValue t) = 0

end JoltConstraints
