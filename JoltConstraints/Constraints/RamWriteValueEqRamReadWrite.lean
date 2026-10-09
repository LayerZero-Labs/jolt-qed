import JoltConstraints.witness
import Mathlib.Data.Fintype.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.Defs

set_option autoImplicit false

namespace JoltConstraints

open scoped BigOperators

/-- Constraint (24) in `constraints.md`:
The RAM address selector selects the value for this cycle.
Rust: https://github.com/abiswas3/jolt/tree/main/crates/jolt-claims/src/protocols/jolt/relations/ram/read_write_checking.rs#L89-L106 -/
def ramWriteValueEqRamReadWrite {F : Type} [Field F] {params : WitnessParams}
    (witness : WitnessType F params) : Prop :=
  ∀ t : Fin params.traceLength,
    witness.RamWriteValue t =
      ∑ address : Fin params.ramSize, witness.RamRa address t * (witness.RamVal address t + witness.RamInc t)

end JoltConstraints
