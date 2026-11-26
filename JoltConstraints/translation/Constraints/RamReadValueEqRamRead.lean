import JoltConstraints.translation.witness
import Mathlib.Data.Fintype.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.Defs

set_option autoImplicit false

namespace JoltConstraints

open scoped BigOperators

/-- Constraint (23) in `constraints.md`:
The RAM address selector selects the value for this cycle.
Rust: https://github.com/a16z/jolt/blob/ff6fc656813d950565c9f6e1258b78bdaf0e60e8/crates/jolt-claims/src/protocols/jolt/relations/ram/read_write_checking.rs#L116-L133 -/
def ramReadValueEqRamRead {F : Type} [Field F] {params : WitnessParams}
    (witness : WitnessType F params) : Prop :=
  ∀ t : Fin params.traceLength,
    witness.RamReadValue t =
      ∑ address : Fin params.ramSize, witness.RamRa address t * witness.RamVal address t

end JoltConstraints
