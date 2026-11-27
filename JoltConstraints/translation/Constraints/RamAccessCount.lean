import JoltConstraints.translation.witness
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option autoImplicit false

namespace JoltConstraints

open scoped BigOperators

/-- The sum of RAM selectors equals the load/store count at each cycle.
For example, an SD row selects one RAM word, and padding selects none.
Jolt at `ff6fc6568`: `crates/jolt-claims/src/protocols/jolt/relations/ram/read_write_checking.rs`
(`unbatched_relation`, fourth claim). -/
def ramAccessCount {F : Type} [Field F] {params : WitnessParams}
    (witness : WitnessType F params) : Prop :=
  ∀ t : Fin params.traceLength,
    witness.OpFlags .Load t + witness.OpFlags .Store t =
      ∑ k : Fin params.ramSize, witness.RamRa k t

end JoltConstraints
