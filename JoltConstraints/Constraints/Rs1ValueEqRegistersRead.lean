import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.honest_witness
import JoltConstraints.Constraints.RegistersReadProofHelpers

set_option autoImplicit false

namespace JoltConstraints

open scoped BigOperators

/-- Constraint (35) in `constraints.md` (stage 4):
the first-source selector reads the corresponding register value.
Rust: https://github.com/abiswas3/jolt/tree/main/crates/jolt-claims/src/protocols/jolt/relations/registers/read_write_checking.rs#L97-L121 -/
def rs1ValueEqRegistersRead {F : Type} [Field F] {params : WitnessParams}
    (witness : WitnessType F params) : Prop :=
  ∀ t : Fin params.traceLength,
    witness.Rs1Value t =
      ∑ register : Fin 128, witness.Rs1Ra register t * witness.RegistersVal register t

end JoltConstraints
