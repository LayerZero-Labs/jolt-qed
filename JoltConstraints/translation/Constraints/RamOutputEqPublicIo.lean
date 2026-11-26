import JoltConstraints.translation.Constraints.RamReadData

open LeanRV64D

set_option autoImplicit false

namespace JoltConstraints

open scoped BigOperators

/-- Constraint (26) in `constraints.md`:
On the public I/O interval, the final RAM value equals the supplied public I/O word.
Rust: https://github.com/a16z/jolt/blob/ff6fc656813d950565c9f6e1258b78bdaf0e60e8/crates/jolt-claims/src/protocols/jolt/relations/ram/output_check.rs -/
def ramOutputEqPublicIo {F : Type} [Field F] {params : WitnessParams}
    (io : JoltPublicIo) (witness : WitnessType F params) : Prop :=
  ∀ address : Fin params.ramSize,
    ramPublicIoMask io address.val *
      (witness.RamValFinal address - ((ramPublicIoWord io address.val).toNat : F)) = 0

end JoltConstraints
