import JoltConstraints.translation.witness
import Mathlib.Algebra.Field.Defs

set_option autoImplicit false

namespace JoltConstraints

/-- Row 21 binds the transition into padding to a halt of the publicly claimed kind.
For example, a success halt has `Halt = 1`, `HaltPanic = 0`, and can enter padding
only when `claimedPanic = false`.
Jolt at `ff6fc6568`: `crates/jolt-claims/src/protocols/composed/r1cs/rv64.rs`
(`NextIsNoopEqIsNoopUnlessHalt`) and `geometry/spartan.rs` (`PRODUCT_HALT_LANE_OUTPUT`). -/
def haltEndRule {F : Type} [Field F] {params : WitnessParams}
    (claimedPanic : Bool) (witness : WitnessType F params) : Prop :=
  ∀ t : Fin params.traceLength,
    2 * (witness.NextIsNoop t - witness.InstructionFlags .IsNoop t) =
      (2 - (if claimedPanic then 1 else 0)) * witness.OpFlags .Halt t +
        witness.OpFlags .HaltPanic t

end JoltConstraints
