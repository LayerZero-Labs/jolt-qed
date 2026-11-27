import JoltConstraints.translation.witness
import JoltBytecode.MathlibTactics
import LeanRV64D.Defs

open LeanRV64D

set_option autoImplicit false

namespace JoltConstraints

/-- Constraint (32) in `constraints.md` (stage 3):
the left instruction input is selected from Rs1Value and UnexpandedPC by the instruction flags.
Rust: https://github.com/a16z/jolt/blob/ff6fc656813d950565c9f6e1258b78bdaf0e60e8/crates/jolt-claims/src/protocols/jolt/relations/instruction/input_virtualization.rs#L115-L134 -/
def leftInstructionInputEqSelection {F : Type} [Field F] {params : WitnessParams}
    (witness : WitnessType F params) : Prop :=
  ∀ t : Fin params.traceLength,
    witness.LeftInstructionInput t =
      witness.InstructionFlags .LeftOperandIsRs1Value t * witness.Rs1Value t +
      witness.InstructionFlags .LeftOperandIsPC t * witness.UnexpandedPC t

end JoltConstraints
