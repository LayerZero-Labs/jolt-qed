import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.witness_helpers

set_option autoImplicit false

namespace JoltConstraints

/-- Constraint (33) in `constraints.md` (stage 3):
the right instruction input sums the flag-selected Rs2Value, Imm and RdWriteValue.
For example, ShiftData selects Rs2Value plus Imm, while LD selects RdWriteValue.
Jolt's verifier: `crates/jolt-claims/src/protocols/jolt/relations/instruction/input_virtualization.rs`
(`InputVirtualization::unbatched_relation`) at `c6703570`. -/
def rightInstructionInputEqSelection {F : Type} [Field F] {params : WitnessParams}
    (witness : WitnessType F params) : Prop :=
  ∀ t : Fin params.traceLength,
    witness.RightInstructionInput t =
      witness.InstructionFlags .RightOperandIsRs2Value t * witness.Rs2Value t +
      witness.InstructionFlags .RightOperandIsImm t * witness.Imm t +
      witness.InstructionFlags .RightOperandIsRdWriteValue t * witness.RdWriteValue t

end JoltConstraints
