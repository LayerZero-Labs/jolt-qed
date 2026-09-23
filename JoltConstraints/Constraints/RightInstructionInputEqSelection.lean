import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.honest_witness

set_option autoImplicit false

namespace JoltConstraints

/-- Constraint (33) in `constraints.md` (stage 3):
the right instruction input is selected from Rs2Value and Imm by the instruction flags.
Rust: https://github.com/abiswas3/jolt/tree/main/crates/jolt-claims/src/protocols/jolt/relations/instruction/input_virtualization.rs#L108-L127 -/
def rightInstructionInputEqSelection {F : Type} [Field F] {params : WitnessParams}
    (witness : WitnessType F params) : Prop :=
  ∀ t : Fin params.traceLength,
    witness.RightInstructionInput t =
      witness.InstructionFlags .RightOperandIsRs2Value t * witness.Rs2Value t +
      witness.InstructionFlags .RightOperandIsImm t * witness.Imm t

/-- The honest witness satisfies constraint (33); proof pending. -/
theorem honestWitness_rightInstructionInputEqSelection
    {F : Type} [Field F] (params : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program)
    (ramFits : params.RamFits trace)
    (traceFits : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor program.expandedBytecode.size) :
    rightInstructionInputEqSelection
      (JoltProgram.honestWitness (F := F) params trace ramFits traceFits bytecodeDomain) := by
  sorry

end JoltConstraints
