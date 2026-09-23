import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.honest_witness

set_option autoImplicit false

namespace JoltConstraints

/-- Constraint (32) in `constraints.md` (stage 3):
the left instruction input is selected from Rs1Value and UnexpandedPC by the instruction flags.
Rust: https://github.com/abiswas3/jolt/tree/main/crates/jolt-claims/src/protocols/jolt/relations/instruction/input_virtualization.rs#L108-L127 -/
def leftInstructionInputEqSelection {F : Type} [Field F] {params : WitnessParams}
    (witness : WitnessType F params) : Prop :=
  ∀ t : Fin params.traceLength,
    witness.LeftInstructionInput t =
      witness.InstructionFlags .LeftOperandIsRs1Value t * witness.Rs1Value t +
      witness.InstructionFlags .LeftOperandIsPC t * witness.UnexpandedPC t

/-- The honest witness satisfies constraint (32); proof pending. -/
theorem honestWitness_leftInstructionInputEqSelection
    {F : Type} [Field F] (params : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program)
    (ramFits : params.RamFits trace)
    (traceFits : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor program.expandedBytecode.size) :
    leftInstructionInputEqSelection
      (JoltProgram.honestWitness (F := F) params trace ramFits traceFits bytecodeDomain) := by
  sorry

end JoltConstraints
