import JoltConstraints.Constraints.BytecodeReadData
import JoltConstraints.Constraints.BytecodeReadSelection
import JoltConstraints.honest_witness

set_option autoImplicit false

namespace JoltConstraints

open scoped BigOperators

/-- Constraint (47) in `constraints.md` (stages 6a–6b):
each instruction flag is selected from the fixed bytecode table.
Rust: https://github.com/abiswas3/jolt/tree/main/crates/jolt-claims/src/protocols/jolt/geometry/bytecode.rs#L559-L594 -/
def instructionFlagsEqBytecodeRead {F : Type} [Field F] {params : WitnessParams}
    (program : JoltProgram) (witness : WitnessType F params) : Prop :=
  ∀ (flag : InstructionFlags) (t : Fin params.traceLength),
    witness.InstructionFlags flag t =
      ∑ address : Fin (2 ^ params.logBytecodeK),
        bytecodeInstructionFlag program flag address.val * bytecodeRa witness address t

/-- The honest witness satisfies constraint (47).
The bytecode domain must contain every program row and the leading no-op slot.
This bound prevents the address chunks from truncating an executed bytecode PC. -/
theorem honestWitness_instructionFlagsEqBytecodeRead
    {F : Type} [Field F] (params : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program)
    (ramFits : params.RamFits trace)
    (traceFits : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor program.expandedBytecode.size) :
    instructionFlagsEqBytecodeRead program
      (JoltProgram.honestWitness (F := F) params trace ramFits traceFits bytecodeDomain) := by
  intro flag t
  rw [bytecodeRead_honest params trace ramFits traceFits bytecodeDomain
    (bytecodeInstructionFlag program flag) t]
  by_cases h : t.val < trace.rows.size
  · simp [JoltProgram.honestWitness, HonestWitness.InstructionFlags,
      HonestWitness.bytecodePc, bytecodeInstructionFlag, bytecodeRow, h]
  · cases flag <;>
      simp [JoltProgram.honestWitness, HonestWitness.InstructionFlags,
        HonestWitness.bytecodePc, bytecodeInstructionFlag, bytecodeRow, h]

end JoltConstraints
