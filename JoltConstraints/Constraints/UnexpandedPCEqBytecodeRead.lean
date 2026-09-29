import JoltConstraints.Constraints.BytecodeReadData
import JoltConstraints.Constraints.BytecodeReadSelection
import JoltConstraints.honest_witness

set_option autoImplicit false

namespace JoltConstraints

open scoped BigOperators

/-- Constraint (44) in `constraints.md` (stages 6a–6b):
the unexpanded PC is the selected row's raw instruction address.
Rust: https://github.com/abiswas3/jolt/tree/main/crates/jolt-claims/src/protocols/jolt/geometry/bytecode.rs#L545-L557 -/
def unexpandedPCEqBytecodeRead {F : Type} [Field F] {params : WitnessParams}
    (program : JoltProgram) (witness : WitnessType F params) : Prop :=
  ∀ (t : Fin params.traceLength),
    witness.UnexpandedPC t =
      ∑ address : Fin (2 ^ params.logBytecodeK),
        bytecodeAddress program address.val * bytecodeRa witness address t

/-- The honest witness satisfies constraint (44).
The bytecode domain must contain every program row and the leading no-op slot.
This bound prevents the address chunks from truncating an executed bytecode PC. -/
theorem honestWitness_unexpandedPCEqBytecodeRead
    {F : Type} [Field F] (params : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program)
    (ramFits : params.RamFits trace)
    (traceFits : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor program.expandedBytecode.size) :
    unexpandedPCEqBytecodeRead program
      (JoltProgram.honestWitness (F := F) params trace ramFits traceFits bytecodeDomain) := by
  intro t
  rw [bytecodeRead_honest params trace ramFits traceFits bytecodeDomain
    (bytecodeAddress program) t]
  by_cases h : t.val < trace.rows.size
  · simp [JoltProgram.honestWitness, HonestWitness.UnexpandedPC,
      HonestWitness.bytecodePc, bytecodeAddress, bytecodeRow, h]
  · simp [JoltProgram.honestWitness, HonestWitness.UnexpandedPC,
      HonestWitness.bytecodePc, bytecodeAddress, bytecodeRow, h]

end JoltConstraints
