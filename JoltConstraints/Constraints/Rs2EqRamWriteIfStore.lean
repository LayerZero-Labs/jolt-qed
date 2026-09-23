import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.honest_witness

set_option autoImplicit false

namespace JoltConstraints

/-- Constraint (05) in `constraints.md` (stage 1):
a store writes its second source register value to RAM.
Rust: https://github.com/abiswas3/jolt/tree/main/crates/jolt-r1cs/src/constraints/rv64.rs -/
def rs2EqRamWriteIfStore {F : Type} [Field F] {params : WitnessParams}
    (witness : WitnessType F params) : Prop :=
  ∀ t : Fin params.traceLength,
    witness.OpFlags .Store t * (witness.Rs2Value t - witness.RamWriteValue t) = 0

/-- Completeness target for the honest witness; proof pending. -/
theorem honestWitness_rs2EqRamWriteIfStore
    {F : Type} [Field F] (params : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program)
    (ramFits : params.RamFits trace)
    (traceFits : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor program.expandedBytecode.size) :
    rs2EqRamWriteIfStore
      (JoltProgram.honestWitness (F := F) params trace ramFits traceFits bytecodeDomain) := by
  intro t
  change HonestWitness.OpFlags params trace .Store t *
    (HonestWitness.Rs2Value params trace t -
      HonestWitness.RamWriteValue params trace t) = 0
  by_cases inBounds : t.val < trace.rows.size
  · let instruction := (program.expandedBytecode[(trace.rows[t.val]'inBounds).rowIndex]).instruction
    by_cases hStore : JoltMetadata.opcodeFlag instruction .Store = true
    · obtain ⟨base, value, imm, hInstr⟩ :=
        JoltMetadata.opcodeFlag_store_requiresSD instruction hStore
      dsimp [instruction] at hInstr
      simp [HonestWitness.OpFlags, HonestWitness.Rs2Value,
        HonestWitness.RamWriteValue, JoltMetadata.circuitFlag, inBounds, hInstr]
    · dsimp [instruction] at hStore
      simp [HonestWitness.OpFlags, JoltMetadata.circuitFlag, inBounds, hStore]
  · simp [HonestWitness.OpFlags, HonestWitness.Rs2Value,
      HonestWitness.RamWriteValue, inBounds]

end JoltConstraints
