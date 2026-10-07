import JoltConstraints.Constraints.Rs2EqRamWriteIfStore
import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.honest_witness

set_option autoImplicit false

namespace JoltConstraints

/-- Completeness target for the honest witness; proof pending. -/
theorem honestWitness_rs2EqRamWriteIfStore
    {F : Type} [Field F] (params : WitnessParams)
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (ramFits : params.RamFits trace)
    (traceFits : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor trace.bytecode.size) :
    rs2EqRamWriteIfStore
      (HonestTrace.honestWitness (F := F) params trace) := by
  intro t
  change HonestWitness.OpFlags params trace .Store t *
    (HonestWitness.Rs2Value params trace t -
      HonestWitness.RamWriteValue params trace t) = 0
  by_cases inBounds : t.val < trace.rows.size
  · let instruction := (trace.bytecode[(trace.rows[t.val]'inBounds).rowIndex]).instruction
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
