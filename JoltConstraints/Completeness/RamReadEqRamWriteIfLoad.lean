import JoltConstraints.Constraints.RamReadEqRamWriteIfLoad
import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.honest_witness

set_option autoImplicit false

namespace JoltConstraints

/-- Completeness target for the honest witness; proof pending. -/
theorem honestWitness_ramReadEqRamWriteIfLoad
    {F : Type} [Field F] (params : WitnessParams)
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (ramFits : params.RamFits trace)
    (traceFits : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor trace.bytecode.size) :
    ramReadEqRamWriteIfLoad
      (HonestTrace.honestWitness (F := F) params trace) := by
  intro t
  change TraceWitness.OpFlags params trace .Load t *
    (HonestWitness.RamReadValue params trace t -
      TraceWitness.RamWriteValue params trace t) = 0
  by_cases inBounds : t.val < trace.rows.size
  · let instruction := (trace.bytecode[(trace.rows[t.val]'inBounds).rowIndex]).instruction
    by_cases hLoad : JoltMetadata.opcodeFlag instruction .Load = true
    · obtain ⟨faultClass, dst, base, imm, hInstr⟩ :=
        JoltMetadata.opcodeFlag_load_requiresLD instruction hLoad
      dsimp [instruction] at hLoad hInstr
      simp [TraceWitness.OpFlags, HonestWitness.RamReadValue,
        TraceWitness.RamWriteValue, JoltMetadata.circuitFlag,
        inBounds, hInstr]
      all_goals split <;> simp_all [JoltMetadata.opcodeFlag]
      case h_3 =>
        rename_i h
        exact False.elim ((h faultClass dst base imm rfl rfl rfl) rfl)
    · dsimp [instruction] at hLoad
      simp [TraceWitness.OpFlags, JoltMetadata.circuitFlag, inBounds, hLoad]
  · simp [TraceWitness.OpFlags, HonestWitness.RamReadValue,
      TraceWitness.RamWriteValue, inBounds]

end JoltConstraints
