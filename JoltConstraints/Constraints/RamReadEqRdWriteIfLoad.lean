import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.honest_witness

set_option autoImplicit false

namespace JoltConstraints

/-- Constraint (04) in `constraints.md` (stage 1):
a load writes its RAM read value to the destination register.
Rust: https://github.com/abiswas3/jolt/tree/main/crates/jolt-r1cs/src/constraints/rv64.rs -/
def ramReadEqRdWriteIfLoad {F : Type} [Field F] {params : WitnessParams}
    (witness : WitnessType F params) : Prop :=
  ∀ t : Fin params.traceLength,
    witness.OpFlags .Load t * (witness.RamReadValue t - witness.RdWriteValue t) = 0

/-- Completeness target for the honest witness; proof pending. -/
theorem honestWitness_ramReadEqRdWriteIfLoad
    {F : Type} [Field F] (params : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program)
    (ramFits : params.RamFits trace)
    (traceFits : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor program.expandedBytecode.size) :
    ramReadEqRdWriteIfLoad
      (JoltProgram.honestWitness (F := F) params trace ramFits traceFits bytecodeDomain) := by
  intro t
  change HonestWitness.OpFlags params trace .Load t *
    (HonestWitness.RamReadValue params trace t -
      HonestWitness.RdWriteValue params trace t) = 0
  by_cases inBounds : t.val < trace.rows.size
  · let instruction := (program.expandedBytecode[(trace.rows[t.val]'inBounds).rowIndex]).instruction
    by_cases hLoad : JoltMetadata.opcodeFlag instruction .Load = true
    · obtain ⟨faultClass, dst, base, imm, hInstr⟩ :=
        JoltMetadata.opcodeFlag_load_requiresLD instruction hLoad
      dsimp [instruction] at hInstr
      simp [HonestWitness.OpFlags, HonestWitness.RamReadValue,
        HonestWitness.RdWriteValue, JoltMetadata.circuitFlag, inBounds, hInstr]
      all_goals split <;> simp_all [JoltMetadata.opcodeFlag]
      case h_3 =>
        rename_i h
        exact False.elim ((h faultClass dst base imm rfl rfl rfl) rfl)
    · dsimp [instruction] at hLoad
      simp [HonestWitness.OpFlags, JoltMetadata.circuitFlag, inBounds, hLoad]
  · simp [HonestWitness.OpFlags, HonestWitness.RamReadValue,
      HonestWitness.RdWriteValue, inBounds]

end JoltConstraints
