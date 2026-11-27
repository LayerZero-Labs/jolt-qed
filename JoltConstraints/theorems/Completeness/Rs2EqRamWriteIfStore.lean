import JoltConstraints.translation.Constraints.Rs2EqRamWriteIfStore
import JoltConstraints.translation.honest_witness
import JoltConstraints.theorems.witness_domain

open LeanRV64D

set_option autoImplicit false

namespace JoltConstraints

/-- A store writes its captured second source to RAM,
including floor rows; for example, a floor byte store writes its merged doubleword.
Jolt's tracer: `tracer/src/instruction/floor_access.rs`
(`store`) at `ff6fc6568`. -/
theorem honestWitness_rs2EqRamWriteIfStore
    {F : Type} [Field F] (params : WitnessParams)
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (_ramFits : params.RamFits trace)
    (_traceFits : params.ProverPaddedFor trace.rows.size)
    (_bytecodeDomain : params.BytecodeDomainFor trace.bytecode.size) :
    rs2EqRamWriteIfStore
      (HonestTrace.honestWitness (F := F) params trace) := by
  intro t
  change TraceWitness.OpFlags params trace .Store t *
    (TraceWitness.Rs2Value params trace t -
      TraceWitness.RamWriteValue params trace t) = 0
  by_cases inBounds : t.val < trace.rows.size
  · let instruction := (trace.bytecode[(trace.rows[t.val]'inBounds).rowIndex]).instruction
    by_cases hStore : JoltMetadata.opcodeFlag instruction .Store = true
    · obtain ⟨base, value, imm, hInstr⟩ :=
        JoltMetadata.opcodeFlag_store_cases instruction hStore
      rcases hInstr with hInstr | ⟨fault, hInstr | hInstr | hInstr⟩ <;>
        dsimp [instruction] at hInstr <;>
        simp [TraceWitness.OpFlags, TraceWitness.Rs2Value, TraceWitness.RamWriteValue,
          JoltMetadata.circuitFlag, JoltMetadata.opcodeFlag,
          inBounds, hInstr]
    · dsimp [instruction] at hStore
      simp [TraceWitness.OpFlags, JoltMetadata.circuitFlag, inBounds, hStore]
  · simp [TraceWitness.OpFlags, TraceWitness.Rs2Value,
      TraceWitness.RamWriteValue, inBounds]

end JoltConstraints
