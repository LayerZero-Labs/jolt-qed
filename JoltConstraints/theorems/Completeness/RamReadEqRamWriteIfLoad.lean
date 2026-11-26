import JoltConstraints.translation.Constraints.RamReadEqRamWriteIfLoad
import JoltConstraints.theorems.Completeness.Helpers.MemoryValueFacts
import JoltConstraints.theorems.witness_domain
import JoltConstraints.translation.honest_witness

open LeanRV64D

set_option autoImplicit false

namespace JoltConstraints

/-- A load preserves its captured doubleword in RAM and its destination,
including floor rows; for example, a floor byte load preserves the whole loaded word.
Jolt's tracer: `tracer/src/instruction/floor_access.rs`
(`load`) at `ff6fc6568`. -/
theorem honestWitness_ramReadEqRamWriteIfLoad
    {F : Type} [Field F] (params : WitnessParams)
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (_ramFits : params.RamFits trace)
    (_traceFits : params.ProverPaddedFor trace.rows.size)
    (_bytecodeDomain : params.BytecodeDomainFor trace.bytecode.size) :
    ramReadEqRamWriteIfLoad
      (HonestTrace.honestWitness (F := F) params trace) := by
  intro t
  change TraceWitness.OpFlags params trace .Load t *
    (HonestWitness.RamReadValue params trace t -
      TraceWitness.RamWriteValue params trace t) = 0
  by_cases inBounds : t.val < trace.rows.size
  · let instruction := (trace.bytecode[(trace.rows[t.val]'inBounds).rowIndex]).instruction
    by_cases hLoad : JoltMetadata.opcodeFlag instruction .Load = true
    · rw [ramReadValue_of_load params trace t inBounds hLoad, ramWriteValue_of_load params trace t inBounds hLoad]
      simp
    · dsimp [instruction] at hLoad
      simp [TraceWitness.OpFlags, JoltMetadata.circuitFlag, inBounds, hLoad]
  · simp [TraceWitness.OpFlags, HonestWitness.RamReadValue,
      TraceWitness.RamWriteValue, inBounds]

end JoltConstraints
