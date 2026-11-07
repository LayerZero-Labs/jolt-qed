import JoltConstraints.Constraints.RamReadEqRdWriteIfLoad
import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.Completeness.Helpers.MemoryValueFacts

open LeanRV64D

set_option autoImplicit false

namespace JoltConstraints

/-- A load preserves its captured doubleword in RAM and its destination,
including floor rows; for example, a floor byte load preserves the whole loaded word.
Jolt's tracer: `tracer/src/instruction/floor_access.rs`
(`load`) at `c6703570`. -/
theorem honestWitness_ramReadEqRdWriteIfLoad
    {F : Type} [Field F] (params : WitnessParams)
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (ramFits : params.RamFits trace)
    (traceFits : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor trace.bytecode.size) :
    ramReadEqRdWriteIfLoad
      (HonestTrace.honestWitness (F := F) params trace) := by
  intro t
  change TraceWitness.OpFlags params trace .Load t *
    (HonestWitness.RamReadValue params trace t -
      TraceWitness.RdWriteValue params trace t) = 0
  by_cases inBounds : t.val < trace.rows.size
  · let instruction := (trace.bytecode[(trace.rows[t.val]'inBounds).rowIndex]).instruction
    by_cases hLoad : JoltMetadata.opcodeFlag instruction .Load = true
    · rw [ramReadValue_of_load params trace t inBounds hLoad]
      simp
    · dsimp [instruction] at hLoad
      simp [TraceWitness.OpFlags, JoltMetadata.circuitFlag, inBounds, hLoad]
  · simp [TraceWitness.OpFlags, HonestWitness.RamReadValue,
      TraceWitness.RdWriteValue, inBounds]

end JoltConstraints
