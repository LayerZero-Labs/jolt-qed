import JoltConstraints.Constraints.RamAddrEqZeroIfNotLoadStore
import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.honest_witness

set_option autoImplicit false

namespace JoltConstraints

private theorem ramAddressZeroWhenNotMemory {F : Type} [Field F]
    (instruction : JoltISA.Instr) (preState : SailJoltState) :
    ((1 : F) - (if JoltMetadata.opcodeFlag instruction .Load then 1 else 0) -
      (if JoltMetadata.opcodeFlag instruction .Store then 1 else 0)) *
      (match HonestWitness.ramAccessAddress instruction preState with
        | some address => (address.toNat : F)
        | none => 0) = 0 := by
  cases instruction <;>
    simp [JoltMetadata.opcodeFlag, HonestWitness.ramAccessAddress]

/-- Completeness target for the honest witness; proof pending. -/
theorem honestWitness_ramAddrEqZeroIfNotLoadStore
    {F : Type} [Field F] (params : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program)
    (ramFits : params.RamFits trace)
    (traceFits : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor program.expandedBytecode.size) :
    ramAddrEqZeroIfNotLoadStore
      (JoltProgram.honestWitness (F := F) params trace ramFits traceFits bytecodeDomain) := by
  intro t
  by_cases inBounds : t.val < trace.rows.size
  · simpa [JoltProgram.honestWitness, HonestWitness.OpFlags,
      HonestWitness.RamAddress, JoltMetadata.circuitFlag, inBounds] using
        (ramAddressZeroWhenNotMemory (F := F)
          (program.expandedBytecode[(trace.rows[t.val]'inBounds).rowIndex]).expandedInstruction
          (trace.rows[t.val]'inBounds).preState)
  · simp [JoltProgram.honestWitness, HonestWitness.OpFlags,
      HonestWitness.RamAddress, inBounds]

end JoltConstraints
