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
      (match TraceWitness.ramAccessAddress instruction preState with
        | some address => (address.toNat : F)
        | none => 0) = 0 := by
  cases instruction <;>
    simp [JoltMetadata.opcodeFlag, TraceWitness.ramAccessAddress]

/-- Completeness target for the honest witness; proof pending. -/
theorem honestWitness_ramAddrEqZeroIfNotLoadStore
    {F : Type} [Field F] (params : WitnessParams)
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (ramFits : params.RamFits trace)
    (traceFits : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor trace.bytecode.size) :
    ramAddrEqZeroIfNotLoadStore
      (HonestTrace.honestWitness (F := F) params trace) := by
  intro t
  by_cases inBounds : t.val < trace.rows.size
  · simpa [HonestTrace.honestWitness, TraceWitness.OpFlags,
      TraceWitness.RamAddress, JoltMetadata.circuitFlag, inBounds] using
        (ramAddressZeroWhenNotMemory (F := F)
          (trace.bytecode[(trace.rows[t.val]'inBounds).rowIndex]).instruction
          (trace.rows[t.val]'inBounds).preState)
  · simp [HonestTrace.honestWitness, TraceWitness.OpFlags,
      TraceWitness.RamAddress, inBounds]

end JoltConstraints
