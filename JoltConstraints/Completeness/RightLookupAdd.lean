import JoltConstraints.Constraints.RightLookupAdd
import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.honest_witness

set_option autoImplicit false

namespace JoltConstraints

private theorem addWide_mod (left right : BitVec 64) :
    JoltISA.addWide left right % 340282366920938463463374607431768211456 =
      JoltISA.addWide left right := by
  have hl := left.isLt
  have hr := right.isLt
  apply Nat.mod_eq_of_lt
  dsimp [JoltISA.addWide]
  omega

private theorem addWide_cast {F : Type} [Field F] (left right : BitVec 64) :
    (JoltISA.addWide left right : F) = (left.toNat : F) + (right.toNat : F) := by
  simp [JoltISA.addWide]

private theorem narrow_mod_128 (value : BitVec 64) :
    value.toNat % 340282366920938463463374607431768211456 = value.toNat :=
  Nat.mod_eq_of_lt (value.isLt.trans (by norm_num))

private theorem masked_mod_128 (value : Nat) :
    value % 18446744073709551616 % 340282366920938463463374607431768211456 =
      value % 18446744073709551616 := by
  apply Nat.mod_eq_of_lt
  exact (Nat.mod_lt _ (by norm_num)).trans (by norm_num)

/-- Completeness target for the honest witness. -/
theorem honestWitness_rightLookupAdd
    {F : Type} [Field F] (params : WitnessParams)
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (ramFits : params.RamFits trace)
    (traceFits : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor trace.bytecode.size) :
    rightLookupAdd
      (HonestTrace.honestWitness (F := F) params trace) := by
  intro t
  by_cases h : t.val < trace.rows.size
  · let row := getElem trace.rows t.val h
    let bytecodeRow := getElem trace.bytecode row.rowIndex.val row.rowIndex.isLt
    by_cases ha : JoltMetadata.opcodeFlag bytecodeRow.instruction .AddOperands = true
    · have heq : TraceWitness.RightLookupOperand (F := F) params trace t =
          TraceWitness.LeftInstructionInput (F := F) params trace t +
          TraceWitness.RightInstructionInput (F := F) params trace t := by
        cases hi : bytecodeRow.instruction
        all_goals simp [JoltMetadata.opcodeFlag, hi] at ha
        all_goals simp only [bytecodeRow, row] at hi
        all_goals
          simp [TraceWitness.RightLookupOperand, TraceWitness.lookupIndex,
            TraceWitness.instructionLookupIndex, TraceWitness.LeftInstructionInput,
            TraceWitness.RightInstructionInput, TraceWitness.Rs1Value,
            TraceWitness.Rs2Value, TraceWitness.Imm, TraceWitness.UnexpandedPC,
            JoltMetadata.hasCombinedLookupOperands, JoltMetadata.opcodeFlag,
            JoltMetadata.instructionFlag, addWide_mod, hi, h]
        all_goals (try simp [addWide_cast, narrow_mod_128, JoltMetadata.immediate])
        all_goals simp [masked_mod_128]
        all_goals norm_cast
      simp [HonestTrace.honestWitness, TraceWitness.OpFlags,
        JoltMetadata.circuitFlag, h, heq]
    · simp [HonestTrace.honestWitness,
        TraceWitness.OpFlags, JoltMetadata.circuitFlag, h, ha, bytecodeRow, row]
  · simp [HonestTrace.honestWitness, TraceWitness.OpFlags, h]

end JoltConstraints
