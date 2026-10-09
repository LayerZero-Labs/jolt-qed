import JoltConstraints.Constraints.RightLookupEqProductIfMul
import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.honest_witness

set_option autoImplicit false

namespace JoltConstraints

private theorem mulWide_toNat (left right : BitVec 64) :
    (BitVec.ofNat 128 (JoltISA.mulWide left right)).toNat =
      left.toNat * right.toNat := by
  have hl := left.isLt
  have hr := right.isLt
  have hbound : left.toNat * right.toNat < 2 ^ 128 := by
    have hle : left.toNat * right.toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) := by
      apply Nat.mul_le_mul
      all_goals omega
    calc
      _ ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) := hle
      _ < 2 ^ 128 := by norm_num
  simp [JoltISA.mulWide, BitVec.toNat_ofNat]
  omega

private theorem mulWide_mod (left right : BitVec 64) :
    JoltISA.mulWide left right % 340282366920938463463374607431768211456 =
      JoltISA.mulWide left right := by
  simpa only [BitVec.toNat_ofNat, JoltISA.mulWide] using mulWide_toNat left right

/-- Completeness target for the honest witness. -/
theorem honestWitness_rightLookupEqProductIfMul
    {F : Type} [Field F] (params : WitnessParams)
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (ramFits : params.RamFits trace)
    (traceFits : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor trace.bytecode.size) :
    rightLookupEqProductIfMul
      (HonestTrace.honestWitness (F := F) params trace) := by
  intro t
  by_cases h : t.val < trace.rows.size
  · let row := getElem trace.rows t.val h
    let bytecodeRow := getElem trace.bytecode row.rowIndex.val row.rowIndex.isLt
    by_cases hm : JoltMetadata.opcodeFlag bytecodeRow.instruction .MultiplyOperands = true
    · have heq : TraceWitness.RightLookupOperand (F := F) params trace t =
          TraceWitness.Product (F := F) params trace t := by
        cases hi : bytecodeRow.instruction
        all_goals simp [JoltMetadata.opcodeFlag, hi] at hm
        all_goals simp only [bytecodeRow, row] at hi
        all_goals
          simp [TraceWitness.RightLookupOperand, TraceWitness.Product,
            TraceWitness.lookupIndex, TraceWitness.instructionLookupIndex,
            TraceWitness.LeftInstructionInput, TraceWitness.RightInstructionInput,
            TraceWitness.Rs1Value, TraceWitness.Rs2Value, TraceWitness.Imm,
            JoltMetadata.hasCombinedLookupOperands, JoltMetadata.opcodeFlag,
            JoltMetadata.instructionFlag, mulWide_mod,
            hi, h]
        all_goals simp [JoltISA.mulWide, JoltMetadata.immediate]
      simp [HonestTrace.honestWitness,
        TraceWitness.OpFlags, JoltMetadata.circuitFlag, h, heq]
    · simp [HonestTrace.honestWitness,
        TraceWitness.OpFlags, JoltMetadata.circuitFlag, h, hm, bytecodeRow, row]
  · simp [HonestTrace.honestWitness,
      TraceWitness.OpFlags, h]

end JoltConstraints
