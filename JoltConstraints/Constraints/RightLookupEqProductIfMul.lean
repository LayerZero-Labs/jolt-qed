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

/-- Constraint (10) in `constraints.md` (stage 1):
multiplication places Product in the right lookup operand.
Rust: https://github.com/abiswas3/jolt/tree/main/crates/jolt-r1cs/src/constraints/rv64.rs -/
def rightLookupEqProductIfMul {F : Type} [Field F] {params : WitnessParams}
    (witness : WitnessType F params) : Prop :=
  ∀ t : Fin params.traceLength,
    witness.OpFlags .MultiplyOperands t *
      (witness.RightLookupOperand t - witness.Product t) = 0

/-- Completeness target for the honest witness. -/
theorem honestWitness_rightLookupEqProductIfMul
    {F : Type} [Field F] (params : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program)
    (ramFits : params.RamFits trace)
    (traceFits : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor program.expandedBytecode.size) :
    rightLookupEqProductIfMul
      (JoltProgram.honestWitness (F := F) params trace ramFits traceFits bytecodeDomain) := by
  intro t
  by_cases h : t.val < trace.rows.size
  · let row := getElem trace.rows t.val h
    let bytecodeRow := getElem program.expandedBytecode row.rowIndex.val row.rowIndex.isLt
    by_cases hm : JoltMetadata.opcodeFlag bytecodeRow.instruction .MultiplyOperands = true
    · have heq : HonestWitness.RightLookupOperand (F := F) params trace t =
          HonestWitness.Product (F := F) params trace t := by
        cases hi : bytecodeRow.instruction
        all_goals simp [JoltMetadata.opcodeFlag, hi] at hm
        all_goals simp only [bytecodeRow, row] at hi
        all_goals
          simp [HonestWitness.RightLookupOperand, HonestWitness.Product,
            HonestWitness.lookupIndex, HonestWitness.instructionLookupIndex,
            HonestWitness.LeftInstructionInput, HonestWitness.RightInstructionInput,
            HonestWitness.Rs1Value, HonestWitness.Rs2Value, HonestWitness.Imm,
            JoltMetadata.hasCombinedLookupOperands, JoltMetadata.opcodeFlag,
            JoltMetadata.instructionFlag, mulWide_mod,
            Nat.cast_mul, hi, h]
        all_goals simp [JoltISA.mulWide, JoltMetadata.immediate]
      simp [JoltProgram.honestWitness,
        HonestWitness.OpFlags, JoltMetadata.circuitFlag, h, hm, heq]
    · simp [JoltProgram.honestWitness,
        HonestWitness.OpFlags, JoltMetadata.circuitFlag, h, hm, bytecodeRow, row]
  · simp [JoltProgram.honestWitness,
      HonestWitness.OpFlags, h]

end JoltConstraints
