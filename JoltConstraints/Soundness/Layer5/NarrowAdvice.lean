import JoltConstraints.Soundness.Layer5.TapeSemantics
import JoltBytecode.InstructionEquivalence.ProofSupport.ExpansionBlocks.ALU

/-! The arithmetic identity for narrow-advice post-processing: a left shift
followed by an arithmetic right shift discards the high bits before sign
extension. AdviceExpansion.lean proves that the generated AdviceLB/LH/LW
programs execute this pair after the advice load, in both destination branches,
and applies this identity to their register values. Agreement with the witness
tables remains a separate Layer 5b obligation. -/

set_option autoImplicit false

namespace JoltConstraints.Soundness

open JoltISA

private theorem shift_pair_signExtend (value : BitVec 64) (width : Nat)
    (positive : 0 < width) (fits : width ≤ 64) :
    (value <<< (64 - width)).sshiftRight (64 - width) =
      (value.setWidth width).signExtend 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro bit inRange
  rw [BitVec.getLsbD_sshiftRight, BitVec.getLsbD_signExtend]
  simp only [Nat.not_le.mpr inRange, inRange, decide_false, decide_true,
    Bool.not_false, Bool.true_and]
  by_cases low : bit < width
  · have inside : 64 - width + bit < 64 := by omega
    have index : 64 - width + bit - (64 - width) = bit := by omega
    simp only [low, inside, ite_true, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_setWidth, decide_true, Bool.true_and, index,
      show ¬64 - width + bit < 64 - width by omega,
      decide_false, Bool.not_false]
  · have outside : ¬64 - width + bit < 64 := by omega
    have signIndex : 64 - 1 - (64 - width) = width - 1 := by omega
    simp only [low, outside, ite_false, BitVec.msb_eq_getLsbD_last,
      BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, signIndex,
      show 64 - 1 < 64 by omega, show ¬64 - 1 < 64 - width by omega,
      show width - 1 < width by omega, decide_true, decide_false,
      Bool.not_false, Bool.true_and]

/-- Multiplying by the expansion's power of two and shifting back arithmetically
returns exactly the signed low-width portion of any answer word. -/
theorem narrowAdvice_value (answer : BitVec 64) (width : Nat)
    (positive : 0 < width) (fits : width ≤ 64) :
    jolt_virtual_srai_value
      (jolt_virtual_muli_value answer (slliMultiplier (BitVec.ofNat 6 (64 - width))))
      (sraiBitmask (BitVec.ofNat 6 (64 - width))) =
        (answer.setWidth width).signExtend 64 := by
  have shiftLt : 64 - width < 2 ^ 6 := by omega
  rw [jolt_virtual_srai_value, ctz_sraiBitmask]
  simp only [slliMultiplier, BitVec.toNat_ofNat, Nat.mod_eq_of_lt shiftLt,
    jolt_virtual_muli_value, mulWide_low]
  rw [← shiftLeft_eq_mul_pow2]
  exact shift_pair_signExtend answer width positive fits

end JoltConstraints.Soundness
