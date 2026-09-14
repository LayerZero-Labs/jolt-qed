import JoltBytecode.Bundles
import JoltBytecode.JoltISA.ExpansionsAutomated
import JoltBytecode.InstructionEquivalence.ProofSupport.Projection
import JoltBytecode.InstructionEquivalence.ProofSupport.Basic
import JoltBytecode.JoltISA.Expansions.ALU
import JoltBytecode.InstructionEquivalence.ProofSupport.InstructionLemmas.VirtualSRAI
import JoltBytecode.InstructionEquivalence.ProofSupport.InstructionLemmas.VirtualSignExtendWord
import JoltBytecode.InstructionEquivalence.ProofSupport.InstructionLemmas
import JoltBytecode.InstructionEquivalence.ProofSupport.ValueLemmas
import JoltBytecode.JoltISA.Values
import Mathlib.Data.Nat.Bitwise

set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# SRAIW: Jolt 3-step decomposition = Sail SRAIW

Jolt program sequence:
1. `VirtualSignExtendWord v1, rs1` — sign-extend `rs1[31:0]` to 64 bits
2. `VirtualSRAI rd, v1, sraiwBitmask shamt` — arithmetic right shift by `ctz(bitmask)`
3. `VirtualSignExtendWord rd, rd` — sign-extend lower 32 bits of `rd`
-/

def sraiw_bitmask (shamt : BitVec 64) : Nat :=
  let shift := (shamt.setWidth 5).toNat
  let ones := (1 <<< (64 - shift)) - 1
  ones <<< shift

lemma ctz_sraiw_bitmask (shamt : BitVec 64) :
    ctz (sraiw_bitmask shamt) = (shamt.setWidth 5).toNat := by
  unfold sraiw_bitmask
  simp only [Nat.shiftLeft_eq, one_mul]
  set shift := (shamt.setWidth 5).toNat
  have h_lt : shift < 32 := by have := (shamt.setWidth 5).isLt; norm_num at this; exact this
  have h_diff_pos : 0 < 64 - shift := by omega
  have h_m_pos : 0 < 2 ^ (64 - shift) - 1 := by
    have : 2 ≤ 2 ^ (64 - shift) :=
      le_trans (show (2 : Nat) ≤ 2 ^ 1 from by norm_num) (Nat.pow_le_pow_right (by omega) (by omega))
    omega
  rw [mul_comm, ctz_mul_pow2 shift h_m_pos, ctz_of_odd (pow2_sub_one_odd h_diff_pos)]; omega

private theorem setWidth_5_roundtrip (shamt : BitVec 5) :
    (shamt.setWidth 64).setWidth 5 = shamt := by
  ext i
  simp

private theorem extract_shamt64_low5 (shamt : BitVec 5) :
    Sail.BitVec.extractLsb (Sail.BitVec.extractLsb (shamt.setWidth 64) 31 0) 4 0 = shamt := by
  apply BitVec.eq_of_toNat_eq
  simp [Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb',
    BitVec.toNat_setWidth]
  exact shamt.isLt

private theorem sraiwProgram_bitmask_eq (shamt : BitVec 5) :
    JoltISA.sraiwBitmask shamt = sraiw_bitmask (shamt.setWidth 64) := by
  unfold JoltISA.sraiwBitmask sraiw_bitmask
  rw [setWidth_5_roundtrip]

abbrev sraiw_sail_operation (shamt : BitVec 5) (v : BitVec 64) : BitVec 64 :=
  sign_extend (m := 64)
    (shift_bits_right_arith (Sail.BitVec.extractLsb v 31 0) shamt)

abbrev sraiw_jolt_val (shamt : BitVec 5) (v : BitVec 64) : BitVec 64 :=
  sign_extend (m := 64)
    (Sail.BitVec.extractLsb
      (jolt_virtual_srai_value
        (sign_extend (m := 64) (Sail.BitVec.extractLsb v 31 0))
        (JoltISA.sraiwBitmask shamt)) 31 0)

private lemma sail_sraw_eq_riscv (v1 v2 : BitVec 64) :
    sign_extend (m := 64) (shift_bits_right_arith (Sail.BitVec.extractLsb v1 31 0)
      (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb v2 31 0) 4 0)) =
    Riscv.sraw v1 v2 := by
  unfold Riscv.sraw sign_extend shift_bits_right_arith
  simp [Sail.BitVec.signExtend, Sail.BitVec.toNatInt, Sail.BitVec.extractLsb,
        BitVec.extractLsb, BitVec.extractLsb']
  congr 2

private lemma signExtend64_sshiftRight_setWidth32 (x : BitVec 32) (s : Nat)
    (hs : s < 32) :
    ((x.signExtend 64).sshiftRight s).setWidth 32 = x.sshiftRight s := by
  ext i hi
  simp only [BitVec.getElem_setWidth]
  rw [BitVec.getLsbD_sshiftRight, BitVec.getElem_sshiftRight]
  have hi64 : ¬64 ≤ i := by omega
  have hi32 : ¬32 ≤ i := by omega
  have hshift64 : s + i < 64 := by omega
  by_cases hshift32 : s + i < 32
  · simp [hi64, hshift64, hshift32, ← BitVec.getLsbD_eq_getElem,
      BitVec.getLsbD_signExtend]
  · simp [hi64, hshift64, hshift32, BitVec.getLsbD_signExtend,
      -BitVec.getLsbD_eq_getElem, BitVec.msb_eq_getLsbD_last]

private theorem sraw_virtual_sra_value (v1 v2 : BitVec 64) :
    sign_extend (m := 64)
      (Sail.BitVec.extractLsb
        ((sign_extend (m := 64) (Sail.BitVec.extractLsb v1 31 0)).sshiftRight
          (v2.setWidth 5).toNat) 31 0) =
    sign_extend (m := 64) (shift_bits_right_arith (Sail.BitVec.extractLsb v1 31 0)
      (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb v2 31 0) 4 0)) := by
  rw [sail_sraw_eq_riscv]
  unfold Riscv.sraw sign_extend
  simp [Sail.BitVec.signExtend, Sail.BitVec.extractLsb,
    BitVec.extractLsb, BitVec.extractLsb']
  exact congrArg (fun x : BitVec 32 => x.signExtend 64)
    (signExtend64_sshiftRight_setWidth32 (v1.setWidth 32) (v2.toNat % 32) (by omega))

-- NOTE: Math theorem: the Jolt bitmask SRAIW sequence computes Sail SRAIW.
private theorem virtual_sraiw_value_eq (v : BitVec 64) (shamt : BitVec 5) :
    sraiw_jolt_val shamt v = sraiw_sail_operation shamt v := by
  simp only [sraiw_jolt_val, sraiw_sail_operation]
  unfold jolt_virtual_srai_value
  rw [sraiwProgram_bitmask_eq, ctz_sraiw_bitmask, setWidth_5_roundtrip]
  simpa only [setWidth_5_roundtrip, extract_shamt64_low5] using
    sraw_virtual_sra_value v (shamt.setWidth 64)

/-- Main program-level equivalence for `SRAIW`. -/
def sraiwProgramEqSailStatement (shamt : BitVec 5) (rs1 rd : regidx) (js : SailJoltState)
    (_h : UnarySourceReadWithLinkedCSRs rs1 js) : Prop :=
  System.systemProjectResult
      ((JoltISA.execProgram (JoltISA.sraiwProgramAuto rd rs1 shamt)).run js) =
    (execute_SHIFTIWOP shamt rs1 rd sopw.SRAIW).run js.sail

/-- Main program-level equivalence for `SRAIW`. -/
theorem sraiwProgram_eq_sail (shamt : BitVec 5) (rs1 rd : regidx) (js : SailJoltState)
    (h : UnarySourceReadWithLinkedCSRs rs1 js) :
    sraiwProgramEqSailStatement shamt rs1 rd js h := by
  unfold sraiwProgramEqSailStatement
  let v := h.rs1_val
  have h_read_rs1 : rX_bits rs1 js.sail = .ok v js.sail := h.rs1_read
  have h_project_initial : System.systemProject js = js.sail :=
    Projection.systemProject_eq_sail_of_compatible js h.linkedCSRs
  by_cases hrd : rd = regidx.Regidx 0
  · subst rd
    unfold JoltISA.sraiwProgramAuto
    rw [JoltISA.isX0_regidx_zero]
    simp only [↓reduceIte]
    change System.systemProjectResult
      ((JoltISA.execProgram JoltISA.pureWritebackRdZeroProgram).run js) = _
    rw [JoltISA.pureWritebackRdZeroProgram_run js]
    simp only [System.systemProjectResult]
    rw [h_project_initial]
    simp only [execute_SHIFTIWOP]
    simp only [EStateM.run_bind]
    simp only [EStateM.run]
    simp only [h_read_rs1, pure, EStateM.pure, wX_bits_regidx_zero]

  have hrd_not_x0 : JoltISA.isX0 rd = false :=
    JoltISA.isX0_eq_false_of_ne_zero hrd
  have h_value :
      jolt_virtual_sraiw_value v ((1 <<< 32) - (1 <<< shamt.toNat)) =
        sraiw_sail_operation shamt v := by
    unfold jolt_virtual_sraiw_value sraiw_sail_operation
    rw [ctz_word_shift_bitmask shamt.toNat shamt.isLt]
    unfold sign_extend shift_bits_right_arith
    simp [Sail.BitVec.signExtend, Sail.BitVec.toNatInt, Sail.BitVec.extractLsb,
      BitVec.extractLsb, BitVec.extractLsb']
  obtain ⟨s', h_write⟩ := wX_shape rd (sraiw_sail_operation shamt v) js.sail

  simp only [execute_SHIFTIWOP]
  simp only [EStateM.run_bind]
  simp only [EStateM.run]
  simp only [h_read_rs1, pure, EStateM.pure, h_write]

  unfold JoltISA.sraiwProgramAuto
  rw [hrd_not_x0]
  simp only [Bool.false_eq_true, ↓reduceIte]
  simp only [JoltISA.execProgram_instr]
  simp only [JoltISA.execInstr]
  simp only [JoltISA.readSrc, JoltISA.writeDst]
  unfold liftSail
  simp only [bind, EStateM.bind]
  simp only [h_read_rs1, h_value, h_write]
  simpa only [JoltISA.execProgram_done, pure, EStateM.pure, EStateM.run] using
    Projection.systemProjectResult_pure_retire_after_xreg_write rd js s'
      (sraiw_sail_operation shamt v) h.linkedCSRs h_write

end
