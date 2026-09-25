import JoltBytecode.Bundles
import JoltBytecode.JoltISA.ExpansionsAutomated
import JoltBytecode.InstructionEquivalence.ProofSupport.Projection
import JoltBytecode.InstructionEquivalence.ProofSupport.Basic
import JoltBytecode.JoltISA.Expansions.ALU
import JoltBytecode.InstructionEquivalence.ProofSupport.ExpansionBlocks.ALU
import JoltBytecode.InstructionEquivalence.ProofSupport.InstructionLemmas.VirtualSRLI
import JoltBytecode.InstructionEquivalence.ProofSupport.InstructionLemmas.VirtualSignExtendWord
import JoltBytecode.InstructionEquivalence.ProofSupport.InstructionLemmas
import JoltBytecode.InstructionEquivalence.ProofSupport.ValueLemmas
import JoltBytecode.JoltISA.Values

set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# SRLIW: Jolt SLLI 32 + VirtualSRLI + VSEW = Sail SRLIW

Jolt program sequence:
1. `SLLI v0, rs1, 32` — clear upper 32 bits
2. `VirtualSRLI rd, v0, srliwBitmask shamt` — logical right shift by `ctz(bitmask)`
3. `VirtualSignExtendWord rd, rd` — sign-extend lower 32 bits of `rd`

The bitmask encodes `shamt + 32` via its count-trailing-zeros; see
`ctz_srliw_imm`.
-/

def srliw_imm (shamt : BitVec 64) : Nat :=
  let shift := (shamt.setWidth 5).toNat + 32
  let len := 64
  let ones := (1 <<< (len - shift)) - 1
  ones <<< shift

theorem ctz_srliw_imm (shamt : BitVec 64) :
    ctz (srliw_imm shamt) = (shamt.setWidth 5).toNat + 32 := by
  unfold srliw_imm
  simp only [Nat.shiftLeft_eq, one_mul]
  have h_lt : (shamt.setWidth 5).toNat < 32 := by
    have := (shamt.setWidth 5).isLt; norm_num at this; exact this
  have h_diff_pos : 0 < 64 - ((shamt.setWidth 5).toNat + 32) := by omega
  have h_m_pos : 0 < 2 ^ (64 - ((shamt.setWidth 5).toNat + 32)) - 1 := by
    have : 2 ≤ 2 ^ (64 - ((shamt.setWidth 5).toNat + 32)) :=
      le_trans (show (2 : Nat) ≤ 2 ^ 1 from by norm_num) (Nat.pow_le_pow_right (by omega) (by omega))
    omega
  rw [mul_comm, ctz_mul_pow2 ((shamt.setWidth 5).toNat + 32) h_m_pos,
      ctz_of_odd (pow2_sub_one_odd h_diff_pos)]

private theorem setWidth_5_roundtrip (shamt : BitVec 5) :
    (shamt.setWidth 64).setWidth 5 = shamt := by
  ext i; simp

private theorem ctz_srliw_imm_shamt5 (shamt : BitVec 5) :
    ctz (srliw_imm (shamt.setWidth 64)) = shamt.toNat + 32 := by
  rw [ctz_srliw_imm, setWidth_5_roundtrip]

private theorem srliw_shift_eq (v : BitVec 64) (shamt : BitVec 5) :
    sign_extend (m := 64)
      (Sail.BitVec.extractLsb
        ((v <<< 32) >>> ctz (srliw_imm (shamt.setWidth 64))) 31 0) =
    sign_extend (m := 64) (shift_bits_right (Sail.BitVec.extractLsb v 31 0) shamt) := by
  rw [ctz_srliw_imm_shamt5]
  simp only [sign_extend, shift_bits_right, Sail.BitVec.signExtend,
             Sail.BitVec.extractLsb, BitVec.extractLsb, Nat.sub_zero, Nat.reduceAdd]
  congr 1
  unfold BitVec.extractLsb'
  have nat_shr_zero : ∀ n : Nat, n >>> 0 = n := by simp
  simp only [nat_shr_zero]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.reducePow]
  have h_shl : (v <<< 32).toNat = v.toNat * 2^32 % 2^64 := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  have hs : shamt.toNat < 32 := by have := shamt.isLt; norm_num at this; exact this
  have h_cancel : v.toNat * 2^32 % 2^64 / 2^(shamt.toNat + 32) = v.toNat % 2^32 / 2^shamt.toNat := by
    have h1 : v.toNat * 2^32 % 2^64 = v.toNat % 2^32 * 2^32 := by omega
    have h2 : (2:Nat)^(shamt.toNat + 32) = 2^shamt.toNat * 2^32 := by rw [Nat.pow_add]
    rw [h1, h2, Nat.mul_div_mul_right _ _ (by positivity : (0:Nat) < 2^32)]
  rw [h_shl, h_cancel]
  simp only [Nat.reducePow]
  have hbound : v.toNat % 4294967296 / 2 ^ shamt.toNat < 4294967296 :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Nat.mod_lt _ (by positivity))
  rw [Nat.mod_eq_of_lt hbound]
  change _ = (BitVec.ofNat 32 v.toNat >>> (shamt).toNat).toNat
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.reducePow]

private theorem srliwProgram_bitmask_eq (shamt : BitVec 5) :
    JoltISA.srliwBitmask shamt = srliw_imm (shamt.setWidth 64) := by
  unfold JoltISA.srliwBitmask srliw_imm
  rw [setWidth_5_roundtrip]

abbrev srliw_sail_operation (shamt : BitVec 5) (v : BitVec 64) : BitVec 64 :=
  sign_extend (m := 64) (shift_bits_right (Sail.BitVec.extractLsb v 31 0) shamt)

abbrev srliw_jolt_val (shamt : BitVec 5) (v : BitVec 64) : BitVec 64 :=
  sign_extend (m := 64)
    (Sail.BitVec.extractLsb
      (jolt_virtual_srli_value (shift_bits_left v (32 : BitVec 6))
        (JoltISA.srliwBitmask shamt)) 31 0)

-- NOTE: Math theorem: the Jolt bitmask SRLIW sequence computes Sail SRLIW.
private theorem virtual_srliw_value_eq (v : BitVec 64) (shamt : BitVec 5) :
    srliw_jolt_val shamt v = srliw_sail_operation shamt v := by
  simp only [srliw_jolt_val, srliw_sail_operation]
  rw [srliwProgram_bitmask_eq]
  simpa only [jolt_virtual_srli_value, shift_bits_left] using srliw_shift_eq v shamt

/-- Main program-level equivalence for `SRLIW`. -/
def srliwProgramEqSailStatement (shamt : BitVec 5) (rs1 rd : regidx) (js : SailJoltState)
    (_h : UnarySourceReadWithLinkedCSRs rs1 js) : Prop :=
  System.systemProjectResult
      ((JoltISA.execProgram (JoltISA.srliwProgramAuto rd rs1 shamt)).run js) =
    (execute_SHIFTIWOP shamt rs1 rd sopw.SRLIW).run js.sail

/-- Main program-level equivalence for `SRLIW`. -/
theorem srliwProgram_eq_sail (shamt : BitVec 5) (rs1 rd : regidx) (js : SailJoltState)
    (h : UnarySourceReadWithLinkedCSRs rs1 js) :
    srliwProgramEqSailStatement shamt rs1 rd js h := by
  unfold srliwProgramEqSailStatement
  let v := h.rs1_val
  have h_read_rs1 : rX_bits rs1 js.sail = .ok v js.sail := h.rs1_read
  have h_project_initial : System.systemProject js = js.sail :=
    Projection.systemProject_eq_sail_of_compatible js h.linkedCSRs
  by_cases hrd : rd = regidx.Regidx 0
  · subst rd
    unfold JoltISA.srliwProgramAuto
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
      jolt_virtual_srliw_value v ((1 <<< 32) - (1 <<< shamt.toNat)) =
        srliw_sail_operation shamt v := by
    -- The expansion's mask 2^32 - 2^shamt is nonzero, so the zero-mask case is unused.
    have hmask : (1 <<< 32) - (1 <<< shamt.toNat) ≠ 0 := by
      rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.one_mul, Nat.one_mul]
      exact Nat.sub_ne_zero_of_lt (Nat.pow_lt_pow_right (by decide) (by simpa using shamt.isLt))
    unfold jolt_virtual_srliw_value srliw_sail_operation
    rw [if_neg hmask]
    rw [ctz_word_shift_bitmask shamt.toNat shamt.isLt]
    unfold sign_extend shift_bits_right
    simp [Sail.BitVec.signExtend, Sail.BitVec.extractLsb,
      BitVec.extractLsb, BitVec.extractLsb']
  obtain ⟨s', h_write⟩ := wX_shape rd (srliw_sail_operation shamt v) js.sail

  simp only [execute_SHIFTIWOP]
  simp only [EStateM.run_bind]
  simp only [EStateM.run]
  simp only [h_read_rs1, pure, EStateM.pure, h_write]

  unfold JoltISA.srliwProgramAuto
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
      (srliw_sail_operation shamt v) h.linkedCSRs h_write

end
