import JoltBytecode.InstructionEquivalence.ProofSupport.Memory.Write
import JoltBytecode.JoltISA.Values

/-!
# Pure splice facts for store-family expansions

The RV64 store inline sequences all use the same read-modify-write idea:

1. load the enclosing 64-bit dword;
2. shift a byte/halfword/word-sized mask into the target lane;
3. shift the low bits of `rs2` into the same lane; and
4. compute `dword ^ ((dword ^ shiftedValue) & shiftedMask)`.

This file proves the non-monadic facts about that expression.  The program
proofs should use these lemmas after the Jolt-ISA execution block has reduced
the bytecode sequence to a concrete spliced dword.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option mvcgen.warning false

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace StoreSplice

/-- Facts about an effective address and its enclosing dword address that are
common to all byte/halfword/word store splice proofs.  `ea_toNat` is the Nat
level bridge used when comparing hashmap keys. -/
structure DwordWindowFacts (ea base : BitVec 64) : Prop where
  base_is_aligned : base = ea &&& (-8 : BitVec 64)
  no_ovf : base.toNat + 7 < 2 ^ 64
  ea_toNat : ea.toNat = base.toNat + (ea - base).toNat

/-- Byte-store facts: the target offset may be any byte lane in the dword. -/
structure ByteStoreFacts (ea base : BitVec 64) : Prop extends DwordWindowFacts ea base where
  byte_offset_cases :
    (ea - base).toNat = 0 ∨ (ea - base).toNat = 1 ∨
    (ea - base).toNat = 2 ∨ (ea - base).toNat = 3 ∨
    (ea - base).toNat = 4 ∨ (ea - base).toNat = 5 ∨
    (ea - base).toNat = 6 ∨ (ea - base).toNat = 7

/-- Halfword-store facts: the target offset is one of the four halfword lanes. -/
structure HalfwordStoreFacts (ea base : BitVec 64) : Prop extends DwordWindowFacts ea base where
  halfword_aligned : ea &&& 1 = 0
  halfword_offset_cases :
    (ea - base).toNat = 0 ∨ (ea - base).toNat = 2 ∨
    (ea - base).toNat = 4 ∨ (ea - base).toNat = 6

/-- Word-store facts expressed in the same vocabulary as byte/halfword stores. -/
structure WordStoreFacts (ea base : BitVec 64) : Prop extends DwordWindowFacts ea base where
  word_aligned : ea &&& 3 = 0
  word_offset_cases : (ea - base).toNat = 0 ∨ (ea - base).toNat = 4

/-- The enclosing dword base used by store expansions is eight-byte aligned. -/
theorem dword_base_aligns (val : BitVec 64) (imm : BitVec 12) :
    compute_aligned_dword_base_address val imm &&& (7 : BitVec 64) = 0 := by
  unfold compute_aligned_dword_base_address load_effective_address
  exact align_down_8_and_7_eq_zero _

/-- The enclosing dword base has room for all eight bytes in the 64-bit address
space. -/
theorem dword_base_no_ovf (val : BitVec 64) (imm : BitVec 12) :
    (compute_aligned_dword_base_address val imm).toNat + 7 < 2 ^ 64 := by
  exact aligned_addr_no_ovf_of_align _ (dword_base_aligns val imm)

private theorem offset_bv_eq_low_three (ea : BitVec 64) :
    BitVec.ofNat 64 (ea &&& (7 : BitVec 64)).toNat =
      ea &&& (7 : BitVec 64) := by
  simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]

private theorem offset_sub_eq_low_three (ea : BitVec 64) :
    ea - (ea &&& (-8 : BitVec 64)) = ea &&& (7 : BitVec 64) := by
  have hsplit := write_addr_split_aligned_offset ea
  rw [offset_bv_eq_low_three ea] at hsplit
  nth_rewrite 1 [← hsplit]
  simpa only [BitVec.add_comm] using
    (BitVec.add_sub_cancel (ea &&& (7 : BitVec 64)) (ea &&& (-8 : BitVec 64)))

theorem ea_toNat_eq_base_plus_offset (ea : BitVec 64) :
    ea.toNat =
      (ea &&& (-8 : BitVec 64)).toNat +
        (ea - (ea &&& (-8 : BitVec 64))).toNat := by
  let base := ea &&& (-8 : BitVec 64)
  let off := (ea &&& (7 : BitVec 64)).toNat
  have hoff_lt : off < 8 := by
    exact write_addr_and_seven_lt_eight ea
  have hbase_no_ovf : base.toNat + 7 < 2 ^ 64 := by
    have hbase_align : base &&& (7 : BitVec 64) = 0 := by
      unfold base
      exact align_down_8_and_7_eq_zero _
    exact aligned_addr_no_ovf_of_align base hbase_align
  have hsub_toNat : (ea - base).toNat = off := by
    unfold base off
    rw [offset_sub_eq_low_three ea]
  have hoff_toNat : (BitVec.ofNat 64 off).toNat = off := by
    rw [BitVec.toNat_ofNat]
    have hoff64 : off < 2 ^ 64 := by omega
    exact Nat.mod_eq_of_lt hoff64
  have hsum_lt : base.toNat + (BitVec.ofNat 64 off).toNat < 2 ^ 64 := by
    rw [hoff_toNat]
    omega
  have hnat := BitVec.toNat_add_of_lt
    (x := base) (y := BitVec.ofNat 64 off) hsum_lt
  have hsplit := write_addr_split_aligned_offset ea
  unfold base off at hnat
  rw [hsplit] at hnat
  rw [hoff_toNat] at hnat
  rw [hsub_toNat]
  exact hnat

theorem byte_offset_cases (ea : BitVec 64) :
    (ea - (ea &&& (-8 : BitVec 64))).toNat = 0 ∨
    (ea - (ea &&& (-8 : BitVec 64))).toNat = 1 ∨
    (ea - (ea &&& (-8 : BitVec 64))).toNat = 2 ∨
    (ea - (ea &&& (-8 : BitVec 64))).toNat = 3 ∨
    (ea - (ea &&& (-8 : BitVec 64))).toNat = 4 ∨
    (ea - (ea &&& (-8 : BitVec 64))).toNat = 5 ∨
    (ea - (ea &&& (-8 : BitVec 64))).toNat = 6 ∨
    (ea - (ea &&& (-8 : BitVec 64))).toNat = 7 := by
  have hsub_toNat :
      (ea - (ea &&& (-8 : BitVec 64))).toNat =
        (ea &&& (7 : BitVec 64)).toNat := by
    rw [offset_sub_eq_low_three ea]
  have hoff_lt : (ea &&& (7 : BitVec 64)).toNat < 8 := by
    exact write_addr_and_seven_lt_eight ea
  rw [hsub_toNat]
  omega

theorem halfword_offset_cases (ea : BitVec 64)
    (halign : ea &&& (1 : BitVec 64) = 0) :
    (ea - (ea &&& (-8 : BitVec 64))).toNat = 0 ∨
    (ea - (ea &&& (-8 : BitVec 64))).toNat = 2 ∨
    (ea - (ea &&& (-8 : BitVec 64))).toNat = 4 ∨
    (ea - (ea &&& (-8 : BitVec 64))).toNat = 6 := by
  have hsub_toNat :
      (ea - (ea &&& (-8 : BitVec 64))).toNat =
        (ea &&& (7 : BitVec 64)).toNat := by
    rw [offset_sub_eq_low_three ea]
  have hoff_cases := write_halfword_offset_cases ea halign
  rw [hsub_toNat]
  exact hoff_cases

theorem word_offset_cases (ea : BitVec 64)
    (halign : ea &&& (3 : BitVec 64) = 0) :
    (ea - (ea &&& (-8 : BitVec 64))).toNat = 0 ∨
    (ea - (ea &&& (-8 : BitVec 64))).toNat = 4 := by
  have hsub_toNat :
      (ea - (ea &&& (-8 : BitVec 64))).toNat =
        (ea &&& (7 : BitVec 64)).toNat := by
    rw [offset_sub_eq_low_three ea]
  have hoff_cases := write_word_offset_cases ea halign
  rw [hsub_toNat]
  exact hoff_cases

theorem byteStoreFacts_of_effective_address
    (val : BitVec 64) (imm : BitVec 12) :
    ByteStoreFacts
      (load_effective_address val imm)
      (compute_aligned_dword_base_address val imm) := by
  exact
    { base_is_aligned := rfl
      no_ovf := dword_base_no_ovf val imm
      ea_toNat := ea_toNat_eq_base_plus_offset
        (load_effective_address val imm)
      byte_offset_cases := byte_offset_cases (load_effective_address val imm) }

theorem halfwordStoreFacts_of_effective_address
    (val : BitVec 64) (imm : BitVec 12)
    (halign : load_effective_address val imm &&& (1 : BitVec 64) = 0) :
    HalfwordStoreFacts
      (load_effective_address val imm)
      (compute_aligned_dword_base_address val imm) := by
  exact
    { base_is_aligned := rfl
      no_ovf := dword_base_no_ovf val imm
      ea_toNat := ea_toNat_eq_base_plus_offset
        (load_effective_address val imm)
      halfword_aligned := halign
      halfword_offset_cases := halfword_offset_cases
        (load_effective_address val imm) halign }

theorem wordStoreFacts_of_effective_address
    (val : BitVec 64) (imm : BitVec 12)
    (halign : load_effective_address val imm &&& (3 : BitVec 64) = 0) :
    WordStoreFacts
      (load_effective_address val imm)
      (compute_aligned_dword_base_address val imm) := by
  exact
    { base_is_aligned := rfl
      no_ovf := dword_base_no_ovf val imm
      ea_toNat := ea_toNat_eq_base_plus_offset
        (load_effective_address val imm)
      word_aligned := halign
      word_offset_cases := word_offset_cases
        (load_effective_address val imm) halign }

/-- The byte-store XOR-mask-XOR expression.  `shift` is measured in bits. -/
def byteSplice (dword_orig : BitVec 64) (byte_val : BitVec 8) (shift : Nat) : BitVec 64 :=
  let b_ext : BitVec 64 := byte_val.zeroExtend 64 <<< shift
  let mask : BitVec 64 := (0x00000000000000FF : BitVec 64) <<< shift
  dword_orig ^^^ ((dword_orig ^^^ b_ext) &&& mask)

/-- The halfword-store XOR-mask-XOR expression.  `shift` is measured in bits. -/
def halfwordSplice (dword_orig : BitVec 64) (halfword_val : BitVec 16) (shift : Nat) :
    BitVec 64 :=
  let h_ext : BitVec 64 := halfword_val.zeroExtend 64 <<< shift
  let mask : BitVec 64 := (0x000000000000FFFF : BitVec 64) <<< shift
  dword_orig ^^^ ((dword_orig ^^^ h_ext) &&& mask)

/-- The word-store XOR-mask-XOR expression.  `shift` is measured in bits. -/
def wordSplice (dword_orig : BitVec 64) (word_val : BitVec 32) (shift : Nat) : BitVec 64 :=
  let w_ext : BitVec 64 := word_val.zeroExtend 64 <<< shift
  let mask : BitVec 64 := (0x00000000FFFFFFFF : BitVec 64) <<< shift
  dword_orig ^^^ ((dword_orig ^^^ w_ext) &&& mask)

private theorem ofNat_shift_mask (mask n : Nat) :
    BitVec.ofNat 64 (mask <<< n) = (BitVec.ofNat 64 mask) <<< n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  apply (Nat.mul_mod mask (2 ^ n) (2 ^ 64)).trans
  have h := (Nat.mul_mod (mask % 2 ^ 64) (2 ^ n) (2 ^ 64)).symm
  rw [Nat.mod_mod] at h
  exact h

private theorem lowByte_zeroExtend (value : BitVec 64) :
    (Sail.BitVec.extractLsb value 7 0).zeroExtend 64 =
      value &&& (0xff : BitVec 64) := by
  unfold Sail.BitVec.extractLsb
  bv_decide

private theorem lowHalfword_zeroExtend (value : BitVec 64) :
    (Sail.BitVec.extractLsb value 15 0).zeroExtend 64 =
      value &&& (0xffff : BitVec 64) := by
  unfold Sail.BitVec.extractLsb
  bv_decide

private theorem lowWord_zeroExtend (value : BitVec 64) :
    (Sail.BitVec.extractLsb value 31 0).zeroExtend 64 =
      value &&& (0xffff_ffff : BitVec 64) := by
  unfold Sail.BitVec.extractLsb
  bv_decide

private theorem masked_add_eq_splice (original value mask : BitVec 64)
    (hcontained : value &&& mask = value) :
    (original &&& ~~~mask) + value =
      original ^^^ ((original ^^^ value) &&& mask) := by
  bv_decide

private theorem offset_toNat_eq_low_three {ea base : BitVec 64}
    (hbase : base = ea &&& (-8 : BitVec 64)) :
    (ea - base).toNat = (ea &&& (7 : BitVec 64)).toNat := by
  subst base
  exact congrArg BitVec.toNat (offset_sub_eq_low_three ea)

/-- The fused byte-store mask/shift/add expression is the existing byte splice. -/
theorem fusedByteSplice_eq (dword value ea base : BitVec 64)
    (hsetup : ByteStoreFacts ea base) :
    (dword &&& ~~~(jolt_virtual_window_mask_b_value ea 0)) +
        jolt_virtual_shift_data_b_value value ea =
      byteSplice dword (Sail.BitVec.extractLsb value 7 0)
        ((ea - base).toNat * 8) := by
  have hoff := offset_toNat_eq_low_three hsetup.base_is_aligned
  let off := (ea - base).toNat
  have hmask : jolt_virtual_window_mask_b_value ea 0 =
      (0xff : BitVec 64) <<< (off * 8) := by
    have hea0 : ea + sign_extend (m := 64) (0 : BitVec 12) = ea := by
      rw [show sign_extend (m := 64) (0 : BitVec 12) = 0 by decide]
      exact BitVec.add_zero ea
    unfold jolt_virtual_window_mask_b_value
    rw [hea0]
    dsimp only
    rw [← hoff, Nat.mul_comm]
    exact ofNat_shift_mask 0xff (off * 8)
  have hshift : jolt_virtual_shift_data_b_value value ea =
      (value &&& (0xff : BitVec 64)) <<< (off * 8) := by
    unfold jolt_virtual_shift_data_b_value
    rw [← hoff, Nat.mul_comm]
  have hcontained :
      ((value &&& (0xff : BitVec 64)) <<< (off * 8)) &&&
          ((0xff : BitVec 64) <<< (off * 8)) =
        (value &&& (0xff : BitVec 64)) <<< (off * 8) := by
    rw [← BitVec.shiftLeft_and_distrib]
    apply congrArg (fun x : BitVec 64 => x <<< (off * 8))
    bv_decide
  rw [hmask, hshift]
  rw [masked_add_eq_splice _ _ _ hcontained]
  unfold byteSplice
  rw [lowByte_zeroExtend]

/-- The fused halfword-store mask/shift/add expression is the existing halfword splice. -/
theorem fusedHalfwordSplice_eq (dword value ea base : BitVec 64)
    (hsetup : HalfwordStoreFacts ea base) :
    (dword &&& ~~~(jolt_virtual_window_mask_h_value ea 0)) +
        jolt_virtual_shift_data_h_value value ea =
      halfwordSplice dword (Sail.BitVec.extractLsb value 15 0)
        ((ea - base).toNat * 8) := by
  have hoff7 := offset_toNat_eq_low_three hsetup.base_is_aligned
  have hlow : ea &&& (7 : BitVec 64) = ea &&& (6 : BitVec 64) := by
    bv_decide
  have hoff : (ea - base).toNat = (ea &&& (6 : BitVec 64)).toNat :=
    hoff7.trans (congrArg BitVec.toNat hlow)
  let off := (ea - base).toNat
  have hmask : jolt_virtual_window_mask_h_value ea 0 =
      (0xffff : BitVec 64) <<< (off * 8) := by
    have hea0 : ea + sign_extend (m := 64) (0 : BitVec 12) = ea := by
      rw [show sign_extend (m := 64) (0 : BitVec 12) = 0 by decide]
      exact BitVec.add_zero ea
    unfold jolt_virtual_window_mask_h_value
    rw [hea0]
    dsimp only
    rw [← hoff, Nat.mul_comm]
    exact ofNat_shift_mask 0xffff (off * 8)
  have hshift : jolt_virtual_shift_data_h_value value ea =
      (value &&& (0xffff : BitVec 64)) <<< (off * 8) := by
    unfold jolt_virtual_shift_data_h_value
    rw [← hoff, Nat.mul_comm]
  have hcontained :
      ((value &&& (0xffff : BitVec 64)) <<< (off * 8)) &&&
          ((0xffff : BitVec 64) <<< (off * 8)) =
        (value &&& (0xffff : BitVec 64)) <<< (off * 8) := by
    rw [← BitVec.shiftLeft_and_distrib]
    apply congrArg (fun x : BitVec 64 => x <<< (off * 8))
    bv_decide
  rw [hmask, hshift]
  rw [masked_add_eq_splice _ _ _ hcontained]
  unfold halfwordSplice
  rw [lowHalfword_zeroExtend]

/-- The fused word-store mask/shift/add expression is the existing word splice. -/
theorem fusedWordSplice_eq (dword value ea base : BitVec 64)
    (hsetup : WordStoreFacts ea base) :
    (dword &&& ~~~(jolt_virtual_window_mask_w_value ea 0)) +
        jolt_virtual_shift_data_w_value value ea =
      wordSplice dword (Sail.BitVec.extractLsb value 31 0)
        ((ea - base).toNat * 8) := by
  have hoff7 := offset_toNat_eq_low_three hsetup.base_is_aligned
  have hlow : ea &&& (7 : BitVec 64) = ea &&& (4 : BitVec 64) := by
    bv_decide
  have hoff : (ea - base).toNat = (ea &&& (4 : BitVec 64)).toNat :=
    hoff7.trans (congrArg BitVec.toNat hlow)
  let off := (ea - base).toNat
  let word := ((ea >>> 2) &&& (1 : BitVec 64)).toNat
  have hwordBits : (ea >>> 2) &&& (1 : BitVec 64) =
      (ea &&& (4 : BitVec 64)) >>> 2 := by
    bv_decide
  have hwordShift : 32 * word = off * 8 := by
    dsimp only [word, off]
    rw [hwordBits]
    simp only [BitVec.toNat_ushiftRight]
    rcases hsetup.word_offset_cases with h0 | h4
    · have hoff0 : (ea &&& (4 : BitVec 64)).toNat = 0 := by omega
      rw [hoff0, h0]
      norm_num
    · have hoff4 : (ea &&& (4 : BitVec 64)).toNat = 4 := by omega
      rw [hoff4, h4]
      decide
  have hmask : jolt_virtual_window_mask_w_value ea 0 =
      (0xffff_ffff : BitVec 64) <<< (off * 8) := by
    have hea0 : ea + sign_extend (m := 64) (0 : BitVec 12) = ea := by
      rw [show sign_extend (m := 64) (0 : BitVec 12) = 0 by decide]
      exact BitVec.add_zero ea
    unfold jolt_virtual_window_mask_w_value
    rw [hea0]
    dsimp only
    rw [show ((ea >>> 2) &&& (1 : BitVec 64)).toNat = word by rfl]
    rw [hwordShift]
    exact ofNat_shift_mask 0xffff_ffff (off * 8)
  have hshift : jolt_virtual_shift_data_w_value value ea =
      (value &&& (0xffff_ffff : BitVec 64)) <<< (off * 8) := by
    unfold jolt_virtual_shift_data_w_value
    rw [← hoff, Nat.mul_comm]
  have hcontained :
      ((value &&& (0xffff_ffff : BitVec 64)) <<< (off * 8)) &&&
          ((0xffff_ffff : BitVec 64) <<< (off * 8)) =
        (value &&& (0xffff_ffff : BitVec 64)) <<< (off * 8) := by
    rw [← BitVec.shiftLeft_and_distrib]
    apply congrArg (fun x : BitVec 64 => x <<< (off * 8))
    bv_decide
  rw [hmask, hshift]
  rw [masked_add_eq_splice _ _ _ hcontained]
  unfold wordSplice
  rw [lowWord_zeroExtend]

/-- `spliced` is obtained from `original` by replacing one byte at `offset`. -/
def IsByteSplice (original spliced : BitVec 64) (byte_val : BitVec 8) (offset : Nat) :
    Prop :=
  (∀ j : Nat, j < 1 →
    dword_byte spliced (offset + j) = byte_byte byte_val j) ∧
  (∀ k : Nat, k < 8 →
    (k < offset ∨ k ≥ offset + 1) →
    dword_byte spliced k = dword_byte original k)

/-- `spliced` is obtained from `original` by replacing two bytes at `offset`. -/
def IsHalfwordSplice (original spliced : BitVec 64) (halfword_val : BitVec 16)
    (offset : Nat) : Prop :=
  (∀ j : Nat, j < 2 →
    dword_byte spliced (offset + j) = halfword_byte halfword_val j) ∧
  (∀ k : Nat, k < 8 →
    (k < offset ∨ k ≥ offset + 2) →
    dword_byte spliced k = dword_byte original k)

/-- `spliced` is obtained from `original` by replacing four bytes at `offset`. -/
def IsWordSplice (original spliced : BitVec 64) (word_val : BitVec 32) (offset : Nat) :
    Prop :=
  (∀ j : Nat, j < 4 →
    dword_byte spliced (offset + j) = word_byte word_val j) ∧
  (∀ k : Nat, k < 8 →
    (k < offset ∨ k ≥ offset + 4) →
    dword_byte spliced k = dword_byte original k)

private theorem byteMask_getElem_true {i : Nat} (hi : i < 8) :
    (255#64)[i] = true := by
  have hi64 : i < 64 := by omega
  have hmaskNat : Nat.testBit 255 i = true := by
    rw [show 255 = 2 ^ 8 - 1 by norm_num, Nat.testBit_two_pow_sub_one]
    simp [hi]
  have hmaskBase : (255#64).getLsbD i = true := by
    rw [BitVec.getLsbD_ofNat]
    simp [hi64, hmaskNat]
  rw [← BitVec.getLsbD_eq_getElem (x := (255#64)) hi64]
  exact hmaskBase

private theorem byteMask_getElem_false_of_ge8 {i : Nat} (hge : 8 ≤ i) (hi64 : i < 64) :
    (255#64)[i] = false := by
  have hmaskNat : Nat.testBit 255 i = false := by
    rw [show 255 = 2 ^ 8 - 1 by norm_num, Nat.testBit_two_pow_sub_one]
    simp [not_lt.mpr hge]
  have hmaskBase : (255#64).getLsbD i = false := by
    rw [BitVec.getLsbD_ofNat]
    simp [hi64, hmaskNat]
  rw [← BitVec.getLsbD_eq_getElem (x := (255#64)) hi64]
  exact hmaskBase

private theorem byteSplice_target_bytes_of_lt (dword_orig : BitVec 64)
    (byte_val : BitVec 8) (off : Nat) (hoff : off < 8) :
    ∀ j : Nat, j < 1 →
      dword_byte (byteSplice dword_orig byte_val (8 * off)) (off + j) =
      byte_byte byte_val j := by
  intro j hj
  have hj0 : j = 0 := by omega
  subst j
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hglobal64 : 8 * off + i < 64 := by omega
  have hsrc64 : i < 64 := by omega
  have hmaskIdx : (255#64)[i] = true := byteMask_getElem_true hi
  simp [dword_byte, byte_byte, byteSplice,
    BitVec.getLsbD_extractLsb', BitVec.getLsbD_xor, BitVec.getLsbD_and,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
    hglobal64, hsrc64, hi]
  rw [hmaskIdx]
  simp

private theorem byteSplice_other_bytes_of_lt (dword_orig : BitVec 64)
    (byte_val : BitVec 8) (off : Nat) (hoff : off < 8) :
    ∀ k : Nat, k < 8 →
      (k < off ∨ k ≥ off + 1) →
      dword_byte (byteSplice dword_orig byte_val (8 * off)) k =
      dword_byte dword_orig k := by
  intro k hk hout
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hglobal64 : 8 * k + i < 64 := by omega
  simp [dword_byte, byteSplice,
    BitVec.getLsbD_extractLsb', BitVec.getLsbD_xor, BitVec.getLsbD_and,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
    hglobal64, hi]
  by_cases hbefore : 8 * k + i < 8 * off
  · simp [hbefore]
  · have hidx_ge8 : 8 ≤ 8 * k + i - 8 * off := by
      rcases hout with hlt | hge
      · omega
      · omega
    have hidx_lt64 : 8 * k + i - 8 * off < 64 := by omega
    have hmaskIdx : (255#64)[8 * k + i - 8 * off] = false :=
      byteMask_getElem_false_of_ge8 hidx_ge8 hidx_lt64
    simp [hbefore, hmaskIdx]

private theorem halfwordMask_getElem_true {i : Nat} (hi : i < 16) :
    (65535#64)[i] = true := by
  have hi64 : i < 64 := by omega
  have hmaskNat : Nat.testBit 65535 i = true := by
    rw [show 65535 = 2 ^ 16 - 1 by norm_num, Nat.testBit_two_pow_sub_one]
    simp [hi]
  have hmaskBase : (65535#64).getLsbD i = true := by
    rw [BitVec.getLsbD_ofNat]
    simp [hi64, hmaskNat]
  rw [← BitVec.getLsbD_eq_getElem (x := (65535#64)) hi64]
  exact hmaskBase

private theorem halfwordMask_getElem_false_of_ge16 {i : Nat} (hge : 16 ≤ i)
    (hi64 : i < 64) :
    (65535#64)[i] = false := by
  have hmaskNat : Nat.testBit 65535 i = false := by
    rw [show 65535 = 2 ^ 16 - 1 by norm_num, Nat.testBit_two_pow_sub_one]
    simp [not_lt.mpr hge]
  have hmaskBase : (65535#64).getLsbD i = false := by
    rw [BitVec.getLsbD_ofNat]
    simp [hi64, hmaskNat]
  rw [← BitVec.getLsbD_eq_getElem (x := (65535#64)) hi64]
  exact hmaskBase

private theorem halfwordSplice_target_bytes_of_bound (dword_orig : BitVec 64)
    (halfword_val : BitVec 16) (off : Nat) (hoff : off + 2 ≤ 8) :
    ∀ j : Nat, j < 2 →
      dword_byte (halfwordSplice dword_orig halfword_val (8 * off)) (off + j) =
      halfword_byte halfword_val j := by
  intro j hj
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hglobal64 : 8 * (off + j) + i < 64 := by omega
  have hsrc64 : 8 * j + i < 64 := by omega
  have hsrc16 : 8 * j + i < 16 := by omega
  have hnotlt : ¬8 * (off + j) + i < 8 * off := by omega
  have hsub : 8 * (off + j) + i - 8 * off = 8 * j + i := by omega
  have hmaskIdx : (65535#64)[8 * j + i] = true :=
    halfwordMask_getElem_true hsrc16
  simp [dword_byte, halfword_byte, halfwordSplice,
    BitVec.getLsbD_extractLsb', BitVec.getLsbD_xor, BitVec.getLsbD_and,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
    hglobal64, hsrc64, hnotlt, hsub, hi]
  rw [hmaskIdx]
  simp

private theorem halfwordSplice_other_bytes_of_bound (dword_orig : BitVec 64)
    (halfword_val : BitVec 16) (off : Nat) (hoff : off + 2 ≤ 8) :
    ∀ k : Nat, k < 8 →
      (k < off ∨ k ≥ off + 2) →
      dword_byte (halfwordSplice dword_orig halfword_val (8 * off)) k =
      dword_byte dword_orig k := by
  intro k hk hout
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hglobal64 : 8 * k + i < 64 := by omega
  simp [dword_byte, halfwordSplice,
    BitVec.getLsbD_extractLsb', BitVec.getLsbD_xor, BitVec.getLsbD_and,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
    hglobal64, hi]
  by_cases hbefore : 8 * k + i < 8 * off
  · simp [hbefore]
  · have hidx_ge16 : 16 ≤ 8 * k + i - 8 * off := by
      rcases hout with hlt | hge
      · omega
      · omega
    have hidx_lt64 : 8 * k + i - 8 * off < 64 := by omega
    have hmaskIdx : (65535#64)[8 * k + i - 8 * off] = false :=
      halfwordMask_getElem_false_of_ge16 hidx_ge16 hidx_lt64
    simp [hbefore, hmaskIdx]

private theorem wordMask_getElem_true {i : Nat} (hi : i < 32) :
    (4294967295#64)[i] = true := by
  have hi64 : i < 64 := by omega
  have hmaskNat : Nat.testBit 4294967295 i = true := by
    rw [show 4294967295 = 2 ^ 32 - 1 by norm_num, Nat.testBit_two_pow_sub_one]
    simp [hi]
  have hmaskBase : (4294967295#64).getLsbD i = true := by
    rw [BitVec.getLsbD_ofNat]
    simp [hi64, hmaskNat]
  rw [← BitVec.getLsbD_eq_getElem (x := (4294967295#64)) hi64]
  exact hmaskBase

private theorem wordMask_getElem_false_of_ge32 {i : Nat} (hge : 32 ≤ i)
    (hi64 : i < 64) :
    (4294967295#64)[i] = false := by
  have hmaskNat : Nat.testBit 4294967295 i = false := by
    rw [show 4294967295 = 2 ^ 32 - 1 by norm_num, Nat.testBit_two_pow_sub_one]
    simp [not_lt.mpr hge]
  have hmaskBase : (4294967295#64).getLsbD i = false := by
    rw [BitVec.getLsbD_ofNat]
    simp [hi64, hmaskNat]
  rw [← BitVec.getLsbD_eq_getElem (x := (4294967295#64)) hi64]
  exact hmaskBase

private theorem wordSplice_target_bytes_of_bound (dword_orig : BitVec 64)
    (word_val : BitVec 32) (off : Nat) (hoff : off + 4 ≤ 8) :
    ∀ j : Nat, j < 4 →
      dword_byte (wordSplice dword_orig word_val (8 * off)) (off + j) =
      word_byte word_val j := by
  intro j hj
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hglobal64 : 8 * (off + j) + i < 64 := by omega
  have hsrc64 : 8 * j + i < 64 := by omega
  have hsrc32 : 8 * j + i < 32 := by omega
  have hnotlt : ¬8 * (off + j) + i < 8 * off := by omega
  have hsub : 8 * (off + j) + i - 8 * off = 8 * j + i := by omega
  have hmaskIdx : (4294967295#64)[8 * j + i] = true :=
    wordMask_getElem_true hsrc32
  simp [dword_byte, word_byte, wordSplice,
    BitVec.getLsbD_extractLsb', BitVec.getLsbD_xor, BitVec.getLsbD_and,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
    hglobal64, hsrc64, hnotlt, hsub, hi]
  rw [hmaskIdx]
  simp

private theorem wordSplice_other_bytes_of_bound (dword_orig : BitVec 64)
    (word_val : BitVec 32) (off : Nat) (hoff : off + 4 ≤ 8) :
    ∀ k : Nat, k < 8 →
      (k < off ∨ k ≥ off + 4) →
      dword_byte (wordSplice dword_orig word_val (8 * off)) k =
      dword_byte dword_orig k := by
  intro k hk hout
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hglobal64 : 8 * k + i < 64 := by omega
  simp [dword_byte, wordSplice,
    BitVec.getLsbD_extractLsb', BitVec.getLsbD_xor, BitVec.getLsbD_and,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
    hglobal64, hi]
  by_cases hbefore : 8 * k + i < 8 * off
  · simp [hbefore]
  · have hidx_ge32 : 32 ≤ 8 * k + i - 8 * off := by
      rcases hout with hlt | hge
      · omega
      · omega
    have hidx_lt64 : 8 * k + i - 8 * off < 64 := by omega
    have hmaskIdx : (4294967295#64)[8 * k + i - 8 * off] = false :=
      wordMask_getElem_false_of_ge32 hidx_ge32 hidx_lt64
    simp [hbefore, hmaskIdx]

/-- The byte splice writes the target byte. -/
theorem byteSplice_target_bytes (dword_orig : BitVec 64) (byte_val : BitVec 8)
    (off : Nat)
    (hoff :
      off = 0 ∨ off = 1 ∨ off = 2 ∨ off = 3 ∨
      off = 4 ∨ off = 5 ∨ off = 6 ∨ off = 7) :
    ∀ j : Nat, j < 1 →
      dword_byte (byteSplice dword_orig byte_val (8 * off)) (off + j) =
      byte_byte byte_val j := by
  have hoff_lt : off < 8 := by
    rcases hoff with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 <;> omega
  exact byteSplice_target_bytes_of_lt dword_orig byte_val off hoff_lt

/-- The byte splice preserves every non-target byte. -/
theorem byteSplice_other_bytes (dword_orig : BitVec 64) (byte_val : BitVec 8)
    (off : Nat)
    (hoff :
      off = 0 ∨ off = 1 ∨ off = 2 ∨ off = 3 ∨
      off = 4 ∨ off = 5 ∨ off = 6 ∨ off = 7) :
    ∀ k : Nat, k < 8 →
      (k < off ∨ k ≥ off + 1) →
      dword_byte (byteSplice dword_orig byte_val (8 * off)) k =
      dword_byte dword_orig k := by
  have hoff_lt : off < 8 := by
    rcases hoff with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 <;> omega
  exact byteSplice_other_bytes_of_lt dword_orig byte_val off hoff_lt

/-- The byte-store XOR-mask-XOR expression is a one-byte splice. -/
theorem byteSplice_spec (dword_orig : BitVec 64) (byte_val : BitVec 8)
    (off : Nat)
    (hoff :
      off = 0 ∨ off = 1 ∨ off = 2 ∨ off = 3 ∨
      off = 4 ∨ off = 5 ∨ off = 6 ∨ off = 7) :
    let spliced := byteSplice dword_orig byte_val (8 * off)
    IsByteSplice dword_orig spliced byte_val off := by
  dsimp [IsByteSplice]
  refine ⟨?_, ?_⟩
  · intro j hj
    simpa using byteSplice_target_bytes dword_orig byte_val off hoff j hj
  · intro k hk hout
    simpa using byteSplice_other_bytes dword_orig byte_val off hoff k hk hout

/-- The halfword splice writes the target two bytes. -/
theorem halfwordSplice_target_bytes (dword_orig : BitVec 64)
    (halfword_val : BitVec 16) (off : Nat)
    (hoff : off = 0 ∨ off = 2 ∨ off = 4 ∨ off = 6) :
    ∀ j : Nat, j < 2 →
      dword_byte (halfwordSplice dword_orig halfword_val (8 * off)) (off + j) =
      halfword_byte halfword_val j := by
  have hoff_bound : off + 2 ≤ 8 := by
    rcases hoff with h0 | h2 | h4 | h6 <;> omega
  exact halfwordSplice_target_bytes_of_bound dword_orig halfword_val off hoff_bound

/-- The halfword splice preserves every non-target byte. -/
theorem halfwordSplice_other_bytes (dword_orig : BitVec 64)
    (halfword_val : BitVec 16) (off : Nat)
    (hoff : off = 0 ∨ off = 2 ∨ off = 4 ∨ off = 6) :
    ∀ k : Nat, k < 8 →
      (k < off ∨ k ≥ off + 2) →
      dword_byte (halfwordSplice dword_orig halfword_val (8 * off)) k =
      dword_byte dword_orig k := by
  have hoff_bound : off + 2 ≤ 8 := by
    rcases hoff with h0 | h2 | h4 | h6 <;> omega
  exact halfwordSplice_other_bytes_of_bound dword_orig halfword_val off hoff_bound

/-- The halfword-store XOR-mask-XOR expression is a two-byte splice. -/
theorem halfwordSplice_spec (dword_orig : BitVec 64) (halfword_val : BitVec 16)
    (off : Nat) (hoff : off = 0 ∨ off = 2 ∨ off = 4 ∨ off = 6) :
    let spliced := halfwordSplice dword_orig halfword_val (8 * off)
    IsHalfwordSplice dword_orig spliced halfword_val off := by
  dsimp [IsHalfwordSplice]
  refine ⟨?_, ?_⟩
  · intro j hj
    simpa using halfwordSplice_target_bytes dword_orig halfword_val off hoff j hj
  · intro k hk hout
    simpa using halfwordSplice_other_bytes dword_orig halfword_val off hoff k hk hout

/-- The word splice writes the target four bytes. -/
theorem wordSplice_target_bytes (dword_orig : BitVec 64) (word_val : BitVec 32)
    (off : Nat) (hoff : off = 0 ∨ off = 4) :
    ∀ j : Nat, j < 4 →
      dword_byte (wordSplice dword_orig word_val (8 * off)) (off + j) =
      word_byte word_val j := by
  have hoff_bound : off + 4 ≤ 8 := by
    rcases hoff with h0 | h4 <;> omega
  exact wordSplice_target_bytes_of_bound dword_orig word_val off hoff_bound

/-- The word splice preserves every non-target byte. -/
theorem wordSplice_other_bytes (dword_orig : BitVec 64) (word_val : BitVec 32)
    (off : Nat) (hoff : off = 0 ∨ off = 4) :
    ∀ k : Nat, k < 8 →
      (k < off ∨ k ≥ off + 4) →
      dword_byte (wordSplice dword_orig word_val (8 * off)) k =
      dword_byte dword_orig k := by
  have hoff_bound : off + 4 ≤ 8 := by
    rcases hoff with h0 | h4 <;> omega
  exact wordSplice_other_bytes_of_bound dword_orig word_val off hoff_bound

/-- The word-store XOR-mask-XOR expression is a four-byte splice. -/
theorem wordSplice_spec (dword_orig : BitVec 64) (word_val : BitVec 32)
    (off : Nat) (hoff : off = 0 ∨ off = 4) :
    let spliced := wordSplice dword_orig word_val (8 * off)
    IsWordSplice dword_orig spliced word_val off := by
  dsimp [IsWordSplice]
  refine ⟨?_, ?_⟩
  · intro j hj
    simpa using wordSplice_target_bytes dword_orig word_val off hoff j hj
  · intro k hk hout
    simpa using wordSplice_other_bytes dword_orig word_val off hoff k hk hout

private theorem dword_align_down_8_and_7_eq_zero (x : BitVec 64) :
    (x &&& (-8 : BitVec 64)) &&& (7 : BitVec 64) = 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_and]
  have hneg8 : (-8 : BitVec 64).toNat = 2 ^ 64 - 8 := by decide
  have h7 : (7 : BitVec 64).toNat = 7 := by decide
  have h0 : (0 : BitVec 64).toNat = 0 := by decide
  rw [hneg8, h7, h0]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.zero_testBit]
  by_cases hlt : i < 3
  · have hmask : (2 ^ 64 - 8).testBit i = false := by
      interval_cases i <;> decide
    norm_num at hmask
    rw [Nat.testBit_and]
    simp [hmask]
  · have h7bit : (7 : Nat).testBit i = false := by
      apply Nat.testBit_lt_two_pow
      have : 3 ≤ i := by omega
      exact lt_of_lt_of_le (by norm_num : 7 < 2 ^ 3)
        (Nat.pow_le_pow_right (by norm_num : 0 < 2) this)
    simp [h7bit]

/-- The absolute address for the `j`-th target byte can be written either from
the dword base plus the lane offset or from the native effective address. -/
private theorem target_addr_eq_of_window {ea base : BitVec 64}
    (h : DwordWindowFacts ea base) (j : Nat) :
    base.toNat + ((ea - base).toNat + j) = ea.toNat + j := by
  rw [h.ea_toNat]
  omega

/-- Every dword byte is either outside a target sub-window of width `width`, or
is the `j`-th byte inside that target window. -/
private theorem k_in_target_or_outside_width (off width k : Nat) :
    (k < off ∨ k ≥ off + width) ∨
    ∃ j : Nat, j < width ∧ k = off + j := by
  by_cases hlt : k < off
  · exact Or.inl (Or.inl hlt)
  · by_cases hge : k ≥ off + width
    · exact Or.inl (Or.inr hge)
    · right
      refine ⟨k - off, ?_, ?_⟩ <;> omega

/-- If an address is outside the enclosing dword window, it is outside the
native byte-store window as well. -/
private theorem outside_dword_window_implies_outside_byte_window
    {ea base : BitVec 64} (a : Nat) (h : ByteStoreFacts ea base)
    (hout : a < base.toNat ∨ a ≥ base.toNat + 8) :
    a < ea.toNat ∨ a ≥ ea.toNat + 1 := by
  rw [h.ea_toNat]
  have hoff_le : (ea - base).toNat + 1 ≤ 8 := by
    rcases h.byte_offset_cases with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 <;> omega
  rcases hout with hlt | hge
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

/-- If an address is outside the enclosing dword window, it is outside the
native halfword-store window as well. -/
private theorem outside_dword_window_implies_outside_halfword_window
    {ea base : BitVec 64} (a : Nat) (h : HalfwordStoreFacts ea base)
    (hout : a < base.toNat ∨ a ≥ base.toNat + 8) :
    a < ea.toNat ∨ a ≥ ea.toNat + 2 := by
  rw [h.ea_toNat]
  have hoff_le : (ea - base).toNat + 2 ≤ 8 := by
    rcases h.halfword_offset_cases with h0 | h2 | h4 | h6 <;> omega
  rcases hout with hlt | hge
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

/-- If an address is outside the enclosing dword window, it is outside the
native word-store window as well. -/
private theorem outside_dword_window_implies_outside_word_window
    {ea base : BitVec 64} (a : Nat) (h : WordStoreFacts ea base)
    (hout : a < base.toNat ∨ a ≥ base.toNat + 8) :
    a < ea.toNat ∨ a ≥ ea.toNat + 4 := by
  rw [h.ea_toNat]
  have hoff_le : (ea - base).toNat + 4 ≤ 8 := by
    rcases h.word_offset_cases with h0 | h4 <;> omega
  rcases hout with hlt | hge
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

/-- If a dword byte index lies outside the byte target lane, then the absolute
address lies outside the native byte-store window. -/
private theorem outside_target_addr_outside_byte_window
    {ea base : BitVec 64} (k : Nat) (h : ByteStoreFacts ea base)
    (hout : k < (ea - base).toNat ∨ k ≥ (ea - base).toNat + 1) :
    base.toNat + k < ea.toNat ∨ base.toNat + k ≥ ea.toNat + 1 := by
  rw [h.ea_toNat]
  omega

/-- Halfword analogue of `outside_target_addr_outside_byte_window`. -/
private theorem outside_target_addr_outside_halfword_window
    {ea base : BitVec 64} (k : Nat) (h : HalfwordStoreFacts ea base)
    (hout : k < (ea - base).toNat ∨ k ≥ (ea - base).toNat + 2) :
    base.toNat + k < ea.toNat ∨ base.toNat + k ≥ ea.toNat + 2 := by
  rw [h.ea_toNat]
  omega

/-- Word analogue of `outside_target_addr_outside_byte_window`. -/
private theorem outside_target_addr_outside_word_window
    {ea base : BitVec 64} (k : Nat) (h : WordStoreFacts ea base)
    (hout : k < (ea - base).toNat ∨ k ≥ (ea - base).toNat + 4) :
    base.toNat + k < ea.toNat ∨ base.toNat + k ≥ ea.toNat + 4 := by
  rw [h.ea_toNat]
  omega

/-- Writing a spliced dword is the same hashmap update as a native byte store,
provided the spliced dword has the byte-store shape and the original dword was
loaded from the enclosing dword window. -/
theorem dword_store_splice_eq_byte_store_populated
    (s : SailState) (ea base : BitVec 64)
    (byte_val : BitVec 8) (dword_orig dword_new : BitVec 64)
    (hsetup : ByteStoreFacts ea base)
    (hpop : ∀ k : Nat, k < 8 -> s.mem.get? (base.toNat + k) ≠ none)
    (hload : ∀ k : Nat, (hk : k < 8) →
      dword_byte dword_orig k =
        loaded_byte_at s (base + BitVec.ofNat 64 k)
          (by
            rw [toNat_base_add_small base k hk hsetup.no_ovf]
            exact Option.ne_none_iff_exists'.mp (hpop k hk)))
    (hsplice_target : ∀ j : Nat, j < 1 →
      dword_byte dword_new ((ea - base).toNat + j) = byte_byte byte_val j)
    (hsplice_other : ∀ k : Nat, k < 8 →
      (k < (ea - base).toNat ∨ k ≥ (ea - base).toNat + 1) →
      dword_byte dword_new k = dword_byte dword_orig k) :
    (state_after_dword_store s base dword_new).mem =
    (state_after_byte_store s ea byte_val).mem := by
  apply mem_eq_of_eq_on_dword_window base.toNat
      (state_after_dword_store s base dword_new).mem
      (state_after_byte_store s ea byte_val).mem
      s.mem
  · intro a ha
    simpa using stored_dword_untouched s base base dword_new a ha
  · intro a ha
    have ha_byte : a < ea.toNat ∨ a ≥ ea.toNat + 1 :=
      outside_dword_window_implies_outside_byte_window a hsetup ha
    simpa using stored_byte_untouched s ea byte_val a ha_byte
  · intro k hk
    rcases k_in_target_or_outside_width (ea - base).toNat 1 k with hout | htarget
    ·
        rw [stored_dword_get?_hit s base dword_new k hk]
        rw [hsplice_other k hk hout]
        have haddr : (base + BitVec.ofNat 64 k).toNat = base.toNat + k :=
          toNat_base_add_small base k hk hsetup.no_ovf
        have hpresent :
            MemBytePresentAt s (base + BitVec.ofNat 64 k).toNat := by
          simpa [haddr] using Option.ne_none_iff_exists'.mp (hpop k hk)
        have hload' : loaded_byte_at s (base + BitVec.ofNat 64 k) hpresent =
            dword_byte dword_orig k := by
          simpa using (hload k hk).symm
        have hsome : s.mem.get? (base.toNat + k) = some (dword_byte dword_orig k) := by
          simpa [haddr] using get?_of_loaded_byte_at_eq s (base + BitVec.ofNat 64 k)
            (dword_byte dword_orig k) hpresent hload'
        rw [← hsome]
        have haddr_out : base.toNat + k < ea.toNat ∨ base.toNat + k ≥ ea.toNat + 1 :=
          outside_target_addr_outside_byte_window k hsetup hout
        symm
        simpa using stored_byte_untouched s ea byte_val (base.toNat + k) haddr_out
    ·
        obtain ⟨j, hj, hk_eq⟩ := htarget
        rw [hk_eq]
        rw [stored_dword_get?_hit s base dword_new ((ea - base).toNat + j) (by omega)]
        rw [hsplice_target j hj]
        rw [target_addr_eq_of_window hsetup.toDwordWindowFacts j]
        symm
        simpa using stored_byte_get?_hit s ea byte_val j hj

/-- Writing a spliced dword is the same hashmap update as a native halfword
store. -/
theorem dword_store_splice_eq_halfword_store_populated
    (s : SailState) (ea base : BitVec 64)
    (halfword_val : BitVec 16) (dword_orig dword_new : BitVec 64)
    (hsetup : HalfwordStoreFacts ea base)
    (hpop : ∀ k : Nat, k < 8 -> s.mem.get? (base.toNat + k) ≠ none)
    (hload : ∀ k : Nat, (hk : k < 8) →
      dword_byte dword_orig k =
        loaded_byte_at s (base + BitVec.ofNat 64 k)
          (by
            rw [toNat_base_add_small base k hk hsetup.no_ovf]
            exact Option.ne_none_iff_exists'.mp (hpop k hk)))
    (hsplice_target : ∀ j : Nat, j < 2 →
      dword_byte dword_new ((ea - base).toNat + j) = halfword_byte halfword_val j)
    (hsplice_other : ∀ k : Nat, k < 8 →
      (k < (ea - base).toNat ∨ k ≥ (ea - base).toNat + 2) →
      dword_byte dword_new k = dword_byte dword_orig k) :
    (state_after_dword_store s base dword_new).mem =
    (state_after_halfword_store s ea halfword_val).mem := by
  apply mem_eq_of_eq_on_dword_window base.toNat
      (state_after_dword_store s base dword_new).mem
      (state_after_halfword_store s ea halfword_val).mem
      s.mem
  · intro a ha
    simpa using stored_dword_untouched s base base dword_new a ha
  · intro a ha
    have ha_half : a < ea.toNat ∨ a ≥ ea.toNat + 2 :=
      outside_dword_window_implies_outside_halfword_window a hsetup ha
    simpa using stored_halfword_untouched s ea halfword_val a ha_half
  · intro k hk
    rcases k_in_target_or_outside_width (ea - base).toNat 2 k with hout | htarget
    ·
        rw [stored_dword_get?_hit s base dword_new k hk]
        rw [hsplice_other k hk hout]
        have haddr : (base + BitVec.ofNat 64 k).toNat = base.toNat + k :=
          toNat_base_add_small base k hk hsetup.no_ovf
        have hpresent :
            MemBytePresentAt s (base + BitVec.ofNat 64 k).toNat := by
          simpa [haddr] using Option.ne_none_iff_exists'.mp (hpop k hk)
        have hload' : loaded_byte_at s (base + BitVec.ofNat 64 k) hpresent =
            dword_byte dword_orig k := by
          simpa using (hload k hk).symm
        have hsome : s.mem.get? (base.toNat + k) = some (dword_byte dword_orig k) := by
          simpa [haddr] using get?_of_loaded_byte_at_eq s (base + BitVec.ofNat 64 k)
            (dword_byte dword_orig k) hpresent hload'
        rw [← hsome]
        have haddr_out : base.toNat + k < ea.toNat ∨ base.toNat + k ≥ ea.toNat + 2 :=
          outside_target_addr_outside_halfword_window k hsetup hout
        symm
        simpa using stored_halfword_untouched s ea halfword_val (base.toNat + k) haddr_out
    ·
        obtain ⟨j, hj, hk_eq⟩ := htarget
        rw [hk_eq]
        rw [stored_dword_get?_hit s base dword_new ((ea - base).toNat + j) (by omega)]
        rw [hsplice_target j hj]
        rw [target_addr_eq_of_window hsetup.toDwordWindowFacts j]
        symm
        simpa using stored_halfword_get?_hit s ea halfword_val j hj

/-- Writing a spliced dword is the same hashmap update as a native word store. -/
theorem dword_store_splice_eq_word_store_populated
    (s : SailState) (ea base : BitVec 64)
    (word_val : BitVec 32) (dword_orig dword_new : BitVec 64)
    (hsetup : WordStoreFacts ea base)
    (hpop : ∀ k : Nat, k < 8 -> s.mem.get? (base.toNat + k) ≠ none)
    (hload : ∀ k : Nat, (hk : k < 8) →
      dword_byte dword_orig k =
        loaded_byte_at s (base + BitVec.ofNat 64 k)
          (by
            rw [toNat_base_add_small base k hk hsetup.no_ovf]
            exact Option.ne_none_iff_exists'.mp (hpop k hk)))
    (hsplice_target : ∀ j : Nat, j < 4 →
      dword_byte dword_new ((ea - base).toNat + j) = word_byte word_val j)
    (hsplice_other : ∀ k : Nat, k < 8 →
      (k < (ea - base).toNat ∨ k ≥ (ea - base).toNat + 4) →
      dword_byte dword_new k = dword_byte dword_orig k) :
    (state_after_dword_store s base dword_new).mem =
    (state_after_word_store s ea word_val).mem := by
  apply mem_eq_of_eq_on_dword_window base.toNat
      (state_after_dword_store s base dword_new).mem
      (state_after_word_store s ea word_val).mem
      s.mem
  · intro a ha
    simpa using stored_dword_untouched s base base dword_new a ha
  · intro a ha
    have ha_word : a < ea.toNat ∨ a ≥ ea.toNat + 4 :=
      outside_dword_window_implies_outside_word_window a hsetup ha
    simpa using stored_word_untouched s ea word_val a ha_word
  · intro k hk
    rcases k_in_target_or_outside_width (ea - base).toNat 4 k with hout | htarget
    ·
        rw [stored_dword_get?_hit s base dword_new k hk]
        rw [hsplice_other k hk hout]
        have haddr : (base + BitVec.ofNat 64 k).toNat = base.toNat + k :=
          toNat_base_add_small base k hk hsetup.no_ovf
        have hpresent :
            MemBytePresentAt s (base + BitVec.ofNat 64 k).toNat := by
          simpa [haddr] using Option.ne_none_iff_exists'.mp (hpop k hk)
        have hload' : loaded_byte_at s (base + BitVec.ofNat 64 k) hpresent =
            dword_byte dword_orig k := by
          simpa using (hload k hk).symm
        have hsome : s.mem.get? (base.toNat + k) = some (dword_byte dword_orig k) := by
          simpa [haddr] using get?_of_loaded_byte_at_eq s (base + BitVec.ofNat 64 k)
            (dword_byte dword_orig k) hpresent hload'
        rw [← hsome]
        have haddr_out : base.toNat + k < ea.toNat ∨ base.toNat + k ≥ ea.toNat + 4 :=
          outside_target_addr_outside_word_window k hsetup hout
        symm
        simpa using stored_word_untouched s ea word_val (base.toNat + k) haddr_out
    ·
        obtain ⟨j, hj, hk_eq⟩ := htarget
        rw [hk_eq]
        rw [stored_dword_get?_hit s base dword_new ((ea - base).toNat + j) (by omega)]
        rw [hsplice_target j hj]
        rw [target_addr_eq_of_window hsetup.toDwordWindowFacts j]
        symm
        simpa using stored_word_get?_hit s ea word_val j hj

end StoreSplice

end
