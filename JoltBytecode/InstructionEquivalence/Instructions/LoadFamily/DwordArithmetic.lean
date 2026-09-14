import JoltBytecode.InstructionEquivalence.ProofSupport.Memory.Read
import JoltBytecode.InstructionEquivalence.ProofSupport.Memory.Windows
import JoltBytecode.InstructionEquivalence.ProofSupport.InstructionLemmas.VirtualPext
import Mathlib.Tactic.IntervalCases

set_option linter.unusedVariables false
set_option mvcgen.warning false

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

/-!
# Pure dword-arithmetic helpers for the Jolt load family

This file collects every fact that is purely about

* extracting a byte / word / (TODO: halfword) slice from a 64-bit dword,
* how those slices relate to the hashmap-keyed `loaded_byte_at` /
  `loaded_word_at` calls the Sail side uses,
* how a 64-bit address decomposes as `(addr & -8)` plus the low-3-bit offset,
* the pure bit-vector identities that express a Jolt inline-sequence's
  logic-phase output as `sign_extend (byte_of_dword d k)` or
  `sign_extend (word_of_dword d k)`.

There are no monads here, no Sail pipeline reductions, no instruction-specific
signatures. Every load instruction (`LB`, `LBU`, `LH`, `LHU`, `LW`, `LWU`)
reuses the helpers in this file when closing its bridge lemma.

## What lives here (by shape)

* Slice definitions (`def`): `byte_of_dword`, `word_of_dword`.
* Slice-of-dword-equals-direct-load lemmas: `loaded_dword_byte_k`,
  `loaded_dword_word_k`, `word_of_dword_eq_bytes`.
* Address-decomposition facts: `addr_split_aligned_offset`,
  `addr_and_seven_lt_eight`, `addr_and_seven_word_lt_five`,
  `word_offset_cases`.
* Memory-shape bridges: `loaded_byte_in_dword`, `loaded_word_in_dword`.
* Jolt logic-phase bit-vector identities: `sll_srai_extracts_byte`,
  `srl_sign_extend_word_extracts_word`.
-/

-- ============================================================================
-- Slice definitions
-- ============================================================================

/-- The `k`-th byte (0-indexed from the low end) of a 64-bit dword. -/
def byte_of_dword (d : BitVec 64) (k : Nat) : BitVec 8 :=
  (d >>> (8 * k)).setWidth 8

/-- The halfword starting at byte-position `k` of a 64-bit dword. Well-
    defined for `k ∈ 0..6`. -/
def halfword_of_dword (d : BitVec 64) (k : Nat) : BitVec 16 :=
  (d >>> (8 * k)).setWidth 16

/-- The word starting at byte-position `k` of a 64-bit dword. Well-defined for
    `k ∈ 0..4`. -/
def word_of_dword (d : BitVec 64) (k : Nat) : BitVec 32 :=
  (d >>> (8 * k)).setWidth 32

-- ============================================================================
-- Slice-of-loaded-dword identities
-- ============================================================================

/-- The `k`-th byte of the loaded dword at `V` is the same as the direct byte
    load at `V + k`. Case-bashes on `k ∈ 0..7`. -/
theorem loaded_dword_byte_k (s : SailState) (V : BitVec 64) (k : Nat)
    (hbytes : MemBytesPresentAt s V 8)
    (h_no_ovf : V.toNat + 7 < 2 ^ 64)
    (hk : k < 8) :
  byte_of_dword (loaded_dword_at s V hbytes h_no_ovf) k =
    loaded_byte_at s (V + BitVec.ofNat 64 k)
      (hbytes.byte_addr (k := k) hk (by omega)) := by
  unfold byte_of_dword loaded_dword_at
  interval_cases k
  all_goals
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have hi_bool : (i <b 8) = true := by
      simpa only [Nat.blt_eq, decide_eq_true_eq] using hi
    simp (disch := omega) only [hi_bool, Bool.true_and, BitVec.getLsbD_setWidth,
      BitVec.getLsbD_ushiftRight, Nat.reduceMul, Nat.reduceAdd]
    repeat rw [BitVec.getLsbD_append]
    simp (disch := omega) only [if_pos, if_neg, BitVec.add_zero]
    congr 1
    omega

/-- A 16-bit halfword of a dword is the concatenation of its two bytes
    (little-endian). Side condition `k < 7` because the halfword must fit
    within the dword's 8 bytes. -/
theorem halfword_of_dword_eq_bytes (d : BitVec 64) (k : Nat)
    (hk : k < 7) :
    halfword_of_dword d k =
    byte_of_dword d (k + 1) ++ byte_of_dword d k := by
  unfold halfword_of_dword byte_of_dword
  interval_cases k <;>
    apply BitVec.eq_of_getLsbD_eq <;>
    intro i hi <;>
    interval_cases i <;>
    simp [BitVec.getLsbD_eq_getElem, BitVec.getElem_setWidth] <;>
    rw [BitVec.getElem_append] <;>
    simp [BitVec.getElem_setWidth]

/-- The halfword starting at byte-offset `k` of the loaded dword at `V` is
    the same as the direct halfword load at `V + k`. Stated in the
    *unfolded* shift-and-setWidth form (matching the convention of
    `loaded_dword_word_k`). -/
theorem loaded_dword_halfword_k (s : SailState) (V : BitVec 64) (k : Nat)
    (hbytes : MemBytesPresentAt s V 8)
    (h_no_ovf : V.toNat + 7 < 2 ^ 64)
    (hk : k < 7) :
    ((loaded_dword_at s V hbytes h_no_ovf) >>> (8 * k)).setWidth 16 =
    loaded_halfword_at s (V + BitVec.ofNat 64 k)
      (memBytesPresentAt_subaccess hbytes (by omega) (by omega))
      (by
        rw [toNat_add_small_of_no_ovf V k (by omega)]
        omega) := by
  change halfword_of_dword (loaded_dword_at s V hbytes h_no_ovf) k =
    loaded_halfword_at s (V + BitVec.ofNat 64 k)
      (memBytesPresentAt_subaccess hbytes (by omega) (by omega))
      (by
        rw [toNat_add_small_of_no_ovf V k (by omega)]
        omega)
  rw [halfword_of_dword_eq_bytes (loaded_dword_at s V hbytes h_no_ovf) k hk]
  unfold loaded_halfword_at
  rw [loaded_dword_byte_k s V (k + 1) hbytes h_no_ovf (by omega),
    loaded_dword_byte_k s V k hbytes h_no_ovf (by omega)]
  have haddr : V + BitVec.ofNat 64 (k + 1) = (1 : BitVec 64) + (V + BitVec.ofNat 64 k) := by
    interval_cases k <;> norm_num <;> ac_rfl
  have haddr' : (1 : BitVec 64) + (V + BitVec.ofNat 64 k) = V + BitVec.ofNat 64 k + 1 := by
    interval_cases k <;> norm_num <;> ac_rfl
  have haddr_final : V + BitVec.ofNat 64 (k + 1) = V + BitVec.ofNat 64 k + 1 := by
    rw [haddr, haddr']
  rw [loaded_byte_at_eq_of_addr_eq (s := s) haddr_final]

/-- A 32-bit word of a dword is the concatenation of its four bytes (little-
    endian). Side condition `k < 5` because the word must fit within the
    dword's 8 bytes. -/
theorem word_of_dword_eq_bytes (d : BitVec 64) (k : Nat)
    (hk : k < 5) :
    word_of_dword d k =
    byte_of_dword d (k + 3) ++ byte_of_dword d (k + 2) ++
    byte_of_dword d (k + 1) ++ byte_of_dword d k := by
  unfold word_of_dword byte_of_dword
  interval_cases k <;>
    apply BitVec.eq_of_getLsbD_eq <;>
    intro i hi <;>
    interval_cases i <;>
    simp [BitVec.getLsbD_eq_getElem, BitVec.getElem_setWidth] <;>
    repeat rw [BitVec.getElem_append] <;>
    simp [BitVec.getElem_setWidth]

/-- The word starting at byte-offset `k` of the loaded dword at `V` is the
    same as the direct word load at `V + k`. Proof: decompose the word into
    four bytes via `word_of_dword_eq_bytes`, then translate each byte via
    `loaded_dword_byte_k`. Stated in the *unfolded* shift-and-setWidth form
    to match LW's `word_of_dword` unfolding style. -/
theorem loaded_dword_word_k (s : SailState) (V : BitVec 64) (k : Nat)
    (hbytes : MemBytesPresentAt s V 8)
    (h_no_ovf : V.toNat + 7 < 2 ^ 64)
    (hk : k < 5) :
    ((loaded_dword_at s V hbytes h_no_ovf) >>> (8 * k)).setWidth 32 =
    loaded_word_at s (V + BitVec.ofNat 64 k)
      (memBytesPresentAt_subaccess hbytes (by omega) (by omega))
      (by
        rw [toNat_add_small_of_no_ovf V k (by omega)]
        omega) := by
  change word_of_dword (loaded_dword_at s V hbytes h_no_ovf) k =
    loaded_word_at s (V + BitVec.ofNat 64 k)
      (memBytesPresentAt_subaccess hbytes (by omega) (by omega))
      (by
        rw [toNat_add_small_of_no_ovf V k (by omega)]
        omega)
  rw [word_of_dword_eq_bytes (loaded_dword_at s V hbytes h_no_ovf) k hk]
  unfold loaded_word_at
  rw [loaded_dword_byte_k s V (k + 3) hbytes h_no_ovf (by omega)]
  rw [loaded_dword_byte_k s V (k + 2) hbytes h_no_ovf (by omega)]
  rw [loaded_dword_byte_k s V (k + 1) hbytes h_no_ovf (by omega)]
  rw [loaded_dword_byte_k s V k hbytes h_no_ovf (by omega)]
  have h3 : V + BitVec.ofNat 64 (k + 3) = (3 : BitVec 64) + (V + BitVec.ofNat 64 k) := by
    interval_cases k <;> norm_num <;> ac_rfl
  have h2 : V + BitVec.ofNat 64 (k + 2) = (2 : BitVec 64) + (V + BitVec.ofNat 64 k) := by
    interval_cases k <;> norm_num <;> ac_rfl
  have h1 : V + BitVec.ofNat 64 (k + 1) = (1 : BitVec 64) + (V + BitVec.ofNat 64 k) := by
    interval_cases k <;> norm_num <;> ac_rfl
  have h3' : (3 : BitVec 64) + (V + BitVec.ofNat 64 k) = V + BitVec.ofNat 64 k + 3 := by
    interval_cases k <;> norm_num <;> ac_rfl
  have h2' : (2 : BitVec 64) + (V + BitVec.ofNat 64 k) = V + BitVec.ofNat 64 k + 2 := by
    interval_cases k <;> norm_num <;> ac_rfl
  have h1' : (1 : BitVec 64) + (V + BitVec.ofNat 64 k) = V + BitVec.ofNat 64 k + 1 := by
    interval_cases k <;> norm_num <;> ac_rfl
  have h3_final : V + BitVec.ofNat 64 (k + 3) = V + BitVec.ofNat 64 k + 3 := by
    rw [h3, h3']
  have h2_final : V + BitVec.ofNat 64 (k + 2) = V + BitVec.ofNat 64 k + 2 := by
    rw [h2, h2']
  have h1_final : V + BitVec.ofNat 64 (k + 1) = V + BitVec.ofNat 64 k + 1 := by
    rw [h1, h1']
  rw [loaded_byte_at_eq_of_addr_eq (s := s) h3_final]
  rw [loaded_byte_at_eq_of_addr_eq (s := s) h2_final]
  rw [loaded_byte_at_eq_of_addr_eq (s := s) h1_final]

-- ============================================================================
-- Address decomposition facts
-- ============================================================================

private lemma and_neg8_eq_shr_shl (addr : BitVec 64) :
    addr &&& (-8 : BitVec 64) = (addr >>> 3) <<< 3 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_ushiftRight]
  interval_cases i <;> simp

/-- Every 64-bit address splits as `(addr & -8) + (addr & 7)`: the 8-aligned
    base plus the 3-bit byte offset. Pure bit-vector identity. -/
theorem addr_split_aligned_offset (addr : BitVec 64) :
    (addr &&& (-8 : BitVec 64)) + BitVec.ofNat 64 (addr &&& 7).toNat = addr := by
  simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rw [and_neg8_eq_shr_shl]
  apply BitVec.eq_of_toNat_eq
  have hbase : (((addr >>> 3) <<< 3) : BitVec 64).toNat =
      addr.toNat / 8 * 8 := by
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight]
    simp [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
    have hlt : addr.toNat / 8 * 8 ≤ addr.toNat := by
      simpa [Nat.mul_comm] using Nat.mul_div_le addr.toNat 8
    exact lt_of_le_of_lt hlt addr.isLt
  have hlow : (addr &&& (7 : BitVec 64)).toNat = addr.toNat % 8 := by
    rw [BitVec.toNat_and]
    have h7 : (7 : BitVec 64).toNat = 7 := by decide
    rw [h7, show (7 : Nat) = 2 ^ 3 - 1 by norm_num,
      Nat.and_two_pow_sub_one_eq_mod]
  have hsum_lt :
      (((addr >>> 3) <<< 3) : BitVec 64).toNat +
          (addr &&& (7 : BitVec 64)).toNat < 2 ^ 64 := by
    rw [hbase, hlow]
    have h := Nat.div_add_mod addr.toNat 8
    omega
  rw [BitVec.toNat_add_of_lt hsum_lt, hbase, hlow]
  have h := Nat.div_add_mod addr.toNat 8
  omega

/-- The 3-bit offset `(addr & 7)` is always in the range `0..7`. Used as the
    side condition for `loaded_dword_byte_k`. -/
theorem addr_and_seven_lt_eight (addr : BitVec 64) : (addr &&& 7).toNat < 8 := by
  rw [BitVec.toNat_and]
  exact Nat.and_lt_two_pow addr.toNat (by decide : (7 : BitVec 64).toNat < 2^3)

/-- For a 2-aligned address, the 3-bit offset `(addr & 7)` is in the range
    `0..6`. Used as the side condition for `loaded_dword_halfword_k`
    applied to a halfword-aligned address. -/
theorem addr_and_seven_halfword_lt_seven (addr : BitVec 64)
    (halign : addr &&& 1 = 0) :
    (addr &&& 7).toNat < 7 := by
  have hk_lt : (addr &&& 7).toNat < 8 := addr_and_seven_lt_eight addr
  have hk_mod8 : (addr &&& 7).toNat = addr.toNat % 8 := by
    rw [BitVec.toNat_and]
    have h7 : BitVec.toNat (7 : BitVec 64) = 7 := by decide
    rw [h7]
    rw [show (7 : Nat) = 2^3 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod]
  have h_even_addr : addr.toNat % 2 = 0 := by
    have h := congrArg BitVec.toNat halign
    rw [BitVec.toNat_and] at h
    have h1 : BitVec.toNat (1 : BitVec 64) = 1 := by decide
    have h0 : BitVec.toNat (0 : BitVec 64) = 0 := by decide
    rw [h1, h0] at h
    rw [show (1 : Nat) = 2^1 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod] at h
    exact h
  have hk_even : (addr &&& 7).toNat % 2 = 0 := by
    rw [hk_mod8]
    omega
  omega

/-- For a 4-aligned address, the 3-bit offset `(addr & 7)` is in the range
    `0..4`. Used as the side condition for `loaded_dword_word_k` applied to a
    word-aligned address. -/
theorem addr_and_seven_word_lt_five (addr : BitVec 64)
    (halign : addr &&& 3 = 0) :
    (addr &&& 7).toNat < 5 := by
  have hk_mod8 : (addr &&& 7).toNat = addr.toNat % 8 := by
    rw [BitVec.toNat_and]
    have h7 : BitVec.toNat (7 : BitVec 64) = 7 := by decide
    rw [h7]
    rw [show (7 : Nat) = 2^3 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod]
  have h_word_addr : addr.toNat % 4 = 0 := by
    have h := congrArg BitVec.toNat halign
    rw [BitVec.toNat_and] at h
    have h3 : BitVec.toNat (3 : BitVec 64) = 3 := by decide
    have h0 : BitVec.toNat (0 : BitVec 64) = 0 := by decide
    rw [h3, h0] at h
    rw [show (3 : Nat) = 2^2 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod] at h
    exact h
  have hk_mod4 : (addr &&& 7).toNat % 4 = 0 := by
    rw [hk_mod8]
    omega
  have hk_lt : (addr &&& 7).toNat < 8 := addr_and_seven_lt_eight addr
  omega

/-- For a 2-aligned address, the only possible values of the 3-bit offset
    are `0`, `2`, `4`, or `6` (even offsets ≤ 6). -/
theorem halfword_offset_cases (addr : BitVec 64) (halign : addr &&& 1 = 0) :
    (addr &&& 7).toNat = 0 ∨ (addr &&& 7).toNat = 2 ∨
    (addr &&& 7).toNat = 4 ∨ (addr &&& 7).toNat = 6 := by
  have hk_lt : (addr &&& 7).toNat < 7 := addr_and_seven_halfword_lt_seven addr halign
  have hk_even : (addr &&& 7).toNat % 2 = 0 := by
    have hk_mod8 : (addr &&& 7).toNat = addr.toNat % 8 := by
      rw [BitVec.toNat_and]
      have h7 : BitVec.toNat (7 : BitVec 64) = 7 := by decide
      rw [h7]
      rw [show (7 : Nat) = 2^3 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod]
    have h_even_addr : addr.toNat % 2 = 0 := by
      have h := congrArg BitVec.toNat halign
      rw [BitVec.toNat_and] at h
      have h1 : BitVec.toNat (1 : BitVec 64) = 1 := by decide
      have h0 : BitVec.toNat (0 : BitVec 64) = 0 := by decide
      rw [h1, h0] at h
      rw [show (1 : Nat) = 2^1 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod] at h
      exact h
    rw [hk_mod8]
    omega
  omega

/-- For a 4-aligned address, the only possible values of the 3-bit offset are
    `0` (the word is in the low half of the dword) or `4` (high half). -/
theorem word_offset_cases (addr : BitVec 64) (halign : addr &&& 3 = 0) :
    (addr &&& 7).toNat = 0 ∨ (addr &&& 7).toNat = 4 := by
  have hk_lt : (addr &&& 7).toNat < 5 := addr_and_seven_word_lt_five addr halign
  have hk_mod4 : (addr &&& 7).toNat % 4 = 0 := by
    have hk_mod8 : (addr &&& 7).toNat = addr.toNat % 8 := by
      rw [BitVec.toNat_and]
      have h7 : BitVec.toNat (7 : BitVec 64) = 7 := by decide
      rw [h7]
      rw [show (7 : Nat) = 2^3 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod]
    have h_word_addr : addr.toNat % 4 = 0 := by
      have h := congrArg BitVec.toNat halign
      rw [BitVec.toNat_and] at h
      have h3 : BitVec.toNat (3 : BitVec 64) = 3 := by decide
      have h0 : BitVec.toNat (0 : BitVec 64) = 0 := by decide
      rw [h3, h0] at h
      rw [show (3 : Nat) = 2^2 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod] at h
      exact h
    rw [hk_mod8]
    omega
  omega

-- ============================================================================
-- Fused window-mask / parallel-extract identities
-- ============================================================================

/-- The byte window mask selects exactly the addressed byte from a dword. -/
theorem window_mask_b_pext (d base : BitVec 64) (imm : BitVec 12) :
    jolt_virtual_pext_value d (jolt_virtual_window_mask_b_value base imm) =
      zero_extend (m := 64)
        (byte_of_dword d
          ((load_effective_address base imm) &&& (7 : BitVec 64)).toNat) := by
  let offset := ((load_effective_address base imm) &&& (7 : BitVec 64)).toNat
  have hoffset : offset < 8 := by
    simpa only [offset] using addr_and_seven_lt_eight (load_effective_address base imm)
  have hfit : 8 * offset + 8 ≤ 64 := by omega
  have hpext := JoltISA.pext_value_contiguous d (8 * offset) 8 hfit
  simpa only [jolt_virtual_window_mask_b_value, load_effective_address, offset,
    byte_of_dword, Nat.shiftLeft_eq,
    show (0xFF : Nat) = 2 ^ 8 - 1 by norm_num] using hpext

/-- Signed byte extraction is the same selected byte sign-extended to XLEN. -/
theorem window_mask_b_pext_signed (d base : BitVec 64) (imm : BitVec 12) :
    jolt_virtual_pext_signed_value d (jolt_virtual_window_mask_b_value base imm) =
      sign_extend (m := 64)
        (byte_of_dword d
          ((load_effective_address base imm) &&& (7 : BitVec 64)).toNat) := by
  let offset := ((load_effective_address base imm) &&& (7 : BitVec 64)).toNat
  have hoffset : offset < 8 := by
    simpa only [offset] using addr_and_seven_lt_eight (load_effective_address base imm)
  have hfit : 8 * offset + 8 ≤ 64 := by omega
  have hpext := JoltISA.pext_signed_value_contiguous d (8 * offset) 8 (by omega) hfit
  simpa only [jolt_virtual_window_mask_b_value, load_effective_address, offset,
    byte_of_dword, Nat.shiftLeft_eq,
    show (0xFF : Nat) = 2 ^ 8 - 1 by norm_num] using hpext

private theorem halfword_window_offset_eq (addr : BitVec 64)
    (halign : addr &&& (1 : BitVec 64) = 0) :
    (addr &&& (6 : BitVec 64)).toNat = (addr &&& (7 : BitVec 64)).toNat := by
  have hseven : (7 : BitVec 64) = (6 : BitVec 64) ||| (1 : BitVec 64) := by decide
  have hvec : addr &&& (7 : BitVec 64) = addr &&& (6 : BitVec 64) := by
    rw [hseven, BitVec.and_or_distrib_left, halign]
    exact BitVec.or_zero
  exact congrArg BitVec.toNat hvec.symm

private theorem word_selector_eq_offset_div_four (addr : BitVec 64) :
    (((addr >>> 2) &&& (1 : BitVec 64)).toNat) =
      (addr &&& (7 : BitVec 64)).toNat / 4 := by
  rw [BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_and]
  have hone : (1 : BitVec 64).toNat = 1 := by decide
  have hseven : (7 : BitVec 64).toNat = 7 := by decide
  rw [hone, hseven, Nat.shiftRight_eq_div_pow]
  rw [show (1 : Nat) = 2 ^ 1 - 1 by norm_num,
    Nat.and_two_pow_sub_one_eq_mod]
  rw [show (7 : Nat) = 2 ^ 3 - 1 by norm_num,
    Nat.and_two_pow_sub_one_eq_mod]
  norm_num
  exact (Nat.mod_mul_right_div_self addr.toNat 4 2).symm

/-- The halfword window mask selects the addressed aligned halfword. -/
theorem window_mask_h_pext (d base : BitVec 64) (imm : BitVec 12)
    (halign : load_effective_address base imm &&& (1 : BitVec 64) = 0) :
    jolt_virtual_pext_value d (jolt_virtual_window_mask_h_value base imm) =
      zero_extend (m := 64)
        (halfword_of_dword d
          ((load_effective_address base imm) &&& (7 : BitVec 64)).toNat) := by
  let ea := load_effective_address base imm
  let offset := (ea &&& (7 : BitVec 64)).toNat
  have hoffset : offset < 7 := by
    simpa only [ea, offset] using addr_and_seven_halfword_lt_seven ea halign
  have hfit : 8 * offset + 16 ≤ 64 := by omega
  have hpext := JoltISA.pext_value_contiguous d (8 * offset) 16 hfit
  have hoffset_eq := halfword_window_offset_eq ea halign
  simpa only [jolt_virtual_window_mask_h_value, load_effective_address, ea, offset,
    hoffset_eq, halfword_of_dword, Nat.shiftLeft_eq,
    show (0xFFFF : Nat) = 2 ^ 16 - 1 by norm_num] using hpext

/-- Signed halfword extraction sign-extends the selected aligned halfword. -/
theorem window_mask_h_pext_signed (d base : BitVec 64) (imm : BitVec 12)
    (halign : load_effective_address base imm &&& (1 : BitVec 64) = 0) :
    jolt_virtual_pext_signed_value d (jolt_virtual_window_mask_h_value base imm) =
      sign_extend (m := 64)
        (halfword_of_dword d
          ((load_effective_address base imm) &&& (7 : BitVec 64)).toNat) := by
  let ea := load_effective_address base imm
  let offset := (ea &&& (7 : BitVec 64)).toNat
  have hoffset : offset < 7 := by
    simpa only [ea, offset] using addr_and_seven_halfword_lt_seven ea halign
  have hfit : 8 * offset + 16 ≤ 64 := by omega
  have hpext := JoltISA.pext_signed_value_contiguous d (8 * offset) 16 (by omega) hfit
  have hoffset_eq := halfword_window_offset_eq ea halign
  simpa only [jolt_virtual_window_mask_h_value, load_effective_address, ea, offset,
    hoffset_eq, halfword_of_dword, Nat.shiftLeft_eq,
    show (0xFFFF : Nat) = 2 ^ 16 - 1 by norm_num] using hpext

/-- The word window mask selects the addressed aligned word. -/
theorem window_mask_w_pext (d base : BitVec 64) (imm : BitVec 12)
    (halign : load_effective_address base imm &&& (3 : BitVec 64) = 0) :
    jolt_virtual_pext_value d (jolt_virtual_window_mask_w_value base imm) =
      zero_extend (m := 64)
        (word_of_dword d
          ((load_effective_address base imm) &&& (7 : BitVec 64)).toNat) := by
  let ea := load_effective_address base imm
  let offset := (ea &&& (7 : BitVec 64)).toNat
  let word := ((ea >>> 2) &&& (1 : BitVec 64)).toNat
  have hoffset : offset < 5 := by
    simpa only [ea, offset] using addr_and_seven_word_lt_five ea halign
  have hword : word = offset / 4 := by
    simpa only [word, offset] using word_selector_eq_offset_div_four ea
  have hshift : 32 * word = 8 * offset := by
    rcases word_offset_cases ea halign with hzero | hfour
    · simp only [offset, hzero, hword]
    · simp only [offset, hfour, hword]
  have hfit : 32 * word + 32 ≤ 64 := by omega
  have hpext := JoltISA.pext_value_contiguous d (32 * word) 32 hfit
  simpa only [jolt_virtual_window_mask_w_value, load_effective_address, ea, word,
    offset, hshift, word_of_dword, Nat.shiftLeft_eq,
    show (0xFFFF_FFFF : Nat) = 2 ^ 32 - 1 by norm_num] using hpext

/-- Signed word extraction sign-extends the selected aligned word. -/
theorem window_mask_w_pext_signed (d base : BitVec 64) (imm : BitVec 12)
    (halign : load_effective_address base imm &&& (3 : BitVec 64) = 0) :
    jolt_virtual_pext_signed_value d (jolt_virtual_window_mask_w_value base imm) =
      sign_extend (m := 64)
        (word_of_dword d
          ((load_effective_address base imm) &&& (7 : BitVec 64)).toNat) := by
  let ea := load_effective_address base imm
  let offset := (ea &&& (7 : BitVec 64)).toNat
  let word := ((ea >>> 2) &&& (1 : BitVec 64)).toNat
  have hoffset : offset < 5 := by
    simpa only [ea, offset] using addr_and_seven_word_lt_five ea halign
  have hword : word = offset / 4 := by
    simpa only [word, offset] using word_selector_eq_offset_div_four ea
  have hshift : 32 * word = 8 * offset := by
    rcases word_offset_cases ea halign with hzero | hfour
    · simp only [offset, hzero, hword]
    · simp only [offset, hfour, hword]
  have hfit : 32 * word + 32 ≤ 64 := by omega
  have hpext := JoltISA.pext_signed_value_contiguous d (32 * word) 32 (by omega) hfit
  simpa only [jolt_virtual_window_mask_w_value, load_effective_address, ea, word,
    offset, hshift, word_of_dword, Nat.shiftLeft_eq,
    show (0xFFFF_FFFF : Nat) = 2 ^ 32 - 1 by norm_num] using hpext

-- ============================================================================
-- Memory-shape bridges: the hashmap key fact for the direct load
-- ============================================================================

/-- The byte at an arbitrary address equals the appropriate byte-slice of the
    enclosing aligned dword. Composes `loaded_dword_byte_k` with
    `addr_split_aligned_offset`. -/
theorem loaded_byte_in_dword (s : SailState) (addr : BitVec 64)
    (hbytes : MemBytesPresentAt s (addr &&& (-8 : BitVec 64)) 8)
    (h_no_ovf : (addr &&& (-8 : BitVec 64)).toNat + 7 < 2 ^ 64)
    (hpresent : MemBytePresentAt s addr.toNat) :
    loaded_byte_at s addr hpresent =
    byte_of_dword
      (loaded_dword_at s (addr &&& (-8 : BitVec 64)) hbytes h_no_ovf)
      (addr &&& 7).toNat := by
  rw [loaded_dword_byte_k s (addr &&& -8) (addr &&& 7).toNat hbytes h_no_ovf
        (addr_and_seven_lt_eight addr)]
  exact (loaded_byte_at_eq_of_addr_eq (s := s)
    (addr_split_aligned_offset addr) _ _).symm

/-- The halfword at a 2-aligned address equals the appropriate halfword-
    slice of the enclosing aligned dword. Requires `halign : addr & 1 = 0`. -/
theorem loaded_halfword_in_dword (s : SailState) (addr : BitVec 64)
    (halign : addr &&& 1 = 0)
    (hbytes_base : MemBytesPresentAt s (addr &&& (-8 : BitVec 64)) 8)
    (h_no_ovf_base : (addr &&& (-8 : BitVec 64)).toNat + 7 < 2 ^ 64)
    (hbytes_addr : MemBytesPresentAt s addr 2)
    (h_no_ovf_addr : addr.toNat + 1 < 2 ^ 64) :
    loaded_halfword_at s addr hbytes_addr h_no_ovf_addr =
    halfword_of_dword
      (loaded_dword_at s (addr &&& (-8 : BitVec 64)) hbytes_base h_no_ovf_base)
      (addr &&& 7).toNat := by
  unfold halfword_of_dword
  rw [loaded_dword_halfword_k s (addr &&& -8) (addr &&& 7).toNat hbytes_base h_no_ovf_base
        (addr_and_seven_halfword_lt_seven addr halign)]
  exact (loaded_halfword_at_eq_of_addr_eq (s := s)
    (addr_split_aligned_offset addr) _ _ _ _).symm

/-- The word at a 4-aligned address equals the appropriate word-slice of the
    enclosing aligned dword. Requires `halign : addr & 3 = 0`. -/
theorem loaded_word_in_dword (s : SailState) (addr : BitVec 64)
    (halign : addr &&& 3 = 0)
    (hbytes_base : MemBytesPresentAt s (addr &&& (-8 : BitVec 64)) 8)
    (h_no_ovf_base : (addr &&& (-8 : BitVec 64)).toNat + 7 < 2 ^ 64)
    (hbytes_addr : MemBytesPresentAt s addr 4)
    (h_no_ovf_addr : addr.toNat + 3 < 2 ^ 64) :
    loaded_word_at s addr hbytes_addr h_no_ovf_addr =
    word_of_dword
      (loaded_dword_at s (addr &&& (-8 : BitVec 64)) hbytes_base h_no_ovf_base)
      (addr &&& 7).toNat := by
  unfold word_of_dword
  rw [loaded_dword_word_k s (addr &&& -8) (addr &&& 7).toNat hbytes_base h_no_ovf_base
        (addr_and_seven_word_lt_five addr halign)]
  exact (loaded_word_at_eq_of_addr_eq (s := s)
    (addr_split_aligned_offset addr) _ _ _ _).symm

-- ============================================================================
-- Jolt logic-phase bit-vector identities
-- ============================================================================
-- These say: the 64-bit arithmetic performed by the logic phase of a Jolt
-- load sequence equals the expected `sign_extend (slice_of_dword d k)`. They
-- are the pure bit-vector heart of each instruction's bridge lemma.

private lemma addr_low_bit_eq_of_and7_toNat (addr : BitVec 64) {k i : Nat}
    (hk : (addr &&& 7).toNat = k) (hi : i < 3) :
    addr[i] = (BitVec.ofNat 64 k)[i] := by
  have hk_eq : addr &&& 7 = BitVec.ofNat 64 k := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, hk]
    have hk_lt : k < 8 := by
      rw [← hk]
      exact addr_and_seven_lt_eight addr
    omega
  have h := congrArg (fun x : BitVec 64 => x.getLsbD i) hk_eq
  change (addr &&& 7).getLsbD i =
    (BitVec.ofNat 64 k).getLsbD i at h
  rw [BitVec.getLsbD_and] at h
  have h7 : (7 : BitVec 64).getLsbD i = true := by
    interval_cases i <;> decide
  rw [h7, Bool.and_true] at h
  simpa [BitVec.getLsbD_eq_getElem] using h

private lemma sll_byte_shift_amount (addr : BitVec 64) (k : Nat)
    (hk : (addr &&& 7).toNat = k) (hk_lt : k < 8) :
    BitVec.extractLsb 5 0 ((addr ^^^ (7 : BitVec 64)) <<< 3) =
      BitVec.ofNat 6 (8 * (7 - k)) := by
  have hbit0 : addr[0] = (BitVec.ofNat 64 k)[0] :=
    addr_low_bit_eq_of_and7_toNat addr hk (by omega)
  have hbit1 : addr[1] = (BitVec.ofNat 64 k)[1] :=
    addr_low_bit_eq_of_and7_toNat addr hk (by omega)
  have hbit2 : addr[2] = (BitVec.ofNat 64 k)[2] :=
    addr_low_bit_eq_of_and7_toNat addr hk (by omega)
  interval_cases k <;>
    apply BitVec.eq_of_getLsbD_eq <;>
    intro i hi <;>
    rw [BitVec.getLsbD_extractLsb, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_xor] <;>
    interval_cases i <;>
    simp [hbit0, hbit1, hbit2]

private lemma sll_srli56_extracts_byte_k (d : BitVec 64) (k sh : Nat)
    (hk : k < 8) (hsh : sh = 8 * (7 - k)) :
    (d <<< (BitVec.ofNat 6 sh)) >>> (56 : Nat) =
      zero_extend (m := 64) (byte_of_dword d k) := by
  subst sh
  have hshlt : 8 * (7 - k) < 64 := by omega
  change (d <<< ((8 * (7 - k)) % 2 ^ 6)) >>> (56 : Nat) =
      zero_extend (m := 64) (byte_of_dword d k)
  simp only [Nat.reducePow, Nat.mod_eq_of_lt hshlt]
  unfold zero_extend byte_of_dword Sail.BitVec.zeroExtend
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft]
  by_cases hi8 : i < 8
  · have hsrc : 8 * (7 - k) ≤ 56 + i := by omega
    have hlt64 : 56 + i < 64 := by omega
    have hidx : 56 + i - 8 * (7 - k) = 8 * k + i := by omega
    simp [hi, hi8, hlt64, hsrc, hidx, BitVec.getElem_setWidth]
  · have hge64 : 64 ≤ 56 + i := by omega
    simp [hi8, hge64]

private lemma sll_srai56_extracts_byte_k (d : BitVec 64) (k sh : Nat)
    (hk : k < 8) (hsh : sh = 8 * (7 - k)) :
    BitVec.sshiftRight (d <<< (BitVec.ofNat 6 sh)) 56 =
      sign_extend (m := 64) (byte_of_dword d k) := by
  subst sh
  have hshlt : 8 * (7 - k) < 64 := by omega
  change BitVec.sshiftRight (d <<< ((8 * (7 - k)) % 2 ^ 6)) 56 =
      sign_extend (m := 64) (byte_of_dword d k)
  simp only [Nat.reducePow, Nat.mod_eq_of_lt hshlt]
  unfold sign_extend byte_of_dword Sail.BitVec.signExtend
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_sshiftRight, BitVec.getLsbD_signExtend]
  by_cases hi8 : i < 8
  · have hlt64 : 56 + i < 64 := by omega
    have hnotlt : ¬56 + i < 8 * (7 - k) := by omega
    have hidx : 56 + i - 8 * (7 - k) = 8 * k + i := by omega
    rw [BitVec.getLsbD_shiftLeft]
    simp [hi, hi8, hlt64, hnotlt, hidx, BitVec.getElem_setWidth]
  · have hge64 : ¬56 + i < 64 := by omega
    have hnot64 : ¬64 ≤ i := by omega
    have hnotlt7 : ¬63 < 8 * (7 - k) := by omega
    have hidx7 : 63 - 8 * (7 - k) = 8 * k + 7 := by omega
    simp only [hi, hnot64, decide_false, Bool.not_false, Bool.true_and,
      hge64, if_false, hi8]
    rw [BitVec.msb_eq_getLsbD_last]
    change (d <<< (8 * (7 - k))).getLsbD 63 =
      (BitVec.setWidth 8 (d >>> (8 * k))).getLsbD 7
    rw [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
      BitVec.getLsbD_ushiftRight]
    simp [hnotlt7, hidx7]

/-- Byte-load arithmetic (signed): `XOR addr 7`, `SLL` by 3, `SLL` the dword
    by that, then **arithmetic**-shift right by 56, yields the
    sign-extended byte at offset `(addr & 7)` of the dword. Used by `LB`. -/
theorem sll_srai_extracts_byte (d : BitVec 64) (addr : BitVec 64) :
    (let xor_addr  := addr ^^^ (7 : BitVec 64)
     let shift_amt := shift_bits_left xor_addr (3 : BitVec 6)
     let shift_6   := Sail.BitVec.extractLsb shift_amt 5 0
     let shifted   := shift_bits_left d shift_6
     shift_bits_right_arith shifted (56 : BitVec 6))
    = sign_extend (m := 64) (byte_of_dword d (addr &&& 7).toNat) := by
  unfold shift_bits_left shift_bits_right_arith Sail.BitVec.extractLsb
    Sail.BitVec.toNatInt
  change BitVec.sshiftRight
      (d <<< BitVec.extractLsb 5 0 ((addr ^^^ (7 : BitVec 64)) <<< 3)) 56 =
    sign_extend (m := 64) (byte_of_dword d (addr &&& 7).toNat)
  rw [sll_byte_shift_amount addr (addr &&& 7).toNat rfl
    (addr_and_seven_lt_eight addr)]
  simpa using sll_srai56_extracts_byte_k d (addr &&& 7).toNat
    (8 * (7 - (addr &&& 7).toNat)) (addr_and_seven_lt_eight addr) rfl

/-- Byte-load arithmetic (unsigned): same setup as `sll_srai_extracts_byte`
    but with a **logical** right shift by 56 (zero-fill instead of
    sign-fill), yielding the zero-extended byte at offset `(addr & 7)` of
    the dword. Used by `LBU`. -/
theorem sll_srli_extracts_byte (d : BitVec 64) (addr : BitVec 64) :
    (let xor_addr  := addr ^^^ (7 : BitVec 64)
     let shift_amt := shift_bits_left xor_addr (3 : BitVec 6)
     let shift_6   := Sail.BitVec.extractLsb shift_amt 5 0
     let shifted   := shift_bits_left d shift_6
     shift_bits_right shifted (56 : BitVec 6))
    = zero_extend (m := 64) (byte_of_dword d (addr &&& 7).toNat) := by
  unfold shift_bits_left shift_bits_right Sail.BitVec.extractLsb
  change (d <<< BitVec.extractLsb 5 0 ((addr ^^^ (7 : BitVec 64)) <<< 3)) >>>
      (56 : Nat) =
    zero_extend (m := 64) (byte_of_dword d (addr &&& 7).toNat)
  rw [sll_byte_shift_amount addr (addr &&& 7).toNat rfl
    (addr_and_seven_lt_eight addr)]
  simpa using sll_srli56_extracts_byte_k d (addr &&& 7).toNat
    (8 * (7 - (addr &&& 7).toNat)) (addr_and_seven_lt_eight addr) rfl

private lemma sll_halfword_shift_amount (addr : BitVec 64) (k : Nat)
    (hk : (addr &&& 7).toNat = k) (hk_lt : k < 7) (hkeven : k % 2 = 0) :
    BitVec.extractLsb 5 0 ((addr ^^^ (6 : BitVec 64)) <<< 3) =
      BitVec.ofNat 6 (8 * (6 - k)) := by
  have hbit0 : addr[0] = (BitVec.ofNat 64 k)[0] :=
    addr_low_bit_eq_of_and7_toNat addr hk (by omega)
  have hbit1 : addr[1] = (BitVec.ofNat 64 k)[1] :=
    addr_low_bit_eq_of_and7_toNat addr hk (by omega)
  have hbit2 : addr[2] = (BitVec.ofNat 64 k)[2] :=
    addr_low_bit_eq_of_and7_toNat addr hk (by omega)
  interval_cases k
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [BitVec.getLsbD_extractLsb, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_xor]
    interval_cases i <;> simp [hbit0, hbit1, hbit2]
  · omega
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [BitVec.getLsbD_extractLsb, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_xor]
    interval_cases i <;> simp [hbit0, hbit1, hbit2]
  · omega
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [BitVec.getLsbD_extractLsb, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_xor]
    interval_cases i <;> simp [hbit0, hbit1, hbit2]
  · omega
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [BitVec.getLsbD_extractLsb, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_xor]
    interval_cases i <;> simp [hbit0, hbit1, hbit2]

private lemma sll_srli48_extracts_halfword_k (d : BitVec 64) (k sh : Nat)
    (hk : k < 7) (hsh : sh = 8 * (6 - k)) :
    (d <<< (BitVec.ofNat 6 sh)) >>> (48 : Nat) =
      zero_extend (m := 64) (halfword_of_dword d k) := by
  subst sh
  have hshlt : 8 * (6 - k) < 64 := by omega
  change (d <<< ((8 * (6 - k)) % 2 ^ 6)) >>> (48 : Nat) =
      zero_extend (m := 64) (halfword_of_dword d k)
  simp only [Nat.reducePow, Nat.mod_eq_of_lt hshlt]
  unfold zero_extend halfword_of_dword Sail.BitVec.zeroExtend
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft]
  by_cases hi16 : i < 16
  · have hsrc : 8 * (6 - k) ≤ 48 + i := by omega
    have hlt64 : 48 + i < 64 := by omega
    have hidx : 48 + i - 8 * (6 - k) = 8 * k + i := by omega
    simp [hi, hi16, hlt64, hsrc, hidx, BitVec.getElem_setWidth]
  · have hge64 : 64 ≤ 48 + i := by omega
    simp [hi16, hge64]

private lemma sll_srai48_extracts_halfword_k (d : BitVec 64) (k sh : Nat)
    (hk : k < 7) (hsh : sh = 8 * (6 - k)) :
    BitVec.sshiftRight (d <<< (BitVec.ofNat 6 sh)) 48 =
      sign_extend (m := 64) (halfword_of_dword d k) := by
  subst sh
  have hshlt : 8 * (6 - k) < 64 := by omega
  change BitVec.sshiftRight (d <<< ((8 * (6 - k)) % 2 ^ 6)) 48 =
      sign_extend (m := 64) (halfword_of_dword d k)
  simp only [Nat.reducePow, Nat.mod_eq_of_lt hshlt]
  unfold sign_extend halfword_of_dword Sail.BitVec.signExtend
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_sshiftRight, BitVec.getLsbD_signExtend]
  by_cases hi16 : i < 16
  · have hlt64 : 48 + i < 64 := by omega
    have hnotlt : ¬48 + i < 8 * (6 - k) := by omega
    have hidx : 48 + i - 8 * (6 - k) = 8 * k + i := by omega
    rw [BitVec.getLsbD_shiftLeft]
    simp [hi, hi16, hlt64, hnotlt, hidx, BitVec.getElem_setWidth]
  · have hge64 : ¬48 + i < 64 := by omega
    have hnot64 : ¬64 ≤ i := by omega
    have hnotlt15 : ¬63 < 8 * (6 - k) := by omega
    have hidx15 : 63 - 8 * (6 - k) = 8 * k + 15 := by omega
    simp only [hi, hnot64, decide_false, Bool.not_false, Bool.true_and,
      hge64, if_false, hi16]
    rw [BitVec.msb_eq_getLsbD_last]
    change (d <<< (8 * (6 - k))).getLsbD 63 =
      (BitVec.setWidth 16 (d >>> (8 * k))).getLsbD 15
    rw [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
      BitVec.getLsbD_ushiftRight]
    simp [hnotlt15, hidx15]

private lemma sll_srai_extracts_halfword_k0 (d addr : BitVec 64)
    (hk : (addr &&& 7).toNat = 0) :
    (let xor_addr := addr ^^^ (6 : BitVec 64)
     let shift_amt := shift_bits_left xor_addr (3 : BitVec 6)
     let shift_6 := Sail.BitVec.extractLsb shift_amt 5 0
     let shifted := shift_bits_left d shift_6
     shift_bits_right_arith shifted (48 : BitVec 6))
    = sign_extend (m := 64) (halfword_of_dword d 0) := by
  unfold shift_bits_left shift_bits_right_arith Sail.BitVec.extractLsb
    Sail.BitVec.toNatInt
  change BitVec.sshiftRight
      (d <<< BitVec.extractLsb 5 0 ((addr ^^^ (6 : BitVec 64)) <<< 3)) 48 =
    sign_extend (m := 64) (halfword_of_dword d 0)
  rw [sll_halfword_shift_amount addr 0 hk (by omega) (by decide)]
  simpa using sll_srai48_extracts_halfword_k d 0 (8 * (6 - 0))
    (by omega) rfl

private lemma sll_srai_extracts_halfword_k2 (d addr : BitVec 64)
    (hk : (addr &&& 7).toNat = 2) :
    (let xor_addr := addr ^^^ (6 : BitVec 64)
     let shift_amt := shift_bits_left xor_addr (3 : BitVec 6)
     let shift_6 := Sail.BitVec.extractLsb shift_amt 5 0
     let shifted := shift_bits_left d shift_6
     shift_bits_right_arith shifted (48 : BitVec 6))
    = sign_extend (m := 64) (halfword_of_dword d 2) := by
  unfold shift_bits_left shift_bits_right_arith Sail.BitVec.extractLsb
    Sail.BitVec.toNatInt
  change BitVec.sshiftRight
      (d <<< BitVec.extractLsb 5 0 ((addr ^^^ (6 : BitVec 64)) <<< 3)) 48 =
    sign_extend (m := 64) (halfword_of_dword d 2)
  rw [sll_halfword_shift_amount addr 2 hk (by omega) (by decide)]
  simpa using sll_srai48_extracts_halfword_k d 2 (8 * (6 - 2))
    (by omega) rfl

private lemma sll_srai_extracts_halfword_k4 (d addr : BitVec 64)
    (hk : (addr &&& 7).toNat = 4) :
    (let xor_addr := addr ^^^ (6 : BitVec 64)
     let shift_amt := shift_bits_left xor_addr (3 : BitVec 6)
     let shift_6 := Sail.BitVec.extractLsb shift_amt 5 0
     let shifted := shift_bits_left d shift_6
     shift_bits_right_arith shifted (48 : BitVec 6))
    = sign_extend (m := 64) (halfword_of_dword d 4) := by
  unfold shift_bits_left shift_bits_right_arith Sail.BitVec.extractLsb
    Sail.BitVec.toNatInt
  change BitVec.sshiftRight
      (d <<< BitVec.extractLsb 5 0 ((addr ^^^ (6 : BitVec 64)) <<< 3)) 48 =
    sign_extend (m := 64) (halfword_of_dword d 4)
  rw [sll_halfword_shift_amount addr 4 hk (by omega) (by decide)]
  simpa using sll_srai48_extracts_halfword_k d 4 (8 * (6 - 4))
    (by omega) rfl

private lemma sll_srai_extracts_halfword_k6 (d addr : BitVec 64)
    (hk : (addr &&& 7).toNat = 6) :
    (let xor_addr := addr ^^^ (6 : BitVec 64)
     let shift_amt := shift_bits_left xor_addr (3 : BitVec 6)
     let shift_6 := Sail.BitVec.extractLsb shift_amt 5 0
     let shifted := shift_bits_left d shift_6
     shift_bits_right_arith shifted (48 : BitVec 6))
    = sign_extend (m := 64) (halfword_of_dword d 6) := by
  unfold shift_bits_left shift_bits_right_arith Sail.BitVec.extractLsb
    Sail.BitVec.toNatInt
  change BitVec.sshiftRight
      (d <<< BitVec.extractLsb 5 0 ((addr ^^^ (6 : BitVec 64)) <<< 3)) 48 =
    sign_extend (m := 64) (halfword_of_dword d 6)
  rw [sll_halfword_shift_amount addr 6 hk (by omega) (by decide)]
  simpa using sll_srai48_extracts_halfword_k d 6 (8 * (6 - 6))
    (by omega) rfl

/-- Halfword-load arithmetic (signed): `XOR addr 6`, `SLL` by 3, `SLL` the
    dword by that, then arithmetic-shift right by 48, yields the sign-
    extended halfword at offset `(addr & 7)` of the dword. Requires
    halfword alignment `halign : addr & 1 = 0`. Used by `LH`. Dispatches
    on the four possible halfword offsets (0, 2, 4, 6). -/
theorem sll_srai_extracts_halfword (d : BitVec 64) (addr : BitVec 64)
    (halign : addr &&& 1 = 0) :
    (let xor_addr := addr ^^^ (6 : BitVec 64)
     let shift_amt := shift_bits_left xor_addr (3 : BitVec 6)
     let shift_6 := Sail.BitVec.extractLsb shift_amt 5 0
     let shifted := shift_bits_left d shift_6
     shift_bits_right_arith shifted (48 : BitVec 6))
    = sign_extend (m := 64) (halfword_of_dword d (addr &&& 7).toNat) := by
  rcases halfword_offset_cases addr halign with hk | hk | hk | hk
  · rw [hk]
    simpa using sll_srai_extracts_halfword_k0 d addr hk
  · rw [hk]
    simpa using sll_srai_extracts_halfword_k2 d addr hk
  · rw [hk]
    simpa using sll_srai_extracts_halfword_k4 d addr hk
  · rw [hk]
    simpa using sll_srai_extracts_halfword_k6 d addr hk

private lemma sll_srli_extracts_halfword_k0 (d addr : BitVec 64)
    (hk : (addr &&& 7).toNat = 0) :
    (let xor_addr := addr ^^^ (6 : BitVec 64)
     let shift_amt := shift_bits_left xor_addr (3 : BitVec 6)
     let shift_6 := Sail.BitVec.extractLsb shift_amt 5 0
     let shifted := shift_bits_left d shift_6
     shift_bits_right shifted (48 : BitVec 6))
    = zero_extend (m := 64) (halfword_of_dword d 0) := by
  unfold shift_bits_left shift_bits_right Sail.BitVec.extractLsb
  change (d <<< BitVec.extractLsb 5 0 ((addr ^^^ (6 : BitVec 64)) <<< 3)) >>>
      (48 : Nat) =
    zero_extend (m := 64) (halfword_of_dword d 0)
  rw [sll_halfword_shift_amount addr 0 hk (by omega) (by decide)]
  simpa using sll_srli48_extracts_halfword_k d 0 (8 * (6 - 0))
    (by omega) rfl

private lemma sll_srli_extracts_halfword_k2 (d addr : BitVec 64)
    (hk : (addr &&& 7).toNat = 2) :
    (let xor_addr := addr ^^^ (6 : BitVec 64)
     let shift_amt := shift_bits_left xor_addr (3 : BitVec 6)
     let shift_6 := Sail.BitVec.extractLsb shift_amt 5 0
     let shifted := shift_bits_left d shift_6
     shift_bits_right shifted (48 : BitVec 6))
    = zero_extend (m := 64) (halfword_of_dword d 2) := by
  unfold shift_bits_left shift_bits_right Sail.BitVec.extractLsb
  change (d <<< BitVec.extractLsb 5 0 ((addr ^^^ (6 : BitVec 64)) <<< 3)) >>>
      (48 : Nat) =
    zero_extend (m := 64) (halfword_of_dword d 2)
  rw [sll_halfword_shift_amount addr 2 hk (by omega) (by decide)]
  simpa using sll_srli48_extracts_halfword_k d 2 (8 * (6 - 2))
    (by omega) rfl

private lemma sll_srli_extracts_halfword_k4 (d addr : BitVec 64)
    (hk : (addr &&& 7).toNat = 4) :
    (let xor_addr := addr ^^^ (6 : BitVec 64)
     let shift_amt := shift_bits_left xor_addr (3 : BitVec 6)
     let shift_6 := Sail.BitVec.extractLsb shift_amt 5 0
     let shifted := shift_bits_left d shift_6
     shift_bits_right shifted (48 : BitVec 6))
    = zero_extend (m := 64) (halfword_of_dword d 4) := by
  unfold shift_bits_left shift_bits_right Sail.BitVec.extractLsb
  change (d <<< BitVec.extractLsb 5 0 ((addr ^^^ (6 : BitVec 64)) <<< 3)) >>>
      (48 : Nat) =
    zero_extend (m := 64) (halfword_of_dword d 4)
  rw [sll_halfword_shift_amount addr 4 hk (by omega) (by decide)]
  simpa using sll_srli48_extracts_halfword_k d 4 (8 * (6 - 4))
    (by omega) rfl

private lemma sll_srli_extracts_halfword_k6 (d addr : BitVec 64)
    (hk : (addr &&& 7).toNat = 6) :
    (let xor_addr := addr ^^^ (6 : BitVec 64)
     let shift_amt := shift_bits_left xor_addr (3 : BitVec 6)
     let shift_6 := Sail.BitVec.extractLsb shift_amt 5 0
     let shifted := shift_bits_left d shift_6
     shift_bits_right shifted (48 : BitVec 6))
    = zero_extend (m := 64) (halfword_of_dword d 6) := by
  unfold shift_bits_left shift_bits_right Sail.BitVec.extractLsb
  change (d <<< BitVec.extractLsb 5 0 ((addr ^^^ (6 : BitVec 64)) <<< 3)) >>>
      (48 : Nat) =
    zero_extend (m := 64) (halfword_of_dword d 6)
  rw [sll_halfword_shift_amount addr 6 hk (by omega) (by decide)]
  simpa using sll_srli48_extracts_halfword_k d 6 (8 * (6 - 6))
    (by omega) rfl

/-- Halfword-load arithmetic (unsigned): same setup as
    `sll_srai_extracts_halfword` but with a **logical** right shift by 48,
    yielding the zero-extended halfword at offset `(addr & 7)` of the
    dword. Used by `LHU`. -/
theorem sll_srli_extracts_halfword (d : BitVec 64) (addr : BitVec 64)
    (halign : addr &&& 1 = 0) :
    (let xor_addr := addr ^^^ (6 : BitVec 64)
     let shift_amt := shift_bits_left xor_addr (3 : BitVec 6)
     let shift_6 := Sail.BitVec.extractLsb shift_amt 5 0
     let shifted := shift_bits_left d shift_6
     shift_bits_right shifted (48 : BitVec 6))
    = zero_extend (m := 64) (halfword_of_dword d (addr &&& 7).toNat) := by
  rcases halfword_offset_cases addr halign with hk | hk | hk | hk
  · rw [hk]
    simpa using sll_srli_extracts_halfword_k0 d addr hk
  · rw [hk]
    simpa using sll_srli_extracts_halfword_k2 d addr hk
  · rw [hk]
    simpa using sll_srli_extracts_halfword_k4 d addr hk
  · rw [hk]
    simpa using sll_srli_extracts_halfword_k6 d addr hk

private lemma sll_word_shift_amount_k0 (addr : BitVec 64)
    (hk : (addr &&& 7).toNat = 0) :
    BitVec.extractLsb 5 0 ((addr ^^^ (4 : BitVec 64)) <<< 3) =
      (32 : BitVec 6) := by
  have hk_eq : addr &&& 7 = BitVec.ofNat 64 0 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat]
    omega
  have hbit0 : addr[0] = false := by
    have h := congrArg (fun x : BitVec 64 => x.getLsbD 0) hk_eq
    simpa [BitVec.getLsbD_eq_getElem] using h
  have hbit1 : addr[1] = false := by
    have h := congrArg (fun x : BitVec 64 => x.getLsbD 1) hk_eq
    simpa [BitVec.getLsbD_eq_getElem] using h
  have hbit2 : addr[2] = false := by
    have h := congrArg (fun x : BitVec 64 => x.getLsbD 2) hk_eq
    simpa [BitVec.getLsbD_eq_getElem] using h
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_extractLsb, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_xor]
  interval_cases i <;> simp [hbit0, hbit1, hbit2]

private lemma sll32_srli32_extracts_word0 (d : BitVec 64) :
    (d <<< (32 : Nat)) >>> (32 : Nat) =
      zero_extend (m := 64) (word_of_dword d 0) := by
  unfold zero_extend word_of_dword Sail.BitVec.zeroExtend
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft]
  by_cases hi32 : i < 32
  · have hlt : 32 + i < 64 := by omega
    simp [hi32, hlt, hi]
  · have hge : 64 ≤ 32 + i := by omega
    simp [hi32, hge]

private lemma sll_srli_extracts_word_k0 (d addr : BitVec 64)
    (hk : (addr &&& 7).toNat = 0) :
    (let xor_addr := addr ^^^ (4 : BitVec 64)
     let shift_amt := shift_bits_left xor_addr (3 : BitVec 6)
     let shift_6 := Sail.BitVec.extractLsb shift_amt 5 0
     let shifted := shift_bits_left d shift_6
     shift_bits_right shifted (32 : BitVec 6))
    = zero_extend (m := 64) (word_of_dword d 0) := by
  change shift_bits_right
      (shift_bits_left d (BitVec.extractLsb 5 0 ((addr ^^^ (4 : BitVec 64)) <<< 3)))
      (32 : BitVec 6) =
    zero_extend (m := 64) (word_of_dword d 0)
  rw [sll_word_shift_amount_k0 addr hk]
  simpa [shift_bits_left, shift_bits_right] using sll32_srli32_extracts_word0 d

private lemma sll_word_shift_amount_k4 (addr : BitVec 64)
    (hk : (addr &&& 7).toNat = 4) :
    BitVec.extractLsb 5 0 ((addr ^^^ (4 : BitVec 64)) <<< 3) =
      (0 : BitVec 6) := by
  have hk_eq : addr &&& 7 = BitVec.ofNat 64 4 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat]
    omega
  have hbit0 : addr[0] = false := by
    have h := congrArg (fun x : BitVec 64 => x.getLsbD 0) hk_eq
    simpa [BitVec.getLsbD_eq_getElem] using h
  have hbit1 : addr[1] = false := by
    have h := congrArg (fun x : BitVec 64 => x.getLsbD 1) hk_eq
    simpa [BitVec.getLsbD_eq_getElem] using h
  have hbit2 : addr[2] = true := by
    have h := congrArg (fun x : BitVec 64 => x.getLsbD 2) hk_eq
    simpa [BitVec.getLsbD_eq_getElem] using h
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_extractLsb, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_xor]
  interval_cases i <;> simp [hbit0, hbit1, hbit2]

private lemma sll0_srli32_extracts_word4 (d : BitVec 64) :
    (d <<< (0 : Nat)) >>> (32 : Nat) =
      zero_extend (m := 64) (word_of_dword d 4) := by
  unfold zero_extend word_of_dword Sail.BitVec.zeroExtend
  ext i
  by_cases hi32 : i < 32
  · simp [hi32]
  · have hge : 64 ≤ 32 + i := by omega
    simp [hi32, hge]

private lemma sll_srli_extracts_word_k4 (d addr : BitVec 64)
    (hk : (addr &&& 7).toNat = 4) :
    (let xor_addr := addr ^^^ (4 : BitVec 64)
     let shift_amt := shift_bits_left xor_addr (3 : BitVec 6)
     let shift_6 := Sail.BitVec.extractLsb shift_amt 5 0
     let shifted := shift_bits_left d shift_6
     shift_bits_right shifted (32 : BitVec 6))
    = zero_extend (m := 64) (word_of_dword d 4) := by
  change shift_bits_right
      (shift_bits_left d (BitVec.extractLsb 5 0 ((addr ^^^ (4 : BitVec 64)) <<< 3)))
      (32 : BitVec 6) =
    zero_extend (m := 64) (word_of_dword d 4)
  rw [sll_word_shift_amount_k4 addr hk]
  simpa [shift_bits_left, shift_bits_right] using sll0_srli32_extracts_word4 d

/-- Word-load arithmetic (unsigned): `XOR addr 4`, `SLL` by 3, `SLL` the
    dword by that, then logical-shift right by 32, yields the
    zero-extended word at offset `(addr & 7)` of the dword. Requires word
    alignment `halign : addr & 3 = 0`. Used by `LWU`. Dispatches on the
    two possible word offsets (0, 4). Note: this uses the SLL+SRLI pattern
    (like LB/LH), *not* the SRL+VirtualSignExtendWord pattern that LW
    uses on the signed side. -/
theorem sll_srli_extracts_word (d : BitVec 64) (addr : BitVec 64)
    (halign : addr &&& 3 = 0) :
    (let xor_addr := addr ^^^ (4 : BitVec 64)
     let shift_amt := shift_bits_left xor_addr (3 : BitVec 6)
     let shift_6 := Sail.BitVec.extractLsb shift_amt 5 0
     let shifted := shift_bits_left d shift_6
     shift_bits_right shifted (32 : BitVec 6))
    = zero_extend (m := 64) (word_of_dword d (addr &&& 7).toNat) := by
  rcases word_offset_cases addr halign with hk | hk
  · rw [hk]
    simpa using sll_srli_extracts_word_k0 d addr hk
  · rw [hk]
    simpa using sll_srli_extracts_word_k4 d addr hk

private lemma srl_word_shift_amount_k0 (addr : BitVec 64)
    (hk : (addr &&& 7).toNat = 0) :
    Sail.BitVec.extractLsb (shift_bits_left addr (3 : BitVec 6)) 5 0 =
      (0 : BitVec 6) := by
  change BitVec.extractLsb 5 0 (addr <<< 3) = (0 : BitVec 6)
  have hk_eq : addr &&& 7 = BitVec.ofNat 64 0 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat]
    omega
  have hbit0 : addr[0] = false := by
    have h := congrArg (fun x : BitVec 64 => x.getLsbD 0) hk_eq
    simpa [BitVec.getLsbD_eq_getElem] using h
  have hbit1 : addr[1] = false := by
    have h := congrArg (fun x : BitVec 64 => x.getLsbD 1) hk_eq
    simpa [BitVec.getLsbD_eq_getElem] using h
  have hbit2 : addr[2] = false := by
    have h := congrArg (fun x : BitVec 64 => x.getLsbD 2) hk_eq
    simpa [BitVec.getLsbD_eq_getElem] using h
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_extractLsb, BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp [hbit0, hbit1, hbit2]

private lemma srl_word_shift_amount_k4 (addr : BitVec 64)
    (hk : (addr &&& 7).toNat = 4) :
    Sail.BitVec.extractLsb (shift_bits_left addr (3 : BitVec 6)) 5 0 =
      (32 : BitVec 6) := by
  change BitVec.extractLsb 5 0 (addr <<< 3) = (32 : BitVec 6)
  have hk_eq : addr &&& 7 = BitVec.ofNat 64 4 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat]
    omega
  have hbit0 : addr[0] = false := by
    have h := congrArg (fun x : BitVec 64 => x.getLsbD 0) hk_eq
    simpa [BitVec.getLsbD_eq_getElem] using h
  have hbit1 : addr[1] = false := by
    have h := congrArg (fun x : BitVec 64 => x.getLsbD 1) hk_eq
    simpa [BitVec.getLsbD_eq_getElem] using h
  have hbit2 : addr[2] = true := by
    have h := congrArg (fun x : BitVec 64 => x.getLsbD 2) hk_eq
    simpa [BitVec.getLsbD_eq_getElem] using h
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_extractLsb, BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp [hbit0, hbit1, hbit2]

private lemma extractLsb_31_0_eq_setWidth32 (x : BitVec 64) :
    BitVec.extractLsb 31 0 x = x.setWidth 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_extractLsb]
  simp

/-- Word-load arithmetic: `SLL addr` by 3 and use as shift amount on the
    dword with a logical right shift, then extract the lower 32 bits and
    sign-extend, yields the sign-extended word at offset `(addr & 7)` of the
    dword. Requires word alignment `halign : addr & 3 = 0`. -/
theorem srl_sign_extend_word_extracts_word (d : BitVec 64) (addr : BitVec 64)
    (halign : addr &&& 3 = 0) :
    (let shifted := shift_bits_right d (Sail.BitVec.extractLsb (shift_bits_left addr (3 : BitVec 6)) 5 0)
     sign_extend (m := 64) ((Sail.BitVec.extractLsb shifted 31 0) : BitVec 32))
    = sign_extend (m := 64) (word_of_dword d (addr &&& 7).toNat) := by
  rcases word_offset_cases addr halign with hk | hk
  · rw [hk]
    rw [srl_word_shift_amount_k0 addr hk]
    simp [shift_bits_right, word_of_dword, sign_extend,
      Sail.BitVec.extractLsb, Sail.BitVec.signExtend,
      extractLsb_31_0_eq_setWidth32]
  · rw [hk]
    rw [srl_word_shift_amount_k4 addr hk]
    simp [shift_bits_right, word_of_dword, sign_extend,
      Sail.BitVec.extractLsb, Sail.BitVec.signExtend,
      extractLsb_31_0_eq_setWidth32]
