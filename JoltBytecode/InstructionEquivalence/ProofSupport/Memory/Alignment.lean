import JoltBytecode.JoltISA.MemoryAccess
import JoltBytecode.InstructionEquivalence.ProofSupport.Memory.Basic
import Mathlib.Tactic.IntervalCases

/-!
# Memory alignment facts

This file contains the alignment evidence records and pure bit-vector facts used
by load, store, and atomic memory proofs. It also proves the aligned-dword facts
for the public memory address expressions.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option mvcgen.warning false

open Sail PreSail LeanRV64D.Functions
open Std.Do
open virtaddr MemoryAccessType mem_payload

set_option autoImplicit true

noncomputable section

-- ============================================================================
-- Reusable pipeline evidence
-- ============================================================================

/-- The access at `addr` of `width` bytes will not be split into multiple
    accesses by the Sail pipeline. This means:
    - The misalignment check passes (no trap on this access).
    - `split_misaligned` returns `(1, width)`: one access, full width.
    These hold when the address is naturally aligned or the platform
    allows misaligned access (`plat_enable_misaligned_access = true`). -/
structure AlignedAccess (addr : BitVec 64) (width : Nat) : Prop where
  misalign : access_causes_misaligned_exception (Virtaddr addr) width false = false
  split : split_misaligned (Virtaddr addr) width = (pure (1, width) : SailM (Int × Int))

/-- An 8-byte access that is naturally aligned with no address overflow. -/
structure AlignedDwordAccess (addr : BitVec 64) : Prop extends AlignedAccess addr 8 where
  align : addr &&& 7 = 0
  no_ovf : addr.toNat + 7 < 2 ^ 64

-- ============================================================================
-- Reusable pure alignment facts
-- ============================================================================
-- For each access width `w ∈ {4, 8}` we have three facts:
--   1. `access_misaligned_w_aligned_false` — if `addr` is `w`-aligned then the
--      Sail misalignment guard returns `false` (no exception raised).
--   2. `access_misaligned_w_unaligned_true` — if `addr` is NOT `w`-aligned then
--      the guard returns `true` (Sail raises the misalignment exception).
--   3. `split_misaligned_aligned_w` — if `addr` is `w`-aligned then Sail's
--      `split_misaligned` returns `pure (1, w)` (one access, full width).
-- These collapse the vmem pipeline into the clean "read all `w` bytes at once"
-- branch. Byte (width 1) is trivially aligned so doesn't need lemmas.

/-- Every address is aligned for a 1-byte access. -/
theorem access_misaligned_1_false (addr : BitVec 64) :
    access_causes_misaligned_exception (Virtaddr addr) 1 false = false := by
  unfold access_causes_misaligned_exception is_aligned_vaddr Sail.BitVec.toNatInt
  simp [Int.tmod, LeanRV64D.Functions.not]

/-- A 1-byte access never fragments. -/
theorem split_misaligned_1 (addr : BitVec 64) :
    split_misaligned (Virtaddr addr) 1 = (pure (1, 1) : SailM (Int × Int)) := by
  funext s
  unfold split_misaligned is_aligned_vaddr Sail.BitVec.toNatInt
  simp [Int.tmod, pure, EStateM.pure]

/-- The reusable aligned-access bundle for byte loads. -/
theorem aligned_access_1 (addr : BitVec 64) : AlignedAccess addr 1 := by
  exact
    { misalign := access_misaligned_1_false addr
      split := split_misaligned_1 addr }

/-- An 8-aligned address doesn't trigger the misalignment exception. -/
theorem access_misaligned_8_aligned_false (addr : BitVec 64)
    (halign : addr &&& 7 = 0) :
    access_causes_misaligned_exception (Virtaddr addr) 8 false = false := by
  unfold access_causes_misaligned_exception is_aligned_vaddr Sail.BitVec.toNatInt
  have h_mod : addr.toNat % 8 = 0 := by
    have h := congrArg BitVec.toNat halign
    rw [BitVec.toNat_and] at h
    have h7 : (7 : BitVec 64).toNat = 7 := by decide
    have h0 : (0 : BitVec 64).toNat = 0 := by decide
    rw [h7, h0,
        show (7 : Nat) = 2^3 - 1 from by norm_num,
        Nat.and_two_pow_sub_one_eq_mod] at h
    exact h
  simp [Int.tmod, h_mod, LeanRV64D.Functions.not]

/-- A NON-8-aligned address is not aligned according to Sail's virtual-address
    alignment predicate. -/
theorem is_aligned_vaddr_8_unaligned_false (addr : BitVec 64)
    (halign : addr &&& 7 ≠ 0) :
    is_aligned_vaddr (Virtaddr addr) 8 = false := by
  unfold is_aligned_vaddr Sail.BitVec.toNatInt
  have h_mod : addr.toNat % 8 ≠ 0 := by
    intro h0
    apply halign
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and]
    have h7 : (7 : BitVec 64).toNat = 7 := by decide
    have hzero : (0 : BitVec 64).toNat = 0 := by decide
    rw [h7,
        hzero,
        show (7 : Nat) = 2^3 - 1 from by norm_num,
        Nat.and_two_pow_sub_one_eq_mod,
        h0]
  have h_mod_int : (↑addr.toNat : Int) % 8 ≠ 0 := by
    intro h0
    apply h_mod
    exact_mod_cast h0
  simp [Int.tmod, h_mod_int]

/-- A NON-8-aligned address triggers the misalignment exception for an
    8-byte access. -/
theorem access_misaligned_8_unaligned_true (addr : BitVec 64)
    (halign : addr &&& 7 ≠ 0) :
    access_causes_misaligned_exception (Virtaddr addr) 8 false = true := by
  unfold access_causes_misaligned_exception is_aligned_vaddr Sail.BitVec.toNatInt
  have h_mod : addr.toNat % 8 ≠ 0 := by
    intro h0
    apply halign
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and]
    have h7 : (7 : BitVec 64).toNat = 7 := by decide
    have hzero : (0 : BitVec 64).toNat = 0 := by decide
    rw [h7,
        hzero,
        show (7 : Nat) = 2^3 - 1 from by norm_num,
        Nat.and_two_pow_sub_one_eq_mod,
        h0]
  have h_mod_int : (↑addr.toNat : Int) % 8 ≠ 0 := by
    intro h0
    apply h_mod
    exact_mod_cast h0
  simp [Int.tmod, h_mod_int, LeanRV64D.Functions.not, plat_enable_misaligned_access]

/-- An 8-aligned address doesn't fragment — `split_misaligned` yields the
    single-access `(1, 8)` pair. -/
theorem split_misaligned_aligned_8 (addr : BitVec 64)
    (halign : addr &&& 7 = 0) :
    split_misaligned (Virtaddr addr) 8 = (pure (1, 8) : SailM (Int × Int)) := by
  funext s
  unfold split_misaligned is_aligned_vaddr Sail.BitVec.toNatInt
  have h_mod : addr.toNat % 8 = 0 := by
    have h := congrArg BitVec.toNat halign
    rw [BitVec.toNat_and] at h
    have h7 : (7 : BitVec 64).toNat = 7 := by decide
    have h0 : (0 : BitVec 64).toNat = 0 := by decide
    rw [h7, h0,
        show (7 : Nat) = 2^3 - 1 from by norm_num,
        Nat.and_two_pow_sub_one_eq_mod] at h
    exact h
  simp [Int.tmod, h_mod, pure, EStateM.pure]

/-- A 4-aligned address (low 2 bits zero) doesn't trigger the misalignment
    exception for a 4-byte access. -/
theorem access_misaligned_4_aligned_false (addr : BitVec 64)
    (halign : addr &&& 3 = 0) :
    access_causes_misaligned_exception (Virtaddr addr) 4 false = false := by
  unfold access_causes_misaligned_exception is_aligned_vaddr Sail.BitVec.toNatInt
  have h_mod : addr.toNat % 4 = 0 := by
    have h := congrArg BitVec.toNat halign
    rw [BitVec.toNat_and] at h
    have h3 : (3 : BitVec 64).toNat = 3 := by decide
    have h0 : (0 : BitVec 64).toNat = 0 := by decide
    rw [h3, h0,
        show (3 : Nat) = 2^2 - 1 from by norm_num,
        Nat.and_two_pow_sub_one_eq_mod] at h
    exact h
  simp [Int.tmod, h_mod, LeanRV64D.Functions.not]

/-- A NON-4-aligned address triggers the misalignment exception for a 4-byte
    access (assuming the platform forbids misaligned access, which we have
    configured in `plat_enable_misaligned_access = false`). -/
theorem access_misaligned_4_unaligned_true (addr : BitVec 64)
    (halign : addr &&& 3 ≠ 0) :
    access_causes_misaligned_exception (Virtaddr addr) 4 false = true := by
  unfold access_causes_misaligned_exception is_aligned_vaddr Sail.BitVec.toNatInt
  have h_mod : addr.toNat % 4 ≠ 0 := by
    intro h0
    apply halign
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and]
    have h3 : (3 : BitVec 64).toNat = 3 := by decide
    have hzero : (0 : BitVec 64).toNat = 0 := by decide
    rw [h3,
        hzero,
        show (3 : Nat) = 2^2 - 1 from by norm_num,
        Nat.and_two_pow_sub_one_eq_mod,
        h0]
  have h_mod_int : (↑addr.toNat : Int) % 4 ≠ 0 := by
    intro h0
    apply h_mod
    have hdiv_int : (4 : Int) ∣ (addr.toNat : Int) :=
      Int.dvd_of_emod_eq_zero h0
    have hdiv_nat : 4 ∣ addr.toNat := by
      exact_mod_cast hdiv_int
    exact Nat.mod_eq_zero_of_dvd hdiv_nat
  simp [Int.tmod, h_mod_int, LeanRV64D.Functions.not, plat_enable_misaligned_access]

/-- A 4-aligned address doesn't fragment — `split_misaligned` yields the
    single-access `(1, 4)` pair. -/
theorem split_misaligned_aligned_4 (addr : BitVec 64)
    (halign : addr &&& 3 = 0) :
    split_misaligned (Virtaddr addr) 4 = (pure (1, 4) : SailM (Int × Int)) := by
  funext s
  unfold split_misaligned is_aligned_vaddr Sail.BitVec.toNatInt
  have h_mod : addr.toNat % 4 = 0 := by
    have h := congrArg BitVec.toNat halign
    rw [BitVec.toNat_and] at h
    have h3 : (3 : BitVec 64).toNat = 3 := by decide
    have h0 : (0 : BitVec 64).toNat = 0 := by decide
    rw [h3, h0,
        show (3 : Nat) = 2^2 - 1 from by norm_num,
        Nat.and_two_pow_sub_one_eq_mod] at h
    exact h
  simp [Int.tmod, h_mod, pure, EStateM.pure]

/-- A 4-aligned 64-bit address has room for the full word window. -/
theorem aligned_word_addr_no_ovf (addr : BitVec 64)
    (halign : addr &&& 3 = 0) :
    addr.toNat + 3 < 2 ^ 64 := by
  have h_mod : addr.toNat % 4 = 0 := by
    have h := congrArg BitVec.toNat halign
    rw [BitVec.toNat_and] at h
    have h3 : (3 : BitVec 64).toNat = 3 := by decide
    have h0 : (0 : BitVec 64).toNat = 0 := by decide
    rw [h3, h0,
        show (3 : Nat) = 2^2 - 1 from by norm_num,
        Nat.and_two_pow_sub_one_eq_mod] at h
    exact h
  have hlt : addr.toNat < 2 ^ 64 := addr.isLt
  omega

/-- A 2-aligned 64-bit address has room for the full halfword window. -/
theorem aligned_halfword_addr_no_ovf (addr : BitVec 64)
    (halign : addr &&& 1 = 0) :
    addr.toNat + 1 < 2 ^ 64 := by
  have h_mod : addr.toNat % 2 = 0 := by
    have h := congrArg BitVec.toNat halign
    rw [BitVec.toNat_and] at h
    have h1 : (1 : BitVec 64).toNat = 1 := by decide
    have h0 : (0 : BitVec 64).toNat = 0 := by decide
    rw [h1, h0,
        show (1 : Nat) = 2^1 - 1 from by norm_num,
        Nat.and_two_pow_sub_one_eq_mod] at h
    exact h
  have hlt : addr.toNat < 2 ^ 64 := addr.isLt
  omega

/-- A 2-aligned address (low 1 bit zero) doesn't trigger the misalignment
    exception for a 2-byte access. -/
theorem access_misaligned_2_aligned_false (addr : BitVec 64)
    (halign : addr &&& 1 = 0) :
    access_causes_misaligned_exception (Virtaddr addr) 2 false = false := by
  unfold access_causes_misaligned_exception is_aligned_vaddr Sail.BitVec.toNatInt
  have h_mod : addr.toNat % 2 = 0 := by
    have h := congrArg BitVec.toNat halign
    rw [BitVec.toNat_and] at h
    have h1 : (1 : BitVec 64).toNat = 1 := by decide
    have h0 : (0 : BitVec 64).toNat = 0 := by decide
    rw [h1, h0,
        show (1 : Nat) = 2^1 - 1 from by norm_num,
        Nat.and_two_pow_sub_one_eq_mod] at h
    exact h
  simp [Int.tmod, h_mod, LeanRV64D.Functions.not]

/-- A NON-2-aligned address triggers the misalignment exception for a 2-byte
    access. -/
theorem access_misaligned_2_unaligned_true (addr : BitVec 64)
    (halign : addr &&& 1 ≠ 0) :
    access_causes_misaligned_exception (Virtaddr addr) 2 false = true := by
  unfold access_causes_misaligned_exception is_aligned_vaddr Sail.BitVec.toNatInt
  have h_mod : addr.toNat % 2 ≠ 0 := by
    intro h0
    apply halign
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and]
    have h1 : (1 : BitVec 64).toNat = 1 := by decide
    have hzero : (0 : BitVec 64).toNat = 0 := by decide
    rw [h1,
        hzero,
        show (1 : Nat) = 2^1 - 1 from by norm_num,
        Nat.and_two_pow_sub_one_eq_mod,
        h0]
  have h_mod_int : (↑addr.toNat : Int) % 2 ≠ 0 := by
    intro h0
    apply h_mod
    have hdiv_int : (2 : Int) ∣ (addr.toNat : Int) :=
      Int.dvd_of_emod_eq_zero h0
    have hdiv_nat : 2 ∣ addr.toNat := by
      exact_mod_cast hdiv_int
    exact Nat.mod_eq_zero_of_dvd hdiv_nat
  simp [Int.tmod, h_mod_int, LeanRV64D.Functions.not, plat_enable_misaligned_access]

/-- A 2-aligned address doesn't fragment — `split_misaligned` yields the
    single-access `(1, 2)` pair. -/
theorem split_misaligned_aligned_2 (addr : BitVec 64)
    (halign : addr &&& 1 = 0) :
    split_misaligned (Virtaddr addr) 2 = (pure (1, 2) : SailM (Int × Int)) := by
  funext s
  unfold split_misaligned is_aligned_vaddr Sail.BitVec.toNatInt
  have h_mod : addr.toNat % 2 = 0 := by
    have h := congrArg BitVec.toNat halign
    rw [BitVec.toNat_and] at h
    have h1 : (1 : BitVec 64).toNat = 1 := by decide
    have h0 : (0 : BitVec 64).toNat = 0 := by decide
    rw [h1, h0,
        show (1 : Nat) = 2^1 - 1 from by norm_num,
        Nat.and_two_pow_sub_one_eq_mod] at h
    exact h
  simp [Int.tmod, h_mod, pure, EStateM.pure]

-- ============================================================================
-- Public memory-address alignment facts
-- ============================================================================

/-- `aligned_dword_addr` is just "effective address aligned down to 8 bytes". -/
theorem aligned_dword_addr_eq (v : BitVec 64) (imm : BitVec 12) :
    aligned_dword_addr v imm =
      (v + sign_extend (m := 64) imm) &&& (-8 : BitVec 64) := by
  unfold aligned_dword_addr
  have h8 : sign_extend (m := 64) (-8 : BitVec 12) = (-8 : BitVec 64) := by decide
  rw [h8]

-- ============================================================================
-- Properties of `aligned_dword_addr`
-- ============================================================================
-- These say: the Jolt inline-sequence base address (effective address with its
-- low 3 bits cleared) is 8-aligned, its `.toNat + 7` does not overflow 2^64,
-- and from those two facts it satisfies the full `AlignedDwordAccess` bundle.
-- Used by every load instruction's decomposed-program proof, so they live
-- next to the `aligned_dword_addr` definition rather than inside each
-- instruction file.

/-- The Jolt inline-sequence base address is naturally 8-aligned. -/
theorem align_down_8_and_7_eq_zero (x : BitVec 64) :
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

theorem aligned_dword_addr_aligns (val : BitVec 64) (imm : BitVec 12) :
    aligned_dword_addr val imm &&& 7 = 0 := by
  rw [aligned_dword_addr_eq]
  exact align_down_8_and_7_eq_zero _

/-- An 8-aligned 64-bit address, viewed as a natural number, has no overflow
    when we add 7. -/
theorem aligned_addr_no_ovf_of_align (addr : BitVec 64)
    (halign : addr &&& 7 = 0) :
    addr.toNat + 7 < 2 ^ 64 := by
  have h_mod : addr.toNat % 8 = 0 := by
    have h := congrArg BitVec.toNat halign
    rw [BitVec.toNat_and] at h
    have h7 : BitVec.toNat (7 : BitVec 64) = 7 := by decide
    have h0 : BitVec.toNat (0 : BitVec 64) = 0 := by decide
    rw [h7, h0] at h
    rw [show (7 : Nat) = 2^3 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod] at h
    exact h
  have hlt : addr.toNat < 2 ^ 64 := addr.isLt
  omega

/-- Specialisation of the previous lemma to the Jolt inline-sequence base
    address. -/
theorem aligned_dword_addr_no_ovf (val : BitVec 64) (imm : BitVec 12) :
    (aligned_dword_addr val imm).toNat + 7 < 2 ^ 64 :=
  aligned_addr_no_ovf_of_align _ (aligned_dword_addr_aligns val imm)

/-- The Jolt inline-sequence base address is a proper `AlignedDwordAccess`:
    misalignment check passes, split is trivial, address is 8-aligned, and
    `+7` doesn't overflow. -/
theorem aligned_dword_addr_is_aligned_dword_access (val : BitVec 64) (imm : BitVec 12) :
    AlignedDwordAccess (aligned_dword_addr val imm) := by
  refine
    { misalign := access_misaligned_8_aligned_false _ (aligned_dword_addr_aligns val imm)
      split := split_misaligned_aligned_8 _ (aligned_dword_addr_aligns val imm)
      align := aligned_dword_addr_aligns val imm
      no_ovf := aligned_dword_addr_no_ovf val imm }

end
