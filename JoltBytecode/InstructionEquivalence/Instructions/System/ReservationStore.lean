import JoltBytecode.InstructionEquivalence.Instructions.System.Reservation

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail
open LeanRV64D LeanRV64D.Functions

noncomputable section
namespace SystemProofs

/-- Replacing a word by the same slice of its containing doubleword is an identity.
For example, extracting and reinserting the upper 32 bits preserves all 64 bits. -/
theorem wordSplice_read_self (value : BitVec 64) (shift : Nat) :
    StoreSplice.wordSplice value ((value >>> shift).setWidth 32) shift = value := by
  have hmask : (0xffffffff : BitVec 64) = (BitVec.allOnes 32).zeroExtend 64 := rfl
  unfold StoreSplice.wordSplice
  rw [hmask]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft,
    BitVec.zeroExtend_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_allOnes]
  by_cases hs : i < shift
  · simp [hi, hs]
  · have hindex : shift + (i - shift) = i := by omega
    by_cases hl : i - shift < 32
    · have hi' : i - shift < 64 := by omega
      simp [hi, hs, hl, hindex, hi']
    · simp [hi, hs, hl]

/-- The byte offset from an aligned doubleword base is the address's low bits.
For example, address 12 has offset 4 from its base 8. -/
theorem reservation_offset (addr : BitVec 64) :
    (addr - amoWordBase addr).toNat = (addr &&& (7 : BitVec 64)).toNat := by
  have h := congrArg (fun v => v - amoWordBase addr) (addr_split_aligned_offset addr)
  rw [BitVec.add_comm, BitVec.add_sub_cancel] at h
  rw [← h, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (by have := (addr &&& (7 : BitVec 64)).isLt; exact this)

/-- Merging the signed old word back into its original lane preserves the data.
For example, a failed SC.W's lane merge reconstructs the original doubleword. -/
theorem scWord_merge_old (addr value : BitVec 64) (ha : addr &&& 3#64 = 0#64) :
    AtomicFamily.amoWordLaneMerged addr value (AtomicFamily.amoWordLaneOld addr value) = value := by
  have hsetup := AtomicFamily.amo_word_store_facts addr (AtomicFamily.amo_word_base_no_ovf addr) ha
  rw [AtomicFamily.amo_word_lane_old_eq addr value ha]
  change (value &&& ~~~(jolt_virtual_window_mask_w_value addr 0)) +
      jolt_virtual_shift_data_w_value (sign_extend (m := 64)
        (word_of_dword value (addr &&& (7 : BitVec 64)).toNat)) addr = value
  have hlow (word : BitVec 32) :
      (Sail.BitVec.extractLsb (sign_extend (m := 64) word) 31 0 : BitVec 32) = word := by
    change BitVec.ofNat 32 ((sign_extend (m := 64) word).toNat >>> 0) = word
    rw [Nat.shiftRight_zero]
    have h := AtomicFamily.sign_extend_64_setWidth_32 word
    have hn : ¬(64 : Nat) ≤ 32 := by decide
    simpa only [BitVec.setWidth, dif_neg hn] using h

  rw [StoreSplice.fusedWordSplice_eq value _ addr (amoWordBase addr) hsetup, hlow]
  rw [reservation_offset, Nat.mul_comm]
  exact wordSplice_read_self value _

end SystemProofs
