import JoltConstraints.Constraints.LookupOperandData
import JoltConstraints.lookup_table

/-! Pure identities for the interleaved lookup address, shared with completeness.
Odd positions hold the left operand and even positions the right, counting from
bit zero at the least significant end. The bit-unpacking implementation mirrors
Jolt's `uninterleave_bits` at revision 43cc043332762034b5f65379441576e06e7a3890. -/

set_option autoImplicit false

namespace JoltConstraints

open TraceWitness

-- Keep the mask calculations in four small proofs at the default heartbeat
-- limit. `simp` checks the constant mask bits in the kernel; these helpers
-- replace the completeness proof's native `bv_decide` dependencies.
private theorem uninterleave_snd_bits_0_15
    (v : BitVec 128) (i : Nat) (upper : i < 16) :
    (uninterleave v.toFin).2.getLsbD i = v.getLsbD (2 * i) := by
  interval_cases i <;>
    simp only [uninterleave, BitVec.ofFin_toFin, BitVec.getLsbD_setWidth,
      BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight,
      BitVec.getLsbD_ofNat, Nat.testBit_eq_decide_div_mod_eq, Nat.reduceAdd, Nat.reduceMul,
      Nat.reduceLT, Nat.reducePow, Nat.reduceDiv, Nat.reduceMod, Nat.reduceEqDiff, decide_true, decide_false, Bool.true_and, Bool.and_true,
      Bool.and_false, Bool.false_or, Bool.or_false]

private theorem uninterleave_snd_bits_16_31
    (v : BitVec 128) (i : Nat) (lower : 16 ≤ i) (upper : i < 32) :
    (uninterleave v.toFin).2.getLsbD i = v.getLsbD (2 * i) := by
  interval_cases i <;>
    simp only [uninterleave, BitVec.ofFin_toFin, BitVec.getLsbD_setWidth,
      BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight,
      BitVec.getLsbD_ofNat, Nat.testBit_eq_decide_div_mod_eq, Nat.reduceAdd, Nat.reduceMul,
      Nat.reduceLT, Nat.reducePow, Nat.reduceDiv, Nat.reduceMod, Nat.reduceEqDiff, decide_true, decide_false, Bool.true_and, Bool.and_true,
      Bool.and_false, Bool.false_or, Bool.or_false]

private theorem uninterleave_snd_bits_32_47
    (v : BitVec 128) (i : Nat) (lower : 32 ≤ i) (upper : i < 48) :
    (uninterleave v.toFin).2.getLsbD i = v.getLsbD (2 * i) := by
  interval_cases i <;>
    simp only [uninterleave, BitVec.ofFin_toFin, BitVec.getLsbD_setWidth,
      BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight,
      BitVec.getLsbD_ofNat, Nat.testBit_eq_decide_div_mod_eq, Nat.reduceAdd, Nat.reduceMul,
      Nat.reduceLT, Nat.reducePow, Nat.reduceDiv, Nat.reduceMod, Nat.reduceEqDiff, decide_true, decide_false, Bool.true_and, Bool.and_true,
      Bool.and_false, Bool.false_or, Bool.or_false]

private theorem uninterleave_snd_bits_48_63
    (v : BitVec 128) (i : Nat) (lower : 48 ≤ i) (upper : i < 64) :
    (uninterleave v.toFin).2.getLsbD i = v.getLsbD (2 * i) := by
  interval_cases i <;>
    simp only [uninterleave, BitVec.ofFin_toFin, BitVec.getLsbD_setWidth,
      BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight,
      BitVec.getLsbD_ofNat, Nat.testBit_eq_decide_div_mod_eq, Nat.reduceAdd, Nat.reduceMul,
      Nat.reduceLT, Nat.reducePow, Nat.reduceDiv, Nat.reduceMod, Nat.reduceEqDiff, decide_true, decide_false, Bool.true_and, Bool.and_true,
      Bool.and_false, Bool.false_or, Bool.or_false]

/-- Unpacking the right word reads the address's even bit positions. -/
theorem uninterleave_snd_getLsbD (v : BitVec 128) (i : Nat) (hi : i < 64) :
    (uninterleave v.toFin).2.getLsbD i = v.getLsbD (2 * i) := by
  by_cases first : i < 16
  · exact uninterleave_snd_bits_0_15 v i first
  by_cases second : i < 32
  · exact uninterleave_snd_bits_16_31 v i (by omega) second
  by_cases third : i < 48
  · exact uninterleave_snd_bits_32_47 v i (by omega) third
  exact uninterleave_snd_bits_48_63 v i (by omega) hi

/-- Unpacking the left word reads the address's odd bit positions. -/
theorem uninterleave_fst_getLsbD (v : BitVec 128) (i : Nat) (hi : i < 64) :
    (uninterleave v.toFin).1.getLsbD i = v.getLsbD (2 * i + 1) := by
  change (uninterleave (v >>> 1).toFin).2.getLsbD i = _
  simpa only [BitVec.getLsbD_ushiftRight, Nat.add_comm] using
    uninterleave_snd_getLsbD (v >>> 1) i hi

/-- Unpacking an interleaving recovers both original words. -/
theorem uninterleave_interleave (l r : BitVec 64) :
    uninterleave (interleaveLookupOperands l r).toFin = (l, r) := by
  ext i hi
  · rw [← BitVec.getLsbD_eq_getElem, ← BitVec.getLsbD_eq_getElem,
      uninterleave_fst_getLsbD _ i hi, BitVec.getLsbD,
      interleaveLookupOperands_testBit l r (by omega)]
    have h1 : (2 * i + 1) % 2 = 1 := by omega
    have h2 : (2 * i + 1) / 2 = i := by omega
    simp only [h1, h2, ↓reduceIte]
  · rw [← BitVec.getLsbD_eq_getElem, ← BitVec.getLsbD_eq_getElem,
      uninterleave_snd_getLsbD _ i hi, BitVec.getLsbD,
      interleaveLookupOperands_testBit l r (by omega)]
    have h1 : 2 * i % 2 = 0 := by omega
    have h2 : 2 * i / 2 = i := by omega
    simp only [h1, h2, Nat.zero_ne_one, ↓reduceIte]

/-- Packing the two decoded words recovers every 128-bit address. -/
theorem interleave_uninterleave (address : Fin (2 ^ 128)) :
    (interleaveLookupOperands (uninterleave address).1 (uninterleave address).2).toFin =
      address := by
  suffices same : interleaveLookupOperands (uninterleave address).1
      (uninterleave address).2 = BitVec.ofFin address by
    exact congrArg BitVec.toFin same
  ext i hi
  rw [← BitVec.getLsbD_eq_getElem, ← BitVec.getLsbD_eq_getElem,
    BitVec.getLsbD, interleaveLookupOperands_testBit _ _ hi]
  have half : i / 2 < 64 := by omega
  rcases Nat.mod_two_eq_zero_or_one i with even | odd
  · have decoded := uninterleave_snd_getLsbD (BitVec.ofFin address) (i / 2) half
    have index : 2 * (i / 2) = i := by omega
    simpa only [even, Nat.zero_ne_one, ↓reduceIte, BitVec.toFin_ofFin, index] using decoded
  · have decoded := uninterleave_fst_getLsbD (BitVec.ofFin address) (i / 2) half
    have index : 2 * (i / 2) + 1 = i := by omega
    simpa only [odd, ↓reduceIte, BitVec.toFin_ofFin, index] using decoded

/-- The left operand's field polynomial encodes the word obtained by unpacking
odd address bits. -/
theorem lookupAddressLeft_eq_uninterleave {F : Type} [Field F]
    (address : Fin (2 ^ 128)) :
    lookupAddressLeft (F := F) address = ((uninterleave address).1.toNat : F) := by
  rw [bitVec_toNat_cast_eq_sum]
  apply Finset.sum_congr rfl
  intro bit _
  have decoded := uninterleave_fst_getLsbD (BitVec.ofFin address) bit.val bit.isLt
  simpa only [BitVec.toFin_ofFin, BitVec.getLsbD, BitVec.toNat_ofFin] using
    congrArg (fun value => if value then (2 : F) ^ bit.val else 0) decoded.symm

/-- The right operand's field polynomial encodes the word obtained by unpacking
even address bits. -/
theorem lookupAddressRight_eq_uninterleave {F : Type} [Field F]
    (address : Fin (2 ^ 128)) :
    lookupAddressRight (F := F) address = ((uninterleave address).2.toNat : F) := by
  rw [bitVec_toNat_cast_eq_sum]
  apply Finset.sum_congr rfl
  intro bit _
  have decoded := uninterleave_snd_getLsbD (BitVec.ofFin address) bit.val bit.isLt
  simpa only [BitVec.toFin_ofFin, BitVec.getLsbD, BitVec.toNat_ofFin] using
    congrArg (fun value => if value then (2 : F) ^ bit.val else 0) decoded.symm

/-- An odd address bit is the corresponding bit of the left operand. -/
theorem interleave_testBit_odd (l r : BitVec 64) (i : Nat) (hi : i < 64) :
    (interleaveLookupOperands l r).toNat.testBit (2 * i + 1) = l.getLsbD i := by
  rw [interleaveLookupOperands_testBit l r (by omega)]
  have h1 : (2 * i + 1) % 2 = 1 := by omega
  have h2 : (2 * i + 1) / 2 = i := by omega
  simp only [h1, h2, ↓reduceIte]

/-- An even address bit is the corresponding bit of the right operand. -/
theorem interleave_testBit_even (l r : BitVec 64) (i : Nat) (hi : i < 64) :
    (interleaveLookupOperands l r).toNat.testBit (2 * i) = r.getLsbD i := by
  rw [interleaveLookupOperands_testBit l r (by omega)]
  have h1 : 2 * i % 2 = 0 := by omega
  have h2 : 2 * i / 2 = i := by omega
  simp only [h1, h2, Nat.zero_ne_one, ↓reduceIte]

end JoltConstraints
