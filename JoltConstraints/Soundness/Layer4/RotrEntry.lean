import JoltConstraints.Soundness.Layer4.ShiftEntry
import JoltConstraints.Soundness.Layer4.RotateEntry

open LeanRV64D

/-!
# The plain rotate tables on right-shift bitmasks

Jolt's VIRTUAL_ROTR and VIRTUAL_ROTRW tables read their right operand as a right-shift
bitmask, like the shift tables: set exactly at bits `s` and above (for VIRTUAL_ROTRW,
at bits `s` to 31). Inline rows use them through `VirtualROTRI` and `VirtualROTRIW`,
for example in SHA-256's Σ functions and Keccak's ρ step.

At Jolt a6b6dc717:
See : jolt/crates/jolt-lookup-tables/src/tables/virtual_rotr.rs (`VirtualROTRTable::materialize_entry`)
See : jolt/crates/jolt-lookup-tables/src/tables/virtual_rotrw.rs (`VirtualROTRWTable::materialize_entry`)
See : jolt/tracer/src/instruction/virtual_rotri.rs (`VirtualROTRI::exec`)
See : jolt/tracer/src/instruction/virtual_rotriw.rs (`VirtualROTRIW::exec`)

Each loop keeps three accumulators. `firstSum` follows the VIRTUAL_SRL recurrence and
ends as `x >>> s`. `prodOnePlusY` doubles at every set mask bit, so at a clear bit
`i < s` it is `2^(n - s)`, and `secondSum` collects `x`'s bits below `s`, moved up by
`n - s`. The sum is `x` rotated right by `s` within `n = 64` (or 32) bits.
-/

set_option autoImplicit false

namespace JoltConstraints

namespace ShiftTables

open Sail LeanRV64D.Functions

variable {F : Type} [Field F]

/-- Sail's right rotation by `s ≤ n` as a number: the bits from `s` up move down, and
the bits below `s` move to the top. For example, rotating the 4-bit word `0b0011`
right by 1 gives `0b0001 + 2^3 * 0b1 = 0b1001`. -/
theorem rotater_toNat {n : Nat} (z : BitVec n) (s : Nat) (sLe : s ≤ n) :
    (rotater z s).toNat = z.toNat / 2 ^ s + 2 ^ (n - s) * (z.toNat % 2 ^ s) := by
  have disjoint : (z >>> s) &&& (z <<< (n - s)) = 0#n := by
    ext i below
    simp only [BitVec.getElem_and, BitVec.getElem_ushiftRight, BitVec.getElem_shiftLeft,
      BitVec.getElem_zero]
    by_cases low : i < n - s
    · simp [low]
    · rw [BitVec.getLsbD_of_ge z (s + i) (by omega)]
      simp
  have split : 2 ^ s * 2 ^ (n - s) = 2 ^ n := by rw [← Nat.pow_add]; congr 1; omega
  have wrapped : z.toNat * 2 ^ (n - s) % 2 ^ n = 2 ^ (n - s) * (z.toNat % 2 ^ s) := by
    conv => lhs; rw [← Nat.mod_add_div z.toNat (2 ^ s)]
    rw [Nat.add_mul, Nat.mul_assoc, Nat.mul_left_comm (2 ^ s), split,
      Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt, Nat.mul_comm]
    rw [← split]
    exact Nat.mul_lt_mul_of_pos_right (Nat.mod_lt _ (by positivity)) (by positivity)
  rw [rotater_eq z s sLe, ← BitVec.add_eq_or_of_and_eq_zero _ _ disjoint, BitVec.toNat_add,
    BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, Nat.shiftRight_eq_div_pow,
    Nat.shiftLeft_eq, wrapped, Nat.mod_eq_of_lt]
  have high : z.toNat / 2 ^ s < 2 ^ (n - s) :=
    Nat.div_lt_of_lt_mul (by rw [split]; exact z.isLt)
  have low : z.toNat % 2 ^ s + 1 ≤ 2 ^ s := Nat.mod_lt _ (by positivity)
  rw [← split]
  nlinarith [Nat.mul_le_mul_left (2 ^ (n - s)) low]

/-- One pass of a plain rotate loop at bit i, with a product accumulator of width w:
the product, the shifted value and the wrapped-around low bits. For example, at a
clear mask bit the product is unchanged and bit i of x is added at the product's
position. -/
def rotrStep (w : Nat) (x y : BitVec 64) (r : BitVec w × BitVec 64 × BitVec 64) (i : Nat) :
    BitVec w × BitVec 64 × BitVec 64 :=
  ⟨r.1 * (1 + ((y >>> i) &&& 1).setWidth w), srlStep x y r.2.1 i,
    r.2.2 + ((x >>> i) &&& 1) * ((1 - ((y >>> i) &&& 1).setWidth w) * r.1).setWidth 64 *
      (1#64 <<< i)⟩

/-- The shifted-value accumulator follows the VIRTUAL_SRL recurrence. For example, on
the empty list both sides are the starting value. -/
theorem rotrStep_first (w : Nat) (x y : BitVec 64) :
    ∀ (l : List Nat) (r : BitVec w × BitVec 64 × BitVec 64),
      (l.foldl (rotrStep w x y) r).2.1 = l.foldl (srlStep x y) r.2.1
  | [], _ => rfl
  | i :: l, r => rotrStep_first w x y l (rotrStep w x y r i)

/-- The 0/1 word of a bit keeps its value at any width. -/
private theorem bit_setWidth (w : Nat) (b : Bool) :
    (if b then (1 : BitVec 64) else 0).setWidth w = if b then 1 else 0 := by
  apply BitVec.eq_of_toNat_eq
  cases b
  · simp
  · change (BitVec.setWidth w (BitVec.ofNat 64 1)).toNat = (BitVec.ofNat w 1).toNat
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show 1 < 2 ^ 64 by decide)]

/-- The zero word stays zero at any width. -/
private theorem zero_setWidth (w v : Nat) : (0 : BitVec w).setWidth v = 0 := by
  apply BitVec.eq_of_toNat_eq
  simp

/-- With y set exactly at bits s and above, reading bits n - 1 down to 0 multiplies the
product by `2^(n - s)` and adds x's bits below `min s n`, moved up by the final product.
For example, with `n = 0` nothing changes. -/
theorem rotr_foldl (w : Nat) (x y : BitVec 64) (s N : Nat)
    (shape : ∀ i < N, y.getLsbD i = decide (s ≤ i)) :
    ∀ n ≤ N, ∀ r : BitVec w × BitVec 64 × BitVec 64,
      ((List.range n).reverse.foldl (rotrStep w x y) r).1 =
          r.1 * BitVec.ofNat w (2 ^ (n - s)) ∧
        ((List.range n).reverse.foldl (rotrStep w x y) r).2.2 =
          r.2.2 + (r.1 * BitVec.ofNat w (2 ^ (n - s))).setWidth 64 *
            BitVec.ofNat 64 (x.toNat % 2 ^ min s n)
  | 0, _, r => by
    refine ⟨?_, ?_⟩
    · change r.1 = r.1 * BitVec.ofNat w (2 ^ (0 - s))
      rw [Nat.zero_sub, pow_zero, show BitVec.ofNat w 1 = 1 from rfl, mul_one]
    · change r.2.2 = r.2.2 + _ * BitVec.ofNat 64 (x.toNat % 2 ^ min s 0)
      rw [Nat.min_zero, pow_zero, Nat.mod_one, show BitVec.ofNat 64 0 = 0 from rfl, mul_zero,
        add_zero]
  | n + 1, inRange, r => by
    rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
      List.foldl_cons]
    obtain ⟨product, sum⟩ := rotr_foldl w x y s N shape n (by omega) (rotrStep w x y r n)
    rw [product, sum]
    simp only [rotrStep, bit_word y, bit_word_ofNat x, shape n (by omega), bit_setWidth]
    by_cases sn : s ≤ n
    · simp only [sn, decide_true, ite_true, sub_self, zero_mul, zero_setWidth, mul_zero,
        add_zero,
        show min s (n + 1) = min s n by omega, show n + 1 - s = n - s + 1 by omega,
        Nat.pow_succ, BitVec.ofNat_mul, show BitVec.ofNat w 2 = 2 from rfl]
      constructor
      · ring
      · rw [show r.1 * (1 + 1) * BitVec.ofNat w (2 ^ (n - s)) =
          r.1 * (BitVec.ofNat w (2 ^ (n - s)) * 2) by ring]
    · simp only [sn, decide_false, Bool.false_eq_true, ite_false, add_zero, mul_one, one_mul,
        sub_zero, show n - s = 0 by omega, show n + 1 - s = 0 by omega, pow_zero,
        show min s (n + 1) = n + 1 by omega, show min s n = n by omega,
        show BitVec.ofNat w 1 = 1 from rfl]
      refine ⟨trivial, ?_⟩
      rw [Nat.mod_pow_succ, BitVec.ofNat_add, BitVec.ofNat_mul, one_shiftLeft_eq]
      ring

/-- The VIRTUAL_ROTR sum is the right rotation. For example, with `s = 0` the second
summand is zero and the first is x. -/
theorem rotr_value (x : BitVec 64) (s : Nat) (sLt : s < 64) :
    x >>> s + BitVec.ofNat 64 (2 ^ (64 - s)) * BitVec.ofNat 64 (x.toNat % 2 ^ s) =
      rotater x s := by
  apply BitVec.eq_of_toNat_eq
  rw [← shiftRight_ofNat, ← BitVec.ofNat_mul, ← BitVec.ofNat_add, BitVec.toNat_ofNat,
    rotater_toNat x s sLt.le]
  apply Nat.mod_eq_of_lt
  rw [← rotater_toNat x s sLt.le]
  exact (rotater x s).isLt

/-- The VIRTUAL_ROTRW sum is the right rotation of the low word, zero-extended. For
example, with `s = 0` it is the low word of x. -/
theorem rotrw_value (x : BitVec 64) (s : Nat) (sLt : s < 32) :
    BitVec.ofNat 64 (x.toNat % 2 ^ 32 / 2 ^ s) +
        BitVec.ofNat 64 (2 ^ (32 - s)) * BitVec.ofNat 64 (x.toNat % 2 ^ s) =
      (rotater (x.setWidth 32) s).setWidth 64 := by
  apply BitVec.eq_of_toNat_eq
  have lowLow : x.toNat % 2 ^ 32 % 2 ^ s = x.toNat % 2 ^ s :=
    Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 sLt.le)
  rw [← BitVec.ofNat_mul, ← BitVec.ofNat_add, BitVec.toNat_ofNat, BitVec.toNat_setWidth,
    rotater_toNat _ s sLt.le, BitVec.toNat_setWidth, lowLow]

/-- The VIRTUAL_ROTR table on x and a mask set exactly at bits s and above is x rotated
right by s. For example, the all-ones mask (s = 0) gives x. -/
theorem rotr_entry (address : Fin (2 ^ 128)) (x y : BitVec 64)
    (split : uninterleave address = (x, y)) (s : Nat) (sLt : s < 64)
    (shape : ∀ i < 64, y.getLsbD i = decide (s ≤ i)) :
    virtualROTRTableEntry (F := F) address = ((rotater x s).toNat : F) := by
  unfold virtualROTRTableEntry
  simp only [split, Id.run]
  rw [forIn_eq_foldl (rotrStep 128 x y) _ (by intro i r; rfl)]
  simp only [pure_bind]
  rw [(rotr_foldl 128 x y s 64 shape 64 le_rfl ⟨1, 0, 0⟩).2, rotrStep_first,
    srl_foldl x y s 64 shape 64 le_rfl]
  simp only [zero_mul, zero_add, one_mul, Nat.mod_eq_of_lt x.isLt, shiftRight_ofNat,
    BitVec.setWidth_ofNat_of_le (show 64 ≤ 128 by decide), Nat.min_eq_left sLt.le]
  change (((x >>> s + BitVec.ofNat 64 (2 ^ (64 - s)) *
    BitVec.ofNat 64 (x.toNat % 2 ^ s)).toNat : Nat) : F) = _
  rw [rotr_value x s sLt]

/-- The VIRTUAL_ROTRW table on x and a mask whose low word is set exactly at bits s and
above is the low word of x rotated right by s, zero-extended. For example, the mask
with low word all ones (s = 0) gives the low word of x. -/
theorem rotrw_entry (address : Fin (2 ^ 128)) (x y : BitVec 64)
    (split : uninterleave address = (x, y)) (s : Nat) (sLt : s < 32)
    (shape : ∀ i < 32, y.getLsbD i = decide (s ≤ i)) :
    virtualROTRWTableEntry (F := F) address =
      (((rotater (x.setWidth 32) s).setWidth 64).toNat : F) := by
  unfold virtualROTRWTableEntry
  simp only [split, Id.run]
  rw [show (List.range 64).reverse.drop 32 = (List.range 32).reverse from rfl,
    forIn_eq_foldl (rotrStep 64 x y) _ (by
      intro i r
      simp only [rotrStep, srlStep, BitVec.setWidth_eq, mul_assoc])]
  simp only [pure_bind]
  rw [(rotr_foldl 64 x y s 32 shape 32 le_rfl ⟨1, 0, 0⟩).2, rotrStep_first,
    srl_foldl x y s 32 shape 32 le_rfl]
  simp only [zero_mul, zero_add, one_mul, BitVec.setWidth_eq, Nat.min_eq_left sLt.le]
  change (((BitVec.ofNat 64 (x.toNat % 2 ^ 32 / 2 ^ s) + BitVec.ofNat 64 (2 ^ (32 - s)) *
    BitVec.ofNat 64 (x.toNat % 2 ^ s)).toNat : Nat) : F) = _
  rw [rotrw_value x s sLt]

/-- The word rotate's value is the low word rotated right by the mask's shift, then
zero-extended. For example, with mask `wordShiftMask 0` it is the low word of x. -/
theorem rotriw_value_eq (x : BitVec 64) (mask : Nat) (shiftLt : ctz mask < 32) :
    jolt_virtual_rotriw_value x mask = (rotater (x.setWidth 32) (ctz mask)).setWidth 64 := by
  apply BitVec.eq_of_toNat_eq
  rw [jolt_virtual_rotriw_value, Nat.min_eq_left shiftLt.le]
  change ((rotater (BitVec.extractLsb 31 0 x) (ctz mask)).setWidth 64).toNat = _
  have low : (BitVec.extractLsb 31 0 x).toNat = (x.setWidth 32).toNat := by
    simp [BitVec.toNat_setWidth]
  rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth, rotater_toNat _ _ (by omega),
    rotater_toNat _ _ (by omega), low]

end ShiftTables

end JoltConstraints
