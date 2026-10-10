import Mathlib.Tactic.Ring
import JoltConstraints.lookup_table
import JoltBytecode.JoltISA.Values

/-!
# The shift tables on right-shift bitmasks

Jolt's VIRTUAL_SRL, VIRTUAL_SRA, VIRTUAL_SRLW and VIRTUAL_SRAW tables read their
right operand as a right-shift bitmask: set exactly at bits `s` and above (for the
W tables, at bits `s` to 31). On such a mask each table gives `x` shifted right by
`s`. `ExpansionFacts` shows `ctz` of such a mask is `s`.

Each table loop is rewritten as a `List.foldl`. `srl_foldl` carries the shifted
value through the loop by induction on the number of bits read, and `sign_foldl`
carries the sign-extension bits of the arithmetic shifts.
-/

set_option autoImplicit false

namespace JoltConstraints

/-- Shifting the one-bit word left encodes the corresponding power of two. -/
theorem one_shiftLeft_eq (k : Nat) : 1#64 <<< k = BitVec.ofNat 64 (2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  norm_num

namespace ShiftTables

variable {F : Type} [Field F]

/-- Bit i of x, as the 0/1 word the shift tables read. -/
theorem bit_word (x : BitVec 64) (i : Nat) :
    (x >>> i) &&& 1 = if x.getLsbD i then 1 else 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ushiftRight, ← BitVec.testBit_toNat,
    Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow,
    show (1 : BitVec 64).toNat = 1 from rfl, Nat.and_one_is_mod]
  rcases Nat.mod_two_eq_zero_or_one (x.toNat / 2 ^ i) with bit | bit <;> simp [bit]

/-- The same bit as a number. -/
theorem bit_word_ofNat (x : BitVec 64) (i : Nat) :
    (x >>> i) &&& 1 = BitVec.ofNat 64 (x.toNat / 2 ^ i % 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
    show (1 : BitVec 64).toNat = 1 from rfl, Nat.and_one_is_mod, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide))]

/-- Dropping bits below s from x's low n + 1 bits: bit n lands at n - s. -/
theorem low_bits_succ (x n s : Nat) (sn : s ≤ n) :
    x % 2 ^ (n + 1) / 2 ^ s = x % 2 ^ n / 2 ^ s + 2 ^ (n - s) * (x / 2 ^ n % 2) := by
  have split : 2 ^ n = 2 ^ s * 2 ^ (n - s) := by rw [← Nat.pow_add]; congr 1; omega
  rw [Nat.mod_pow_succ, split, Nat.mul_assoc, Nat.add_mul_div_left _ _ (by positivity)]

/-- Shifting past the retained low bits leaves zero. -/
theorem low_bits_zero (x n s : Nat) (ns : n ≤ s) : x % 2 ^ n / 2 ^ s = 0 :=
  Nat.div_eq_of_lt (lt_of_lt_of_le (Nat.mod_lt _ (by positivity)) (Nat.pow_le_pow_right (by decide) ns))

/-- One pass of the VIRTUAL_SRL loop at bit i. -/
def srlStep (x y : BitVec 64) (entry : BitVec 64) (i : Nat) : BitVec 64 :=
  entry * (1 + ((y >>> i) &&& 1)) + ((x >>> i) &&& 1) * ((y >>> i) &&& 1)

/-- With y set exactly at bits s and above, reading bits n - 1 down to 0 appends x's
bits s .. n - 1 to the entry. -/
theorem srl_foldl (x y : BitVec 64) (s N : Nat)
    (shape : ∀ i < N, y.getLsbD i = decide (s ≤ i)) :
    ∀ n ≤ N, ∀ entry : BitVec 64, (List.range n).reverse.foldl (srlStep x y) entry =
      entry * BitVec.ofNat 64 (2 ^ (n - s)) + BitVec.ofNat 64 (x.toNat % 2 ^ n / 2 ^ s)
  | 0, _, entry => by simp [Nat.mod_one]
  | n + 1, inRange, entry => by
    rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
      List.foldl_cons, srl_foldl x y s N shape n (by omega)]
    unfold srlStep
    rw [bit_word y, bit_word_ofNat x, shape n (by omega)]
    by_cases sn : s ≤ n
    · rw [low_bits_succ _ _ _ sn, show n + 1 - s = n - s + 1 by omega]
      simp only [sn, decide_true, ite_true, BitVec.ofNat_add, BitVec.ofNat_mul, Nat.pow_succ]
      rw [show BitVec.ofNat 64 2 = 2 from rfl]
      ring
    · rw [low_bits_zero _ _ _ (by omega), low_bits_zero _ _ _ (by omega),
        show n + 1 - s = n - s by omega]
      simp only [sn, decide_false, Bool.false_eq_true, ite_false]
      ring

/-- Dividing a word by a power of two gives its logical right shift. -/
theorem shiftRight_ofNat (x : BitVec 64) (s : Nat) :
    BitVec.ofNat 64 (x.toNat / 2 ^ s) = x >>> s := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_le_self _ _) x.isLt)]

/-- The VIRTUAL_SRL table on x and a mask set exactly at bits s and above is x >>> s. -/
theorem srl_entry (address : Fin (2 ^ 128)) (x y : BitVec 64)
    (split : uninterleave address = (x, y)) (s : Nat)
    (shape : ∀ i < 64, y.getLsbD i = decide (s ≤ i)) :
    virtualSRLTableEntry (F := F) address = ((x >>> s).toNat : F) := by
  unfold virtualSRLTableEntry
  simp only [split, Id.run, pure_bind, List.forIn_pure_yield_eq_foldl, bind_pure]
  change ((((List.range 64).reverse.foldl (srlStep x y) 0).toNat : Nat) : F) = _
  rw [srl_foldl x y s 64 shape 64 le_rfl, zero_mul, zero_add, Nat.mod_eq_of_lt x.isLt,
    shiftRight_ofNat]

/-! ## VIRTUAL_SRA -/

/-- A loop whose body always yields is a left fold of its state updates. -/
theorem forIn_eq_foldl {S : Type} (g : S → Nat → S) (f : Nat → S → Id (ForInStep S))
    (hf : ∀ i r, f i r = pure (.yield (g r i))) (l : List Nat) (s : S) :
    forIn l s f = pure (l.foldl g s) := by
  have : f = fun i r => pure (.yield (g r i)) := funext fun i => funext fun r => hf i r
  subst this
  simp

/-- Reading bits n - 1 down to 0 by counting i up and reading bit n - 1 - i. -/
theorem foldl_range_flip {S : Type} (f : S → Nat → S) : ∀ (n : Nat) (s : S),
    (List.range n).foldl (fun r i => f r (n - 1 - i)) s = (List.range n).reverse.foldl f s
  | 0, _ => rfl
  | n + 1, s => by
    have reversed : (List.range (n + 1)).reverse.foldl f s =
        (List.range n).reverse.foldl f (f s n) := by
      rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
        List.foldl_cons]
    rw [reversed, ← foldl_range_flip f n (f s n), List.range_succ_eq_map, List.foldl_cons,
      List.foldl_map]
    have step : (fun r i => f r (n + 1 - 1 - i.succ)) = fun r i => f r (n - 1 - i) := by
      funext r i
      congr 1
      omega
    rw [step, show n + 1 - 1 - 0 = n by omega]

/-- The sign-extension accumulator of VIRTUAL_SRA (top = 63) and VIRTUAL_SRAW (top = 31):
step i reads bit top - i. -/
def signStep (top : Nat) (y : BitVec 64) (extension : BitVec 64) (i : Nat) : BitVec 64 :=
  if i ≠ 0 then extension + (1#64 <<< i) * (1 - ((y >>> (top - i)) &&& 1)) else extension

/-- With y set exactly at bits s and above, steps 0 .. n - 1 add bits max 1 (top + 1 - s)
up to n - 1. -/
theorem sign_foldl (top : Nat) (y : BitVec 64) (s : Nat)
    (shape : ∀ i ≤ top, y.getLsbD i = decide (s ≤ i)) :
    ∀ n ≤ top + 1, ∀ extension : BitVec 64,
      (List.range n).foldl (signStep top y) extension =
        extension + BitVec.ofNat 64 (2 ^ n - 2 ^ (max 1 (top + 1 - s)))
  | 0, _, extension => by
    have : 1 ≤ 2 ^ (max 1 (top + 1 - s)) := Nat.one_le_two_pow
    simp [Nat.sub_eq_zero_of_le this]
  | n + 1, inRange, extension => by
    have powers : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [Nat.pow_succ]; ring
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      sign_foldl top y s shape n (by omega)]
    unfold signStep
    by_cases zero : n = 0
    · subst zero
      have : 2 ≤ 2 ^ (max 1 (top + 1 - s)) := by
        calc 2 = 2 ^ 1 := rfl
          _ ≤ _ := Nat.pow_le_pow_right (by decide) (le_max_left _ _)
      simp only [ne_eq, not_true_eq_false, ite_false, pow_zero]
      rw [Nat.sub_eq_zero_of_le (by omega), Nat.sub_eq_zero_of_le (by omega)]
    · rw [if_pos zero, bit_word y, shape (top - n) (by omega)]
      by_cases high : top + 1 - s ≤ n
      · have below : 2 ^ (max 1 (top + 1 - s)) ≤ 2 ^ n :=
          Nat.pow_le_pow_right (by decide) (by omega)
        rw [show 2 ^ (n + 1) - 2 ^ (max 1 (top + 1 - s)) =
            (2 ^ n - 2 ^ (max 1 (top + 1 - s))) + 2 ^ n by omega]
        simp only [show ¬ s ≤ top - n by omega, decide_false, Bool.false_eq_true, ite_false,
          BitVec.ofNat_add, one_shiftLeft_eq]
        ring
      · have above : 2 ^ (n + 1) ≤ 2 ^ (max 1 (top + 1 - s)) :=
          Nat.pow_le_pow_right (by decide) (by omega)
        rw [Nat.sub_eq_zero_of_le above, Nat.sub_eq_zero_of_le (by omega)]
        simp only [show s ≤ top - n by omega, decide_true, ite_true, sub_self, mul_zero, add_zero]

/-- 2^64 - 2^m is set exactly at bits m .. 63. -/
theorem top_bits (m i : Nat) (mLe : m ≤ 64) :
    (BitVec.ofNat 64 (2 ^ 64 - 2 ^ m)).getLsbD i = (decide (i < 64) && decide (m ≤ i)) := by
  have eq : 2 ^ 64 - 2 ^ m = (2 ^ (64 - m) - 1) <<< m := by
    rw [Nat.shiftLeft_eq, Nat.sub_mul, ← Nat.pow_add, Nat.sub_add_cancel mLe, one_mul]
  rw [BitVec.getLsbD_ofNat, eq, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
  by_cases above : m ≤ i <;> by_cases inside : i < 64
  all_goals simp [above, inside]
  omega

/-- x >>> s with the vacated top bits set to the sign is the arithmetic shift. -/
theorem sra_value (x : BitVec 64) (s : Nat) (sLt : s < 64) :
    x >>> s + (if x.msb then 1 else 0) * BitVec.ofNat 64 (2 ^ 64 - 2 ^ (max 1 (64 - s))) =
      x.sshiftRight s := by
  cases msb : x.msb
  · rw [BitVec.sshiftRight_eq_of_msb_false msb]
    simp
  · simp only [ite_true, one_mul]
    rw [BitVec.add_eq_or_of_and_eq_zero]
    · apply BitVec.eq_of_getLsbD_eq
      intro i iLt
      rw [BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight, top_bits _ _ (by omega),
        BitVec.getLsbD_sshiftRight, msb]
      by_cases inside : s + i < 64
      · simp [inside, iLt, show ¬ max 1 (64 - s) ≤ i by omega]
      · simp [inside, iLt, show max 1 (64 - s) ≤ i by omega]
    · apply BitVec.eq_of_getLsbD_eq
      intro i iLt
      rw [BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight, top_bits _ _ (by omega)]
      by_cases inside : s + i < 64
      · simp [show ¬ max 1 (64 - s) ≤ i by omega]
      · simp [BitVec.getLsbD_of_ge x (s + i) (by omega)]

/-- One pass of the VIRTUAL_SRA loop: step i reads bit 63 - i. -/
def sraStep (x y : BitVec 64) (r : MProd (BitVec 64) (BitVec 64)) (i : Nat) :
    MProd (BitVec 64) (BitVec 64) :=
  ⟨srlStep x y r.fst (63 - i), signStep 63 y r.snd i⟩

/-- The first SRA accumulator follows the logical-shift recurrence. -/
theorem sraStep_fst (x y : BitVec 64) : ∀ (l : List Nat) (r : MProd (BitVec 64) (BitVec 64)),
    (l.foldl (sraStep x y) r).fst = l.foldl (fun entry i => srlStep x y entry (63 - i)) r.fst
  | [], _ => rfl
  | i :: l, r => sraStep_fst x y l (sraStep x y r i)

/-- The second SRA accumulator follows the sign-extension recurrence. -/
theorem sraStep_snd (x y : BitVec 64) : ∀ (l : List Nat) (r : MProd (BitVec 64) (BitVec 64)),
    (l.foldl (sraStep x y) r).snd = l.foldl (signStep 63 y) r.snd
  | [], _ => rfl
  | i :: l, r => sraStep_snd x y l (sraStep x y r i)

/-- The VIRTUAL_SRA table on x and a mask set exactly at bits s and above is
x.sshiftRight s. -/
theorem sra_entry (address : Fin (2 ^ 128)) (x y : BitVec 64)
    (split : uninterleave address = (x, y)) (s : Nat) (sLt : s < 64)
    (shape : ∀ i < 64, y.getLsbD i = decide (s ≤ i)) :
    virtualSRATableEntry (F := F) address = ((x.sshiftRight s).toNat : F) := by
  unfold virtualSRATableEntry
  simp only [split, Id.run, pure_bind]
  rw [forIn_eq_foldl (sraStep x y) _ (by
    intro i r
    by_cases zero : i = 0 <;> simp [sraStep, srlStep, signStep, zero])]
  simp only [pure_bind]
  rw [sraStep_fst, sraStep_snd, foldl_range_flip (srlStep x y) 64 0,
    srl_foldl x y s 64 shape 64 le_rfl,
    sign_foldl 63 y s (fun i iLe => shape i (by omega)) 64 le_rfl,
    zero_mul, zero_add, zero_add, Nat.mod_eq_of_lt x.isLt, shiftRight_ofNat,
    show 63 + 1 - s = 64 - s by omega]
  change (((x >>> s + (if x.msb then 1 else 0) *
    BitVec.ofNat 64 (2 ^ 64 - 2 ^ (max 1 (64 - s)))).toNat : Nat) : F) = _
  rw [sra_value x s sLt]

/-! ## VIRTUAL_SRAW and VIRTUAL_SRLW -/

/-- Bits s and up of x's low word. -/
theorem low_word_bits (x : BitVec 64) (s i : Nat) :
    (BitVec.ofNat 64 (x.toNat % 2 ^ 32 / 2 ^ s)).getLsbD i =
      (decide (i < 64) && (decide (i + s < 32) && x.getLsbD (i + s))) := by
  rw [BitVec.getLsbD_ofNat, Nat.testBit_div_two_pow, Nat.testBit_mod_two_pow,
    BitVec.testBit_toNat]

/-- Bit i of the low word shifted right arithmetically by s, then sign-extended. -/
theorem sraw_bits (x : BitVec 64) (s i : Nat) :
    (((x.setWidth 32).sshiftRight s).signExtend 64).getLsbD i =
      (decide (i < 64) && if i + s < 32 then x.getLsbD (i + s) else x.getLsbD 31) := by
  rw [BitVec.getLsbD_signExtend, BitVec.msb_sshiftRight, BitVec.msb_setWidth]
  by_cases small : i < 32
  · rw [if_pos small, BitVec.getLsbD_sshiftRight, BitVec.msb_setWidth, BitVec.getLsbD_setWidth]
    by_cases inside : i + s < 32
    · simp [inside, Nat.add_comm s i, show ¬ 32 ≤ i by omega]
    · simp [show ¬ s + i < 32 by omega, inside, show ¬ 32 ≤ i by omega]
  · simp [small, show ¬ i + s < 32 by omega]

/-- The low word's bits s and up, with the bits above set to bit 31, is the low word
shifted right arithmetically by s and sign-extended. -/
theorem sraw_value (x : BitVec 64) (s : Nat) (sLt : s < 32) :
    BitVec.ofNat 64 (x.toNat % 2 ^ 32 / 2 ^ s) +
        (if x.getLsbD 31 then 1 else 0) * BitVec.ofNat 64 (2 ^ 64 - 2 ^ (max 1 (32 - s))) =
      ((x.setWidth 32).sshiftRight s).signExtend 64 := by
  cases bit : x.getLsbD 31
  · have bit31 : x[31] = false := by simpa using bit
    simp only [Bool.false_eq_true, ite_false, zero_mul, add_zero]
    apply BitVec.eq_of_getLsbD_eq
    intro i iLt
    rw [low_word_bits, sraw_bits]
    by_cases inside : i + s < 32 <;> simp [inside, iLt, bit31]
  · simp only [ite_true, one_mul]
    rw [BitVec.add_eq_or_of_and_eq_zero]
    · apply BitVec.eq_of_getLsbD_eq
      intro i iLt
      rw [BitVec.getLsbD_or, low_word_bits, top_bits _ _ (by omega), sraw_bits]
      by_cases inside : i + s < 32
      · simp [inside, iLt, show ¬ max 1 (32 - s) ≤ i by omega]
      · simp [inside, iLt, bit, show max 1 (32 - s) ≤ i by omega]
    · apply BitVec.eq_of_getLsbD_eq
      intro i iLt
      rw [BitVec.getLsbD_and, low_word_bits, top_bits _ _ (by omega)]
      by_cases inside : i + s < 32
      · simp [inside, show ¬ max 1 (32 - s) ≤ i by omega]
      · simp [inside]

/-- The concrete upper-word mask sets exactly bits 32 through 63. -/
theorem upper_word_mask :
    ((1#128 <<< 64) - (1#128 <<< 32)).setWidth 64 = BitVec.ofNat 64 (2 ^ 64 - 2 ^ 32) := by
  decide

/-- One pass of the VIRTUAL_SRAW loop: step i reads bit 31 - i. -/
def srawStep (x y : BitVec 64) (r : MProd (BitVec 64) (BitVec 64)) (i : Nat) :
    MProd (BitVec 64) (BitVec 64) :=
  ⟨srlStep x y r.fst (31 - i), signStep 31 y r.snd i⟩

/-- The first SRAW accumulator extracts bits of the low word. -/
theorem srawStep_fst (x y : BitVec 64) : ∀ (l : List Nat) (r : MProd (BitVec 64) (BitVec 64)),
    (l.foldl (srawStep x y) r).fst = l.foldl (fun entry i => srlStep x y entry (31 - i)) r.fst
  | [], _ => rfl
  | i :: l, r => srawStep_fst x y l (srawStep x y r i)

/-- The second SRAW accumulator builds the sign-extension mask. -/
theorem srawStep_snd (x y : BitVec 64) : ∀ (l : List Nat) (r : MProd (BitVec 64) (BitVec 64)),
    (l.foldl (srawStep x y) r).snd = l.foldl (signStep 31 y) r.snd
  | [], _ => rfl
  | i :: l, r => srawStep_snd x y l (srawStep x y r i)

/-- The VIRTUAL_SRAW table on x and a mask whose low word is set exactly at bits s and
above is the low word of x shifted right arithmetically by s, sign-extended. -/
theorem sraw_entry (address : Fin (2 ^ 128)) (x y : BitVec 64)
    (split : uninterleave address = (x, y)) (s : Nat) (sLt : s < 32)
    (shape : ∀ i < 32, y.getLsbD i = decide (s ≤ i)) :
    virtualSRAWTableEntry (F := F) address =
      ((((x.setWidth 32).sshiftRight s).signExtend 64).toNat : F) := by
  unfold virtualSRAWTableEntry
  simp only [split, Id.run, pure_bind]
  rw [forIn_eq_foldl (srawStep x y) _ (by
    intro i r
    by_cases zero : i = 0 <;> simp [srawStep, srlStep, signStep, zero])]
  simp only [pure_bind]
  have upper : 2 ^ (max 1 (32 - s)) ≤ 2 ^ 32 := Nat.pow_le_pow_right (by decide) (by omega)
  rw [srawStep_fst, srawStep_snd, foldl_range_flip (srlStep x y) 32 0,
    srl_foldl x y s 32 shape 32 le_rfl,
    sign_foldl 31 y s (fun i iLe => shape i (by omega)) 32 le_rfl,
    zero_mul, zero_add, show 31 + 1 - s = 32 - s by omega, upper_word_mask, ← BitVec.ofNat_add,
    show 2 ^ 64 - 2 ^ 32 + (2 ^ 32 - 2 ^ (max 1 (32 - s))) = 2 ^ 64 - 2 ^ (max 1 (32 - s)) by
      omega]
  change (((BitVec.ofNat 64 (x.toNat % 2 ^ 32 / 2 ^ s) + (if x.getLsbD 31 then 1 else 0) *
    BitVec.ofNat 64 (2 ^ 64 - 2 ^ (max 1 (32 - s)))).toNat : Nat) : F) = _
  rw [sraw_value x s sLt]

/-- With s = 0 the low word is sign-extended; with s > 0 its shifted top bit is 0. -/
theorem srlw_value (x : BitVec 64) (s : Nat) (sLt : s < 32) :
    BitVec.ofNat 64 (x.toNat % 2 ^ 32 / 2 ^ s) +
        (if x.getLsbD 31 then 1 else 0) * (if s = 0 then 1 else 0) *
          BitVec.ofNat 64 (2 ^ 64 - 2 ^ 32) =
      ((x.setWidth 32) >>> s).signExtend 64 := by
  by_cases zero : s = 0
  · subst zero
    rw [BitVec.ushiftRight_zero, ← BitVec.sshiftRight_zero (x := x.setWidth 32),
      ← sraw_value x 0 (by decide)]
    simp
  · simp only [zero, ite_false, mul_zero, zero_mul, add_zero]
    rw [BitVec.signExtend_eq_setWidth_of_msb_false (by
      rw [BitVec.msb_ushiftRight]
      simp only [Bool.and_eq_false_imp, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not]
      omega)]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_setWidth,
      Nat.shiftRight_eq_div_pow]

/-- One pass of the VIRTUAL_SRLW loop at bit i; the second slot keeps the last mask bit. -/
def srlwStep (x y : BitVec 64) (r : MProd (BitVec 64) (BitVec 64)) (i : Nat) :
    MProd (BitVec 64) (BitVec 64) :=
  ⟨srlStep x y r.fst i, (y >>> i) &&& 1⟩

/-- The first SRLW accumulator follows the logical-shift recurrence. -/
theorem srlwStep_fst (x y : BitVec 64) : ∀ (l : List Nat) (r : MProd (BitVec 64) (BitVec 64)),
    (l.foldl (srlwStep x y) r).fst = l.foldl (srlStep x y) r.fst
  | [], _ => rfl
  | i :: l, r => srlwStep_fst x y l (srlwStep x y r i)

/-- After processing bit zero, the second SRLW accumulator is mask bit zero. -/
theorem srlwStep_snd (x y : BitVec 64) (l : List Nat) (r : MProd (BitVec 64) (BitVec 64)) :
    ((l ++ [0]).foldl (srlwStep x y) r).snd = (y >>> 0) &&& 1 := by
  rw [List.foldl_append]
  rfl

/-- The VIRTUAL_SRLW table on x and a mask whose low word is set exactly at bits s and
above is the low word of x shifted right by s, sign-extended. -/
theorem srlw_entry (address : Fin (2 ^ 128)) (x y : BitVec 64)
    (split : uninterleave address = (x, y)) (s : Nat) (sLt : s < 32)
    (shape : ∀ i < 32, y.getLsbD i = decide (s ≤ i)) :
    virtualSRLWTableEntry (F := F) address =
      ((((x.setWidth 32) >>> s).signExtend 64).toNat : F) := by
  unfold virtualSRLWTableEntry
  simp only [split, Id.run, pure_bind]
  rw [forIn_eq_foldl (srlwStep x y) _ (by intro i r; rfl)]
  simp only [pure_bind]
  have last : (List.range 32).reverse = ((List.range 31).map Nat.succ).reverse ++ [0] := by
    rw [List.range_succ_eq_map, List.reverse_cons]
  rw [srlwStep_fst, srl_foldl x y s 32 shape 32 le_rfl, zero_mul, zero_add, last, srlwStep_snd,
    bit_word y 0, shape 0 (by decide), upper_word_mask]
  change (((BitVec.ofNat 64 (x.toNat % 2 ^ 32 / 2 ^ s) + (if x.getLsbD 31 then 1 else 0) *
    (if decide (s ≤ 0) = true then 1 else 0) * BitVec.ofNat 64 (2 ^ 64 - 2 ^ 32)).toNat : Nat) : F) = _
  simp only [Nat.le_zero, decide_eq_true_eq]
  rw [srlw_value x s sLt]

end ShiftTables

end JoltConstraints
