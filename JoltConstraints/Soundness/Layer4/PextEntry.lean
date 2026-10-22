import Mathlib.Tactic.Ring
import JoltConstraints.lookup_table
import JoltBytecode.JoltISA.Values

/-!
# PEXT table identities for arbitrary operand words

`pext_eq_jolt_virtual_pext_value` shows that the table's `pext` (a contiguous
fast path plus a 64-pass clear-lowest-set-bit loop) equals
`jolt_virtual_pext_value`, the fuel recursion `jolt_pext_nat 64` used by the
instruction semantics. `pextSigned_eq_jolt_virtual_pext_signed_value` adds the sign
extension: `windowSignBit` reads the source bit at the mask's highest set bit,
which `jolt_pext_nat_testBit_top` shows is bit `popcount - 1` of the extracted
value, and adding `2^64 - 2^popcount` to a value below `2^popcount` is the same
as or-ing in the high ones.

The loop is handled by rewriting its `forIn` as a `List.foldl` of `pextStep`
and carrying `PextInv`: after `n` passes the extracted prefix `out` and the
remaining mask `bits` satisfy
`jolt_pext_nat 64 x y = out + 2^k * jolt_pext_nat 64 x bits`, and the low `n`
bits of `bits` are clear, so `bits = 0` after 64 passes.
-/

set_option autoImplicit false

namespace JoltConstraints

/-- Peel the lowest set bit `p` of the mask `2^p * (2q+1)`. -/
theorem jolt_pext_nat_peel (p : Nat) : ∀ (fuel x q : Nat), p < fuel →
    jolt_pext_nat fuel x (2 ^ p * (2 * q + 1)) =
      x / 2 ^ p % 2 + 2 * jolt_pext_nat fuel x (2 ^ (p + 1) * q) := by
  induction p with
  | zero =>
    intro fuel x q hp
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    rw [jolt_pext_nat, jolt_pext_nat]
    simp only [zero_add, pow_zero, pow_one, one_mul, Nat.div_one]
    rw [if_pos (by omega), if_neg (by omega)]
    rw [(show (2 * q + 1) / 2 = q by omega), (show 2 * q / 2 = q by omega)]
  | succ p ih =>
    intro fuel x q hp
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    rw [jolt_pext_nat, jolt_pext_nat]
    have e1 : 2 ^ (p + 1) * (2 * q + 1) = 2 * (2 ^ p * (2 * q + 1)) := by ring
    have e2 : 2 ^ (p + 1 + 1) * q = 2 * (2 ^ (p + 1) * q) := by ring
    rw [e1, e2, if_neg (by omega), if_neg (by omega),
      Nat.mul_div_cancel_left _ (by decide), Nat.mul_div_cancel_left _ (by decide),
      ih f (x / 2) q (by omega), Nat.div_div_eq_div_mul, pow_succ, mul_comm (2 ^ p) 2]

/-- An empty mask extracts zero bits and returns zero. -/
theorem jolt_pext_nat_zero (fuel x : Nat) : jolt_pext_nat fuel x 0 = 0 := by
  induction fuel generalizing x with
  | zero => rfl
  | succ fuel ih => rw [jolt_pext_nat, if_neg (by decide), Nat.zero_div, ih]

/-- A low-ones mask (`n &&& (n+1) = 0`) extracts by masking. -/
theorem jolt_pext_nat_of_low_ones : ∀ (fuel x n : Nat), n < 2 ^ fuel → n &&& (n + 1) = 0 →
    jolt_pext_nat fuel x n = x &&& n := by
  intro fuel
  induction fuel with
  | zero => intro x n hn _; simp at hn; subst hn; simp [jolt_pext_nat]
  | succ f ih =>
    intro x n hn hlow
    rw [jolt_pext_nat]
    split_ifs with hodd
    · have hm : (n / 2) &&& (n / 2 + 1) = 0 := by
        have := congrArg (· / 2) hlow
        simp only [Nat.and_div_two, Nat.zero_div] at this
        rwa [show (n + 1) / 2 = n / 2 + 1 by omega] at this
      rw [ih (x / 2) (n / 2) (by rw [pow_succ] at hn; omega) hm]
      apply Nat.eq_of_testBit_eq
      intro i
      cases i with
      | zero => simp [Nat.testBit_zero, hodd]
      | succ i =>
        have hd : (x % 2 + 2 * (x / 2 &&& n / 2)) / 2 = x / 2 &&& n / 2 := by omega
        simp only [Nat.testBit_succ, hd, Nat.and_div_two]
    · have hn0 : n = 0 := by
        by_contra hne
        have h2 : (n &&& (n + 1)) % 2 = 0 := by simp [hlow]
        have hb : n &&& (n + 1) = n := by
          apply Nat.eq_of_testBit_eq; intro i
          cases i with
          | zero => simp [Nat.testBit_zero]; omega
          | succ i =>
            have hd : (n + 1) / 2 = n / 2 := by omega
            simp only [Nat.testBit_succ, Nat.and_div_two, hd, Nat.and_self]
        omega
      subst hn0
      simp [jolt_pext_nat_zero]


/-- One pass of the table's general `pext` loop on the state (bits, k, out). -/
private def pextStep (x : BitVec 64) (r : MProd (BitVec 64) (MProd Nat (BitVec 64))) :
    MProd (BitVec 64) (MProd Nat (BitVec 64)) :=
  if r.fst = 0 then r
  else ⟨r.fst &&& r.fst - 1, r.snd.fst + 1,
    r.snd.snd ||| ((x >>> r.fst.ctz.toNat) &&& 1) <<< r.snd.fst⟩

private theorem forIn_eq_foldl_of {S : Type} (g : S → S) (f : Nat → S → Id (ForInStep S))
    (hf : ∀ a r, f a r = pure (.yield (g r))) (l : List Nat) (s : S) :
    forIn l s f = pure (l.foldl (fun r _ => g r) s) := by
  have : f = fun _ r => pure (.yield (g r)) := funext fun a => funext fun r => hf a r
  subst this
  simp

private theorem pext_general (x y : BitVec 64) (hy : y ≠ 0)
    (hc : ¬ (y >>> y.ctz.toNat) &&& ((y >>> y.ctz.toNat) + 1) = 0) :
    pext x y = ((List.range 64).foldl (fun r _ => pextStep x r) ⟨y, 0, 0⟩).snd.snd := by
  unfold pext
  simp only [Id.run, hy, if_false, hc, pure_bind]
  rw [forIn_eq_foldl_of (pextStep x)]
  · simp only [pure_bind]
    generalize List.foldl _ _ _ = r
    rfl
  · rintro _ ⟨b, k, o⟩
    by_cases h0 : b = 0
    · subst h0; simp [pextStep]
    · simp only [pextStep]; rw [if_neg h0, if_pos h0]

private theorem two_pow_mul_odd_and_pred (p q : Nat) :
    (2 ^ p * (2 * q + 1)) &&& (2 ^ p * (2 * q + 1) - 1) = 2 ^ (p + 1) * q := by
  have hp : 0 < 2 ^ p := Nat.two_pow_pos p
  have ha : 2 ^ p * (2 * q + 1) = 2 ^ (p + 1) * q + 2 ^ p := by rw [pow_succ]; ring
  have hb : 2 ^ p * (2 * q + 1) - 1 = 2 ^ (p + 1) * q + (2 ^ p - 1) := by rw [ha]; omega
  have h1 : 2 ^ p < 2 ^ (p + 1) := Nat.pow_lt_pow_right (by decide) (by omega)
  rw [hb, ha]
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and, Nat.testBit_two_pow_mul_add _ h1, Nat.testBit_two_pow_mul_add _ (by omega),
    Nat.testBit_two_pow_mul]
  by_cases hj : j < p + 1
  · simp only [hj, if_true, Nat.testBit_two_pow, Nat.testBit_two_pow_sub_one]
    have h3 : ¬ (p + 1 ≤ j) := by omega
    by_cases hjp : p = j
    · subst hjp; simp
    · simp [hjp, ge_iff_le, h3]
  · simp only [hj, if_false, Bool.and_self]
    simp; omega

private theorem eq_two_pow_mul_odd (m p : Nat) (hlow : m % 2 ^ p = 0) (hbit : m.testBit p = true) :
    m = 2 ^ p * (2 * (m / 2 ^ p / 2) + 1) := by
  have h1 : (m / 2 ^ p) % 2 = 1 := by
    have := Nat.testBit_div_two_pow (n := p) m 0
    rw [zero_add, hbit, Nat.testBit_zero] at this
    simpa using this
  have h2 : 2 * (m / 2 ^ p / 2) + 1 = m / 2 ^ p := by omega
  rw [h2, Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hlow)]


/-- Loop invariant after `n` passes from `⟨y, 0, 0⟩`. -/
private def PextInv (x y : BitVec 64) (n : Nat)
    (r : MProd (BitVec 64) (MProd Nat (BitVec 64))) : Prop :=
  jolt_pext_nat 64 x.toNat y.toNat =
      r.snd.snd.toNat + 2 ^ r.snd.fst * jolt_pext_nat 64 x.toNat r.fst.toNat ∧
    r.snd.snd.toNat < 2 ^ r.snd.fst ∧ r.snd.fst ≤ n ∧ 2 ^ n ∣ r.fst.toNat

private theorem toNat_sub_one_of_ne_zero {b : BitVec 64} (hb : b ≠ 0) :
    (b - 1).toNat = b.toNat - 1 := by
  have : b.toNat ≠ 0 := fun h => hb (BitVec.eq_of_toNat_eq (by simpa using h))
  rw [BitVec.toNat_sub]; simp; omega

private theorem pextInv_step (x y : BitVec 64) (n : Nat)
    (r : MProd (BitVec 64) (MProd Nat (BitVec 64)))
    (h : PextInv x y n r) : PextInv x y (n + 1) (pextStep x r) := by
  obtain ⟨b, k, o⟩ := r
  obtain ⟨hJ, ho, hk, hd⟩ := h
  simp only at hJ ho hk hd
  by_cases hb : b = 0
  · subst hb
    simp only [pextStep, if_true]
    exact ⟨hJ, ho, show k ≤ n + 1 by omega, by simp⟩
  · simp only [pextStep, if_neg hb]
    generalize hp : b.ctz.toNat = p
    have hlow : b.toNat % 2 ^ p = 0 := by
      apply Nat.eq_of_testBit_eq; intro i
      rw [Nat.testBit_mod_two_pow, Nat.zero_testBit]
      by_cases hi : i < p
      · rw [BitVec.testBit_toNat, BitVec.getLsbD_false_of_lt_ctz (by omega)]; simp
      · simp [hi]
    have hbit : b.toNat.testBit p = true := by
      rw [BitVec.testBit_toNat, ← hp]; exact BitVec.getLsbD_true_ctz_of_ne_zero hb
    have hp64 : p < 64 := by
      by_contra hc
      have := Nat.testBit_lt_two_pow
        (lt_of_lt_of_le b.isLt (Nat.pow_le_pow_right (by decide) (by omega : 64 ≤ p)))
      rw [hbit] at this; exact absurd this (by decide)
    have hnp : n ≤ p := by
      by_contra hc
      obtain ⟨c, hc'⟩ := hd
      have : b.toNat.testBit p = false := by
        rw [hc', Nat.testBit_two_pow_mul]; simp; omega
      rw [hbit] at this; exact absurd this (by decide)
    obtain ⟨q, hq⟩ : ∃ q, b.toNat = 2 ^ p * (2 * q + 1) := ⟨_, eq_two_pow_mul_odd _ _ hlow hbit⟩
    have hbits : (b &&& (b - 1)).toNat = 2 ^ (p + 1) * q := by
      rw [BitVec.toNat_and, toNat_sub_one_of_ne_zero hb, hq, two_pow_mul_odd_and_pred]
    have hc : ((x >>> p) &&& 1).toNat = x.toNat / 2 ^ p % 2 := by
      simp [BitVec.toNat_and, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    have hc1 : x.toNat / 2 ^ p % 2 ≤ 1 := by omega
    have hk64 : 2 ^ k ≤ 2 ^ 63 := Nat.pow_le_pow_right (by decide) (by omega)
    have hsh : (((x >>> p) &&& 1) <<< k).toNat = 2 ^ k * (x.toNat / 2 ^ p % 2) := by
      rw [BitVec.toNat_shiftLeft, hc, Nat.shiftLeft_eq, Nat.mul_comm]
      apply Nat.mod_eq_of_lt
      have := Nat.mul_le_mul hk64 hc1
      omega
    have hor : (o ||| ((x >>> p) &&& 1) <<< k).toNat = o.toNat + 2 ^ k * (x.toNat / 2 ^ p % 2) := by
      rw [BitVec.toNat_or, hsh, Nat.or_comm, ← Nat.two_pow_add_eq_or_of_lt ho]; ring
    refine ⟨?_, ?_, by simp only; omega, ?_⟩
    · simp only [hbits, hor]
      rw [hJ, hq, jolt_pext_nat_peel p 64 _ q hp64, pow_succ]; ring
    · simp only [hor]
      have := Nat.mul_le_mul_left (2 ^ k) hc1
      rw [pow_succ]; omega
    · simp only [hbits]
      exact Dvd.dvd.mul_right (Nat.pow_dvd_pow 2 (by omega)) q

private theorem pextInv_foldl (x y : BitVec 64) :
    ∀ (l : List Nat) (n : Nat) (r : MProd (BitVec 64) (MProd Nat (BitVec 64))),
    PextInv x y n r → PextInv x y (n + l.length) (l.foldl (fun r _ => pextStep x r) r)
  | [], n, r, h => by simpa using h
  | _ :: l, n, r, h => by
    simp only [List.foldl_cons, List.length_cons]
    have := pextInv_foldl x y l (n + 1) _ (pextInv_step x y n r h)
    rwa [show n + 1 + l.length = n + (l.length + 1) by omega] at this

private theorem pext_eq_of_general (x y : BitVec 64) (hy : y ≠ 0)
    (hc : ¬ (y >>> y.ctz.toNat) &&& ((y >>> y.ctz.toNat) + 1) = 0) :
    pext x y = jolt_virtual_pext_value x y := by
  rw [pext_general x y hy hc]
  have h := pextInv_foldl x y (List.range 64) 0 ⟨y, 0, 0⟩ ⟨by simp, by simp, le_refl _, by simp⟩
  generalize (List.range 64).foldl _ _ = r at h ⊢
  obtain ⟨b, k, o⟩ := r
  obtain ⟨hJ, -, -, hd⟩ := h
  simp only [List.length_range, zero_add] at hd hJ
  have hb0 : b.toNat = 0 := Nat.eq_zero_of_dvd_of_lt hd b.isLt
  rw [hb0, jolt_pext_nat_zero, mul_zero, add_zero] at hJ
  apply BitVec.eq_of_toNat_eq
  simp only [jolt_virtual_pext_value, BitVec.toNat_ofNat, hJ]
  exact (Nat.mod_eq_of_lt o.isLt).symm


/-- Dropping trailing zero mask bits shifts the source and reduces the recursion fuel. -/
theorem jolt_pext_nat_two_pow_mul (f X : Nat) : ∀ (t m : Nat),
    jolt_pext_nat (f + t) X (2 ^ t * m) = jolt_pext_nat f (X / 2 ^ t) m := by
  intro t
  induction t generalizing X with
  | zero => intro m; simp
  | succ t ih =>
    intro m
    rw [show f + (t + 1) = (f + t) + 1 by omega, jolt_pext_nat,
      show 2 ^ (t + 1) * m = 2 * (2 ^ t * m) by rw [pow_succ]; ring,
      if_neg (by omega), Nat.mul_div_cancel_left _ (by decide), ih,
      Nat.div_div_eq_div_mul, pow_succ, mul_comm (2 ^ t) 2]

private theorem toNat_mod_two_pow_ctz (b : BitVec 64) : b.toNat % 2 ^ b.ctz.toNat = 0 := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_mod_two_pow, Nat.zero_testBit]
  by_cases hi : i < b.ctz.toNat
  · rw [BitVec.testBit_toNat, BitVec.getLsbD_false_of_lt_ctz hi]; simp
  · simp [hi]

private theorem ctz_toNat_lt (b : BitVec 64) (hb : b ≠ 0) : b.ctz.toNat < 64 := by
  by_contra hc
  have := Nat.testBit_lt_two_pow
    (lt_of_lt_of_le b.isLt (Nat.pow_le_pow_right (by decide) (by omega : 64 ≤ b.ctz.toNat)))
  rw [BitVec.testBit_toNat, BitVec.getLsbD_true_ctz_of_ne_zero hb] at this
  exact absurd this (by decide)

private theorem pext_eq_of_contiguous (x y : BitVec 64) (hy : y ≠ 0)
    (hc : (y >>> y.ctz.toNat) &&& ((y >>> y.ctz.toNat) + 1) = 0) :
    pext x y = jolt_virtual_pext_value x y := by
  have hpx : pext x y = (x >>> y.ctz.toNat) &&& (y >>> y.ctz.toNat) := by
    unfold pext
    simp only [Id.run, hy, if_false, hc, if_true, pure_bind]
    rfl
  rw [hpx]
  generalize ht : y.ctz.toNat = t at hc
  have ht64 : t < 64 := ht ▸ ctz_toNat_lt y hy
  have hlow : y.toNat % 2 ^ t = 0 := ht ▸ toNat_mod_two_pow_ctz y
  have hy' : y.toNat = 2 ^ t * (y.toNat / 2 ^ t) :=
    (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hlow)).symm
  have hN : y.toNat / 2 ^ t < 2 ^ (64 - t) := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos t), ← pow_add, show 64 - t + t = 64 by omega]
    exact y.isLt
  have hNlow : (y.toNat / 2 ^ t) &&& (y.toNat / 2 ^ t + 1) = 0 := by
    have h := congrArg BitVec.toNat hc
    simp only [BitVec.toNat_and, BitVec.toNat_add, BitVec.toNat_ushiftRight,
      Nat.shiftRight_eq_div_pow] at h
    rw [show (1 : BitVec 64).toNat = 1 from rfl, show (0 : BitVec 64).toNat = 0 from rfl] at h
    by_cases hw : y.toNat / 2 ^ t + 1 < 2 ^ 64
    · rwa [Nat.mod_eq_of_lt hw] at h
    · have he : y.toNat / 2 ^ t = 2 ^ 64 - 1 := by
        have : y.toNat / 2 ^ t ≤ y.toNat := Nat.div_le_self _ _
        have := y.isLt; omega
      rw [he, show 2 ^ 64 - 1 + 1 = 2 ^ 64 by rfl]
      apply Nat.eq_of_testBit_eq; intro i
      simp only [Nat.testBit_and, Nat.testBit_two_pow_sub_one, Nat.testBit_two_pow,
        Nat.zero_testBit]
      by_cases hi : i < 64 <;> simp [hi]; omega
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
    jolt_virtual_pext_value, BitVec.toNat_ofNat]
  have hs : jolt_pext_nat 64 x.toNat (2 ^ t * (y.toNat / 2 ^ t)) =
      jolt_pext_nat (64 - t) (x.toNat / 2 ^ t) (y.toNat / 2 ^ t) := by
    have := jolt_pext_nat_two_pow_mul (64 - t) x.toNat t (y.toNat / 2 ^ t)
    rwa [show 64 - t + t = 64 by omega] at this
  rw [hy', hs, Nat.mul_div_cancel_left _ (Nat.two_pow_pos t),
    jolt_pext_nat_of_low_ones _ _ _ hN hNlow]
  have : y.toNat / 2 ^ t < 2 ^ 64 := lt_of_le_of_lt (Nat.div_le_self _ _) y.isLt
  exact (Nat.mod_eq_of_lt (lt_of_le_of_lt Nat.and_le_right this)).symm

/-- The PEXT table's `pext` equals the instruction value for arbitrary words. -/
theorem pext_eq_jolt_virtual_pext_value (x y : BitVec 64) :
    pext x y = jolt_virtual_pext_value x y := by
  by_cases hy : y = 0
  · subst hy
    unfold pext
    simp [Id.run, jolt_virtual_pext_value, jolt_pext_nat_zero]
    rfl
  by_cases hc : (y >>> y.ctz.toNat) &&& ((y >>> y.ctz.toNat) + 1) = 0
  · exact pext_eq_of_contiguous x y hy hc
  · exact pext_eq_of_general x y hy hc


/-! ## PextSigned -/

/-- The recursive population count is the sum of the inspected bits. -/
theorem jolt_popcount_nat_eq_sum : ∀ (f m : Nat),
    jolt_popcount_nat f m = ∑ i ∈ Finset.range f, (m.testBit i).toNat := by
  intro f
  induction f with
  | zero => intro m; rfl
  | succ f ih =>
    intro m
    rw [jolt_popcount_nat, ih, Finset.sum_range_succ']
    simp only [Nat.testBit_succ, Nat.testBit_zero]
    rw [add_comm]; congr 1
    by_cases h : m % 2 = 1 <;> simp [h]; omega

private theorem cpopNatRec_eq_sum (b : BitVec 64) : ∀ n : Nat,
    b.cpopNatRec n 0 = ∑ i ∈ Finset.range n, (b.getLsbD i).toNat := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih => rw [BitVec.cpopNatRec_succ, BitVec.cpopNatRec_eq, ih, Finset.sum_range_succ]; simp

private theorem cpop_toNat_eq (y : BitVec 64) : y.cpop.toNat = jolt_popcount_nat 64 y.toNat := by
  rw [BitVec.toNat_cpop, cpopNatRec_eq_sum, jolt_popcount_nat_eq_sum]
  rfl

/-- The population count is at most the number of inspected bits. -/
theorem jolt_popcount_nat_le : ∀ (f m : Nat), jolt_popcount_nat f m ≤ f := by
  intro f; induction f with
  | zero => intro m; rfl
  | succ f ih => intro m; rw [jolt_popcount_nat]; have := ih (m / 2); omega

/-- The population count of zero is zero for every fuel value. -/
theorem jolt_popcount_nat_zero : ∀ (f : Nat), jolt_popcount_nat f 0 = 0 := by
  intro f; induction f with
  | zero => rfl
  | succ f ih => rw [jolt_popcount_nat, Nat.zero_div, ih]

/-- A nonzero mask fitting within the inspected bits has positive population count. -/
theorem jolt_popcount_nat_pos : ∀ (f m : Nat), m ≠ 0 → m < 2 ^ f → 0 < jolt_popcount_nat f m := by
  intro f; induction f with
  | zero => intro m hm hlt; simp at hlt; omega
  | succ f ih =>
    intro m hm hlt
    rw [jolt_popcount_nat]
    by_cases h : m % 2 = 1
    · omega
    · have := ih (m / 2) (by omega) (by rw [pow_succ] at hlt; omega); omega

/-- The extracted value fits within the number of bits selected by the mask. -/
theorem jolt_pext_nat_lt : ∀ (f X m : Nat), jolt_pext_nat f X m < 2 ^ jolt_popcount_nat f m := by
  intro f; induction f with
  | zero => intro X m; simp [jolt_pext_nat, jolt_popcount_nat]
  | succ f ih =>
    intro X m
    have := ih (X / 2) (m / 2)
    rw [jolt_pext_nat, jolt_popcount_nat]
    split_ifs with h
    · rw [h, Nat.add_comm 1, pow_succ]; omega
    · rw [show m % 2 = 0 by omega, zero_add]; exact this

/-- The top extracted bit is the source bit at the highest set mask position. -/
theorem jolt_pext_nat_testBit_top : ∀ (f X m : Nat), m ≠ 0 → m < 2 ^ f →
    (jolt_pext_nat f X m).testBit (jolt_popcount_nat f m - 1) = X.testBit m.log2 := by
  intro f; induction f with
  | zero => intro X m hm hlt; simp at hlt; omega
  | succ f ih =>
    intro X m hm hlt
    have hlt' : m / 2 < 2 ^ f := by rw [pow_succ] at hlt; omega
    rw [jolt_pext_nat, jolt_popcount_nat]
    split_ifs with h
    · by_cases h0 : m / 2 = 0
      · have hm1 : m = 1 := by omega
        subst hm1
        simp only [h0, jolt_pext_nat_zero, jolt_popcount_nat_zero, (Nat.log2_eq_iff (by decide)).mpr
          (by decide : 2 ^ 0 ≤ 1 ∧ 1 < 2 ^ (0 + 1))]
        simp [Nat.testBit_zero]
      · have hpos := jolt_popcount_nat_pos f (m / 2) h0 hlt'
        have hlog : m.log2 = (m / 2).log2 + 1 := by
          rw [Nat.log2_def, if_pos (by omega)]
        rw [h, hlog, show 1 + jolt_popcount_nat f (m / 2) - 1 =
            (jolt_popcount_nat f (m / 2) - 1) + 1 by omega, Nat.testBit_succ, Nat.testBit_succ,
          show (X % 2 + 2 * jolt_pext_nat f (X / 2) (m / 2)) / 2 = jolt_pext_nat f (X / 2) (m / 2)
            by omega]
        exact ih _ _ h0 hlt'
    · have h0 : m / 2 ≠ 0 := by omega
      have hlog : m.log2 = (m / 2).log2 + 1 := by
        rw [Nat.log2_def, if_pos (by omega)]
      rw [show m % 2 = 0 by omega, zero_add, hlog, Nat.testBit_succ]
      exact ih _ _ h0 hlt'

private theorem shift_and_one_toNat (x : BitVec 64) (p : Nat) :
    ((x >>> p) &&& 1).toNat = x.toNat / 2 ^ p % 2 := by
  simp [BitVec.toNat_and, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

/-- The PEXT_SIGNED table's `pextSigned` is the honest `VirtualPextSigned` value. -/
theorem pextSigned_eq_jolt_virtual_pext_signed_value (x y : BitVec 64) :
    pextSigned x y = jolt_virtual_pext_signed_value x y := by
  unfold pextSigned jolt_virtual_pext_signed_value
  rw [cpop_toNat_eq, pext_eq_jolt_virtual_pext_value]
  generalize hP : jolt_popcount_nat 64 y.toNat = P
  by_cases hP0 : P = 0
  · simp [hP0]
  simp only [hP0, if_false]
  have hy : y ≠ 0 := by
    rintro rfl
    rw [show (0 : BitVec 64).toNat = 0 from rfl, jolt_popcount_nat_zero] at hP; exact hP0 hP.symm
  have hY : y.toNat ≠ 0 := fun h => hy (BitVec.eq_of_toNat_eq (by simpa using h))
  have hP64 : P ≤ 64 := hP ▸ jolt_popcount_nat_le 64 y.toNat
  have hJ : jolt_pext_nat 64 x.toNat y.toNat < 2 ^ P := hP ▸ jolt_pext_nat_lt 64 x.toNat y.toNat
  have hPle : 2 ^ P ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) hP64
  have hE : (jolt_virtual_pext_value x y).toNat = jolt_pext_nat 64 x.toNat y.toNat := by
    simp only [jolt_virtual_pext_value, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have htop : (jolt_virtual_pext_value x y).getLsbD (P - 1) = x.toNat.testBit y.toNat.log2 := by
    rw [← BitVec.testBit_toNat, hE, ← hP]; exact jolt_pext_nat_testBit_top 64 _ _ hY y.isLt
  have hsign : (windowSignBit x y = 1) ↔ x.toNat.testBit y.toNat.log2 = true := by
    unfold windowSignBit
    rw [if_neg hy, ← BitVec.toNat_inj, shift_and_one_toNat, Nat.testBit_eq_decide_div_mod_eq]
    simp
  rw [htop]
  by_cases hb : x.toNat.testBit y.toNat.log2 = true
  · rw [if_pos (hsign.mpr hb), if_pos hb]
    apply BitVec.eq_of_toNat_eq
    have hsub : (((1#128 <<< 64) - (1#128 <<< P)).setWidth 64).toNat = 2 ^ 64 - 2 ^ P := by
      rw [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_shiftLeft, BitVec.toNat_shiftLeft,
        show (1#128).toNat = 1 from rfl, Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.one_mul,
        Nat.one_mul]
      have hP2 : 2 ≤ 2 ^ P := by
        calc 2 = 2 ^ 1 := rfl
          _ ≤ 2 ^ P := Nat.pow_le_pow_right (by decide) (by omega)
      generalize 2 ^ P = Q at *
      omega
    have hlow : (BitVec.ofNat 64 (2 ^ P - 1)).toNat = 2 ^ P - 1 := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
    have hsplit : 2 ^ 64 - 2 ^ P = 2 ^ P * (2 ^ (64 - P) - 1) := by
      rw [Nat.mul_sub_one, ← pow_add, show P + (64 - P) = 64 by omega]
    rw [BitVec.toNat_add, BitVec.toNat_or, BitVec.toNat_not, hlow, hE, hsub,
      show 2 ^ 64 - 1 - (2 ^ P - 1) = 2 ^ 64 - 2 ^ P by omega, hsplit, Nat.or_comm,
      ← Nat.two_pow_add_eq_or_of_lt hJ, ← hsplit, Nat.mod_eq_of_lt (by omega)]
    omega
  · have hns : ¬ windowSignBit x y = 1 := fun h => hb (hsign.mp h)
    rw [if_neg hns, if_neg hb]; simp

end JoltConstraints
