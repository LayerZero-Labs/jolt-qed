import JoltBytecode.JoltISA.Expansions.Mul
import JoltBytecode.JoltISA.ExpansionsAutomated
import JoltBytecode.InstructionEquivalence.ProofSupport.InstructionLemmas
import JoltBytecode.Bundles
import JoltBytecode.InstructionEquivalence.ProofSupport.Projection
import JoltBytecode.InstructionEquivalence.ProofSupport.Basic
import Mathlib

set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# MULHSU: Rust inline sequence = Sail MULHSU

This file follows the same proof pattern as `Mulh.lean`, but the inline
sequence is longer because Rust computes a signed-by-unsigned high multiply by
first conditionally negating the signed operand and then correcting the high
half of the product.

The statement we want to be the stable API is program-level:

```
System.systemProjectResult
  ((JoltISA.execProgram (JoltISA.mulhsuProgramAuto rd rs1 rs2)).run js)
  =
(execute_MUL rs2 rs1 rd mulhsuOp).run js.sail
```

As in `Mulh.lean`, the proof separates concerns:

1. `JoltISA.mulhsuProgramAuto` is the faithful Rust inline sequence.
2. `mulhsuProgramAuto_concrete` executes that program one instruction at a time
   and proves what it writes.
3. `jolt_mulhsu_value_eq_mulhsu` proves that the Jolt term is Sail's `MULHSU`.

The Rust inline sequence, with allocator choices fixed to `v0` through `v3`, is:

```
VirtualMovsign v0, rs1
ANDI           v1, v0, 1
XOR            v2, rs1, v0
ADD            v2, v2, v1
MULHU          v3, v2, rs2
MUL            v2, v2, rs2
XOR            v3, v3, v0
XOR            v2, v2, v0
ADD            v0, v2, v1
SLTU           v0, v0, v2
ADD            rd, v3, v0
```
-/

def mulhsuOp : mul_op :=
  { result_part := VectorHalf.High
    signed_rs1 := Signedness.Signed
    signed_rs2 := Signedness.Unsigned }

/-- Upper 64 bits of a signed-by-unsigned 64x64 multiply. -/
def mulhsu (a b : BitVec 64) : BitVec 64 :=
  BitVec.ofInt 64 ((a.toInt * (b.toNat : Int)) / (2 ^ 64))

/-- Auxiliary arithmetic form used internally to relate the Rust sequence to
RV64 `MULHSU`.  It is private because the public proof interface should talk
about either the literal Jolt value `jolt_mulhsu_value` or the Sail value
`mulhsu`. -/
private def jolt_mulhsu_correction_value (x y : BitVec 64) : BitVec 64 :=
  jolt_mulhu_value x y + jolt_movsign_value x * y

/-- The pure value written by the Rust `MULHSU` inline sequence. -/
def jolt_mulhsu_value (x y : BitVec 64) : BitVec 64 :=
  let rs1SignMask := jolt_movsign_value x
  let signBit := rs1SignMask &&& sign_extend (m := 64) (1#12 : BitVec 12)
  let absoluteRs1 := (x ^^^ rs1SignMask) + signBit
  let unsignedHighProduct := jolt_mulhu_value absoluteRs1 y
  let lowProduct := absoluteRs1 * y
  let correctedHighProduct := unsignedHighProduct ^^^ rs1SignMask
  let correctedLowProduct := lowProduct ^^^ rs1SignMask
  correctedHighProduct + jolt_sltu_value (correctedLowProduct + signBit) correctedLowProduct

/-- Extracting the upper half of a 128-bit truncated integer is the same as
division by `2^64`, viewed as a 64-bit bitvector. -/
private theorem extract_high64_to_bits_truncate_eq_ofInt_div (p : Int) :
    (Sail.BitVec.extractLsb (to_bits_truncate (l := 128) p) 127 64 : BitVec 64) =
      BitVec.ofInt 64 (p / 2^64) := by
  apply BitVec.eq_of_toNat_eq
  simp [Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb',
    to_bits_truncate, Sail.get_slice_int, Nat.shiftRight_eq_div_pow]
  omega
/-- The local `mulhsu` value agrees with Sail's generic signed/unsigned
high-half multiply operator. -/
private theorem mulhsu_eq_sail_mulhsu_value (v1 v2 : BitVec 64) :
    mulhsu v1 v2 =
      mult_to_bits_half (l := LeanRV64D.Functions.xlen)
        Signedness.Signed Signedness.Unsigned v1 v2 VectorHalf.High := by
  unfold mulhsu mult_to_bits_half LeanRV64D.Functions.xlen
  simp only
  change BitVec.ofInt 64 (v1.toInt * (v2.toNat : Int) / 2^64) =
    BitVec.setWidth 64
      (Sail.BitVec.extractLsb
        (to_bits_truncate (l := 128) (v1.toInt * (v2.toNat : Int))) 127 64)
  rw [extract_high64_to_bits_truncate_eq_ofInt_div]
  simp
/-- A 64-bit word below `2^63` has signed interpretation equal to its unsigned
natural-number value. -/
private theorem toInt_of_toNat_lt_half (x : BitVec 64)
    (h : x.toNat < 9223372036854775808) :
    x.toInt = (x.toNat : Int) := by
  rw [BitVec.toInt]
  have hcond : 2 * x.toNat < 18446744073709551616 := by omega
  simp only [Nat.reducePow, hcond, ↓reduceIte]
/-- A 64-bit word at least `2^63` has signed interpretation equal to its
unsigned value minus `2^64`. -/
private theorem toInt_of_half_le (x : BitVec 64)
    (h : ¬ x.toNat < 9223372036854775808) :
    x.toInt = (x.toNat : Int) - (18446744073709551616 : Int) := by
  rw [BitVec.toInt]
  have hcond : ¬ 2 * x.toNat < 18446744073709551616 := by omega
  simp only [Nat.reducePow, hcond, ↓reduceIte]
  norm_num
/-- Xoring a 64-bit word with all ones complements its natural-number value
inside the `2^64` range. -/
private theorem xor_neg_one_toNat (x : BitVec 64) :
    (x ^^^ (-1 : BitVec 64)).toNat =
      18446744073709551616 - 1 - x.toNat := by
  change (x ^^^ (-1#64 : BitVec 64)).toNat =
    18446744073709551616 - 1 - x.toNat
  rw [show (-1#64 : BitVec 64) = BitVec.allOnes 64 from by decide,
    BitVec.xor_allOnes]
  rw [BitVec.toNat_not]
/-- For a negative signed 64-bit word, `xor -1` followed by `+ 1` computes the
magnitude `2^64 - x.toNat`. -/
private theorem abs_neg_toNat (x : BitVec 64)
    (hx : ¬ x.toNat < 9223372036854775808) :
    ((x ^^^ (-1 : BitVec 64)) + 1).toNat =
      18446744073709551616 - x.toNat := by
  rw [BitVec.toNat_add, xor_neg_one_toNat]
  have hxpos : 0 < x.toNat := by omega
  rw [show (1 : BitVec 64).toNat = 1 by decide]
  norm_num
  omega
/-- The bitvector absolute-value expression for a negative operand is equal to
the corresponding `BitVec.ofNat` magnitude. -/
private theorem abs_neg_eq_ofNat (x : BitVec 64)
    (hx : ¬ x.toNat < 9223372036854775808) :
    ((x ^^^ (-1 : BitVec 64)) + 1) =
      BitVec.ofNat 64 (18446744073709551616 - x.toNat) := by
  apply BitVec.eq_of_toNat_eq
  rw [abs_neg_toNat x hx, BitVec.toNat_ofNat]
  have hxpos : 0 < x.toNat := by omega
  norm_num
  omega

/-- Arithmetic correction for the negative signed operand case in `MULHSU`. -/
private theorem mulhsu_corr_neg_arith (a b : Nat) :
    (a * b / 18446744073709551616 + 18446744073709551615 * b) %
        18446744073709551616 =
      ((((a : Int) - 18446744073709551616) * (b : Int) /
            18446744073709551616) % 18446744073709551616).toNat := by
  rw [show ((a : Int) - 18446744073709551616) * (b : Int) =
      ((a * b : Nat) : Int) - 18446744073709551616 * (b : Int) by
    rw [Nat.cast_mul]
    ring]
  omega

/-- If the complementary product has zero low half, the high-half quotient of
the original product is exactly the unsigned operand minus the complementary
quotient. -/
private theorem div_complement_mod_zero (a b : Nat)
    (ha : ¬ a < 9223372036854775808)
    (haN : a < 18446744073709551616)
    (hr : (18446744073709551616 - a) * b %
        18446744073709551616 = 0) :
    a * b / 18446744073709551616 =
      b - ((18446744073709551616 - a) * b /
        18446744073709551616) := by
  have ha_le : a ≤ 18446744073709551616 := by omega
  have hmul : a * b + (18446744073709551616 - a) * b =
      18446744073709551616 * b := by
    have ha_sum : a + (18446744073709551616 - a) =
        18446744073709551616 := Nat.add_sub_of_le ha_le
    nlinarith [Nat.left_distrib b a (18446744073709551616 - a)]
  have hdiv := Nat.div_add_mod ((18446744073709551616 - a) * b)
    18446744073709551616
  omega

/-- If the complementary product has nonzero low half, the high-half quotient
of the original product is one less than the zero-remainder case. -/
private theorem div_complement_mod_pos (a b : Nat)
    (ha : ¬ a < 9223372036854775808)
    (haN : a < 18446744073709551616)
    (hr : ¬ (18446744073709551616 - a) * b %
        18446744073709551616 = 0) :
    a * b / 18446744073709551616 =
      b - ((18446744073709551616 - a) * b /
        18446744073709551616) - 1 := by
  have ha_le : a ≤ 18446744073709551616 := by omega
  have hmul : a * b + (18446744073709551616 - a) * b =
      18446744073709551616 * b := by
    have ha_sum : a + (18446744073709551616 - a) =
        18446744073709551616 := Nat.add_sub_of_le ha_le
    nlinarith [Nat.left_distrib b a (18446744073709551616 - a)]
  have hdiv := Nat.div_add_mod ((18446744073709551616 - a) * b)
    18446744073709551616
  have hrpos : 0 < (18446744073709551616 - a) * b %
      18446744073709551616 := by omega
  have hrlt : (18446744073709551616 - a) * b %
      18446744073709551616 < 18446744073709551616 :=
    Nat.mod_lt _ (by norm_num)
  omega

/-- Modular identity for the negated high half when the low-half correction
does not borrow. -/
private theorem neg_high_mod_zero (b q : Nat)
    (hb : b < 18446744073709551616) (hq : q ≤ b) :
    (18446744073709551616 - q) % 18446744073709551616 =
      (b - q + 18446744073709551615 * b) %
        18446744073709551616 := by
  by_cases hq0 : q = 0
  · subst q
    simp only [Nat.sub_zero]
    rw [show b + 18446744073709551615 * b =
        18446744073709551616 * b by omega]
    rw [Nat.mul_mod_right]
  · have hqpos : 0 < q := by omega
    have hbpos : 0 < b := by omega
    have hqN : q < 18446744073709551616 := by omega
    have hleft : (18446744073709551616 - q) %
        18446744073709551616 = 18446744073709551616 - q := by
      apply Nat.mod_eq_of_lt
      omega
    rw [hleft]
    have hright_eq :
        b - q + 18446744073709551615 * b =
          18446744073709551616 * (b - 1) +
            (18446744073709551616 - q) := by
      omega
    rw [hright_eq]
    rw [Nat.add_mod, Nat.mul_mod_right]
    simp
    exact hleft.symm

/-- Modular identity for the negated high half when the low-half correction
does borrow. -/
private theorem neg_high_mod_pos (b q : Nat)
    (hb : b < 18446744073709551616) (hq : q + 1 ≤ b) :
    (18446744073709551616 - 1 - q) % 18446744073709551616 =
      (b - q - 1 + 18446744073709551615 * b) %
        18446744073709551616 := by
  have hbpos : 0 < b := by omega
  have hqN : q < 18446744073709551616 := by omega
  have hleft : (18446744073709551616 - 1 - q) %
      18446744073709551616 = 18446744073709551616 - 1 - q := by
    apply Nat.mod_eq_of_lt
    omega
  rw [hleft]
  have hright_eq :
      b - q - 1 + 18446744073709551615 * b =
        18446744073709551616 * (b - 1) +
          (18446744073709551616 - 1 - q) := by
    omega
  rw [hright_eq]
  rw [Nat.add_mod, Nat.mul_mod_right]
  simp
  exact hleft.symm

/-- The high-half correction produced by the Rust/Jolt sequence agrees with
the compact signed/unsigned correction formula. -/
private theorem neg_high_eq_mulhsu_correction (a b : Nat)
    (ha : ¬ a < 9223372036854775808)
    (haN : a < 18446744073709551616)
    (hbN : b < 18446744073709551616) :
    (18446744073709551615 -
          ((18446744073709551616 - a) * b /
            18446744073709551616) +
        (if ((18446744073709551615 -
                ((18446744073709551616 - a) * b %
                  18446744073709551616) + 1) %
              18446744073709551616) <
            18446744073709551615 -
              ((18446744073709551616 - a) * b %
                18446744073709551616)
          then 1 else 0)) % 18446744073709551616 =
      (a * b / 18446744073709551616 + 18446744073709551615 * b) %
        18446744073709551616 := by
  by_cases hr : (18446744073709551616 - a) * b %
      18446744073709551616 = 0
  · rw [div_complement_mod_zero a b ha haN hr]
    simp [hr]
    have hq_le : (18446744073709551616 - a) * b /
        18446744073709551616 ≤ b := by
      apply Nat.div_le_of_le_mul
      have hm : 18446744073709551616 - a ≤ 18446744073709551616 :=
        Nat.sub_le _ _
      nlinarith
    rw [show 18446744073709551615 -
        ((18446744073709551616 - a) * b / 18446744073709551616) + 1 =
          18446744073709551616 -
            ((18446744073709551616 - a) * b /
              18446744073709551616) by omega]
    exact neg_high_mod_zero b
      ((18446744073709551616 - a) * b / 18446744073709551616)
      hbN hq_le
  · have hcond : ¬
        ((18446744073709551615 -
              ((18446744073709551616 - a) * b %
                18446744073709551616) + 1) %
            18446744073709551616) <
          18446744073709551615 -
            ((18446744073709551616 - a) * b %
              18446744073709551616) := by
      have hrpos : 0 < (18446744073709551616 - a) * b %
          18446744073709551616 := by omega
      have hrlt : (18446744073709551616 - a) * b %
          18446744073709551616 < 18446744073709551616 :=
        Nat.mod_lt _ (by norm_num)
      rw [show 18446744073709551615 -
          ((18446744073709551616 - a) * b %
            18446744073709551616) + 1 =
        18446744073709551616 -
          ((18446744073709551616 - a) * b %
            18446744073709551616) by omega]
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    rw [div_complement_mod_pos a b ha haN hr]
    simp [hcond]
    apply neg_high_mod_pos
    · exact hbN
    · have hbpos : 0 < b := by
        by_contra hb
        have hb0 : b = 0 := by omega
        simp [hb0] at hr
      have hm_lt : 18446744073709551616 - a <
          18446744073709551616 := by omega
      have hdivlt : (18446744073709551616 - a) * b /
          18446744073709551616 < b := by
        rw [Nat.div_lt_iff_lt_mul
          (by norm_num : 0 < 18446744073709551616)]
        nlinarith
      omega

/-- The literal Rust/Jolt `MULHSU` value simplifies to the compact correction
formula `jolt_mulhu_value x y + sign(x) * y`. -/
private theorem jolt_mulhsu_value_eq_correction (x y : BitVec 64) :
    jolt_mulhsu_value x y = jolt_mulhsu_correction_value x y := by
  by_cases hx : x.toNat < 9223372036854775808
  · rw [jolt_mulhsu_value, jolt_mulhsu_correction_value,
      jolt_movsign_value_eq_zero_of_toNat_lt_half x hx]
    unfold jolt_mulhu_value
    rw [jolt_sltu_value_eq_zero_of_not_lt]
    · apply BitVec.eq_of_toNat_eq
      simp
    · simp
  · rw [jolt_mulhsu_value, jolt_mulhsu_correction_value,
      jolt_movsign_value_eq_neg_one_of_half_le x hx]
    change (jolt_mulhu_value
          ((x ^^^ (-1 : BitVec 64)) +
            ((-1 : BitVec 64) &&& sign_extend (m := 64) (1#12 : BitVec 12))) y ^^^ (-1 : BitVec 64)) +
        jolt_sltu_value (((((x ^^^ (-1 : BitVec 64)) + 1) * y) ^^^ (-1 : BitVec 64)) + 1)
          ((((x ^^^ (-1 : BitVec 64)) + 1) * y) ^^^ (-1 : BitVec 64)) =
      jolt_mulhu_value x y + (-1 : BitVec 64) * y
    rw [show ((-1 : BitVec 64) &&& sign_extend (m := 64) (1#12 : BitVec 12)) =
      1 by decide]
    rw [abs_neg_eq_ofNat x hx]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add]
    rw [xor_neg_one_toNat
      (jolt_mulhu_value (BitVec.ofNat 64 (18446744073709551616 - x.toNat)) y)]
    rw [jolt_sltu_value_toNat]
    rw [BitVec.toNat_add]
    rw [xor_neg_one_toNat
      ((BitVec.ofNat 64 (18446744073709551616 - x.toNat)) * y)]
    unfold jolt_mulhu_value
    rw [BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_mul,
      BitVec.toNat_ofNat, BitVec.toNat_mul]
    rw [show (1 : BitVec 64).toNat = 1 by decide]
    rw [show (-1 : BitVec 64).toNat = 18446744073709551615 by decide]
    norm_num
    have hNx : (18446744073709551616 - x.toNat) %
        18446744073709551616 = 18446744073709551616 - x.toNat := by
      apply Nat.mod_eq_of_lt
      have hxpos : 0 < x.toNat := by omega
      omega
    rw [hNx]
    have hq1 : (18446744073709551616 - x.toNat) * y.toNat /
        18446744073709551616 < 18446744073709551616 := by
      rw [Nat.div_lt_iff_lt_mul
        (by norm_num : 0 < 18446744073709551616)]
      have hxpos : 0 < x.toNat := by omega
      have hm_lt : 18446744073709551616 - x.toNat <
          18446744073709551616 := by omega
      nlinarith [hm_lt, y.isLt]
    rw [Nat.mod_eq_of_lt hq1]
    exact neg_high_eq_mulhsu_correction x.toNat y.toNat hx x.isLt y.isLt

/-- The compact signed/unsigned correction formula equals the RV64 `MULHSU`
value. -/
private theorem jolt_mulhsu_correction_eq_mulhsu (x y : BitVec 64) :
    jolt_mulhsu_correction_value x y = mulhsu x y := by
  by_cases hx : x.toNat < 9223372036854775808
  · rw [jolt_mulhsu_correction_value,
      jolt_movsign_value_eq_zero_of_toNat_lt_half x hx]
    unfold jolt_mulhu_value mulhsu
    rw [toInt_of_toNat_lt_half x hx]
    apply BitVec.eq_of_toNat_eq
    simp
    omega
  · rw [jolt_mulhsu_correction_value,
      jolt_movsign_value_eq_neg_one_of_half_le x hx]
    unfold jolt_mulhu_value mulhsu
    rw [toInt_of_half_le x hx]
    apply BitVec.eq_of_toNat_eq
    simp
    exact mulhsu_corr_neg_arith x.toNat y.toNat

/-- The literal Rust/Jolt `MULHSU` value equals the Sail/RISC-V `MULHSU` value. -/
private theorem jolt_mulhsu_value_eq_mulhsu (x y : BitVec 64) :
    jolt_mulhsu_value x y = mulhsu x y := by
  rw [jolt_mulhsu_value_eq_correction, jolt_mulhsu_correction_eq_mulhsu]

/-- Factor Sail's generated `execute_MUL` body for `MULHSU` into the simple
shape used by the generic R-type equivalence bridge. -/
theorem execute_MULHSU_factored (rs2 rs1 rd : regidx) :
    execute_MUL rs2 rs1 rd mulhsuOp = (do
      let v1 ← rX_bits rs1
      let v2 ← rX_bits rs2
      wX_bits rd (mulhsu v1 v2)
      pure RETIRE_SUCCESS) := by
  simp [execute_MUL, mulhsuOp, mulhsu_eq_sail_mulhsu_value, bind_pure_comp]

private theorem inlineTmp0_ne_inlineTmp1 :
    JoltISA.inlineTmp0 ≠ JoltISA.inlineTmp1 := by decide

private theorem inlineTmp0_ne_inlineTmp2 :
    JoltISA.inlineTmp0 ≠ JoltISA.inlineTmp2 := by decide

private theorem inlineTmp0_ne_inlineTmp3 :
    JoltISA.inlineTmp0 ≠ JoltISA.inlineTmp3 := by decide

private theorem inlineTmp1_ne_inlineTmp2 :
    JoltISA.inlineTmp1 ≠ JoltISA.inlineTmp2 := by decide

private theorem inlineTmp1_ne_inlineTmp3 :
    JoltISA.inlineTmp1 ≠ JoltISA.inlineTmp3 := by decide

private theorem inlineTmp2_ne_inlineTmp0 :
    JoltISA.inlineTmp2 ≠ JoltISA.inlineTmp0 := by decide

private theorem inlineTmp2_ne_inlineTmp3 :
    JoltISA.inlineTmp2 ≠ JoltISA.inlineTmp3 := by decide

private theorem inlineTmp3_ne_inlineTmp0 :
    JoltISA.inlineTmp3 ≠ JoltISA.inlineTmp0 := by decide

private theorem inlineTmp3_ne_inlineTmp2 :
    JoltISA.inlineTmp3 ≠ JoltISA.inlineTmp2 := by decide

/-- Program-level concrete theorem for `MULHSU`.

The instruction blocks prove the emitted Jolt sequence writes
`jolt_mulhsu_value`.  The final value block is the only place where the pure
arithmetic theorem changes that Jolt value into Sail's `MULHSU` value. -/
theorem mulhsuProgramAuto_concrete (rs2 rs1 rd : regidx) (js : SailJoltState)
    (v1 v2 : BitVec 64)
    (h_read_rs1 : rX_bits rs1 js.sail = .ok v1 js.sail)
    (h_read_rs2 : rX_bits rs2 js.sail = .ok v2 js.sail)
    (hrd : rd ≠ regidx.Regidx 0) :
    ∃ (jsf : SailJoltState),
      (JoltISA.execProgram (JoltISA.mulhsuProgramAuto rd rs1 rs2)).run js =
        .ok RETIRE_SUCCESS jsf ∧
      jsf.sail = stateAfterWrite js.sail rd (mulhsu v1 v2) := by

  -- Instruction 1: `VirtualMovsign v0, rs1` writes the sign mask of `rs1`.
  let rs1SignMask := jolt_movsign_value v1
  obtain ⟨js_afterRs1SignMask, h_rs1_sign_mask_reads_rs1,
      h_rs1_sign_mask_keeps_sail, h_rs1_sign_mask_writes_rs1SignMask,
      h_rs1_sign_mask_preserves, h_rs1_sign_mask_succeeds⟩ :=
    JoltISA.exists_state_after_movsign_run_vreg_xreg
      JoltISA.inlineTmp0 rs1 js js.sail v1 rfl h_read_rs1
      (by unfold WritableVReg; decide)

  -- Instruction 2: `ANDI v1, v0, 1` extracts the low bit of the sign mask.
  let signBit := rs1SignMask &&& sign_extend (m := 64) (1#12 : BitVec 12)
  obtain ⟨js_afterSignBit, h_sign_bit_keeps_sail, h_sign_bit_writes_signBit,
      h_sign_bit_preserves, h_sign_bit_succeeds⟩ :=
    JoltISA.exists_state_after_andi_run_vreg_vreg
      JoltISA.inlineTmp1 JoltISA.inlineTmp0 (1 : BitVec 12)
      js_afterRs1SignMask rs1SignMask
      (by unfold WritableVReg; decide) h_rs1_sign_mask_writes_rs1SignMask
  have h_sign_bit_sail : js_afterSignBit.sail = js.sail := by
    rw [h_sign_bit_keeps_sail, h_rs1_sign_mask_keeps_sail]
  have h_sign_bit_preserves_rs1SignMask :
      js_afterSignBit.vregs JoltISA.inlineTmp0 = rs1SignMask :=
    (h_sign_bit_preserves JoltISA.inlineTmp0 inlineTmp0_ne_inlineTmp1).trans
      h_rs1_sign_mask_writes_rs1SignMask

  -- Instruction 3: `XOR v2, rs1, v0` starts the absolute-value computation.
  let absoluteValueXor := v1 ^^^ rs1SignMask
  obtain ⟨js_afterAbsXor, h_abs_xor_reads_rs1, h_abs_xor_keeps_sail,
      h_abs_xor_writes_absoluteValueXor, h_abs_xor_preserves,
      h_abs_xor_succeeds⟩ :=
    JoltISA.exists_state_after_xor_run_vreg_xreg_vreg
      JoltISA.inlineTmp2 rs1 JoltISA.inlineTmp0 js_afterSignBit js.sail
      v1 rs1SignMask h_sign_bit_sail h_read_rs1 h_sign_bit_preserves_rs1SignMask
      (by unfold WritableVReg; decide)
  have h_abs_xor_sail : js_afterAbsXor.sail = js.sail := by
    rw [h_abs_xor_keeps_sail]
  have h_abs_xor_preserves_rs1SignMask :
      js_afterAbsXor.vregs JoltISA.inlineTmp0 = rs1SignMask :=
    (h_abs_xor_preserves JoltISA.inlineTmp0 inlineTmp0_ne_inlineTmp2).trans
      h_sign_bit_preserves_rs1SignMask
  have h_abs_xor_preserves_signBit :
      js_afterAbsXor.vregs JoltISA.inlineTmp1 = signBit :=
    (h_abs_xor_preserves JoltISA.inlineTmp1 inlineTmp1_ne_inlineTmp2).trans
      h_sign_bit_writes_signBit

  -- Instruction 4: `ADD v2, v2, v1` finishes the absolute-value computation.
  let absoluteRs1 := absoluteValueXor + signBit
  obtain ⟨js_afterAbsoluteRs1, h_absolute_rs1_keeps_sail,
      h_absolute_rs1_writes_absoluteRs1, h_absolute_rs1_preserves,
      h_absolute_rs1_succeeds⟩ :=
    JoltISA.exists_state_after_add_run_vreg_vreg_vreg
      JoltISA.inlineTmp2 JoltISA.inlineTmp2 JoltISA.inlineTmp1 js_afterAbsXor
      absoluteValueXor signBit
      (by unfold WritableVReg; decide) h_abs_xor_writes_absoluteValueXor
      h_abs_xor_preserves_signBit
  have h_absolute_rs1_sail : js_afterAbsoluteRs1.sail = js.sail := by
    rw [h_absolute_rs1_keeps_sail, h_abs_xor_sail]
  have h_absolute_rs1_preserves_rs1SignMask :
      js_afterAbsoluteRs1.vregs JoltISA.inlineTmp0 = rs1SignMask :=
    (h_absolute_rs1_preserves JoltISA.inlineTmp0 inlineTmp0_ne_inlineTmp2).trans
      h_abs_xor_preserves_rs1SignMask
  have h_absolute_rs1_preserves_signBit :
      js_afterAbsoluteRs1.vregs JoltISA.inlineTmp1 = signBit :=
    (h_absolute_rs1_preserves JoltISA.inlineTmp1 inlineTmp1_ne_inlineTmp2).trans
      h_abs_xor_preserves_signBit

  -- Instruction 5: `MULHU v3, v2, rs2` writes the unsigned high product.
  let unsignedHighProduct := jolt_mulhu_value absoluteRs1 v2
  obtain ⟨js_afterMulhu, h_mulhu_reads_rs2, h_mulhu_keeps_sail,
      h_mulhu_writes_unsignedHighProduct, h_mulhu_preserves, h_mulhu_succeeds⟩ :=
    JoltISA.exists_state_after_mulhu_run_vreg_vreg_xreg
      JoltISA.inlineTmp3 JoltISA.inlineTmp2 rs2 js_afterAbsoluteRs1 js.sail
      absoluteRs1 v2 h_absolute_rs1_sail h_absolute_rs1_writes_absoluteRs1
      h_read_rs2
      (by unfold WritableVReg; decide)
  have h_mulhu_sail : js_afterMulhu.sail = js.sail := by
    rw [h_mulhu_keeps_sail]
  have h_mulhu_preserves_rs1SignMask :
      js_afterMulhu.vregs JoltISA.inlineTmp0 = rs1SignMask :=
    (h_mulhu_preserves JoltISA.inlineTmp0 inlineTmp0_ne_inlineTmp3).trans
      h_absolute_rs1_preserves_rs1SignMask
  have h_mulhu_preserves_signBit :
      js_afterMulhu.vregs JoltISA.inlineTmp1 = signBit :=
    (h_mulhu_preserves JoltISA.inlineTmp1 inlineTmp1_ne_inlineTmp3).trans
      h_absolute_rs1_preserves_signBit
  have h_mulhu_preserves_absoluteRs1 :
      js_afterMulhu.vregs JoltISA.inlineTmp2 = absoluteRs1 :=
    (h_mulhu_preserves JoltISA.inlineTmp2 inlineTmp2_ne_inlineTmp3).trans
      h_absolute_rs1_writes_absoluteRs1

  -- Instruction 6: `MUL v2, v2, rs2` writes the low product.
  let lowProduct := absoluteRs1 * v2
  obtain ⟨js_afterMulLow, h_low_mul_reads_rs2, h_low_mul_keeps_sail,
      h_low_mul_writes_lowProduct, h_low_mul_preserves, h_low_mul_succeeds⟩ :=
    JoltISA.exists_state_after_mul_run_vreg_vreg_xreg
      JoltISA.inlineTmp2 JoltISA.inlineTmp2 rs2 js_afterMulhu js.sail
      absoluteRs1 v2 h_mulhu_sail h_mulhu_preserves_absoluteRs1 h_read_rs2
      (by unfold WritableVReg; decide)
  have h_low_mul_sail : js_afterMulLow.sail = js.sail := by
    rw [h_low_mul_keeps_sail]
  have h_low_mul_preserves_rs1SignMask :
      js_afterMulLow.vregs JoltISA.inlineTmp0 = rs1SignMask :=
    (h_low_mul_preserves JoltISA.inlineTmp0 inlineTmp0_ne_inlineTmp2).trans
      h_mulhu_preserves_rs1SignMask
  have h_low_mul_preserves_signBit :
      js_afterMulLow.vregs JoltISA.inlineTmp1 = signBit :=
    (h_low_mul_preserves JoltISA.inlineTmp1 inlineTmp1_ne_inlineTmp2).trans
      h_mulhu_preserves_signBit
  have h_low_mul_preserves_unsignedHighProduct :
      js_afterMulLow.vregs JoltISA.inlineTmp3 = unsignedHighProduct :=
    (h_low_mul_preserves JoltISA.inlineTmp3 inlineTmp3_ne_inlineTmp2).trans
      h_mulhu_writes_unsignedHighProduct

  -- Instruction 7: `XOR v3, v3, v0` corrects the high half.
  let correctedHighProduct := unsignedHighProduct ^^^ rs1SignMask
  obtain ⟨js_afterHighCorrectionXor, h_high_correction_xor_keeps_sail,
      h_high_correction_xor_writes_correctedHighProduct,
      h_high_correction_xor_preserves, h_high_correction_xor_succeeds⟩ :=
    JoltISA.exists_state_after_xor_run_vreg_vreg_vreg
      JoltISA.inlineTmp3 JoltISA.inlineTmp3 JoltISA.inlineTmp0 js_afterMulLow
      unsignedHighProduct rs1SignMask h_low_mul_preserves_unsignedHighProduct
      h_low_mul_preserves_rs1SignMask
      (by unfold WritableVReg; decide)
  have h_high_correction_xor_sail : js_afterHighCorrectionXor.sail = js.sail := by
    rw [h_high_correction_xor_keeps_sail, h_low_mul_sail]
  have h_high_correction_xor_preserves_rs1SignMask :
      js_afterHighCorrectionXor.vregs JoltISA.inlineTmp0 = rs1SignMask :=
    (h_high_correction_xor_preserves JoltISA.inlineTmp0 inlineTmp0_ne_inlineTmp3).trans
      h_low_mul_preserves_rs1SignMask
  have h_high_correction_xor_preserves_signBit :
      js_afterHighCorrectionXor.vregs JoltISA.inlineTmp1 = signBit :=
    (h_high_correction_xor_preserves JoltISA.inlineTmp1 inlineTmp1_ne_inlineTmp3).trans
      h_low_mul_preserves_signBit
  have h_high_correction_xor_preserves_lowProduct :
      js_afterHighCorrectionXor.vregs JoltISA.inlineTmp2 = lowProduct :=
    (h_high_correction_xor_preserves JoltISA.inlineTmp2 inlineTmp2_ne_inlineTmp3).trans
      h_low_mul_writes_lowProduct

  -- Instruction 8: `XOR v2, v2, v0` corrects the low half.
  let correctedLowProduct := lowProduct ^^^ rs1SignMask
  obtain ⟨js_afterLowCorrectionXor, h_low_correction_xor_keeps_sail,
      h_low_correction_xor_writes_correctedLowProduct,
      h_low_correction_xor_preserves, h_low_correction_xor_succeeds⟩ :=
    JoltISA.exists_state_after_xor_run_vreg_vreg_vreg
      JoltISA.inlineTmp2 JoltISA.inlineTmp2 JoltISA.inlineTmp0
      js_afterHighCorrectionXor lowProduct rs1SignMask
      h_high_correction_xor_preserves_lowProduct
      h_high_correction_xor_preserves_rs1SignMask
      (by unfold WritableVReg; decide)
  have h_low_correction_xor_sail : js_afterLowCorrectionXor.sail = js.sail := by
    rw [h_low_correction_xor_keeps_sail, h_high_correction_xor_sail]
  have h_low_correction_xor_preserves_signBit :
      js_afterLowCorrectionXor.vregs JoltISA.inlineTmp1 = signBit :=
    (h_low_correction_xor_preserves JoltISA.inlineTmp1 inlineTmp1_ne_inlineTmp2).trans
      h_high_correction_xor_preserves_signBit
  have h_low_correction_xor_preserves_correctedHighProduct :
      js_afterLowCorrectionXor.vregs JoltISA.inlineTmp3 = correctedHighProduct :=
    (h_low_correction_xor_preserves JoltISA.inlineTmp3 inlineTmp3_ne_inlineTmp2).trans
      h_high_correction_xor_writes_correctedHighProduct

  -- Instruction 9: `ADD v0, v2, v1` computes the carry candidate.
  let carryCandidate := correctedLowProduct + signBit
  obtain ⟨js_afterCarryCandidate, h_carry_candidate_keeps_sail,
      h_carry_candidate_writes_carryCandidate, h_carry_candidate_preserves,
      h_carry_candidate_succeeds⟩ :=
    JoltISA.exists_state_after_add_run_vreg_vreg_vreg
      JoltISA.inlineTmp0 JoltISA.inlineTmp2 JoltISA.inlineTmp1
      js_afterLowCorrectionXor correctedLowProduct signBit
      (by unfold WritableVReg; decide) h_low_correction_xor_writes_correctedLowProduct
      h_low_correction_xor_preserves_signBit
  have h_carry_candidate_sail : js_afterCarryCandidate.sail = js.sail := by
    rw [h_carry_candidate_keeps_sail, h_low_correction_xor_sail]
  have h_carry_candidate_preserves_correctedLowProduct :
      js_afterCarryCandidate.vregs JoltISA.inlineTmp2 = correctedLowProduct :=
    (h_carry_candidate_preserves JoltISA.inlineTmp2 inlineTmp2_ne_inlineTmp0).trans
      h_low_correction_xor_writes_correctedLowProduct
  have h_carry_candidate_preserves_correctedHighProduct :
      js_afterCarryCandidate.vregs JoltISA.inlineTmp3 = correctedHighProduct :=
    (h_carry_candidate_preserves JoltISA.inlineTmp3 inlineTmp3_ne_inlineTmp0).trans
      h_low_correction_xor_preserves_correctedHighProduct

  -- Instruction 10: `SLTU v0, v0, v2` computes the carry correction.
  let carryCorrection := jolt_sltu_value carryCandidate correctedLowProduct
  obtain ⟨js_afterCarry, h_carry_keeps_sail, h_carry_writes_carryCorrection,
      h_carry_preserves, h_carry_succeeds⟩ :=
    JoltISA.exists_state_after_sltu_run_vreg_vreg_vreg
      JoltISA.inlineTmp0 JoltISA.inlineTmp0 JoltISA.inlineTmp2
      js_afterCarryCandidate carryCandidate correctedLowProduct
      h_carry_candidate_writes_carryCandidate
      h_carry_candidate_preserves_correctedLowProduct
      (by unfold WritableVReg; decide)
  have h_carry_sail : js_afterCarry.sail = js.sail := by
    rw [h_carry_keeps_sail, h_carry_candidate_sail]
  have h_carry_preserves_correctedHighProduct :
      js_afterCarry.vregs JoltISA.inlineTmp3 = correctedHighProduct :=
    (h_carry_preserves JoltISA.inlineTmp3 inlineTmp3_ne_inlineTmp0).trans
      h_carry_candidate_preserves_correctedHighProduct

  -- Instruction 11: `ADD rd, v3, v0` writes the final Jolt `MULHSU` value.
  let mulhsuJoltResult := jolt_mulhsu_value v1 v2
  obtain ⟨js_afterFinalAdd, h_final_add_writes_mulhsuJoltResult,
      h_final_add_succeeds⟩ :=
    JoltISA.exists_state_after_add_run_xreg_vreg_vreg
      rd JoltISA.inlineTmp3 JoltISA.inlineTmp0 js_afterCarry js.sail
      correctedHighProduct carryCorrection h_carry_sail
      h_carry_preserves_correctedHighProduct h_carry_writes_carryCorrection

  -- Full program succeeds by stepping through the eleven instruction runs.
  have h_program_succeeds :
      (JoltISA.execProgram (JoltISA.mulhsuProgramAuto rd rs1 rs2)).run js =
        .ok RETIRE_SUCCESS js_afterFinalAdd := by
    unfold JoltISA.mulhsuProgramAuto
    rw [JoltISA.isX0_eq_false_of_ne_zero hrd]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show (BitVec.ofNat 7 40 : JoltISA.VReg) = JoltISA.inlineTmp0 by rfl,
      show (BitVec.ofNat 7 41 : JoltISA.VReg) = JoltISA.inlineTmp1 by rfl,
      show (BitVec.ofNat 7 42 : JoltISA.VReg) = JoltISA.inlineTmp2 by rfl,
      show (BitVec.ofNat 7 43 : JoltISA.VReg) = JoltISA.inlineTmp3 by rfl]
    rw [JoltISA.execProgram_instr_run_retire _ _ js js_afterRs1SignMask
      h_rs1_sign_mask_succeeds]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_afterRs1SignMask js_afterSignBit
      h_sign_bit_succeeds]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_afterSignBit js_afterAbsXor
      h_abs_xor_succeeds]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_afterAbsXor js_afterAbsoluteRs1
      h_absolute_rs1_succeeds]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_afterAbsoluteRs1 js_afterMulhu
      h_mulhu_succeeds]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_afterMulhu js_afterMulLow
      h_low_mul_succeeds]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_afterMulLow js_afterHighCorrectionXor
      h_high_correction_xor_succeeds]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_afterHighCorrectionXor
      js_afterLowCorrectionXor h_low_correction_xor_succeeds]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_afterLowCorrectionXor
      js_afterCarryCandidate h_carry_candidate_succeeds]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_afterCarryCandidate js_afterCarry
      h_carry_succeeds]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_afterCarry js_afterFinalAdd
      h_final_add_succeeds]
    rfl

  refine ⟨js_afterFinalAdd, h_program_succeeds, ?_⟩

  -- The instruction trace leaves `rd` containing the Jolt MULHSU value.
  have h_final_jolt_value :
      js_afterFinalAdd.sail = stateAfterWrite js.sail rd mulhsuJoltResult := by
    simp only [mulhsuJoltResult, jolt_mulhsu_value]
    exact h_final_add_writes_mulhsuJoltResult

  -- No more execution reasoning remains.
  -- The only real content left is the pure value equality:
  -- Jolt's correction sequence is Sail's MULHSU value.
  have h_mulhsu_value :
      mulhsuJoltResult = mulhsu v1 v2 := by
    simp only [mulhsuJoltResult]
    -- NOTE: The core math theorem.
    exact jolt_mulhsu_value_eq_mulhsu v1 v2

  -- After the value theorem, the final state claim is mechanical.
  rw [← h_mulhsu_value]
  exact h_final_jolt_value

/-- `MULHSU` never writes the persistent CSR virtual registers materialized by
`systemProject`. -/
theorem mulhsuProgramAuto_preserves_projected_vregs
    (rs2 rs1 rd : regidx)
    {js js' : SailJoltState}
    {result : ExecutionResult}
    (hrun : (JoltISA.execProgram (JoltISA.mulhsuProgramAuto rd rs1 rs2)).run js =
      .ok result js') :
    Projection.ProjectedVRegsPreserved js js' := by
  have hsafe :
      JoltISA.ProgramWritesNoProtectedVReg
        (JoltISA.mulhsuProgramAuto rd rs1 rs2) := by
    unfold JoltISA.mulhsuProgramAuto
    split
    · simp only [JoltISA.ProgramWritesNoProtectedVReg,
        JoltISA.InstrWritesNoProtectedVReg,
        JoltISA.DstWritesNoProtectedVReg,
        and_true]
    · rw [show (BitVec.ofNat 7 40 : JoltISA.VReg) = JoltISA.inlineTmp0 by rfl,
        show (BitVec.ofNat 7 41 : JoltISA.VReg) = JoltISA.inlineTmp1 by rfl,
        show (BitVec.ofNat 7 42 : JoltISA.VReg) = JoltISA.inlineTmp2 by rfl,
        show (BitVec.ofNat 7 43 : JoltISA.VReg) = JoltISA.inlineTmp3 by rfl]
      simp only [JoltISA.ProgramWritesNoProtectedVReg,
        JoltISA.InstrWritesNoProtectedVReg,
        JoltISA.DstWritesNoProtectedVReg,
        and_true]
      exact ⟨JoltISA.inlineTmp0_not_protected, JoltISA.inlineTmp1_not_protected,
        JoltISA.inlineTmp2_not_protected, JoltISA.inlineTmp2_not_protected,
        JoltISA.inlineTmp3_not_protected, JoltISA.inlineTmp2_not_protected,
        JoltISA.inlineTmp3_not_protected, JoltISA.inlineTmp2_not_protected,
        JoltISA.inlineTmp0_not_protected, JoltISA.inlineTmp0_not_protected⟩
  exact Projection.execProgram_preserves_projected_vregs_of_no_protected_writes
    (js := js) (js' := js') (result := result) hsafe hrun

/-- Main program-level theorem: interpreting the Jolt ISA `MULHSU` expansion
has the same projected architectural result as Sail's `MULHSU` semantics. -/
def mulhsuProgramEqSailStatement (rs2 rs1 rd : regidx)
    (js : SailJoltState)
    (_h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) : Prop :=
  System.systemProjectResult
      ((JoltISA.execProgram (JoltISA.mulhsuProgramAuto rd rs1 rs2)).run js) =
    (execute_MUL rs2 rs1 rd mulhsuOp).run js.sail

/-- Main program-level theorem: interpreting the Jolt ISA `MULHSU` expansion
has the same projected architectural result as Sail's `MULHSU` semantics. -/
theorem mulhsuProgram_eq_sail (rs2 rs1 rd : regidx)
    (js : SailJoltState)
    (h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) :
    mulhsuProgramEqSailStatement rs2 rs1 rd js h := by
  unfold mulhsuProgramEqSailStatement
  let v1 := h.rs1_val
  have h_read_rs1 : rX_bits rs1 js.sail = .ok v1 js.sail := h.rs1_read
  let v2 := h.rs2_val
  have h_read_rs2 : rX_bits rs2 js.sail = .ok v2 js.sail := h.rs2_read
  have h_project_initial : System.systemProject js = js.sail :=
    Projection.systemProject_eq_sail_of_compatible js h.linkedCSRs
  by_cases hrd : rd = regidx.Regidx 0
  · subst rd
    unfold JoltISA.mulhsuProgramAuto
    rw [JoltISA.isX0_regidx_zero]
    simp only [↓reduceIte]
    have hzero := JoltISA.pureWritebackRdZeroProgram_run js
    unfold JoltISA.pureWritebackRdZeroProgram at hzero
    rw [hzero]
    simp only [System.systemProjectResult]
    rw [h_project_initial]
    rw [execute_MULHSU_factored rs2 rs1 (regidx.Regidx 0)]
    simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure]
    simp only [h_read_rs1, h_read_rs2]
    simp only [wX_bits_regidx_zero]

  obtain ⟨js_afterFinalAdd, h_program_succeeds, h_final_sail⟩ :=
    mulhsuProgramAuto_concrete rs2 rs1 rd js v1 v2 h_read_rs1 h_read_rs2 hrd
  have h_projected_vregs :
      Projection.ProjectedVRegsPreserved js js_afterFinalAdd :=
    mulhsuProgramAuto_preserves_projected_vregs rs2 rs1 rd h_program_succeeds

  rw [h_program_succeeds]
  simp only [System.systemProjectResult]

  rw [execute_MULHSU_factored rs2 rs1 rd]
  simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure]
  simp only [h_read_rs1, h_read_rs2]

  obtain ⟨s', h_write⟩ := wX_shape rd (mulhsu v1 v2) js.sail
  simp only [h_write]
  congr 1

  rw [Projection.systemProject_stateAfterWrite_of_projected_vregs_preserved
    js js_afterFinalAdd rd (mulhsu v1 v2) h_final_sail h_projected_vregs]
  rw [h_project_initial]
  exact (wX_bits_eq_stateAfterWrite rd (mulhsu v1 v2) js.sail s' h_write).symm

end
