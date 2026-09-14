import JoltBytecode.JoltISA.Expansions.Store
import JoltBytecode.InstructionEquivalence.ProofSupport.ExpansionBlocks.ALU
import JoltBytecode.InstructionEquivalence.ProofSupport.InstructionLemmas
import JoltBytecode.InstructionEquivalence.ProofSupport.Memory.Read
import JoltBytecode.InstructionEquivalence.Instructions.StoreFamily.Splice
import JoltBytecode.InstructionEquivalence.ProofSupport.Basic

/-!
# Program blocks for store-family Jolt-ISA proofs

The store-family programs have the same shape as load programs until the
middle dword operation:

* compute `ea = rs1 + imm` in virtual register `v0`;
* compute the enclosing dword address in virtual register `v1`;
* load the current dword into virtual register `v2`;
* splice the low byte/halfword/word of `rs2` into that dword; and
* write the spliced dword back with `SD`.

This file is the store analogue of `LoadFamily/ProgramBlocks.lean`.  The block
theorems are tail-parametric so the public instruction files can follow the
Rust program top-to-bottom while keeping each proof phase small enough to read.
-/

set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions
open virtaddr MemoryAccessType mem_payload

set_option autoImplicit true

noncomputable section

namespace StoreProgramBlocks

private theorem shift_bits_left_eq_shiftLeft_nat (x : BitVec 64) (sh : BitVec 6) :
    shift_bits_left x sh = x <<< sh.toNat := by
  rfl

private theorem setWidth6_eq_extractLsb_5_0 (v : BitVec 64) :
    v.setWidth 6 = Sail.BitVec.extractLsb v 5 0 := by
  unfold Sail.BitVec.extractLsb
  ext i
  simp

private theorem shift6_eq_of_offset_byte (ea base : BitVec 64)
    (hsetup : StoreSplice.ByteStoreFacts ea base) :
    Sail.BitVec.extractLsb (shift_bits_left ea (3 : BitVec 6)) 5 0 =
      BitVec.ofNat 6 (((ea - base).toNat) * 8) := by
  rw [← setWidth6_eq_extractLsb_5_0 (shift_bits_left ea (3 : BitVec 6))]
  apply BitVec.eq_of_toNat_eq
  simp only [shift_bits_left, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  change (BitVec.shiftLeft ea 3).toNat % 2 ^ 6 =
    (ea - base).toNat * 8 % 2 ^ 6
  rw [show (BitVec.shiftLeft ea 3).toNat = ea.toNat <<< 3 % 2 ^ 64 by
    exact BitVec.toNat_shiftLeft]
  simp only [Nat.shiftLeft_eq]
  norm_num
  conv_lhs => rw [hsetup.ea_toNat]
  have hbase8 : base &&& (7 : BitVec 64) = 0 := by
    rw [hsetup.base_is_aligned]
    exact align_down_8_and_7_eq_zero ea
  have hbase_low : (base &&& (7 : BitVec 64)).toNat = base.toNat % 8 := by
    rw [BitVec.toNat_and]
    have h7 : (7 : BitVec 64).toNat = 7 := by decide
    rw [h7, show (7 : Nat) = 2 ^ 3 - 1 by norm_num,
      Nat.and_two_pow_sub_one_eq_mod]
  have hbase_mod8 : base.toNat % 8 = 0 := by
    have hzero := congrArg BitVec.toNat hbase8
    rw [hbase_low] at hzero
    simpa using hzero
  have hmod :
      ((base.toNat + (ea - base).toNat) * 8) % 64 =
        ((ea - base).toNat * 8) % 64 := by
    have hb_dvd : 8 ∣ base.toNat := Nat.dvd_of_mod_eq_zero hbase_mod8
    rcases hb_dvd with ⟨q, hq⟩
    rw [hq]
    rw [show (8 * q + (ea - base).toNat) * 8 =
        (ea - base).toNat * 8 + 64 * q by ring]
    rw [Nat.add_mul_mod_self_left]
  rw [hmod]
  have hsub_toNat :
      (18446744073709551616 - base.toNat + ea.toNat) %
          18446744073709551616 =
        (ea - base).toNat := by
    rw [show 18446744073709551616 = 2 ^ 64 by norm_num]
    exact (BitVec.toNat_sub ea base).symm
  conv_rhs => rw [hsub_toNat]

private theorem shift6_eq_of_offset_halfword (ea base : BitVec 64)
    (hsetup : StoreSplice.HalfwordStoreFacts ea base) :
    Sail.BitVec.extractLsb (shift_bits_left ea (3 : BitVec 6)) 5 0 =
      BitVec.ofNat 6 (((ea - base).toNat) * 8) := by
  have hbyte : StoreSplice.ByteStoreFacts ea base :=
    { base_is_aligned := hsetup.base_is_aligned
      no_ovf := hsetup.no_ovf
      ea_toNat := hsetup.ea_toNat
      byte_offset_cases := by
        rcases hsetup.halfword_offset_cases with h0 | h2 | h4 | h6
        · exact Or.inl h0
        · exact Or.inr (Or.inr (Or.inl h2))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h4))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h6))))))
    }
  exact shift6_eq_of_offset_byte ea base hbyte

private theorem shift6_eq_of_offset_word (ea base : BitVec 64)
    (hsetup : StoreSplice.WordStoreFacts ea base) :
    Sail.BitVec.extractLsb (shift_bits_left ea (3 : BitVec 6)) 5 0 =
      BitVec.ofNat 6 (((ea - base).toNat) * 8) := by
  have hbyte : StoreSplice.ByteStoreFacts ea base :=
    { base_is_aligned := hsetup.base_is_aligned
      no_ovf := hsetup.no_ovf
      ea_toNat := hsetup.ea_toNat
      byte_offset_cases := by
        rcases hsetup.word_offset_cases with h0 | h4
        · exact Or.inl h0
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h4))))
    }
  exact shift6_eq_of_offset_byte ea base hbyte

private theorem byteSequenceMask_getLsbD_true {i : Nat} (hi : i < 8) :
    (255#64).getLsbD i = true := by
  have hi64 : i < 64 := by omega
  have hmaskNat : Nat.testBit 255 i = true := by
    rw [show 255 = 2 ^ 8 - 1 by norm_num, Nat.testBit_two_pow_sub_one]
    simp [hi]
  rw [BitVec.getLsbD_ofNat]
  simp [hi64, hmaskNat]

private theorem byteSequenceMask_getLsbD_false_of_ge8 {i : Nat} (hge : 8 ≤ i) :
    (255#64).getLsbD i = false := by
  have hmaskNat : Nat.testBit 255 i = false := by
    rw [show 255 = 2 ^ 8 - 1 by norm_num, Nat.testBit_two_pow_sub_one]
    simp [not_lt.mpr hge]
  rw [BitVec.getLsbD_ofNat]
  simp [hmaskNat]

private theorem halfwordSequenceMask_getLsbD_true {i : Nat} (hi : i < 16) :
    (65535#64).getLsbD i = true := by
  have hi64 : i < 64 := by omega
  have hmaskNat : Nat.testBit 65535 i = true := by
    rw [show 65535 = 2 ^ 16 - 1 by norm_num, Nat.testBit_two_pow_sub_one]
    simp [hi]
  rw [BitVec.getLsbD_ofNat]
  simp [hi64, hmaskNat]

private theorem halfwordSequenceMask_getLsbD_false_of_ge16 {i : Nat}
    (hge : 16 ≤ i) :
    (65535#64).getLsbD i = false := by
  have hmaskNat : Nat.testBit 65535 i = false := by
    rw [show 65535 = 2 ^ 16 - 1 by norm_num, Nat.testBit_two_pow_sub_one]
    simp [not_lt.mpr hge]
  rw [BitVec.getLsbD_ofNat]
  simp [hmaskNat]

private theorem wordSequenceMask_getLsbD_true {i : Nat} (hi : i < 32) :
    (4294967295#64).getLsbD i = true := by
  have hi64 : i < 64 := by omega
  have hmaskNat : Nat.testBit 4294967295 i = true := by
    rw [show 4294967295 = 2 ^ 32 - 1 by norm_num, Nat.testBit_two_pow_sub_one]
    simp [hi]
  rw [BitVec.getLsbD_ofNat]
  simp [hi64, hmaskNat]

private theorem wordSequenceMask_getLsbD_false_of_ge32 {i : Nat}
    (hge : 32 ≤ i) :
    (4294967295#64).getLsbD i = false := by
  have hmaskNat : Nat.testBit 4294967295 i = false := by
    rw [show 4294967295 = 2 ^ 32 - 1 by norm_num, Nat.testBit_two_pow_sub_one]
    simp [not_lt.mpr hge]
  rw [BitVec.getLsbD_ofNat]
  simp [hmaskNat]

private theorem byteSplice_eq_sequence_of_bound
    (dword_orig rs2_val : BitVec 64) (off : Nat) (hoff : off + 1 ≤ 8) :
    dword_orig ^^^
        ((dword_orig ^^^ shift_bits_left rs2_val (BitVec.ofNat 6 (off * 8))) &&&
          shift_bits_left (0x00000000000000FF : BitVec 64) (BitVec.ofNat 6 (off * 8))) =
      StoreSplice.byteSplice dword_orig (Sail.BitVec.extractLsb rs2_val 7 0) (off * 8) := by
  rw [shift_bits_left_eq_shiftLeft_nat rs2_val (BitVec.ofNat 6 (off * 8))]
  rw [shift_bits_left_eq_shiftLeft_nat (0x00000000000000FF : BitVec 64)
    (BitVec.ofNat 6 (off * 8))]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hshift_lt64 : off * 8 < 64 := by omega
  have hshift_toNat : (BitVec.ofNat 6 (off * 8)).toNat = off * 8 := by
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt hshift_lt64
  simp only [StoreSplice.byteSplice, Sail.BitVec.extractLsb,
    BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb,
    hshift_toNat]
  by_cases hbefore : i < off * 8
  · simp [hbefore]
  · by_cases hinside : i - off * 8 < 8
    · have hsub64 : i - off * 8 < 64 := by omega
      simp [hbefore, hinside, hsub64]
    · have hge : 8 ≤ i - off * 8 := by omega
      have hmask : (255#64).getLsbD (i - off * 8) = false :=
        byteSequenceMask_getLsbD_false_of_ge8 hge
      simp [hbefore, hinside, hmask]

private theorem halfwordSplice_eq_sequence_of_bound
    (dword_orig rs2_val : BitVec 64) (off : Nat) (hoff : off + 2 ≤ 8) :
    dword_orig ^^^
        ((dword_orig ^^^ shift_bits_left rs2_val (BitVec.ofNat 6 (off * 8))) &&&
          shift_bits_left (0x000000000000FFFF : BitVec 64) (BitVec.ofNat 6 (off * 8))) =
      StoreSplice.halfwordSplice dword_orig (Sail.BitVec.extractLsb rs2_val 15 0) (off * 8) := by
  rw [shift_bits_left_eq_shiftLeft_nat rs2_val (BitVec.ofNat 6 (off * 8))]
  rw [shift_bits_left_eq_shiftLeft_nat (0x000000000000FFFF : BitVec 64)
    (BitVec.ofNat 6 (off * 8))]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hshift_lt64 : off * 8 < 64 := by omega
  have hshift_toNat : (BitVec.ofNat 6 (off * 8)).toNat = off * 8 := by
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt hshift_lt64
  simp only [StoreSplice.halfwordSplice, Sail.BitVec.extractLsb,
    BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb,
    hshift_toNat]
  by_cases hbefore : i < off * 8
  · simp [hbefore]
  · by_cases hinside : i - off * 8 < 16
    · have hsub64 : i - off * 8 < 64 := by omega
      simp [hbefore, hinside, hsub64]
    · have hge : 16 ≤ i - off * 8 := by omega
      have hmask : (65535#64).getLsbD (i - off * 8) = false :=
        halfwordSequenceMask_getLsbD_false_of_ge16 hge
      simp [hbefore, hinside, hmask]

private theorem wordSplice_eq_sequence_of_bound
    (dword_orig rs2_val : BitVec 64) (off : Nat) (hoff : off + 4 ≤ 8) :
    dword_orig ^^^
        ((dword_orig ^^^ shift_bits_left rs2_val (BitVec.ofNat 6 (off * 8))) &&&
          shift_bits_left (0x00000000FFFFFFFF : BitVec 64) (BitVec.ofNat 6 (off * 8))) =
      StoreSplice.wordSplice dword_orig (Sail.BitVec.extractLsb rs2_val 31 0) (off * 8) := by
  rw [shift_bits_left_eq_shiftLeft_nat rs2_val (BitVec.ofNat 6 (off * 8))]
  rw [shift_bits_left_eq_shiftLeft_nat (0x00000000FFFFFFFF : BitVec 64)
    (BitVec.ofNat 6 (off * 8))]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hshift_lt64 : off * 8 < 64 := by omega
  have hshift_toNat : (BitVec.ofNat 6 (off * 8)).toNat = off * 8 := by
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt hshift_lt64
  simp only [StoreSplice.wordSplice, Sail.BitVec.extractLsb,
    BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb,
    hshift_toNat]
  by_cases hbefore : i < off * 8
  · simp [hbefore]
  · by_cases hinside : i - off * 8 < 32
    · have hsub64 : i - off * 8 < 64 := by omega
      simp [hbefore, hinside, hsub64]
    · have hge : 32 ≤ i - off * 8 := by omega
      have hmask : (4294967295#64).getLsbD (i - off * 8) = false :=
        wordSequenceMask_getLsbD_false_of_ge32 hge
      simp [hbefore, hinside, hmask]

private theorem byteSplice_eq_sequence
    (dword_orig rs2_val : BitVec 64) (off : Nat)
    (hoff :
      off = 0 ∨ off = 1 ∨ off = 2 ∨ off = 3 ∨
      off = 4 ∨ off = 5 ∨ off = 6 ∨ off = 7) :
    dword_orig ^^^
        ((dword_orig ^^^ shift_bits_left rs2_val (BitVec.ofNat 6 (off * 8))) &&&
          shift_bits_left (0x00000000000000FF : BitVec 64) (BitVec.ofNat 6 (off * 8))) =
      StoreSplice.byteSplice dword_orig (Sail.BitVec.extractLsb rs2_val 7 0) (off * 8) := by
  have hoff_bound : off + 1 ≤ 8 := by
    rcases hoff with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 <;> omega
  exact byteSplice_eq_sequence_of_bound dword_orig rs2_val off hoff_bound

private theorem halfwordSplice_eq_sequence
    (dword_orig rs2_val : BitVec 64) (off : Nat)
    (hoff : off = 0 ∨ off = 2 ∨ off = 4 ∨ off = 6) :
    dword_orig ^^^
        ((dword_orig ^^^ shift_bits_left rs2_val (BitVec.ofNat 6 (off * 8))) &&&
          shift_bits_left (0x000000000000FFFF : BitVec 64) (BitVec.ofNat 6 (off * 8))) =
      StoreSplice.halfwordSplice dword_orig (Sail.BitVec.extractLsb rs2_val 15 0) (off * 8) := by
  have hoff_bound : off + 2 ≤ 8 := by
    rcases hoff with h0 | h2 | h4 | h6 <;> omega
  exact halfwordSplice_eq_sequence_of_bound dword_orig rs2_val off hoff_bound

private theorem wordSplice_eq_sequence
    (dword_orig rs2_val : BitVec 64) (off : Nat)
    (hoff : off = 0 ∨ off = 4) :
    dword_orig ^^^
        ((dword_orig ^^^ shift_bits_left rs2_val (BitVec.ofNat 6 (off * 8))) &&&
          shift_bits_left (0x00000000FFFFFFFF : BitVec 64) (BitVec.ofNat 6 (off * 8))) =
      StoreSplice.wordSplice dword_orig (Sail.BitVec.extractLsb rs2_val 31 0) (off * 8) := by
  have hoff_bound : off + 4 ≤ 8 := by
    rcases hoff with h0 | h4 <;> omega
  exact wordSplice_eq_sequence_of_bound dword_orig rs2_val off hoff_bound

private theorem shift_bits_right_allOnes_32 :
    shift_bits_right (-1 : BitVec 64) (32 : BitVec 6) =
      (0x00000000FFFFFFFF : BitVec 64) := by
  decide

private theorem shift_bits_right_signExtend_neg_one_32 :
    shift_bits_right (sign_extend (m := 64) (-1 : BitVec 12)) (32 : BitVec 6) =
      (0x00000000FFFFFFFF : BitVec 64) := by
  decide

private theorem shift_bits_right_signExtend_4095_32 :
    shift_bits_right (sign_extend (m := 64) (4095#12)) (32#6) =
      (0x00000000FFFFFFFF : BitVec 64) := by
  decide

private theorem zero_or_signExtend_neg_one :
    (0#64) ||| sign_extend (m := 64) (-1 : BitVec 12) = (-1 : BitVec 64) := by
  decide

/-!
## The `SW` mask prefix

The Rust `SW` expansion does not use `LUI` to materialize the 32-bit mask.
Instead it runs the four-instruction prefix

```
SLLI v0, v0, 3
ORI  v3, x0, -1
SRLI v3, v3, 32
SLL  v3, v3, v0
```

The following private definitions name the exact intermediate states for this
prefix.  Naming the states keeps the public block theorem below readable and,
more importantly, prevents the proof from becoming one large monadic reduction
that is hard for Lean to elaborate.
-/

private def swWordShiftState (js : SailJoltState) : SailJoltState :=
  { sail := js.sail
    vregs := fun r =>
      if r = JoltISA.inlineTmp0 then
        shift_bits_left (js.vregs JoltISA.inlineTmp0) (3 : BitVec 6)
      else js.vregs r }

private def swWordOnesState (js : SailJoltState) : SailJoltState :=
  { sail := js.sail
    vregs := fun r =>
      if r = JoltISA.inlineTmp3 then
        (0#64) ||| sign_extend (m := 64) (-1 : BitVec 12)
      else js.vregs r }

private def swWordBaseMaskState (js : SailJoltState) : SailJoltState :=
  { sail := js.sail
    vregs := fun r =>
      if r = JoltISA.inlineTmp3 then
        shift_bits_right (js.vregs JoltISA.inlineTmp3) (32 : BitVec 6)
      else js.vregs r }

private def swWordMaskState (js : SailJoltState) : SailJoltState :=
  { sail := js.sail
    vregs := fun r =>
      if r = JoltISA.inlineTmp3 then
        shift_bits_left (js.vregs JoltISA.inlineTmp3)
          (Sail.BitVec.extractLsb (js.vregs JoltISA.inlineTmp0) 5 0)
      else if r = JoltISA.inlineTmp4 then
        jolt_virtual_pow2_value (js.vregs JoltISA.inlineTmp0)
      else js.vregs r }

/-- First `SW` mask-prefix step: multiply the byte address by eight, leaving
the bit offset in `v0`. -/
private theorem swWordShiftStep (rest : JoltISA.Program) (js : SailJoltState) :
    (JoltISA.execProgram
      (JoltISA.slliBlock (.vreg JoltISA.inlineTmp0) (.vreg JoltISA.inlineTmp0) (3 : BitVec 6) rest)).run js =
      (JoltISA.execProgram rest).run (swWordShiftState js) := by
  have h :
      (JoltISA.execInstr
        (.VirtualMULI (.vreg JoltISA.inlineTmp0) (.vreg JoltISA.inlineTmp0) (JoltISA.slliMultiplier (3 : BitVec 6)))).run js =
        .ok RETIRE_SUCCESS (swWordShiftState js) := by
    have h_value :
        jolt_virtual_muli_value (js.vregs JoltISA.inlineTmp0)
          (JoltISA.slliMultiplier (3 : BitVec 6)) =
          shift_bits_left (js.vregs JoltISA.inlineTmp0) (3 : BitVec 6) :=
      JoltISA.slli_block_value_eq (js.vregs JoltISA.inlineTmp0) (3 : BitVec 6)
    rw [JoltISA.virtual_muli_run_vreg_vreg JoltISA.inlineTmp0 JoltISA.inlineTmp0
      (JoltISA.slliMultiplier (3 : BitVec 6)) js
      (by unfold WritableVReg; decide)]
    simp [swWordShiftState]
    funext r
    by_cases hr : r = JoltISA.inlineTmp0
    · subst r
      exact h_value
    · rw [if_neg hr, if_neg hr]
  unfold JoltISA.slliBlock
  exact JoltISA.execProgram_instr_run_retire _ _ js (swWordShiftState js) h

/-- Second `SW` mask-prefix step: read architectural `x0` and OR with `-1`,
materializing all ones in `v3`. -/
private theorem swWordOnesStep (rest : JoltISA.Program) (js : SailJoltState)
    (hx0 : rX_bits (regidx.Regidx 0) js.sail = .ok 0#64 js.sail) :
    (JoltISA.execProgram
      (.instr (.ORI (.vreg JoltISA.inlineTmp3) (.xreg (regidx.Regidx 0)) (-1 : BitVec 12)) rest)).run js =
      (JoltISA.execProgram rest).run (swWordOnesState js) := by
  have h :
      (JoltISA.execInstr (.ORI (.vreg JoltISA.inlineTmp3) (.xreg (regidx.Regidx 0)) (-1 : BitVec 12))).run js =
        .ok RETIRE_SUCCESS (swWordOnesState js) := by
    simpa [swWordOnesState] using
      (JoltISA.ori_run_vreg_xreg JoltISA.inlineTmp3 (regidx.Regidx 0)
        (-1 : BitVec 12) js (0#64) hx0 (by unfold WritableVReg; decide))
  exact JoltISA.execProgram_instr_run_retire _ _ js (swWordOnesState js) h

/-- Third `SW` mask-prefix step: logical-right-shift all ones by 32, producing
the unshifted 32-bit store mask. -/
private theorem swWordBaseMaskStep (rest : JoltISA.Program) (js : SailJoltState) :
    (JoltISA.execProgram
      (JoltISA.srliBlock (.vreg JoltISA.inlineTmp3) (.vreg JoltISA.inlineTmp3) (32 : BitVec 6) rest)).run js =
      (JoltISA.execProgram rest).run (swWordBaseMaskState js) := by
  have h :
      (JoltISA.execInstr
        (.VirtualSRLI (.vreg JoltISA.inlineTmp3) (.vreg JoltISA.inlineTmp3) (JoltISA.srliBitmask (32 : BitVec 6)))).run js =
        .ok RETIRE_SUCCESS (swWordBaseMaskState js) := by
    have h_value :
        jolt_virtual_srli_value (js.vregs JoltISA.inlineTmp3)
          (JoltISA.srliBitmask (32 : BitVec 6)) =
          shift_bits_right (js.vregs JoltISA.inlineTmp3) (32 : BitVec 6) :=
      JoltISA.srli_block_value_eq (js.vregs JoltISA.inlineTmp3) (32 : BitVec 6)
    rw [JoltISA.virtual_srli_run_vreg_vreg JoltISA.inlineTmp3 JoltISA.inlineTmp3
      (JoltISA.srliBitmask (32 : BitVec 6)) js
      (by unfold WritableVReg; decide)]
    simp [swWordBaseMaskState]
    funext r
    by_cases hr : r = JoltISA.inlineTmp3
    · subst r
      exact h_value
    · rw [if_neg hr, if_neg hr]
  unfold JoltISA.srliBlock
  exact JoltISA.execProgram_instr_run_retire _ _ js (swWordBaseMaskState js) h

/-- Fourth `SW` mask-prefix step: shift the 32-bit mask into the selected word
lane. -/
private theorem swWordMaskShiftStep (rest : JoltISA.Program) (js : SailJoltState) :
    (JoltISA.execProgram
      (JoltISA.sllBlock (.vreg JoltISA.inlineTmp3) (.vreg JoltISA.inlineTmp3) (.vreg JoltISA.inlineTmp0) JoltISA.inlineTmp4 rest)).run js =
      (JoltISA.execProgram rest).run (swWordMaskState js) := by
  let js_pow2 : SailJoltState :=
    { sail := js.sail
      vregs := fun r =>
        if r = JoltISA.inlineTmp4 then
          jolt_virtual_pow2_value (js.vregs JoltISA.inlineTmp0)
        else js.vregs r }
  have hpow2 :
      (JoltISA.execInstr (.VirtualPow2 (.vreg JoltISA.inlineTmp4) (.vreg JoltISA.inlineTmp0))).run js =
        .ok RETIRE_SUCCESS js_pow2 := by
    simpa [js_pow2] using
      (JoltISA.virtual_pow2_run_vreg_vreg JoltISA.inlineTmp4 JoltISA.inlineTmp0 js
        (by unfold WritableVReg; decide))
  have hmul :
      (JoltISA.execInstr (.MUL (.vreg JoltISA.inlineTmp3) (.vreg JoltISA.inlineTmp3) (.vreg JoltISA.inlineTmp4))).run js_pow2 =
        .ok RETIRE_SUCCESS (swWordMaskState js) := by
    simpa [swWordMaskState, js_pow2, JoltISA.mul_jolt_virtual_pow2_value_eq_shift_bits_left] using
      (JoltISA.mul_run_vreg_vreg_vreg JoltISA.inlineTmp3 JoltISA.inlineTmp3
        JoltISA.inlineTmp4 js_pow2 (by unfold WritableVReg; decide))
  unfold JoltISA.sllBlock
  rw [JoltISA.execProgram_instr_run_retire _ _ js js_pow2 hpow2]
  rw [JoltISA.execProgram_instr_run_retire _ _ js_pow2 (swWordMaskState js) hmul]

private theorem swWordMaskState_sail (js : SailJoltState) :
    (swWordMaskState (swWordBaseMaskState (swWordOnesState (swWordShiftState js)))).sail =
      js.sail := by
  rfl

private theorem swWordMaskState_v0 (js : SailJoltState) :
    (swWordMaskState (swWordBaseMaskState (swWordOnesState (swWordShiftState js)))).vregs
        JoltISA.inlineTmp0 =
      shift_bits_left (js.vregs JoltISA.inlineTmp0) (3 : BitVec 6) := by
  simp [swWordMaskState, swWordBaseMaskState, swWordOnesState, swWordShiftState]

private theorem swWordMaskState_v1 (js : SailJoltState) :
    (swWordMaskState (swWordBaseMaskState (swWordOnesState (swWordShiftState js)))).vregs
        JoltISA.inlineTmp1 =
      js.vregs JoltISA.inlineTmp1 := by
  simp [swWordMaskState, swWordBaseMaskState, swWordOnesState, swWordShiftState]

private theorem swWordMaskState_v2 (js : SailJoltState) :
    (swWordMaskState (swWordBaseMaskState (swWordOnesState (swWordShiftState js)))).vregs
        JoltISA.inlineTmp2 =
      js.vregs JoltISA.inlineTmp2 := by
  simp [swWordMaskState, swWordBaseMaskState, swWordOnesState, swWordShiftState]

private theorem swWordMaskState_v3 (js : SailJoltState) :
    (swWordMaskState (swWordBaseMaskState (swWordOnesState (swWordShiftState js)))).vregs
        JoltISA.inlineTmp3 =
      shift_bits_left (0x00000000FFFFFFFF : BitVec 64)
        (Sail.BitVec.extractLsb
          (shift_bits_left (js.vregs JoltISA.inlineTmp0) (3 : BitVec 6)) 5 0) := by
  simp [swWordMaskState, swWordBaseMaskState, swWordOnesState, swWordShiftState,
    shift_bits_right_signExtend_4095_32]

/-- Common setup block for store expansions.

`ADDI v0, rs1, imm; ANDI v1, v0, -8; LD v2, v1, 0` computes the effective
address, computes the enclosing dword base, and loads that dword into `v2`.
The boundary facts are exactly the store-side inputs needed by later splice
blocks. -/
theorem setupBlock (rest : JoltISA.Program)
    (imm : BitVec 12) (rs1 : regidx)
    (js : SailJoltState)
    (hpriv : Assumptions.CurPrivilegeMachine js.sail)
    (hmprv : Assumptions.MstatusMprvZero js.sail)
    (val : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (h_base_aligned :
      AlignedDwordAccess (compute_aligned_dword_base_address val imm))
    (hbytes :
      MemBytesPresentAt js.sail (compute_aligned_dword_base_address val imm) 8)
    (hpmp :
      Assumptions.LoadPmpOk (compute_aligned_dword_base_address val imm) 8 js.sail)
    (hmmio :
      Assumptions.NotReadableMmio (compute_aligned_dword_base_address val imm) 8 js.sail) :
    ∃ js_load : SailJoltState,
      (JoltISA.execProgram
        (.instr (.ADDI (.vreg JoltISA.inlineTmp0) (.xreg rs1) imm) <|
         .instr (.ANDI (.vreg JoltISA.inlineTmp1) (.vreg JoltISA.inlineTmp0) (-8 : BitVec 12)) <|
         .instr (.LD .normal (.vreg JoltISA.inlineTmp2) (.vreg JoltISA.inlineTmp1) 0) rest)).run js =
        (JoltISA.execProgram rest).run js_load ∧
      js_load.sail = js.sail ∧
      js_load.vregs JoltISA.inlineTmp0 = load_effective_address val imm ∧
      js_load.vregs JoltISA.inlineTmp1 = compute_aligned_dword_base_address val imm ∧
      js_load.vregs JoltISA.inlineTmp2 =
        loaded_dword_at js.sail (compute_aligned_dword_base_address val imm)
          hbytes h_base_aligned.no_ovf := by
  let ea := load_effective_address val imm
  let base := compute_aligned_dword_base_address val imm
  let dword := loaded_dword_at js.sail base (by simpa [base] using hbytes)
    (by simpa [base] using h_base_aligned.no_ovf)
  let js0 : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = JoltISA.inlineTmp0 then ea else js.vregs r }
  let js1 : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = JoltISA.inlineTmp1 then base else js0.vregs r }
  let js_load : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = JoltISA.inlineTmp2 then dword else js1.vregs r }
  have haddi :
      (JoltISA.execInstr (.ADDI (.vreg JoltISA.inlineTmp0) (.xreg rs1) imm)).run js =
        .ok RETIRE_SUCCESS js0 := by
    simpa [js0, ea, load_effective_address] using
      (JoltISA.addi_run_vreg_xreg JoltISA.inlineTmp0 rs1 imm js val hrx
        (by unfold WritableVReg; decide))
  have h8 : sign_extend (m := 64) (-8 : BitVec 12) = (-8 : BitVec 64) := by decide
  have handi :
      (JoltISA.execInstr (.ANDI (.vreg JoltISA.inlineTmp1) (.vreg JoltISA.inlineTmp0) (-8 : BitVec 12))).run js0 =
        .ok RETIRE_SUCCESS js1 := by
    simpa [js0, js1, ea, base, compute_aligned_dword_base_address,
      load_effective_address, h8] using
      (JoltISA.andi_run_vreg_vreg JoltISA.inlineTmp1 JoltISA.inlineTmp0
        (-8 : BitVec 12) js0 (by unfold WritableVReg; decide))
  have h_base_aligned : AlignedDwordAccess base := by
    simpa [base] using h_base_aligned
  have hld_read :
      vmem_read_addr (Virtaddr (js1.vregs JoltISA.inlineTmp1 + sign_extend (m := 64) (0 : BitVec 12))) 0 8
        (Load Data) false false false js1.sail =
        .ok (Ok dword) js1.sail := by
    have h0 : sign_extend (m := 64) (0 : BitVec 12) = (0 : BitVec 64) := by decide
    have haddr0 : base + sign_extend (m := 64) (0 : BitVec 12) = base := by
      rw [h0]
      norm_num
    have hread := aligned_dword_vmem_read_reduces base js.sail
      hpriv hmprv h_base_aligned
      (by simpa [base] using hbytes)
      (by simpa [base] using hpmp)
      (by simpa [base] using hmmio)
    rw [show js1.sail = js.sail by rfl]
    have hv1 : js1.vregs JoltISA.inlineTmp1 = base := by
      simp [js1]
    rw [hv1, haddr0]
    simpa [dword] using hread
  have hld :
      (JoltISA.execInstr (.LD .normal (.vreg JoltISA.inlineTmp2) (.vreg JoltISA.inlineTmp1) 0)).run js1 =
        .ok RETIRE_SUCCESS js_load := by
    have hld_align :
        (js1.vregs JoltISA.inlineTmp1 + sign_extend (m := 64) (0 : BitVec 12)) &&&
            (7 : BitVec 64) =
          0 := by
      have h0 : sign_extend (m := 64) (0 : BitVec 12) = (0 : BitVec 64) := by
        decide
      have hv1 : js1.vregs JoltISA.inlineTmp1 = base := by
        simp [js1]
      have haddr0 : base + (0 : BitVec 64) = base := by
        norm_num
      rw [hv1, h0, haddr0]
      exact h_base_aligned.align
    simpa [js_load, dword] using
      (JoltISA.ld_run_vreg_vreg_from_memory_read JoltISA.inlineTmp2 JoltISA.inlineTmp1
        (0 : BitVec 12) js1 dword hld_align hld_read
        (by unfold WritableVReg; decide))
  refine ⟨js_load, ?_, rfl, ?_, ?_, ?_⟩
  · rw [JoltISA.execProgram_instr_run_retire _ _ js js0 haddi]
    rw [JoltISA.execProgram_instr_run_retire _ _ js0 js1 handi]
    rw [JoltISA.execProgram_instr_run_retire _ _ js1 js_load hld]
  · simp [js_load, js1, js0, ea]
  · simp [js_load, js1, base]
  · simp [js_load, dword, base]

/-- Successful leading halfword store-alignment assertion followed by the
common setup block.  The assertion does not change state on the aligned path. -/
theorem assertHalfwordSetupBlockAligned (rest : JoltISA.Program)
    (imm : BitVec 12) (rs1 : regidx)
    (js : SailJoltState)
    (hpriv : Assumptions.CurPrivilegeMachine js.sail)
    (hmprv : Assumptions.MstatusMprvZero js.sail)
    (val : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (halign : load_effective_address val imm &&& (1 : BitVec 64) = 0)
    (h_base_aligned :
      AlignedDwordAccess (compute_aligned_dword_base_address val imm))
    (hbytes :
      MemBytesPresentAt js.sail (compute_aligned_dword_base_address val imm) 8)
    (hpmp :
      Assumptions.LoadPmpOk (compute_aligned_dword_base_address val imm) 8 js.sail)
    (hmmio :
      Assumptions.NotReadableMmio (compute_aligned_dword_base_address val imm) 8 js.sail) :
    ∃ js_load : SailJoltState,
      (JoltISA.execProgram
        (.instr (.VirtualAssertHalfwordAlignment rs1 imm (ExceptionType.E_SAMO_Addr_Align ())) <|
         .instr (.ADDI (.vreg JoltISA.inlineTmp0) (.xreg rs1) imm) <|
         .instr (.ANDI (.vreg JoltISA.inlineTmp1) (.vreg JoltISA.inlineTmp0) (-8 : BitVec 12)) <|
         .instr (.LD .normal (.vreg JoltISA.inlineTmp2) (.vreg JoltISA.inlineTmp1) 0) rest)).run js =
        (JoltISA.execProgram rest).run js_load ∧
      js_load.sail = js.sail ∧
      js_load.vregs JoltISA.inlineTmp0 = load_effective_address val imm ∧
      js_load.vregs JoltISA.inlineTmp1 = compute_aligned_dword_base_address val imm ∧
      js_load.vregs JoltISA.inlineTmp2 =
        loaded_dword_at js.sail (compute_aligned_dword_base_address val imm)
          hbytes h_base_aligned.no_ovf := by
  have hassert :
      (JoltISA.execInstr
        (.VirtualAssertHalfwordAlignment rs1 imm (ExceptionType.E_SAMO_Addr_Align ()))).run js =
        .ok RETIRE_SUCCESS js := by
    exact JoltISA.virtual_assert_halfword_alignment_run_aligned rs1 imm
      (ExceptionType.E_SAMO_Addr_Align ())
      js val hrx (by simpa [load_effective_address] using halign)
  rcases setupBlock rest imm rs1 js hpriv hmprv val hrx h_base_aligned hbytes hpmp hmmio with
    ⟨js_load, hrun, hsail, hv0, hv1, hv2⟩
  refine ⟨js_load, ?_, hsail, hv0, hv1, hv2⟩
  rw [JoltISA.execProgram_instr_run_retire _ _ js js hassert]
  exact hrun

/-- Successful leading word store-alignment assertion followed by the common
setup block.  The assertion does not change state on the aligned path. -/
theorem assertWordSetupBlockAligned (rest : JoltISA.Program)
    (imm : BitVec 12) (rs1 : regidx)
    (js : SailJoltState)
    (hpriv : Assumptions.CurPrivilegeMachine js.sail)
    (hmprv : Assumptions.MstatusMprvZero js.sail)
    (val : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (halign : load_effective_address val imm &&& (3 : BitVec 64) = 0)
    (h_base_aligned :
      AlignedDwordAccess (compute_aligned_dword_base_address val imm))
    (hbytes :
      MemBytesPresentAt js.sail (compute_aligned_dword_base_address val imm) 8)
    (hpmp :
      Assumptions.LoadPmpOk (compute_aligned_dword_base_address val imm) 8 js.sail)
    (hmmio :
      Assumptions.NotReadableMmio (compute_aligned_dword_base_address val imm) 8 js.sail) :
    ∃ js_load : SailJoltState,
      (JoltISA.execProgram
        (.instr (.VirtualAssertWordAlignment rs1 imm (ExceptionType.E_SAMO_Addr_Align ())) <|
         .instr (.ADDI (.vreg JoltISA.inlineTmp0) (.xreg rs1) imm) <|
         .instr (.ANDI (.vreg JoltISA.inlineTmp1) (.vreg JoltISA.inlineTmp0) (-8 : BitVec 12)) <|
         .instr (.LD .normal (.vreg JoltISA.inlineTmp2) (.vreg JoltISA.inlineTmp1) 0) rest)).run js =
        (JoltISA.execProgram rest).run js_load ∧
      js_load.sail = js.sail ∧
      js_load.vregs JoltISA.inlineTmp0 = load_effective_address val imm ∧
      js_load.vregs JoltISA.inlineTmp1 = compute_aligned_dword_base_address val imm ∧
      js_load.vregs JoltISA.inlineTmp2 =
        loaded_dword_at js.sail (compute_aligned_dword_base_address val imm)
          hbytes h_base_aligned.no_ovf := by
  have hassert :
      (JoltISA.execInstr
        (.VirtualAssertWordAlignment rs1 imm (ExceptionType.E_SAMO_Addr_Align ()))).run js =
        .ok RETIRE_SUCCESS js := by
    exact JoltISA.virtual_assert_word_alignment_run_aligned rs1 imm
      (ExceptionType.E_SAMO_Addr_Align ())
      js val hrx (by simpa [load_effective_address] using halign)
  rcases setupBlock rest imm rs1 js hpriv hmprv val hrx h_base_aligned hbytes hpmp hmmio with
    ⟨js_load, hrun, hsail, hv0, hv1, hv2⟩
  refine ⟨js_load, ?_, hsail, hv0, hv1, hv2⟩
  rw [JoltISA.execProgram_instr_run_retire _ _ js js hassert]
  exact hrun

/-- A failed halfword store-alignment assertion stops the structured program
before any read-modify-write work can occur. -/
theorem assertHalfwordBlockMisaligned (tail : JoltISA.Program)
    (imm : BitVec 12) (rs1 : regidx)
    (js : SailJoltState)
    (val : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (hmis : load_effective_address val imm &&& (1 : BitVec 64) ≠ 0) :
    (JoltISA.execProgram
      (.instr (.VirtualAssertHalfwordAlignment rs1 imm (ExceptionType.E_SAMO_Addr_Align ()))
        tail)).run js =
      .ok (ExecutionResult.Memory_Exception
        (Virtaddr (load_effective_address val imm), ExceptionType.E_SAMO_Addr_Align ())) js := by
  let e :=
    (Virtaddr (load_effective_address val imm), ExceptionType.E_SAMO_Addr_Align ())
  have hassert :
      (JoltISA.execInstr
        (.VirtualAssertHalfwordAlignment rs1 imm (ExceptionType.E_SAMO_Addr_Align ()))).run js =
        .ok (ExecutionResult.Memory_Exception e) js := by
    simpa [e, load_effective_address] using
      (JoltISA.virtual_assert_halfword_alignment_run_misaligned rs1 imm
        (ExceptionType.E_SAMO_Addr_Align ())
        js val hrx (by simpa [load_effective_address] using hmis))
  simpa [e] using
    (JoltISA.execProgram_instr_run_memory_exception
      (.VirtualAssertHalfwordAlignment rs1 imm (ExceptionType.E_SAMO_Addr_Align ()))
      tail js js e hassert)

/-- A failed word store-alignment assertion stops the structured program before
any read-modify-write work can occur. -/
theorem assertWordBlockMisaligned (tail : JoltISA.Program)
    (imm : BitVec 12) (rs1 : regidx)
    (js : SailJoltState)
    (val : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (hmis : load_effective_address val imm &&& (3 : BitVec 64) ≠ 0) :
    (JoltISA.execProgram
      (.instr (.VirtualAssertWordAlignment rs1 imm (ExceptionType.E_SAMO_Addr_Align ()))
        tail)).run js =
      .ok (ExecutionResult.Memory_Exception
        (Virtaddr (load_effective_address val imm), ExceptionType.E_SAMO_Addr_Align ())) js := by
  let e :=
    (Virtaddr (load_effective_address val imm), ExceptionType.E_SAMO_Addr_Align ())
  have hassert :
      (JoltISA.execInstr
        (.VirtualAssertWordAlignment rs1 imm (ExceptionType.E_SAMO_Addr_Align ()))).run js =
        .ok (ExecutionResult.Memory_Exception e) js := by
    simpa [e, load_effective_address] using
      (JoltISA.virtual_assert_word_alignment_run_misaligned rs1 imm
        (ExceptionType.E_SAMO_Addr_Align ())
        js val hrx (by simpa [load_effective_address] using hmis))
  simpa [e] using
    (JoltISA.execProgram_instr_run_memory_exception
      (.VirtualAssertWordAlignment rs1 imm (ExceptionType.E_SAMO_Addr_Align ()))
      tail js js e hassert)

private inductive FusedStoreWidth where
  | byte
  | halfword
  | word

private def fusedWindowInstr (width : FusedStoreWidth) : JoltISA.Instr :=
  match width with
  | .byte => .VirtualWindowMaskB (.vreg JoltISA.inlineTmp3) (.vreg JoltISA.inlineTmp0) 0
  | .halfword => .VirtualWindowMaskH (.vreg JoltISA.inlineTmp3) (.vreg JoltISA.inlineTmp0) 0
  | .word => .VirtualWindowMaskW (.vreg JoltISA.inlineTmp3) (.vreg JoltISA.inlineTmp0) 0

private def fusedShiftInstr (width : FusedStoreWidth) (rs2 : regidx) : JoltISA.Instr :=
  match width with
  | .byte => .VirtualShiftDataB (.vreg JoltISA.inlineTmp3) (.xreg rs2) (.vreg JoltISA.inlineTmp0)
  | .halfword => .VirtualShiftDataH (.vreg JoltISA.inlineTmp3) (.xreg rs2) (.vreg JoltISA.inlineTmp0)
  | .word => .VirtualShiftDataW (.vreg JoltISA.inlineTmp3) (.xreg rs2) (.vreg JoltISA.inlineTmp0)

private def fusedWindowValue (width : FusedStoreWidth) (ea : BitVec 64) : BitVec 64 :=
  match width with
  | .byte => jolt_virtual_window_mask_b_value ea 0
  | .halfword => jolt_virtual_window_mask_h_value ea 0
  | .word => jolt_virtual_window_mask_w_value ea 0

private def fusedShiftValue (width : FusedStoreWidth)
    (value ea : BitVec 64) : BitVec 64 :=
  match width with
  | .byte => jolt_virtual_shift_data_b_value value ea
  | .halfword => jolt_virtual_shift_data_h_value value ea
  | .word => jolt_virtual_shift_data_w_value value ea

private theorem fusedSpliceBlock (rest : JoltISA.Program)
    (width : FusedStoreWidth) (rs2 : regidx)
    (js js_load : SailJoltState) (ea base dword rs2_val : BitVec 64)
    (hload_sail : js_load.sail = js.sail)
    (hload_v0 : js_load.vregs JoltISA.inlineTmp0 = ea)
    (hload_v1 : js_load.vregs JoltISA.inlineTmp1 = base)
    (hload_v2 : js_load.vregs JoltISA.inlineTmp2 = dword)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2_val js.sail) :
    ∃ js_splice : SailJoltState,
      (JoltISA.execProgram
        (.instr (fusedWindowInstr width) <|
         .instr (.ANDN (.vreg JoltISA.inlineTmp2) (.vreg JoltISA.inlineTmp2)
           (.vreg JoltISA.inlineTmp3)) <|
         .instr (fusedShiftInstr width rs2) <|
         .instr (.ADD (.vreg JoltISA.inlineTmp2) (.vreg JoltISA.inlineTmp2)
           (.vreg JoltISA.inlineTmp3)) rest)).run js_load =
        (JoltISA.execProgram rest).run js_splice ∧
      js_splice.sail = js.sail ∧
      js_splice.vregs JoltISA.inlineTmp1 = base ∧
      js_splice.vregs JoltISA.inlineTmp2 =
        (dword &&& ~~~(fusedWindowValue width ea)) +
          fusedShiftValue width rs2_val ea := by
  let mask := fusedWindowValue width ea
  let shifted := fusedShiftValue width rs2_val ea
  let js_mask : SailJoltState :=
    { sail := js_load.sail
      vregs := fun r =>
        if r = JoltISA.inlineTmp3 then mask else js_load.vregs r }
  let js_clear : SailJoltState :=
    { sail := js_mask.sail
      vregs := fun r =>
        if r = JoltISA.inlineTmp2 then dword &&& ~~~mask else js_mask.vregs r }
  let js_shift : SailJoltState :=
    { sail := js_clear.sail
      vregs := fun r =>
        if r = JoltISA.inlineTmp3 then shifted else js_clear.vregs r }
  let js_splice : SailJoltState :=
    { sail := js_shift.sail
      vregs := fun r =>
        if r = JoltISA.inlineTmp2 then (dword &&& ~~~mask) + shifted
        else js_shift.vregs r }
  have hwindow :
      (JoltISA.execInstr (fusedWindowInstr width)).run js_load =
        .ok RETIRE_SUCCESS js_mask := by
    cases width with
    | byte =>
        simpa [fusedWindowInstr, fusedWindowValue, js_mask, mask, hload_v0] using
          (JoltISA.virtual_window_mask_b_run_vreg_vreg
            JoltISA.inlineTmp3 JoltISA.inlineTmp0 0 js_load
            (by unfold WritableVReg; decide))
    | halfword =>
        simpa [fusedWindowInstr, fusedWindowValue, js_mask, mask, hload_v0] using
          (JoltISA.virtual_window_mask_h_run_vreg_vreg
            JoltISA.inlineTmp3 JoltISA.inlineTmp0 0 js_load
            (by unfold WritableVReg; decide))
    | word =>
        simpa [fusedWindowInstr, fusedWindowValue, js_mask, mask, hload_v0] using
          (JoltISA.virtual_window_mask_w_run_vreg_vreg
            JoltISA.inlineTmp3 JoltISA.inlineTmp0 0 js_load
            (by unfold WritableVReg; decide))
  have handn :
      (JoltISA.execInstr
        (.ANDN (.vreg JoltISA.inlineTmp2) (.vreg JoltISA.inlineTmp2)
          (.vreg JoltISA.inlineTmp3))).run js_mask =
        .ok RETIRE_SUCCESS js_clear := by
    simpa [js_clear, js_mask, hload_v2, mask] using
      (JoltISA.andn_run_vreg_vreg_vreg JoltISA.inlineTmp2
        JoltISA.inlineTmp2 JoltISA.inlineTmp3 js_mask
        (by unfold WritableVReg; decide))
  have hrs2_clear :
      rX_bits rs2 js_clear.sail = .ok rs2_val js_clear.sail := by
    simpa [js_clear, js_mask, hload_sail] using hrs2
  have hshift :
      (JoltISA.execInstr (fusedShiftInstr width rs2)).run js_clear =
        .ok RETIRE_SUCCESS js_shift := by
    cases width with
    | byte =>
        simpa [fusedShiftInstr, fusedShiftValue, js_shift, shifted,
          js_clear, js_mask, hload_v0] using
          (JoltISA.virtual_shift_data_b_run_vreg_xreg_vreg
            JoltISA.inlineTmp3 rs2 JoltISA.inlineTmp0 js_clear rs2_val hrs2_clear
            (by unfold WritableVReg; decide))
    | halfword =>
        simpa [fusedShiftInstr, fusedShiftValue, js_shift, shifted,
          js_clear, js_mask, hload_v0] using
          (JoltISA.virtual_shift_data_h_run_vreg_xreg_vreg
            JoltISA.inlineTmp3 rs2 JoltISA.inlineTmp0 js_clear rs2_val hrs2_clear
            (by unfold WritableVReg; decide))
    | word =>
        simpa [fusedShiftInstr, fusedShiftValue, js_shift, shifted,
          js_clear, js_mask, hload_v0] using
          (JoltISA.virtual_shift_data_w_run_vreg_xreg_vreg
            JoltISA.inlineTmp3 rs2 JoltISA.inlineTmp0 js_clear rs2_val hrs2_clear
            (by unfold WritableVReg; decide))
  have hadd :
      (JoltISA.execInstr
        (.ADD (.vreg JoltISA.inlineTmp2) (.vreg JoltISA.inlineTmp2)
          (.vreg JoltISA.inlineTmp3))).run js_shift =
        .ok RETIRE_SUCCESS js_splice := by
    simpa [js_splice, js_shift, js_clear, js_mask, hload_v2, mask, shifted] using
      (JoltISA.add_run_vreg_vreg_vreg JoltISA.inlineTmp2
        JoltISA.inlineTmp2 JoltISA.inlineTmp3 js_shift
        (by unfold WritableVReg; decide))
  refine ⟨js_splice, ?_, ?_, ?_, ?_⟩
  · rw [JoltISA.execProgram_instr_run_retire _ _ js_load js_mask hwindow]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_mask js_clear handn]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_clear js_shift hshift]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_shift js_splice hadd]
  · simp [js_splice, js_shift, js_clear, js_mask, hload_sail]
  · simp [js_splice, js_shift, js_clear, js_mask, hload_v1]
  · simp [js_splice, mask, shifted]

/-- Fused byte-store mask, clear, shift, and add block. -/
theorem fusedByteSpliceBlock (rest : JoltISA.Program)
    (imm : BitVec 12) (rs2 : regidx)
    (js js_load : SailJoltState) (val rs2_val dword : BitVec 64)
    (hsetup : StoreSplice.ByteStoreFacts
      (load_effective_address val imm)
      (compute_aligned_dword_base_address val imm))
    (hload_sail : js_load.sail = js.sail)
    (hload_v0 : js_load.vregs JoltISA.inlineTmp0 = load_effective_address val imm)
    (hload_v1 : js_load.vregs JoltISA.inlineTmp1 = compute_aligned_dword_base_address val imm)
    (hload_v2 : js_load.vregs JoltISA.inlineTmp2 = dword)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2_val js.sail) :
    ∃ js_splice : SailJoltState,
      (JoltISA.execProgram
        (.instr (.VirtualWindowMaskB (.vreg JoltISA.inlineTmp3)
          (.vreg JoltISA.inlineTmp0) 0) <|
         .instr (.ANDN (.vreg JoltISA.inlineTmp2) (.vreg JoltISA.inlineTmp2)
           (.vreg JoltISA.inlineTmp3)) <|
         .instr (.VirtualShiftDataB (.vreg JoltISA.inlineTmp3) (.xreg rs2)
           (.vreg JoltISA.inlineTmp0)) <|
         .instr (.ADD (.vreg JoltISA.inlineTmp2) (.vreg JoltISA.inlineTmp2)
           (.vreg JoltISA.inlineTmp3)) rest)).run js_load =
        (JoltISA.execProgram rest).run js_splice ∧
      js_splice.sail = js.sail ∧
      js_splice.vregs JoltISA.inlineTmp1 = compute_aligned_dword_base_address val imm ∧
      js_splice.vregs JoltISA.inlineTmp2 =
        StoreSplice.byteSplice dword (Sail.BitVec.extractLsb rs2_val 7 0)
          (((load_effective_address val imm -
            compute_aligned_dword_base_address val imm).toNat) * 8) := by
  rcases fusedSpliceBlock rest .byte rs2 js js_load
      (load_effective_address val imm) (compute_aligned_dword_base_address val imm)
      dword rs2_val hload_sail hload_v0 hload_v1 hload_v2 hrs2 with
    ⟨js_splice, hrun, hsail, hv1, hv2⟩
  refine ⟨js_splice, by simpa [fusedWindowInstr, fusedShiftInstr] using hrun,
    hsail, hv1, ?_⟩
  rw [hv2]
  exact StoreSplice.fusedByteSplice_eq dword rs2_val
    (load_effective_address val imm) (compute_aligned_dword_base_address val imm) hsetup

/-- Fused halfword-store mask, clear, shift, and add block. -/
theorem fusedHalfwordSpliceBlock (rest : JoltISA.Program)
    (imm : BitVec 12) (rs2 : regidx)
    (js js_load : SailJoltState) (val rs2_val dword : BitVec 64)
    (hsetup : StoreSplice.HalfwordStoreFacts
      (load_effective_address val imm)
      (compute_aligned_dword_base_address val imm))
    (hload_sail : js_load.sail = js.sail)
    (hload_v0 : js_load.vregs JoltISA.inlineTmp0 = load_effective_address val imm)
    (hload_v1 : js_load.vregs JoltISA.inlineTmp1 = compute_aligned_dword_base_address val imm)
    (hload_v2 : js_load.vregs JoltISA.inlineTmp2 = dword)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2_val js.sail) :
    ∃ js_splice : SailJoltState,
      (JoltISA.execProgram
        (.instr (.VirtualWindowMaskH (.vreg JoltISA.inlineTmp3)
          (.vreg JoltISA.inlineTmp0) 0) <|
         .instr (.ANDN (.vreg JoltISA.inlineTmp2) (.vreg JoltISA.inlineTmp2)
           (.vreg JoltISA.inlineTmp3)) <|
         .instr (.VirtualShiftDataH (.vreg JoltISA.inlineTmp3) (.xreg rs2)
           (.vreg JoltISA.inlineTmp0)) <|
         .instr (.ADD (.vreg JoltISA.inlineTmp2) (.vreg JoltISA.inlineTmp2)
           (.vreg JoltISA.inlineTmp3)) rest)).run js_load =
        (JoltISA.execProgram rest).run js_splice ∧
      js_splice.sail = js.sail ∧
      js_splice.vregs JoltISA.inlineTmp1 = compute_aligned_dword_base_address val imm ∧
      js_splice.vregs JoltISA.inlineTmp2 =
        StoreSplice.halfwordSplice dword (Sail.BitVec.extractLsb rs2_val 15 0)
          (((load_effective_address val imm -
            compute_aligned_dword_base_address val imm).toNat) * 8) := by
  rcases fusedSpliceBlock rest .halfword rs2 js js_load
      (load_effective_address val imm) (compute_aligned_dword_base_address val imm)
      dword rs2_val hload_sail hload_v0 hload_v1 hload_v2 hrs2 with
    ⟨js_splice, hrun, hsail, hv1, hv2⟩
  refine ⟨js_splice, by simpa [fusedWindowInstr, fusedShiftInstr] using hrun,
    hsail, hv1, ?_⟩
  rw [hv2]
  exact StoreSplice.fusedHalfwordSplice_eq dword rs2_val
    (load_effective_address val imm) (compute_aligned_dword_base_address val imm) hsetup

/-- Fused word-store mask, clear, shift, and add block. -/
theorem fusedWordSpliceBlock (rest : JoltISA.Program)
    (imm : BitVec 12) (rs2 : regidx)
    (js js_load : SailJoltState) (val rs2_val dword : BitVec 64)
    (hsetup : StoreSplice.WordStoreFacts
      (load_effective_address val imm)
      (compute_aligned_dword_base_address val imm))
    (hload_sail : js_load.sail = js.sail)
    (hload_v0 : js_load.vregs JoltISA.inlineTmp0 = load_effective_address val imm)
    (hload_v1 : js_load.vregs JoltISA.inlineTmp1 = compute_aligned_dword_base_address val imm)
    (hload_v2 : js_load.vregs JoltISA.inlineTmp2 = dword)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2_val js.sail) :
    ∃ js_splice : SailJoltState,
      (JoltISA.execProgram
        (.instr (.VirtualWindowMaskW (.vreg JoltISA.inlineTmp3)
          (.vreg JoltISA.inlineTmp0) 0) <|
         .instr (.ANDN (.vreg JoltISA.inlineTmp2) (.vreg JoltISA.inlineTmp2)
           (.vreg JoltISA.inlineTmp3)) <|
         .instr (.VirtualShiftDataW (.vreg JoltISA.inlineTmp3) (.xreg rs2)
           (.vreg JoltISA.inlineTmp0)) <|
         .instr (.ADD (.vreg JoltISA.inlineTmp2) (.vreg JoltISA.inlineTmp2)
           (.vreg JoltISA.inlineTmp3)) rest)).run js_load =
        (JoltISA.execProgram rest).run js_splice ∧
      js_splice.sail = js.sail ∧
      js_splice.vregs JoltISA.inlineTmp1 = compute_aligned_dword_base_address val imm ∧
      js_splice.vregs JoltISA.inlineTmp2 =
        StoreSplice.wordSplice dword (Sail.BitVec.extractLsb rs2_val 31 0)
          (((load_effective_address val imm -
            compute_aligned_dword_base_address val imm).toNat) * 8) := by
  rcases fusedSpliceBlock rest .word rs2 js js_load
      (load_effective_address val imm) (compute_aligned_dword_base_address val imm)
      dword rs2_val hload_sail hload_v0 hload_v1 hload_v2 hrs2 with
    ⟨js_splice, hrun, hsail, hv1, hv2⟩
  refine ⟨js_splice, by simpa [fusedWindowInstr, fusedShiftInstr] using hrun,
    hsail, hv1, ?_⟩
  rw [hv2]
  exact StoreSplice.fusedWordSplice_eq dword rs2_val
    (load_effective_address val imm) (compute_aligned_dword_base_address val imm) hsetup

/-- Byte-store splice block.

Starting from the setup boundary (`v0 = ea`, `v1 = base`, `v2 = dword`), the
Rust-faithful `SB` middle sequence materializes a one-byte mask, shifts the low
byte of `rs2` into the target lane, and leaves the spliced dword in `v2`. -/
theorem byteSpliceBlock (rest : JoltISA.Program)
    (imm : BitVec 12) (rs2 : regidx)
    (js js_load : SailJoltState) (val rs2_val dword : BitVec 64)
    (hsetup : StoreSplice.ByteStoreFacts
      (load_effective_address val imm)
      (compute_aligned_dword_base_address val imm))
    (hload_sail : js_load.sail = js.sail)
    (hload_v0 : js_load.vregs JoltISA.inlineTmp0 = load_effective_address val imm)
    (hload_v1 : js_load.vregs JoltISA.inlineTmp1 = compute_aligned_dword_base_address val imm)
    (hload_v2 : js_load.vregs JoltISA.inlineTmp2 = dword)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2_val js.sail) :
    ∃ js_splice : SailJoltState,
      (JoltISA.execProgram
        (JoltISA.slliBlock (.vreg JoltISA.inlineTmp3) (.vreg JoltISA.inlineTmp0) (3 : BitVec 6) <|
         .instr (.LUI (.vreg JoltISA.inlineTmp0) (0xff : BitVec 64)) <|
         JoltISA.sllBlock (.vreg JoltISA.inlineTmp0) (.vreg JoltISA.inlineTmp0) (.vreg JoltISA.inlineTmp3) JoltISA.inlineTmp4 <|
         JoltISA.sllBlock (.vreg JoltISA.inlineTmp3) (.xreg rs2) (.vreg JoltISA.inlineTmp3) JoltISA.inlineTmp4 <|
         .instr (.XOR (.vreg JoltISA.inlineTmp3) (.vreg JoltISA.inlineTmp2) (.vreg JoltISA.inlineTmp3)) <|
         .instr (.AND (.vreg JoltISA.inlineTmp3) (.vreg JoltISA.inlineTmp3) (.vreg JoltISA.inlineTmp0)) <|
         .instr (.XOR (.vreg JoltISA.inlineTmp2) (.vreg JoltISA.inlineTmp2) (.vreg JoltISA.inlineTmp3)) rest)).run js_load =
        (JoltISA.execProgram rest).run js_splice ∧
      js_splice.sail = js.sail ∧
      js_splice.vregs JoltISA.inlineTmp1 = compute_aligned_dword_base_address val imm ∧
      js_splice.vregs JoltISA.inlineTmp2 =
        StoreSplice.byteSplice
          dword (Sail.BitVec.extractLsb rs2_val 7 0)
          (((load_effective_address val imm -
              compute_aligned_dword_base_address val imm).toNat) * 8) := by
  let ea := load_effective_address val imm
  let base := compute_aligned_dword_base_address val imm
  let shift64 := shift_bits_left ea (3 : BitVec 6)
  let shift6 := Sail.BitVec.extractLsb shift64 5 0
  let mask := shift_bits_left (0x00000000000000FF : BitVec 64) shift6
  let shifted := shift_bits_left rs2_val shift6
  let xored := dword ^^^ shifted
  let masked := xored &&& mask
  let spliced :=
    StoreSplice.byteSplice dword (Sail.BitVec.extractLsb rs2_val 7 0) (((ea - base).toNat) * 8)
  let js_slli : SailJoltState :=
    { sail := js_load.sail
      vregs := fun r =>
        if r = JoltISA.inlineTmp3 then
          shift_bits_left (js_load.vregs JoltISA.inlineTmp0) (3 : BitVec 6)
        else js_load.vregs r }
  let js_lui : SailJoltState :=
    { sail := js_slli.sail
      vregs := fun r => if r = JoltISA.inlineTmp0 then (0xff : BitVec 64) else js_slli.vregs r }
  let js_mask : SailJoltState :=
    { sail := js_lui.sail
      vregs := fun r =>
        if r = JoltISA.inlineTmp0 then
          shift_bits_left (js_lui.vregs JoltISA.inlineTmp0)
            (Sail.BitVec.extractLsb (js_lui.vregs JoltISA.inlineTmp3) 5 0)
        else if r = JoltISA.inlineTmp4 then
          jolt_virtual_pow2_value (js_lui.vregs JoltISA.inlineTmp3)
        else js_lui.vregs r }
  let js_shift : SailJoltState :=
    { sail := js_mask.sail
      vregs := fun r =>
        if r = JoltISA.inlineTmp3 then
          shift_bits_left rs2_val
            (Sail.BitVec.extractLsb (js_mask.vregs JoltISA.inlineTmp3) 5 0)
        else if r = JoltISA.inlineTmp4 then
          jolt_virtual_pow2_value (js_mask.vregs JoltISA.inlineTmp3)
        else js_mask.vregs r }
  let js_xor : SailJoltState :=
    { sail := js_shift.sail
      vregs := fun r =>
        if r = JoltISA.inlineTmp3 then
          js_shift.vregs JoltISA.inlineTmp2 ^^^ js_shift.vregs JoltISA.inlineTmp3
        else js_shift.vregs r }
  let js_and : SailJoltState :=
    { sail := js_xor.sail
      vregs := fun r =>
        if r = JoltISA.inlineTmp3 then
          js_xor.vregs JoltISA.inlineTmp3 &&& js_xor.vregs JoltISA.inlineTmp0
        else js_xor.vregs r }
  let js_splice : SailJoltState :=
    { sail := js_and.sail
      vregs := fun r =>
        if r = JoltISA.inlineTmp2 then
          js_and.vregs JoltISA.inlineTmp2 ^^^ js_and.vregs JoltISA.inlineTmp3
        else js_and.vregs r }
  have hslli :
      (JoltISA.execInstr
        (.VirtualMULI (.vreg JoltISA.inlineTmp3) (.vreg JoltISA.inlineTmp0) (JoltISA.slliMultiplier (3 : BitVec 6)))).run js_load =
        .ok RETIRE_SUCCESS js_slli := by
    have h_value :
        jolt_virtual_muli_value (js_load.vregs JoltISA.inlineTmp0)
          (JoltISA.slliMultiplier (3 : BitVec 6)) =
          shift_bits_left (js_load.vregs JoltISA.inlineTmp0) (3 : BitVec 6) :=
      JoltISA.slli_block_value_eq (js_load.vregs JoltISA.inlineTmp0) (3 : BitVec 6)
    rw [JoltISA.virtual_muli_run_vreg_vreg JoltISA.inlineTmp3 JoltISA.inlineTmp0
      (JoltISA.slliMultiplier (3 : BitVec 6)) js_load
      (by unfold WritableVReg; decide)]
    simp [js_slli]
    funext r
    by_cases hr : r = JoltISA.inlineTmp3
    · subst r
      exact h_value
    · rw [if_neg hr, if_neg hr]
  have hslli_run : ∀ tail,
      (JoltISA.execProgram
        (JoltISA.slliBlock (.vreg JoltISA.inlineTmp3) (.vreg JoltISA.inlineTmp0) (3 : BitVec 6) tail)).run js_load =
      (JoltISA.execProgram tail).run js_slli := by
    intro tail
    unfold JoltISA.slliBlock
    rw [JoltISA.execProgram_instr_run_retire _ _ js_load js_slli hslli]
  have hslli_v3 : js_slli.vregs JoltISA.inlineTmp3 = shift64 := by
    change shift_bits_left (js_load.vregs JoltISA.inlineTmp0) (3 : BitVec 6) = shift64
    rw [hload_v0]
  have hlui :
      (JoltISA.execInstr (.LUI (.vreg JoltISA.inlineTmp0) (0xff : BitVec 64))).run js_slli =
        .ok RETIRE_SUCCESS js_lui := by
    simpa [js_lui] using
      (JoltISA.execInstr_lui_vreg_run JoltISA.inlineTmp0 (0xff : BitVec 64) js_slli
        (by unfold WritableVReg; decide))
  have hlui_v3 : js_lui.vregs JoltISA.inlineTmp3 = shift64 := by
    change js_slli.vregs JoltISA.inlineTmp3 = shift64
    exact hslli_v3
  let js_mask_pow2 : SailJoltState :=
    { sail := js_lui.sail
      vregs := fun r =>
        if r = JoltISA.inlineTmp4 then
          jolt_virtual_pow2_value (js_lui.vregs JoltISA.inlineTmp3)
        else js_lui.vregs r }
  have hpow2_mask :
      (JoltISA.execInstr (.VirtualPow2 (.vreg JoltISA.inlineTmp4) (.vreg JoltISA.inlineTmp3))).run js_lui =
        .ok RETIRE_SUCCESS js_mask_pow2 := by
    simpa [js_mask_pow2] using
      (JoltISA.virtual_pow2_run_vreg_vreg JoltISA.inlineTmp4 JoltISA.inlineTmp3 js_lui
        (by unfold WritableVReg; decide))
  have hmul_mask :
      (JoltISA.execInstr (.MUL (.vreg JoltISA.inlineTmp0) (.vreg JoltISA.inlineTmp0) (.vreg JoltISA.inlineTmp4))).run js_mask_pow2 =
        .ok RETIRE_SUCCESS js_mask := by
    simpa [js_mask, js_mask_pow2, JoltISA.mul_jolt_virtual_pow2_value_eq_shift_bits_left] using
      (JoltISA.mul_run_vreg_vreg_vreg JoltISA.inlineTmp0 JoltISA.inlineTmp0
        JoltISA.inlineTmp4 js_mask_pow2 (by unfold WritableVReg; decide))
  have hsll_mask_run : ∀ tail,
      (JoltISA.execProgram
        (JoltISA.sllBlock (.vreg JoltISA.inlineTmp0) (.vreg JoltISA.inlineTmp0) (.vreg JoltISA.inlineTmp3) JoltISA.inlineTmp4 tail)).run
          js_lui =
      (JoltISA.execProgram tail).run js_mask := by
    intro tail
    unfold JoltISA.sllBlock
    rw [JoltISA.execProgram_instr_run_retire _ _ js_lui js_mask_pow2 hpow2_mask]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_mask_pow2 js_mask hmul_mask]
  have hmask_v0 : js_mask.vregs JoltISA.inlineTmp0 = mask := by
    change shift_bits_left (js_lui.vregs JoltISA.inlineTmp0)
      (Sail.BitVec.extractLsb (js_lui.vregs JoltISA.inlineTmp3) 5 0) = mask
    rw [hlui_v3]
    simp [js_lui, mask, shift6, shift64]
  have hmask_v3 : js_mask.vregs JoltISA.inlineTmp3 = shift64 := by
    change js_lui.vregs JoltISA.inlineTmp3 = shift64
    exact hlui_v3
  have hrs2_mask : rX_bits rs2 js_mask.sail = .ok rs2_val js_mask.sail := by
    simpa [js_mask, js_lui, js_slli, hload_sail] using hrs2
  let js_shift_pow2 : SailJoltState :=
    { sail := js_mask.sail
      vregs := fun r =>
        if r = JoltISA.inlineTmp4 then
          jolt_virtual_pow2_value (js_mask.vregs JoltISA.inlineTmp3)
        else js_mask.vregs r }
  have hpow2_value :
      (JoltISA.execInstr (.VirtualPow2 (.vreg JoltISA.inlineTmp4) (.vreg JoltISA.inlineTmp3))).run js_mask =
        .ok RETIRE_SUCCESS js_shift_pow2 := by
    simpa [js_shift_pow2] using
      (JoltISA.virtual_pow2_run_vreg_vreg JoltISA.inlineTmp4 JoltISA.inlineTmp3 js_mask
        (by unfold WritableVReg; decide))
  have hrs2_shift_pow2 : rX_bits rs2 js_shift_pow2.sail = .ok rs2_val js_shift_pow2.sail := by
    exact hrs2_mask
  have hmul_value :
      (JoltISA.execInstr (.MUL (.vreg JoltISA.inlineTmp3) (.xreg rs2) (.vreg JoltISA.inlineTmp4))).run js_shift_pow2 =
        .ok RETIRE_SUCCESS js_shift := by
    simpa [js_shift, js_shift_pow2, JoltISA.mul_jolt_virtual_pow2_value_eq_shift_bits_left] using
      (JoltISA.mul_run_vreg_xreg_vreg JoltISA.inlineTmp3 rs2
        JoltISA.inlineTmp4 js_shift_pow2 rs2_val hrs2_shift_pow2
        (by unfold WritableVReg; decide))
  have hsll_value_run : ∀ tail,
      (JoltISA.execProgram
        (JoltISA.sllBlock (.vreg JoltISA.inlineTmp3) (.xreg rs2) (.vreg JoltISA.inlineTmp3) JoltISA.inlineTmp4 tail)).run
          js_mask =
      (JoltISA.execProgram tail).run js_shift := by
    intro tail
    unfold JoltISA.sllBlock
    rw [JoltISA.execProgram_instr_run_retire _ _ js_mask js_shift_pow2 hpow2_value]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_shift_pow2 js_shift hmul_value]
  have hshift_v0 : js_shift.vregs JoltISA.inlineTmp0 = mask := by
    change js_mask.vregs JoltISA.inlineTmp0 = mask
    exact hmask_v0
  have hshift_v2 : js_shift.vregs JoltISA.inlineTmp2 = dword := by
    change js_mask.vregs JoltISA.inlineTmp2 = dword
    change js_lui.vregs JoltISA.inlineTmp2 = dword
    change js_slli.vregs JoltISA.inlineTmp2 = dword
    change js_load.vregs JoltISA.inlineTmp2 = dword
    exact hload_v2
  have hshift_v3 : js_shift.vregs JoltISA.inlineTmp3 = shifted := by
    change shift_bits_left rs2_val
      (Sail.BitVec.extractLsb (js_mask.vregs JoltISA.inlineTmp3) 5 0) = shifted
    rw [hmask_v3]
  have hxor1 :
      (JoltISA.execInstr (.XOR (.vreg JoltISA.inlineTmp3) (.vreg JoltISA.inlineTmp2) (.vreg JoltISA.inlineTmp3))).run js_shift =
        .ok RETIRE_SUCCESS js_xor := by
    simpa [js_xor] using
      (JoltISA.xor_run_vreg_vreg_vreg JoltISA.inlineTmp3 JoltISA.inlineTmp2
        JoltISA.inlineTmp3 js_shift (by unfold WritableVReg; decide))
  have hxor_v0 : js_xor.vregs JoltISA.inlineTmp0 = mask := by
    change js_shift.vregs JoltISA.inlineTmp0 = mask
    exact hshift_v0
  have hxor_v2 : js_xor.vregs JoltISA.inlineTmp2 = dword := by
    change js_shift.vregs JoltISA.inlineTmp2 = dword
    exact hshift_v2
  have hxor_v3 : js_xor.vregs JoltISA.inlineTmp3 = xored := by
    change js_shift.vregs JoltISA.inlineTmp2 ^^^ js_shift.vregs JoltISA.inlineTmp3 = xored
    rw [hshift_v2, hshift_v3]
  have hand :
      (JoltISA.execInstr (.AND (.vreg JoltISA.inlineTmp3) (.vreg JoltISA.inlineTmp3) (.vreg JoltISA.inlineTmp0))).run js_xor =
        .ok RETIRE_SUCCESS js_and := by
    simpa [js_and] using
      (JoltISA.execInstr_and_vreg_vreg_vreg_run JoltISA.inlineTmp3 JoltISA.inlineTmp3
        JoltISA.inlineTmp0 js_xor (by unfold WritableVReg; decide))
  have hand_v2 : js_and.vregs JoltISA.inlineTmp2 = dword := by
    change js_xor.vregs JoltISA.inlineTmp2 = dword
    exact hxor_v2
  have hand_v3 : js_and.vregs JoltISA.inlineTmp3 = masked := by
    change js_xor.vregs JoltISA.inlineTmp3 &&& js_xor.vregs JoltISA.inlineTmp0 = masked
    rw [hxor_v3, hxor_v0]
  have hshift6 :
      shift6 = BitVec.ofNat 6 (((ea - base).toNat) * 8) := by
    simpa [shift6, shift64, ea, base] using shift6_eq_of_offset_byte ea base hsetup
  have hspliced : dword ^^^ masked = spliced := by
    dsimp [masked, xored, shifted, mask, spliced]
    rw [hshift6]
    simpa using
      byteSplice_eq_sequence dword rs2_val ((ea - base).toNat)
        hsetup.byte_offset_cases
  have hxor2 :
      (JoltISA.execInstr (.XOR (.vreg JoltISA.inlineTmp2) (.vreg JoltISA.inlineTmp2) (.vreg JoltISA.inlineTmp3))).run js_and =
        .ok RETIRE_SUCCESS js_splice := by
    simpa [js_splice] using
      (JoltISA.xor_run_vreg_vreg_vreg JoltISA.inlineTmp2 JoltISA.inlineTmp2
        JoltISA.inlineTmp3 js_and (by unfold WritableVReg; decide))
  refine ⟨js_splice, ?_, ?_, ?_, ?_⟩
  · rw [hslli_run]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_slli js_lui hlui]
    rw [hsll_mask_run]
    rw [hsll_value_run]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_shift js_xor hxor1]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_xor js_and hand]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_and js_splice hxor2]
  · simp [js_splice, js_and, js_xor, js_shift, js_mask, js_lui, js_slli, hload_sail]
  · change js_load.vregs JoltISA.inlineTmp1 = compute_aligned_dword_base_address val imm
    exact hload_v1
  · change js_and.vregs JoltISA.inlineTmp2 ^^^ js_and.vregs JoltISA.inlineTmp3 = spliced
    rw [hand_v2, hand_v3]
    exact hspliced

/-- Halfword-store splice block.

This is the same instruction skeleton as `byteSpliceBlock`, with a two-byte
mask (`0xffff`) and the halfword setup facts.  The theorem boundary says only
what later phases need: `v1` still holds the dword base and `v2` now holds the
pure halfword splice. -/
theorem halfwordSpliceBlock (rest : JoltISA.Program)
    (imm : BitVec 12) (rs2 : regidx)
    (js js_load : SailJoltState) (val rs2_val dword : BitVec 64)
    (hsetup : StoreSplice.HalfwordStoreFacts
      (load_effective_address val imm)
      (compute_aligned_dword_base_address val imm))
    (hload_sail : js_load.sail = js.sail)
    (hload_v0 : js_load.vregs JoltISA.inlineTmp0 = load_effective_address val imm)
    (hload_v1 : js_load.vregs JoltISA.inlineTmp1 = compute_aligned_dword_base_address val imm)
    (hload_v2 : js_load.vregs JoltISA.inlineTmp2 = dword)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2_val js.sail) :
    ∃ js_splice : SailJoltState,
      (JoltISA.execProgram
        (JoltISA.slliBlock (.vreg JoltISA.inlineTmp3) (.vreg JoltISA.inlineTmp0) (3 : BitVec 6) <|
         .instr (.LUI (.vreg JoltISA.inlineTmp0) (0xffff : BitVec 64)) <|
         JoltISA.sllBlock (.vreg JoltISA.inlineTmp0) (.vreg JoltISA.inlineTmp0) (.vreg JoltISA.inlineTmp3) JoltISA.inlineTmp4 <|
         JoltISA.sllBlock (.vreg JoltISA.inlineTmp3) (.xreg rs2) (.vreg JoltISA.inlineTmp3) JoltISA.inlineTmp4 <|
         .instr (.XOR (.vreg JoltISA.inlineTmp3) (.vreg JoltISA.inlineTmp2) (.vreg JoltISA.inlineTmp3)) <|
         .instr (.AND (.vreg JoltISA.inlineTmp3) (.vreg JoltISA.inlineTmp3) (.vreg JoltISA.inlineTmp0)) <|
         .instr (.XOR (.vreg JoltISA.inlineTmp2) (.vreg JoltISA.inlineTmp2) (.vreg JoltISA.inlineTmp3)) rest)).run js_load =
        (JoltISA.execProgram rest).run js_splice ∧
      js_splice.sail = js.sail ∧
      js_splice.vregs JoltISA.inlineTmp1 = compute_aligned_dword_base_address val imm ∧
      js_splice.vregs JoltISA.inlineTmp2 =
        StoreSplice.halfwordSplice
          dword (Sail.BitVec.extractLsb rs2_val 15 0)
          (((load_effective_address val imm -
              compute_aligned_dword_base_address val imm).toNat) * 8) := by
  let ea := load_effective_address val imm
  let base := compute_aligned_dword_base_address val imm
  let shift64 := shift_bits_left ea (3 : BitVec 6)
  let shift6 := Sail.BitVec.extractLsb shift64 5 0
  let mask := shift_bits_left (0x000000000000FFFF : BitVec 64) shift6
  let shifted := shift_bits_left rs2_val shift6
  let xored := dword ^^^ shifted
  let masked := xored &&& mask
  let spliced :=
    StoreSplice.halfwordSplice dword (Sail.BitVec.extractLsb rs2_val 15 0)
      (((ea - base).toNat) * 8)
  let js_slli : SailJoltState :=
    { sail := js_load.sail
      vregs := fun r =>
        if r = JoltISA.inlineTmp3 then
          shift_bits_left (js_load.vregs JoltISA.inlineTmp0) (3 : BitVec 6)
        else js_load.vregs r }
  let js_lui : SailJoltState :=
    { sail := js_slli.sail
      vregs := fun r => if r = JoltISA.inlineTmp0 then (0xffff : BitVec 64) else js_slli.vregs r }
  let js_mask : SailJoltState :=
    { sail := js_lui.sail
      vregs := fun r =>
        if r = JoltISA.inlineTmp0 then
          shift_bits_left (js_lui.vregs JoltISA.inlineTmp0)
            (Sail.BitVec.extractLsb (js_lui.vregs JoltISA.inlineTmp3) 5 0)
        else if r = JoltISA.inlineTmp4 then
          jolt_virtual_pow2_value (js_lui.vregs JoltISA.inlineTmp3)
        else js_lui.vregs r }
  let js_shift : SailJoltState :=
    { sail := js_mask.sail
      vregs := fun r =>
        if r = JoltISA.inlineTmp3 then
          shift_bits_left rs2_val
            (Sail.BitVec.extractLsb (js_mask.vregs JoltISA.inlineTmp3) 5 0)
        else if r = JoltISA.inlineTmp4 then
          jolt_virtual_pow2_value (js_mask.vregs JoltISA.inlineTmp3)
        else js_mask.vregs r }
  let js_xor : SailJoltState :=
    { sail := js_shift.sail
      vregs := fun r =>
        if r = JoltISA.inlineTmp3 then
          js_shift.vregs JoltISA.inlineTmp2 ^^^ js_shift.vregs JoltISA.inlineTmp3
        else js_shift.vregs r }
  let js_and : SailJoltState :=
    { sail := js_xor.sail
      vregs := fun r =>
        if r = JoltISA.inlineTmp3 then
          js_xor.vregs JoltISA.inlineTmp3 &&& js_xor.vregs JoltISA.inlineTmp0
        else js_xor.vregs r }
  let js_splice : SailJoltState :=
    { sail := js_and.sail
      vregs := fun r =>
        if r = JoltISA.inlineTmp2 then
          js_and.vregs JoltISA.inlineTmp2 ^^^ js_and.vregs JoltISA.inlineTmp3
        else js_and.vregs r }
  have hslli :
      (JoltISA.execInstr
        (.VirtualMULI (.vreg JoltISA.inlineTmp3) (.vreg JoltISA.inlineTmp0) (JoltISA.slliMultiplier (3 : BitVec 6)))).run js_load =
        .ok RETIRE_SUCCESS js_slli := by
    have h_value :
        jolt_virtual_muli_value (js_load.vregs JoltISA.inlineTmp0)
          (JoltISA.slliMultiplier (3 : BitVec 6)) =
          shift_bits_left (js_load.vregs JoltISA.inlineTmp0) (3 : BitVec 6) :=
      JoltISA.slli_block_value_eq (js_load.vregs JoltISA.inlineTmp0) (3 : BitVec 6)
    rw [JoltISA.virtual_muli_run_vreg_vreg JoltISA.inlineTmp3 JoltISA.inlineTmp0
      (JoltISA.slliMultiplier (3 : BitVec 6)) js_load
      (by unfold WritableVReg; decide)]
    simp [js_slli]
    funext r
    by_cases hr : r = JoltISA.inlineTmp3
    · subst r
      exact h_value
    · rw [if_neg hr, if_neg hr]
  have hslli_run : ∀ tail,
      (JoltISA.execProgram
        (JoltISA.slliBlock (.vreg JoltISA.inlineTmp3) (.vreg JoltISA.inlineTmp0) (3 : BitVec 6) tail)).run js_load =
      (JoltISA.execProgram tail).run js_slli := by
    intro tail
    unfold JoltISA.slliBlock
    rw [JoltISA.execProgram_instr_run_retire _ _ js_load js_slli hslli]
  have hslli_v3 : js_slli.vregs JoltISA.inlineTmp3 = shift64 := by
    change shift_bits_left (js_load.vregs JoltISA.inlineTmp0) (3 : BitVec 6) = shift64
    rw [hload_v0]
  have hlui :
      (JoltISA.execInstr (.LUI (.vreg JoltISA.inlineTmp0) (0xffff : BitVec 64))).run js_slli =
        .ok RETIRE_SUCCESS js_lui := by
    simpa [js_lui] using
      (JoltISA.execInstr_lui_vreg_run JoltISA.inlineTmp0 (0xffff : BitVec 64) js_slli
        (by unfold WritableVReg; decide))
  have hlui_v3 : js_lui.vregs JoltISA.inlineTmp3 = shift64 := by
    change js_slli.vregs JoltISA.inlineTmp3 = shift64
    exact hslli_v3
  let js_mask_pow2 : SailJoltState :=
    { sail := js_lui.sail
      vregs := fun r =>
        if r = JoltISA.inlineTmp4 then
          jolt_virtual_pow2_value (js_lui.vregs JoltISA.inlineTmp3)
        else js_lui.vregs r }
  have hpow2_mask :
      (JoltISA.execInstr (.VirtualPow2 (.vreg JoltISA.inlineTmp4) (.vreg JoltISA.inlineTmp3))).run js_lui =
        .ok RETIRE_SUCCESS js_mask_pow2 := by
    simpa [js_mask_pow2] using
      (JoltISA.virtual_pow2_run_vreg_vreg JoltISA.inlineTmp4 JoltISA.inlineTmp3 js_lui
        (by unfold WritableVReg; decide))
  have hmul_mask :
      (JoltISA.execInstr (.MUL (.vreg JoltISA.inlineTmp0) (.vreg JoltISA.inlineTmp0) (.vreg JoltISA.inlineTmp4))).run js_mask_pow2 =
        .ok RETIRE_SUCCESS js_mask := by
    simpa [js_mask, js_mask_pow2, JoltISA.mul_jolt_virtual_pow2_value_eq_shift_bits_left] using
      (JoltISA.mul_run_vreg_vreg_vreg JoltISA.inlineTmp0 JoltISA.inlineTmp0
        JoltISA.inlineTmp4 js_mask_pow2 (by unfold WritableVReg; decide))
  have hsll_mask_run : ∀ tail,
      (JoltISA.execProgram
        (JoltISA.sllBlock (.vreg JoltISA.inlineTmp0) (.vreg JoltISA.inlineTmp0) (.vreg JoltISA.inlineTmp3) JoltISA.inlineTmp4 tail)).run
          js_lui =
      (JoltISA.execProgram tail).run js_mask := by
    intro tail
    unfold JoltISA.sllBlock
    rw [JoltISA.execProgram_instr_run_retire _ _ js_lui js_mask_pow2 hpow2_mask]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_mask_pow2 js_mask hmul_mask]
  have hmask_v0 : js_mask.vregs JoltISA.inlineTmp0 = mask := by
    change shift_bits_left (js_lui.vregs JoltISA.inlineTmp0)
      (Sail.BitVec.extractLsb (js_lui.vregs JoltISA.inlineTmp3) 5 0) = mask
    rw [hlui_v3]
    simp [js_lui, mask, shift6, shift64]
  have hmask_v3 : js_mask.vregs JoltISA.inlineTmp3 = shift64 := by
    change js_lui.vregs JoltISA.inlineTmp3 = shift64
    exact hlui_v3
  have hrs2_mask : rX_bits rs2 js_mask.sail = .ok rs2_val js_mask.sail := by
    simpa [js_mask, js_lui, js_slli, hload_sail] using hrs2
  let js_shift_pow2 : SailJoltState :=
    { sail := js_mask.sail
      vregs := fun r =>
        if r = JoltISA.inlineTmp4 then
          jolt_virtual_pow2_value (js_mask.vregs JoltISA.inlineTmp3)
        else js_mask.vregs r }
  have hpow2_value :
      (JoltISA.execInstr (.VirtualPow2 (.vreg JoltISA.inlineTmp4) (.vreg JoltISA.inlineTmp3))).run js_mask =
        .ok RETIRE_SUCCESS js_shift_pow2 := by
    simpa [js_shift_pow2] using
      (JoltISA.virtual_pow2_run_vreg_vreg JoltISA.inlineTmp4 JoltISA.inlineTmp3 js_mask
        (by unfold WritableVReg; decide))
  have hrs2_shift_pow2 : rX_bits rs2 js_shift_pow2.sail = .ok rs2_val js_shift_pow2.sail := by
    exact hrs2_mask
  have hmul_value :
      (JoltISA.execInstr (.MUL (.vreg JoltISA.inlineTmp3) (.xreg rs2) (.vreg JoltISA.inlineTmp4))).run js_shift_pow2 =
        .ok RETIRE_SUCCESS js_shift := by
    simpa [js_shift, js_shift_pow2, JoltISA.mul_jolt_virtual_pow2_value_eq_shift_bits_left] using
      (JoltISA.mul_run_vreg_xreg_vreg JoltISA.inlineTmp3 rs2
        JoltISA.inlineTmp4 js_shift_pow2 rs2_val hrs2_shift_pow2
        (by unfold WritableVReg; decide))
  have hsll_value_run : ∀ tail,
      (JoltISA.execProgram
        (JoltISA.sllBlock (.vreg JoltISA.inlineTmp3) (.xreg rs2) (.vreg JoltISA.inlineTmp3) JoltISA.inlineTmp4 tail)).run
          js_mask =
      (JoltISA.execProgram tail).run js_shift := by
    intro tail
    unfold JoltISA.sllBlock
    rw [JoltISA.execProgram_instr_run_retire _ _ js_mask js_shift_pow2 hpow2_value]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_shift_pow2 js_shift hmul_value]
  have hshift_v0 : js_shift.vregs JoltISA.inlineTmp0 = mask := by
    change js_mask.vregs JoltISA.inlineTmp0 = mask
    exact hmask_v0
  have hshift_v2 : js_shift.vregs JoltISA.inlineTmp2 = dword := by
    change js_mask.vregs JoltISA.inlineTmp2 = dword
    change js_lui.vregs JoltISA.inlineTmp2 = dword
    change js_slli.vregs JoltISA.inlineTmp2 = dword
    change js_load.vregs JoltISA.inlineTmp2 = dword
    exact hload_v2
  have hshift_v3 : js_shift.vregs JoltISA.inlineTmp3 = shifted := by
    change shift_bits_left rs2_val
      (Sail.BitVec.extractLsb (js_mask.vregs JoltISA.inlineTmp3) 5 0) = shifted
    rw [hmask_v3]
  have hxor1 :
      (JoltISA.execInstr (.XOR (.vreg JoltISA.inlineTmp3) (.vreg JoltISA.inlineTmp2) (.vreg JoltISA.inlineTmp3))).run js_shift =
        .ok RETIRE_SUCCESS js_xor := by
    simpa [js_xor] using
      (JoltISA.xor_run_vreg_vreg_vreg JoltISA.inlineTmp3 JoltISA.inlineTmp2
        JoltISA.inlineTmp3 js_shift (by unfold WritableVReg; decide))
  have hxor_v0 : js_xor.vregs JoltISA.inlineTmp0 = mask := by
    change js_shift.vregs JoltISA.inlineTmp0 = mask
    exact hshift_v0
  have hxor_v2 : js_xor.vregs JoltISA.inlineTmp2 = dword := by
    change js_shift.vregs JoltISA.inlineTmp2 = dword
    exact hshift_v2
  have hxor_v3 : js_xor.vregs JoltISA.inlineTmp3 = xored := by
    change js_shift.vregs JoltISA.inlineTmp2 ^^^ js_shift.vregs JoltISA.inlineTmp3 = xored
    rw [hshift_v2, hshift_v3]
  have hand :
      (JoltISA.execInstr (.AND (.vreg JoltISA.inlineTmp3) (.vreg JoltISA.inlineTmp3) (.vreg JoltISA.inlineTmp0))).run js_xor =
        .ok RETIRE_SUCCESS js_and := by
    simpa [js_and] using
      (JoltISA.execInstr_and_vreg_vreg_vreg_run JoltISA.inlineTmp3 JoltISA.inlineTmp3
        JoltISA.inlineTmp0 js_xor (by unfold WritableVReg; decide))
  have hand_v2 : js_and.vregs JoltISA.inlineTmp2 = dword := by
    change js_xor.vregs JoltISA.inlineTmp2 = dword
    exact hxor_v2
  have hand_v3 : js_and.vregs JoltISA.inlineTmp3 = masked := by
    change js_xor.vregs JoltISA.inlineTmp3 &&& js_xor.vregs JoltISA.inlineTmp0 = masked
    rw [hxor_v3, hxor_v0]
  have hshift6 :
      shift6 = BitVec.ofNat 6 (((ea - base).toNat) * 8) := by
    simpa [shift6, shift64, ea, base] using shift6_eq_of_offset_halfword ea base hsetup
  have hspliced : dword ^^^ masked = spliced := by
    dsimp [masked, xored, shifted, mask, spliced]
    rw [hshift6]
    simpa using
      halfwordSplice_eq_sequence dword rs2_val ((ea - base).toNat)
        hsetup.halfword_offset_cases
  have hxor2 :
      (JoltISA.execInstr (.XOR (.vreg JoltISA.inlineTmp2) (.vreg JoltISA.inlineTmp2) (.vreg JoltISA.inlineTmp3))).run js_and =
        .ok RETIRE_SUCCESS js_splice := by
    simpa [js_splice] using
      (JoltISA.xor_run_vreg_vreg_vreg JoltISA.inlineTmp2 JoltISA.inlineTmp2
        JoltISA.inlineTmp3 js_and (by unfold WritableVReg; decide))
  refine ⟨js_splice, ?_, ?_, ?_, ?_⟩
  · rw [hslli_run]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_slli js_lui hlui]
    rw [hsll_mask_run]
    rw [hsll_value_run]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_shift js_xor hxor1]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_xor js_and hand]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_and js_splice hxor2]
  · simp [js_splice, js_and, js_xor, js_shift, js_mask, js_lui, js_slli, hload_sail]
  · change js_load.vregs JoltISA.inlineTmp1 = compute_aligned_dword_base_address val imm
    exact hload_v1
  · change js_and.vregs JoltISA.inlineTmp2 ^^^ js_and.vregs JoltISA.inlineTmp3 = spliced
    rw [hand_v2, hand_v3]
    exact hspliced

/-- Word-store mask block for `SW`.

Rust does not materialize the 32-bit mask with `LUI`.  It emits
`ORI v3, x0, -1; SRLI v3, v3, 32`, then shifts that mask by the byte-lane
offset already computed in `v0`.  This block proves exactly that prefix and
exports the boundary facts needed by the value/splice block.  The `x0` read is
an explicit hypothesis, so this proof stays about the Jolt bytecode block rather
than unfolding Sail's architectural-register implementation. -/
theorem wordMaskBlock (rest : JoltISA.Program)
    (imm : BitVec 12)
    (js js_load : SailJoltState) (val dword : BitVec 64)
    (hload_sail : js_load.sail = js.sail)
    (hload_v0 : js_load.vregs JoltISA.inlineTmp0 = load_effective_address val imm)
    (hload_v1 : js_load.vregs JoltISA.inlineTmp1 = compute_aligned_dword_base_address val imm)
    (hload_v2 : js_load.vregs JoltISA.inlineTmp2 = dword)
    (hx0 : rX_bits (regidx.Regidx 0) js_load.sail = .ok 0#64 js_load.sail) :
    ∃ js_mask : SailJoltState,
      (JoltISA.execProgram
        (JoltISA.slliBlock (.vreg JoltISA.inlineTmp0) (.vreg JoltISA.inlineTmp0) (3 : BitVec 6) <|
         .instr (.ORI (.vreg JoltISA.inlineTmp3) (.xreg (regidx.Regidx 0)) (-1 : BitVec 12)) <|
         JoltISA.srliBlock (.vreg JoltISA.inlineTmp3) (.vreg JoltISA.inlineTmp3) (32 : BitVec 6) <|
         JoltISA.sllBlock (.vreg JoltISA.inlineTmp3) (.vreg JoltISA.inlineTmp3) (.vreg JoltISA.inlineTmp0) JoltISA.inlineTmp4 rest)).run js_load =
        (JoltISA.execProgram rest).run js_mask ∧
      js_mask.sail = js.sail ∧
      js_mask.vregs JoltISA.inlineTmp0 =
        shift_bits_left (load_effective_address val imm) (3 : BitVec 6) ∧
      js_mask.vregs JoltISA.inlineTmp1 = compute_aligned_dword_base_address val imm ∧
      js_mask.vregs JoltISA.inlineTmp2 = dword ∧
      js_mask.vregs JoltISA.inlineTmp3 =
        shift_bits_left (0x00000000FFFFFFFF : BitVec 64)
          (Sail.BitVec.extractLsb
            (shift_bits_left (load_effective_address val imm) (3 : BitVec 6)) 5 0) := by
  let ea := load_effective_address val imm
  let base := compute_aligned_dword_base_address val imm
  let shift64 := shift_bits_left ea (3 : BitVec 6)
  let mask32 := (0x00000000FFFFFFFF : BitVec 64)
  let shiftedMask := shift_bits_left mask32 (Sail.BitVec.extractLsb shift64 5 0)
  let js_slli := swWordShiftState js_load
  let js_ori := swWordOnesState js_slli
  let js_srli := swWordBaseMaskState js_ori
  let js_mask := swWordMaskState js_srli
  have hx0_slli : rX_bits (regidx.Regidx 0) js_slli.sail = .ok 0#64 js_slli.sail := by
    change rX_bits (regidx.Regidx 0) js_load.sail = .ok 0#64 js_load.sail
    exact hx0
  refine ⟨js_mask, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [swWordShiftStep]
    rw [swWordOnesStep _ _ hx0_slli]
    rw [swWordBaseMaskStep]
    rw [swWordMaskShiftStep]
  · calc
      js_mask.sail = js_load.sail := by
        change (swWordMaskState (swWordBaseMaskState (swWordOnesState (swWordShiftState js_load)))).sail =
          js_load.sail
        exact swWordMaskState_sail js_load
      _ = js.sail := hload_sail
  · calc
      js_mask.vregs JoltISA.inlineTmp0 = shift_bits_left (js_load.vregs JoltISA.inlineTmp0) (3 : BitVec 6) := by
        change (swWordMaskState (swWordBaseMaskState (swWordOnesState (swWordShiftState js_load)))).vregs
            JoltISA.inlineTmp0 =
          shift_bits_left (js_load.vregs JoltISA.inlineTmp0) (3 : BitVec 6)
        exact swWordMaskState_v0 js_load
      _ = shift64 := by rw [hload_v0]
  · calc
      js_mask.vregs JoltISA.inlineTmp1 = js_load.vregs JoltISA.inlineTmp1 := by
        change (swWordMaskState (swWordBaseMaskState (swWordOnesState (swWordShiftState js_load)))).vregs
            JoltISA.inlineTmp1 =
          js_load.vregs JoltISA.inlineTmp1
        exact swWordMaskState_v1 js_load
      _ = base := hload_v1
  · calc
      js_mask.vregs JoltISA.inlineTmp2 = js_load.vregs JoltISA.inlineTmp2 := by
        change (swWordMaskState (swWordBaseMaskState (swWordOnesState (swWordShiftState js_load)))).vregs
            JoltISA.inlineTmp2 =
          js_load.vregs JoltISA.inlineTmp2
        exact swWordMaskState_v2 js_load
      _ = dword := hload_v2
  · calc
      js_mask.vregs JoltISA.inlineTmp3 =
          shift_bits_left mask32
            (Sail.BitVec.extractLsb
              (shift_bits_left (js_load.vregs JoltISA.inlineTmp0) (3 : BitVec 6)) 5 0) := by
        change (swWordMaskState (swWordBaseMaskState (swWordOnesState (swWordShiftState js_load)))).vregs
            JoltISA.inlineTmp3 =
          shift_bits_left mask32
            (Sail.BitVec.extractLsb
              (shift_bits_left (js_load.vregs JoltISA.inlineTmp0) (3 : BitVec 6)) 5 0)
        exact swWordMaskState_v3 js_load
      _ = shiftedMask := by rw [hload_v0]

/-- Word-store value/splice block for `SW`.

This is the second half of the Rust `SW` middle sequence.  It assumes the mask
block has already left the bit offset in `v0`, the aligned dword base in `v1`,
the original dword in `v2`, and the shifted 32-bit mask in `v3`.  The block then
shifts the low word of `rs2` into place and performs the standard
`dword ^ ((dword ^ shifted_value) & mask)` splice, leaving the modified dword in
`v2`. -/
theorem wordSpliceBlock (rest : JoltISA.Program)
    (imm : BitVec 12) (rs2 : regidx)
    (js js_mask : SailJoltState) (val rs2_val dword : BitVec 64)
    (hsetup : StoreSplice.WordStoreFacts
      (load_effective_address val imm)
      (compute_aligned_dword_base_address val imm))
    (hmask_sail : js_mask.sail = js.sail)
    (hmask_v0 :
      js_mask.vregs JoltISA.inlineTmp0 =
        shift_bits_left (load_effective_address val imm) (3 : BitVec 6))
    (hmask_v1 : js_mask.vregs JoltISA.inlineTmp1 = compute_aligned_dword_base_address val imm)
    (hmask_v2 : js_mask.vregs JoltISA.inlineTmp2 = dword)
    (hmask_v3 :
      js_mask.vregs JoltISA.inlineTmp3 =
        shift_bits_left (0x00000000FFFFFFFF : BitVec 64)
          (Sail.BitVec.extractLsb
            (shift_bits_left (load_effective_address val imm) (3 : BitVec 6)) 5 0))
    (hrs2 : rX_bits rs2 js.sail = .ok rs2_val js.sail) :
    ∃ js_splice : SailJoltState,
      (JoltISA.execProgram
        (JoltISA.sllBlock (.vreg JoltISA.inlineTmp0) (.xreg rs2) (.vreg JoltISA.inlineTmp0) JoltISA.inlineTmp4 <|
         .instr (.XOR (.vreg JoltISA.inlineTmp0) (.vreg JoltISA.inlineTmp2) (.vreg JoltISA.inlineTmp0)) <|
         .instr (.AND (.vreg JoltISA.inlineTmp0) (.vreg JoltISA.inlineTmp0) (.vreg JoltISA.inlineTmp3)) <|
         .instr (.XOR (.vreg JoltISA.inlineTmp2) (.vreg JoltISA.inlineTmp2) (.vreg JoltISA.inlineTmp0)) rest)).run js_mask =
        (JoltISA.execProgram rest).run js_splice ∧
      js_splice.sail = js.sail ∧
      js_splice.vregs JoltISA.inlineTmp1 = compute_aligned_dword_base_address val imm ∧
      js_splice.vregs JoltISA.inlineTmp2 =
        StoreSplice.wordSplice
          dword (Sail.BitVec.extractLsb rs2_val 31 0)
          (((load_effective_address val imm -
              compute_aligned_dword_base_address val imm).toNat) * 8) := by
  let ea := load_effective_address val imm
  let base := compute_aligned_dword_base_address val imm
  let shift64 := shift_bits_left ea (3 : BitVec 6)
  let shift6 := Sail.BitVec.extractLsb shift64 5 0
  let mask := shift_bits_left (0x00000000FFFFFFFF : BitVec 64) shift6
  let shifted := shift_bits_left rs2_val shift6
  let xored := dword ^^^ shifted
  let masked := xored &&& mask
  let spliced :=
    StoreSplice.wordSplice dword (Sail.BitVec.extractLsb rs2_val 31 0) (((ea - base).toNat) * 8)
  let js_shift : SailJoltState :=
    { sail := js_mask.sail
      vregs := fun r =>
        if r = JoltISA.inlineTmp0 then
          shift_bits_left rs2_val
            (Sail.BitVec.extractLsb (js_mask.vregs JoltISA.inlineTmp0) 5 0)
        else if r = JoltISA.inlineTmp4 then
          jolt_virtual_pow2_value (js_mask.vregs JoltISA.inlineTmp0)
        else js_mask.vregs r }
  let js_xor : SailJoltState :=
    { sail := js_shift.sail
      vregs := fun r =>
        if r = JoltISA.inlineTmp0 then
          js_shift.vregs JoltISA.inlineTmp2 ^^^ js_shift.vregs JoltISA.inlineTmp0
        else js_shift.vregs r }
  let js_and : SailJoltState :=
    { sail := js_xor.sail
      vregs := fun r =>
        if r = JoltISA.inlineTmp0 then
          js_xor.vregs JoltISA.inlineTmp0 &&& js_xor.vregs JoltISA.inlineTmp3
        else js_xor.vregs r }
  let js_splice : SailJoltState :=
    { sail := js_and.sail
      vregs := fun r =>
        if r = JoltISA.inlineTmp2 then
          js_and.vregs JoltISA.inlineTmp2 ^^^ js_and.vregs JoltISA.inlineTmp0
        else js_and.vregs r }
  have hrs2_mask : rX_bits rs2 js_mask.sail = .ok rs2_val js_mask.sail := by
    simpa [hmask_sail] using hrs2
  let js_shift_pow2 : SailJoltState :=
    { sail := js_mask.sail
      vregs := fun r =>
        if r = JoltISA.inlineTmp4 then
          jolt_virtual_pow2_value (js_mask.vregs JoltISA.inlineTmp0)
        else js_mask.vregs r }
  have hpow2_value :
      (JoltISA.execInstr (.VirtualPow2 (.vreg JoltISA.inlineTmp4) (.vreg JoltISA.inlineTmp0))).run js_mask =
        .ok RETIRE_SUCCESS js_shift_pow2 := by
    simpa [js_shift_pow2] using
      (JoltISA.virtual_pow2_run_vreg_vreg JoltISA.inlineTmp4 JoltISA.inlineTmp0 js_mask
        (by unfold WritableVReg; decide))
  have hrs2_shift_pow2 : rX_bits rs2 js_shift_pow2.sail = .ok rs2_val js_shift_pow2.sail := by
    exact hrs2_mask
  have hmul_value :
      (JoltISA.execInstr (.MUL (.vreg JoltISA.inlineTmp0) (.xreg rs2) (.vreg JoltISA.inlineTmp4))).run js_shift_pow2 =
        .ok RETIRE_SUCCESS js_shift := by
    simpa [js_shift, js_shift_pow2, JoltISA.mul_jolt_virtual_pow2_value_eq_shift_bits_left] using
      (JoltISA.mul_run_vreg_xreg_vreg JoltISA.inlineTmp0 rs2
        JoltISA.inlineTmp4 js_shift_pow2 rs2_val hrs2_shift_pow2
        (by unfold WritableVReg; decide))
  have hsll_value_run : ∀ tail,
      (JoltISA.execProgram
        (JoltISA.sllBlock (.vreg JoltISA.inlineTmp0) (.xreg rs2) (.vreg JoltISA.inlineTmp0) JoltISA.inlineTmp4 tail)).run
          js_mask =
      (JoltISA.execProgram tail).run js_shift := by
    intro tail
    unfold JoltISA.sllBlock
    rw [JoltISA.execProgram_instr_run_retire _ _ js_mask js_shift_pow2 hpow2_value]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_shift_pow2 js_shift hmul_value]
  have hshift_v0 : js_shift.vregs JoltISA.inlineTmp0 = shifted := by
    change shift_bits_left rs2_val
      (Sail.BitVec.extractLsb (js_mask.vregs JoltISA.inlineTmp0) 5 0) = shifted
    rw [hmask_v0]
  have hshift_v2 : js_shift.vregs JoltISA.inlineTmp2 = dword := by
    change js_mask.vregs JoltISA.inlineTmp2 = dword
    exact hmask_v2
  have hshift_v3 : js_shift.vregs JoltISA.inlineTmp3 = mask := by
    change js_mask.vregs JoltISA.inlineTmp3 = mask
    exact hmask_v3
  have hxor1 :
      (JoltISA.execInstr (.XOR (.vreg JoltISA.inlineTmp0) (.vreg JoltISA.inlineTmp2) (.vreg JoltISA.inlineTmp0))).run js_shift =
        .ok RETIRE_SUCCESS js_xor := by
    simpa [js_xor] using
      (JoltISA.xor_run_vreg_vreg_vreg JoltISA.inlineTmp0 JoltISA.inlineTmp2
        JoltISA.inlineTmp0 js_shift (by unfold WritableVReg; decide))
  have hxor_v0 : js_xor.vregs JoltISA.inlineTmp0 = xored := by
    change js_shift.vregs JoltISA.inlineTmp2 ^^^ js_shift.vregs JoltISA.inlineTmp0 = xored
    rw [hshift_v2, hshift_v0]
  have hxor_v2 : js_xor.vregs JoltISA.inlineTmp2 = dword := by
    change js_shift.vregs JoltISA.inlineTmp2 = dword
    exact hshift_v2
  have hxor_v3 : js_xor.vregs JoltISA.inlineTmp3 = mask := by
    change js_shift.vregs JoltISA.inlineTmp3 = mask
    exact hshift_v3
  have hand :
      (JoltISA.execInstr (.AND (.vreg JoltISA.inlineTmp0) (.vreg JoltISA.inlineTmp0) (.vreg JoltISA.inlineTmp3))).run js_xor =
        .ok RETIRE_SUCCESS js_and := by
    simpa [js_and] using
      (JoltISA.execInstr_and_vreg_vreg_vreg_run JoltISA.inlineTmp0 JoltISA.inlineTmp0
        JoltISA.inlineTmp3 js_xor (by unfold WritableVReg; decide))
  have hand_v0 : js_and.vregs JoltISA.inlineTmp0 = masked := by
    change js_xor.vregs JoltISA.inlineTmp0 &&& js_xor.vregs JoltISA.inlineTmp3 = masked
    rw [hxor_v0, hxor_v3]
  have hand_v2 : js_and.vregs JoltISA.inlineTmp2 = dword := by
    change js_xor.vregs JoltISA.inlineTmp2 = dword
    exact hxor_v2
  have hshift6 :
      shift6 = BitVec.ofNat 6 (((ea - base).toNat) * 8) := by
    simpa [shift6, shift64, ea, base] using shift6_eq_of_offset_word ea base hsetup
  have hspliced : dword ^^^ masked = spliced := by
    dsimp [masked, xored, shifted, mask, spliced]
    rw [hshift6]
    simpa using
      wordSplice_eq_sequence dword rs2_val ((ea - base).toNat)
        hsetup.word_offset_cases
  have hxor2 :
      (JoltISA.execInstr (.XOR (.vreg JoltISA.inlineTmp2) (.vreg JoltISA.inlineTmp2) (.vreg JoltISA.inlineTmp0))).run js_and =
        .ok RETIRE_SUCCESS js_splice := by
    simpa [js_splice] using
      (JoltISA.xor_run_vreg_vreg_vreg JoltISA.inlineTmp2 JoltISA.inlineTmp2
        JoltISA.inlineTmp0 js_and (by unfold WritableVReg; decide))
  refine ⟨js_splice, ?_, ?_, ?_, ?_⟩
  · rw [hsll_value_run]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_shift js_xor hxor1]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_xor js_and hand]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_and js_splice hxor2]
  · simp [js_splice, js_and, js_xor, js_shift, hmask_sail]
  · simp [js_splice, js_and, js_xor, js_shift]
    exact hmask_v1
  · change js_and.vregs JoltISA.inlineTmp2 ^^^ js_and.vregs JoltISA.inlineTmp0 = spliced
    rw [hand_v2, hand_v0]
    exact hspliced

/-- Final dword-store block shared by all store expansions.

The preceding splice block leaves the aligned dword base in `v1` and the
modified dword in `v2`.  `SD v1, v2, 0` hands those values to Sail's memory
write pipeline and preserves the virtual registers. -/
theorem sdWriteBlock (rest : JoltISA.Program)
    (js_store : SailJoltState) (base dword_new : BitVec 64) (s' : SailState)
    (hbase : js_store.vregs JoltISA.inlineTmp1 = base)
    (hdword : js_store.vregs JoltISA.inlineTmp2 = dword_new)
    (h_align : base &&& (7 : BitVec 64) = 0)
    (hwrite :
      vmem_write_addr (Virtaddr base) 8 dword_new
        (Store Data) false false false js_store.sail =
      .ok (Ok true) s') :
    ∃ js_write : SailJoltState,
      (JoltISA.execProgram (.instr (.SD (.vreg JoltISA.inlineTmp1) (.vreg JoltISA.inlineTmp2) 0) rest)).run js_store =
        (JoltISA.execProgram rest).run js_write ∧
      js_write.sail = s' ∧
      js_write.vregs = js_store.vregs := by
  let js_write : SailJoltState := { sail := s', vregs := js_store.vregs }
  have hzero : sign_extend (m := 64) (0 : BitVec 12) = (0 : BitVec 64) := by decide
  have haddr : js_store.vregs JoltISA.inlineTmp1 + sign_extend (m := 64) (0 : BitVec 12) = base := by
    rw [hzero, hbase]
    norm_num
  have hwrite' :
      vmem_write_addr
        (Virtaddr (js_store.vregs JoltISA.inlineTmp1 + sign_extend (m := 64) (0 : BitVec 12)))
        8 (js_store.vregs JoltISA.inlineTmp2)
        (Store Data) false false false js_store.sail =
      .ok (Ok true) s' := by
    rw [haddr, hdword]
    exact hwrite
  have hsd_align :
      (js_store.vregs JoltISA.inlineTmp1 + sign_extend (m := 64) (0 : BitVec 12)) &&&
          (7 : BitVec 64) =
        0 := by
    rw [haddr]
    exact h_align
  have hsd :
      (JoltISA.execInstr (.SD (.vreg JoltISA.inlineTmp1) (.vreg JoltISA.inlineTmp2) 0)).run js_store =
        .ok RETIRE_SUCCESS js_write := by
    simpa [js_write] using
      (JoltISA.execInstr_sd_vreg_run_of_write
        JoltISA.inlineTmp1 JoltISA.inlineTmp2 (0 : BitVec 12) js_store s' hsd_align hwrite')
  refine ⟨js_write, ?_, rfl, rfl⟩
  rw [JoltISA.execProgram_instr_run_retire _ _ js_store js_write hsd]

end StoreProgramBlocks

end
