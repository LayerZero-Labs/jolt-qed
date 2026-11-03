import JoltBytecode.JoltISA.Expansions.Store
import JoltBytecode.InstructionEquivalence.ProofSupport.ExpansionBlocks.ALU
import JoltBytecode.InstructionEquivalence.ProofSupport.InstructionLemmas.ADDI
import JoltBytecode.InstructionEquivalence.ProofSupport.InstructionLemmas.AND
import JoltBytecode.InstructionEquivalence.ProofSupport.InstructionLemmas.ANDN
import JoltBytecode.InstructionEquivalence.ProofSupport.InstructionLemmas.ANDI
import JoltBytecode.InstructionEquivalence.ProofSupport.InstructionLemmas.Add
import JoltBytecode.InstructionEquivalence.ProofSupport.InstructionLemmas.LD
import JoltBytecode.InstructionEquivalence.ProofSupport.InstructionLemmas.LUI
import JoltBytecode.InstructionEquivalence.ProofSupport.InstructionLemmas.ORI
import JoltBytecode.InstructionEquivalence.ProofSupport.InstructionLemmas.VirtualMULI
import JoltBytecode.InstructionEquivalence.ProofSupport.InstructionLemmas.XOR
import JoltBytecode.InstructionEquivalence.Instructions.LoadFamily.FloorLoad
import JoltBytecode.InstructionEquivalence.ProofSupport.Memory.Write
import JoltBytecode.InstructionEquivalence.ProofSupport.Memory.Read
import JoltBytecode.InstructionEquivalence.Instructions.StoreFamily.Splice
import JoltBytecode.InstructionEquivalence.ProofSupport.Basic

/-!
# Program blocks for store-family Jolt-ISA proofs

The current store programs use `LaneWindow.open` and `LaneWindow.merge`:
a floor load, window mask, clear, shift, add, and floor store.
`laneStoreProgram_run` composes their row proofs for all three widths.
The existing splice identities remain in `StoreFamily/Splice.lean`.

The retained legacy helpers describe this older shape:

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
  { js with
    vregs := fun r =>
      if r = JoltISA.inlineTmp0 then
        shift_bits_left (js.vregs JoltISA.inlineTmp0) (3 : BitVec 6)
      else js.vregs r }

private def swWordOnesState (js : SailJoltState) : SailJoltState :=
  { js with
    vregs := fun r =>
      if r = JoltISA.inlineTmp3 then
        (0#64) ||| sign_extend (m := 64) (-1 : BitVec 12)
      else js.vregs r }

private def swWordBaseMaskState (js : SailJoltState) : SailJoltState :=
  { js with
    vregs := fun r =>
      if r = JoltISA.inlineTmp3 then
        shift_bits_right (js.vregs JoltISA.inlineTmp3) (32 : BitVec 6)
      else js.vregs r }

private def swWordMaskState (js : SailJoltState) : SailJoltState :=
  { js with
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
      (.instr (JoltISA.Encoded.ORI (.vreg JoltISA.inlineTmp3) (.xreg (regidx.Regidx 0)) (-1 : BitVec 12)) rest)).run js =
      (JoltISA.execProgram rest).run (swWordOnesState js) := by
  have h :
      (JoltISA.execInstr (JoltISA.Encoded.ORI (.vreg JoltISA.inlineTmp3) (.xreg (regidx.Regidx 0)) (-1 : BitVec 12))).run js =
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
    { js with
      vregs := fun r =>
        if r = JoltISA.inlineTmp4 then
          jolt_virtual_pow2_value (js.vregs JoltISA.inlineTmp0)
        else js.vregs r }
  have hpow2 :
      (JoltISA.execInstr (.VirtualPow2 (.vreg JoltISA.inlineTmp4) (.vreg JoltISA.inlineTmp0) (0 : BitVec 64))).run js =
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
      Assumptions.NotReadableMmio (compute_aligned_dword_base_address val imm) 8 js.sail)
    (hjolt : Assumptions.JoltRamLoadOk (compute_aligned_dword_base_address val imm) js) :
    ∃ js_load : SailJoltState,
      (JoltISA.execProgram
        (.instr (JoltISA.Encoded.ADDI (.vreg JoltISA.inlineTmp0) (.xreg rs1) imm) <|
         .instr (JoltISA.Encoded.ANDI (.vreg JoltISA.inlineTmp1) (.vreg JoltISA.inlineTmp0) (-8 : BitVec 12)) <|
         .instr (JoltISA.Encoded.LD .normal (.vreg JoltISA.inlineTmp2) (.vreg JoltISA.inlineTmp1) 0) rest)).run js =
        (JoltISA.execProgram rest).run js_load ∧
      js_load.sail = js.sail ∧
      js_load.vregs JoltISA.inlineTmp0 = load_effective_address val imm ∧
      js_load.vregs JoltISA.inlineTmp1 = compute_aligned_dword_base_address val imm ∧
      js_load.vregs JoltISA.inlineTmp2 =
        loaded_dword_at js.sail (compute_aligned_dword_base_address val imm)
          hbytes h_base_aligned.no_ovf ∧
      js_load.jolt_device = js.jolt_device := by
  let ea := load_effective_address val imm
  let base := compute_aligned_dword_base_address val imm
  let dword := loaded_dword_at js.sail base (by simpa [base] using hbytes)
    (by simpa [base] using h_base_aligned.no_ovf)
  let js0 : SailJoltState :=
    { js with
      vregs := fun r => if r = JoltISA.inlineTmp0 then ea else js.vregs r }
  let js1 : SailJoltState :=
    { js with
      vregs := fun r => if r = JoltISA.inlineTmp1 then base else js0.vregs r }
  let js_load : SailJoltState :=
    { js with
      vregs := fun r => if r = JoltISA.inlineTmp2 then dword else js1.vregs r }
  have haddi :
      (JoltISA.execInstr (JoltISA.Encoded.ADDI (.vreg JoltISA.inlineTmp0) (.xreg rs1) imm)).run js =
        .ok RETIRE_SUCCESS js0 := by
    simpa [js0, ea, load_effective_address] using
      (JoltISA.addi_run_vreg_xreg JoltISA.inlineTmp0 rs1 imm js val hrx
        (by unfold WritableVReg; decide))
  have h8 : sign_extend (m := 64) (-8 : BitVec 12) = (-8 : BitVec 64) := by decide
  have handi :
      (JoltISA.execInstr (JoltISA.Encoded.ANDI (.vreg JoltISA.inlineTmp1) (.vreg JoltISA.inlineTmp0) (-8 : BitVec 12))).run js0 =
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
      (JoltISA.execInstr (JoltISA.Encoded.LD .normal (.vreg JoltISA.inlineTmp2) (.vreg JoltISA.inlineTmp1) 0)).run js1 =
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
    have haddr_ld :
        js1.vregs JoltISA.inlineTmp1 + sign_extend (m := 64) (0 : BitVec 12) = base := by
      have h0 : sign_extend (m := 64) (0 : BitVec 12) = (0 : BitVec 64) := by decide
      have hv1 : js1.vregs JoltISA.inlineTmp1 = base := by simp [js1]
      rw [hv1, h0]
      norm_num
    simpa [js_load, dword] using
      (JoltISA.ld_run_vreg_vreg_from_memory_read JoltISA.inlineTmp2 JoltISA.inlineTmp1
        (0 : BitVec 12) js1 dword hld_align hld_read
        (by unfold WritableVReg; decide)
        (by simpa [js1, base, sign_extend, Sail.BitVec.signExtend] using hmmio.ram)
        hpriv hmprv
        (by rw [haddr_ld]; exact hbytes)
        (by rw [haddr_ld]; exact hpmp)
        (by rw [haddr_ld]; exact hmmio)
        (by rw [haddr_ld]; exact ⟨hjolt.below_heap_end⟩))
  refine ⟨js_load, ?_, rfl, ?_, ?_, ?_, rfl⟩
  · rw [JoltISA.execProgram_instr_run_retire _ _ js js0 haddi]
    rw [JoltISA.execProgram_instr_run_retire _ _ js0 js1 handi]
    rw [JoltISA.execProgram_instr_run_retire _ _ js1 js_load hld]
  · simp [js_load, js1, js0, ea]
  · simp [js_load, js1, base]
  · simp [js_load, dword, base]

/-- The mask row emitted by `LaneWindow.open` for the selected width.
For example, word width emits `VirtualWindowMaskW`.
Jolt: `crates/jolt-program/src/expand/memory/shared.rs` (`LaneWindow::open`). -/
private def fusedWindowInstr (width : JoltISA.AccessWidth) (lane : JoltISA.Dst)
    (base : JoltISA.Src) (imm : BitVec 64) : JoltISA.Instr :=
  match JoltISA.laneWindowOpen width lane lane base imm .normal
      (ExceptionType.E_SAMO_Addr_Align ()) (.done RETIRE_SUCCESS) with
  | .instr _ (.instr instruction _) => instruction
  | _ => .FENCE

/-- The shift row emitted by `LaneWindow.merge`, including its address immediate.
For example, base 7 and immediate 1 select byte lane zero.
Jolt: `crates/jolt-program/src/expand/memory/shared.rs` (`LaneWindow::merge`). -/
private def fusedShiftInstr (width : JoltISA.AccessWidth) (lane : JoltISA.Dst)
    (value base : JoltISA.Src) (imm : BitVec 64) : JoltISA.Instr :=
  match JoltISA.laneWindowMerge width lane lane base imm value
      (ExceptionType.E_SAMO_Addr_Align ()) (.done RETIRE_SUCCESS) with
  | .instr _ (.instr instruction _) => instruction
  | _ => .FENCE

private def fusedWindowValue (width : JoltISA.AccessWidth) (ea : BitVec 64) : BitVec 64 :=
  match width with
  | .byte => jolt_virtual_window_mask_b_value ea 0
  | .halfword => jolt_virtual_window_mask_h_value ea 0
  | .word => jolt_virtual_window_mask_w_value ea 0

private def fusedShiftValue (width : JoltISA.AccessWidth)
    (value ea : BitVec 64) : BitVec 64 :=
  match width with
  | .byte => jolt_virtual_shift_data_b_value value ea
  | .halfword => jolt_virtual_shift_data_h_value value ea
  | .word => jolt_virtual_shift_data_w_value value ea

/-- Clear the addressed lane and add the shifted low bytes of `value`.
For example, byte width at address 9 replaces byte one of `dword`.
The width-specific identities with byte, halfword and word splices are proved
in `StoreSplice.fusedByteSplice_eq`, `fusedHalfwordSplice_eq`, and `fusedWordSplice_eq`. -/
def fusedSpliceValue (width : JoltISA.AccessWidth) (dword value ea : BitVec 64) : BitVec 64 :=
  (dword &&& ~~~(fusedWindowValue width ea)) + fusedShiftValue width value ea

private theorem fusedWindow_run (width : JoltISA.AccessWidth) (lane : JoltISA.VReg)
    (rs1 : regidx) (imm baseValue : BitVec 64) (js : SailJoltState)
    (hread : rX_bits rs1 js.sail = .ok baseValue js.sail)
    (hwritable : WritableVReg lane) :
    (JoltISA.execInstr (fusedWindowInstr width (.vreg lane) (.xreg rs1) imm)).run js =
      .ok RETIRE_SUCCESS (stateAfterVRegWrite js lane (fusedWindowValue width (baseValue + imm))) := by
  unfold WritableVReg at hwritable
  cases width <;>
    simp [fusedWindowInstr, JoltISA.laneWindowOpen, JoltISA.execInstr,
      JoltISA.readSrc, liftSail, hread, JoltISA.writeDst, writeVReg, hwritable,
      stateAfterVRegWrite, bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
      modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet,
      fusedWindowValue, jolt_virtual_window_mask_b_value,
      jolt_virtual_window_mask_h_value, jolt_virtual_window_mask_w_value,
      jolt_virtual_window_mask_b_value64, jolt_virtual_window_mask_h_value64,
      jolt_virtual_window_mask_w_value64, JoltISA.addWide, sign_extend, Sail.BitVec.signExtend]

private theorem fusedShift_run (width : JoltISA.AccessWidth) (lane : JoltISA.VReg)
    (rs2 rs1 : regidx) (imm value baseValue : BitVec 64) (js : SailJoltState)
    (hvalue : rX_bits rs2 js.sail = .ok value js.sail)
    (hbase : rX_bits rs1 js.sail = .ok baseValue js.sail)
    (hwritable : WritableVReg lane) :
    (JoltISA.execInstr (fusedShiftInstr width (.vreg lane) (.xreg rs2) (.xreg rs1) imm)).run js =
      .ok RETIRE_SUCCESS (stateAfterVRegWrite js lane (fusedShiftValue width value (baseValue + imm))) := by
  unfold WritableVReg at hwritable
  cases width <;>
    simp only [fusedShiftInstr, JoltISA.laneWindowMerge, JoltISA.execInstr,
      JoltISA.readSrc, liftSail, bind, EStateM.bind, EStateM.run, hvalue, hbase,
      JoltISA.writeDst, writeVReg, hwritable, ↓reduceIte, stateAfterVRegWrite,
      pure, EStateM.pure, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet,
      fusedShiftValue]

/-- The four mask-and-splice rows, before the final floor store.
For example, word width clears a four-byte lane before adding its replacement. -/
private def fusedSpliceProgram (width : JoltISA.AccessWidth)
    (dword lane : JoltISA.VReg) (rs1 rs2 : regidx) (imm : BitVec 64) : JoltISA.Program :=
  .instr (fusedWindowInstr width (.vreg lane) (.xreg rs1) imm) <|
  .instr (.ANDN (.vreg dword) (.vreg dword) (.vreg lane)) <|
  .instr (fusedShiftInstr width (.vreg lane) (.xreg rs2) (.xreg rs1) imm) <|
  .instr (.ADD (.vreg dword) (.vreg dword) (.vreg lane)) <| .done RETIRE_SUCCESS

private theorem fusedSpliceBlock (width : JoltISA.AccessWidth)
    (dword lane : JoltISA.VReg) (hne : dword ≠ lane)
    (hdwrite : WritableVReg dword) (hlwrite : WritableVReg lane)
    (rs1 rs2 : regidx) (imm baseValue value : BitVec 64) (js : SailJoltState)
    (hbase : rX_bits rs1 js.sail = .ok baseValue js.sail)
    (hvalue : rX_bits rs2 js.sail = .ok value js.sail) :
    ∃ js_splice,
      JoltISA.Program.Run (fusedSpliceProgram width dword lane rs1 rs2 imm) js js_splice ∧
      js_splice.sail = js.sail ∧
      js_splice.vregs dword = fusedSpliceValue width (js.vregs dword) value (baseValue + imm) ∧
      js_splice.jolt_device = js.jolt_device := by
  let mask := fusedWindowValue width (baseValue + imm)
  let shifted := fusedShiftValue width value (baseValue + imm)
  let cleared := js.vregs dword &&& ~~~mask
  let js_mask := stateAfterVRegWrite js lane mask
  let js_clear := stateAfterVRegWrite js_mask dword cleared
  let js_shift := stateAfterVRegWrite js_clear lane shifted
  let js_splice := stateAfterVRegWrite js_shift dword (cleared + shifted)
  have hmask := fusedWindow_run width lane rs1 imm baseValue js hbase hlwrite
  have handn : (JoltISA.execInstr (.ANDN (.vreg dword) (.vreg dword) (.vreg lane))).run js_mask =
      .ok RETIRE_SUCCESS js_clear := by
    simpa [js_clear, js_mask, cleared, stateAfterVRegWrite, hne] using
      JoltISA.andn_run_vreg_vreg_vreg dword dword lane js_mask hdwrite
  have hshift := fusedShift_run width lane rs2 rs1 imm value baseValue js_clear hvalue hbase hlwrite
  have hadd : (JoltISA.execInstr (.ADD (.vreg dword) (.vreg dword) (.vreg lane))).run js_shift =
      .ok RETIRE_SUCCESS js_splice := by
    simpa [js_splice, js_shift, js_clear, stateAfterVRegWrite, hne] using
      JoltISA.add_run_vreg_vreg_vreg dword dword lane js_shift hdwrite
  refine ⟨js_splice, ?_, rfl, ?_, rfl⟩
  · exact (LoadFamily.singleRow_run hmask).append
      ((LoadFamily.singleRow_run handn).append
        ((LoadFamily.singleRow_run hshift).append (LoadFamily.singleRow_run hadd)))
  · simp [js_splice, stateAfterVRegWrite, cleared, mask, shifted, fusedSpliceValue]

/-- The final row of `LaneWindow.merge`, which writes the containing doubleword.
For example, word width writes back at address 8 for an effective address of 12.
Jolt: `crates/jolt-program/src/expand/memory/shared.rs` (`LaneWindow::merge`). -/
private def floorStoreRow (width : JoltISA.AccessWidth) (base : JoltISA.Src)
    (value : JoltISA.VReg) (imm : BitVec 64) (fault : ExceptionType) : JoltISA.Instr :=
  match JoltISA.laneWindowMerge width (.vreg value) (.vreg value)
      base imm (.vreg value) fault (.done RETIRE_SUCCESS) with
  | .instr _ (.instr _ (.instr _ (.instr instruction _))) => instruction
  | _ => .FENCE

private theorem floorStore_run (width : JoltISA.AccessWidth) (rs1 : regidx)
    (value : JoltISA.VReg) (imm baseValue : BitVec 64) (fault : ExceptionType)
    (js js' : SailJoltState)
    (hread : rX_bits rs1 js.sail = .ok baseValue js.sail)
    (halign : (baseValue + imm) &&& LoadFamily.alignmentMask width = 0)
    (hmem : JoltISA.Mmu.store_doubleword ((baseValue + imm) &&& ~~~(7 : BitVec 64))
      (js.vregs value) js = .ok (.Ok true) js') :
    (JoltISA.execInstr (floorStoreRow width (.xreg rs1) value imm fault)).run js =
      .ok RETIRE_SUCCESS js' := by
  have hrow : floorStoreRow width (.xreg rs1) value imm fault =
      match width with
      | .byte => .VirtualStoreB (.xreg rs1) (.vreg value) imm fault
      | .halfword => .VirtualStoreH (.xreg rs1) (.vreg value) imm fault
      | .word => .VirtualStoreW (.xreg rs1) (.vreg value) imm fault := by
    cases width <;> rfl
  rw [hrow]
  cases width <;>
    simp only [LoadFamily.alignmentMask] at halign <;>
    simp only [JoltISA.execInstr,
      JoltISA.readSrc, liftSail, bind, EStateM.bind, EStateM.run, hread]
  all_goals
    simp only [halign, ↓reduceIte, readVReg, get, getThe, MonadStateOf.get,
      EStateM.get, pure, EStateM.pure, bind, EStateM.bind, hmem]

/-- The six rows of a narrow store, built from `LaneWindow.open` and `merge`.
For example, word width gives the generated `SW` program, using scratch registers
40 and 41 for the doubleword and lane respectively.
Jolt: `crates/jolt-program/src/expand/memory/shared.rs` (`expand_narrow_store`). -/
def laneStoreProgram (width : JoltISA.AccessWidth) (rs1 rs2 : regidx)
    (imm : BitVec 64) : JoltISA.Program :=
  JoltISA.laneWindowOpen width (.vreg 40) (.vreg 41) (.xreg rs1) imm .normal
    (ExceptionType.E_SAMO_Addr_Align ())
    (JoltISA.laneWindowMerge width (.vreg 40) (.vreg 41) (.xreg rs1) imm (.xreg rs2)
      (ExceptionType.E_SAMO_Addr_Align ()) (.done RETIRE_SUCCESS))

private theorem laneStoreProgram_rows (width : JoltISA.AccessWidth) (rs1 rs2 : regidx)
    (imm : BitVec 64) :
    laneStoreProgram width rs1 rs2 imm =
      (JoltISA.Program.instr (LoadFamily.floorLoadRow width (.vreg 40) (.xreg rs1) imm .normal
        (ExceptionType.E_SAMO_Addr_Align ())) (.done RETIRE_SUCCESS)).append
      ((fusedSpliceProgram width 40 41 rs1 rs2 imm).append
        (.instr (floorStoreRow width (.xreg rs1) 40 imm
          (ExceptionType.E_SAMO_Addr_Align ())) (.done RETIRE_SUCCESS))) := by
  cases width <;> rfl

/-- A narrow store writes the shared splice of the loaded doubleword to RAM.
Only the selected width's alignment is required; for example, a halfword at
address 10 reads and writes the enclosing doubleword at address 8.
Jolt: `crates/jolt-program/src/expand/memory/shared.rs` (`expand_narrow_store`). -/
theorem laneStoreProgram_run (width : JoltISA.AccessWidth) (imm : BitVec 12)
    (rs1 rs2 : regidx) (js : SailJoltState) (baseValue value : BitVec 64)
    (hbase : rX_bits rs1 js.sail = .ok baseValue js.sail)
    (hvalue : rX_bits rs2 js.sail = .ok value js.sail)
    (halign : load_effective_address baseValue imm &&& LoadFamily.alignmentMask width = 0)
    (haligned : AlignedDwordAccess (compute_aligned_dword_base_address baseValue imm))
    (hbytes : MemBytesPresentAt js.sail (compute_aligned_dword_base_address baseValue imm) 8)
    (hram : JoltISA.RAM_START_ADDRESS ≤ (compute_aligned_dword_base_address baseValue imm).toNat)
    (hload : Assumptions.JoltRamLoadOk (compute_aligned_dword_base_address baseValue imm) js)
    (hstore : Assumptions.JoltRamStoreOk (compute_aligned_dword_base_address baseValue imm) js) :
    ∃ js', JoltISA.Program.Run (laneStoreProgram width rs1 rs2 (sign_extend (m := 64) imm)) js js' ∧
      js'.sail = state_after_dword_store js.sail (compute_aligned_dword_base_address baseValue imm)
        (fusedSpliceValue width
          (loaded_dword_at js.sail (compute_aligned_dword_base_address baseValue imm) hbytes haligned.no_ovf)
          value (load_effective_address baseValue imm)) := by
  let base := compute_aligned_dword_base_address baseValue imm
  let dword := loaded_dword_at js.sail base hbytes haligned.no_ovf
  let js_load := stateAfterVRegWrite js (40 : JoltISA.VReg) dword
  have hmem : JoltISA.Mmu.load_doubleword base js = .ok (.Ok dword) js := by
    rw [JoltISA.Mmu.load_doubleword_ram js base haligned.align hram
      (JoltISA.Mmu.effective_address_ok_of_load hram hload),
      JoltISA.Mmu.ram_doubleword_eq_loaded_dword_at js.sail base hbytes haligned.no_ovf]
  have hfirst := LoadFamily.floorLoad_run width 40 rs1 (sign_extend (m := 64) imm)
    baseValue dword .normal (ExceptionType.E_SAMO_Addr_Align ()) js hbase halign hmem
    (by unfold WritableVReg; decide)
  obtain ⟨js_splice, hsplice, hsail, hdword, hdevice⟩ :=
    fusedSpliceBlock width 40 41 (by decide) (by unfold WritableVReg; decide)
      (by unfold WritableVReg; decide) rs1 rs2 (sign_extend (m := 64) imm)
      baseValue value js_load hbase hvalue
  have hstore' : Assumptions.JoltRamStoreOk base js_splice :=
    ⟨by rw [hdevice]; exact hstore.below_heap_end,
     by rw [hdevice]; exact hstore.outside_canary⟩
  have hmem' : JoltISA.Mmu.store_doubleword base (js_splice.vregs 40) js_splice =
      .ok (.Ok true) { js_splice with sail := state_after_dword_store js_splice.sail base (js_splice.vregs 40) } := by
    rw [JoltISA.Mmu.store_doubleword_ram js_splice base (js_splice.vregs 40)
      haligned.align hram (JoltISA.Mmu.effective_address_ok_of_store hram hstore'),
      JoltISA.Mmu.write_ram_doubleword_eq]
  have hlast := floorStore_run width rs1 40 (sign_extend (m := 64) imm) baseValue
    (ExceptionType.E_SAMO_Addr_Align ()) js_splice _ (by rw [hsail]; exact hbase) halign hmem'
  refine ⟨{ js_splice with sail := state_after_dword_store js_splice.sail base (js_splice.vregs 40) }, ?_, ?_⟩
  · rw [laneStoreProgram_rows]
    exact (LoadFamily.singleRow_run hfirst).append (hsplice.append (LoadFamily.singleRow_run hlast))
  · change state_after_dword_store js_splice.sail base (js_splice.vregs 40) = _
    rw [hsail, hdword]
    simp only [js_load, stateAfterVRegWrite, ↓reduceIte]
    rfl

/-- Misalignment stops the first floor load, before any store row runs.
For example, a word store at address 10 reports the store-alignment exception.
Both halfword and word stores use the load family's width-generic proof. -/
theorem laneStoreProgram_misaligned (width : JoltISA.AccessWidth) (imm : BitVec 12)
    (rs1 rs2 : regidx) (js : SailJoltState) (baseValue : BitVec 64)
    (hread : rX_bits rs1 js.sail = .ok baseValue js.sail)
    (hmis : load_effective_address baseValue imm &&& LoadFamily.alignmentMask width ≠ 0) :
    (JoltISA.execProgram (laneStoreProgram width rs1 rs2 (sign_extend (m := 64) imm))).run js =
      .ok (ExecutionResult.Memory_Exception
        (Virtaddr (load_effective_address baseValue imm), ExceptionType.E_SAMO_Addr_Align ())) js := by
  rw [laneStoreProgram_rows]
  exact LoadFamily.floorLoadBlock_misaligned width _ (.vreg 40) rs1
    (sign_extend (m := 64) imm) baseValue .normal (ExceptionType.E_SAMO_Addr_Align ()) js hread hmis

/-- Byte-store splice block.

Starting from the setup boundary (`v0 = ea`, `v1 = base`, `v2 = dword`), the
legacy `SB` middle sequence materializes a one-byte mask, shifts the low
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
    { js_load with
      vregs := fun r =>
        if r = JoltISA.inlineTmp3 then
          shift_bits_left (js_load.vregs JoltISA.inlineTmp0) (3 : BitVec 6)
        else js_load.vregs r }
  let js_lui : SailJoltState :=
    { js_slli with
      vregs := fun r => if r = JoltISA.inlineTmp0 then (0xff : BitVec 64) else js_slli.vregs r }
  let js_mask : SailJoltState :=
    { js_lui with
      vregs := fun r =>
        if r = JoltISA.inlineTmp0 then
          shift_bits_left (js_lui.vregs JoltISA.inlineTmp0)
            (Sail.BitVec.extractLsb (js_lui.vregs JoltISA.inlineTmp3) 5 0)
        else if r = JoltISA.inlineTmp4 then
          jolt_virtual_pow2_value (js_lui.vregs JoltISA.inlineTmp3)
        else js_lui.vregs r }
  let js_shift : SailJoltState :=
    { js_mask with
      vregs := fun r =>
        if r = JoltISA.inlineTmp3 then
          shift_bits_left rs2_val
            (Sail.BitVec.extractLsb (js_mask.vregs JoltISA.inlineTmp3) 5 0)
        else if r = JoltISA.inlineTmp4 then
          jolt_virtual_pow2_value (js_mask.vregs JoltISA.inlineTmp3)
        else js_mask.vregs r }
  let js_xor : SailJoltState :=
    { js_shift with
      vregs := fun r =>
        if r = JoltISA.inlineTmp3 then
          js_shift.vregs JoltISA.inlineTmp2 ^^^ js_shift.vregs JoltISA.inlineTmp3
        else js_shift.vregs r }
  let js_and : SailJoltState :=
    { js_xor with
      vregs := fun r =>
        if r = JoltISA.inlineTmp3 then
          js_xor.vregs JoltISA.inlineTmp3 &&& js_xor.vregs JoltISA.inlineTmp0
        else js_xor.vregs r }
  let js_splice : SailJoltState :=
    { js_and with
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
    { js_lui with
      vregs := fun r =>
        if r = JoltISA.inlineTmp4 then
          jolt_virtual_pow2_value (js_lui.vregs JoltISA.inlineTmp3)
        else js_lui.vregs r }
  have hpow2_mask :
      (JoltISA.execInstr (.VirtualPow2 (.vreg JoltISA.inlineTmp4) (.vreg JoltISA.inlineTmp3) (0 : BitVec 64))).run js_lui =
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
    { js_mask with
      vregs := fun r =>
        if r = JoltISA.inlineTmp4 then
          jolt_virtual_pow2_value (js_mask.vregs JoltISA.inlineTmp3)
        else js_mask.vregs r }
  have hpow2_value :
      (JoltISA.execInstr (.VirtualPow2 (.vreg JoltISA.inlineTmp4) (.vreg JoltISA.inlineTmp3) (0 : BitVec 64))).run js_mask =
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
    { js_load with
      vregs := fun r =>
        if r = JoltISA.inlineTmp3 then
          shift_bits_left (js_load.vregs JoltISA.inlineTmp0) (3 : BitVec 6)
        else js_load.vregs r }
  let js_lui : SailJoltState :=
    { js_slli with
      vregs := fun r => if r = JoltISA.inlineTmp0 then (0xffff : BitVec 64) else js_slli.vregs r }
  let js_mask : SailJoltState :=
    { js_lui with
      vregs := fun r =>
        if r = JoltISA.inlineTmp0 then
          shift_bits_left (js_lui.vregs JoltISA.inlineTmp0)
            (Sail.BitVec.extractLsb (js_lui.vregs JoltISA.inlineTmp3) 5 0)
        else if r = JoltISA.inlineTmp4 then
          jolt_virtual_pow2_value (js_lui.vregs JoltISA.inlineTmp3)
        else js_lui.vregs r }
  let js_shift : SailJoltState :=
    { js_mask with
      vregs := fun r =>
        if r = JoltISA.inlineTmp3 then
          shift_bits_left rs2_val
            (Sail.BitVec.extractLsb (js_mask.vregs JoltISA.inlineTmp3) 5 0)
        else if r = JoltISA.inlineTmp4 then
          jolt_virtual_pow2_value (js_mask.vregs JoltISA.inlineTmp3)
        else js_mask.vregs r }
  let js_xor : SailJoltState :=
    { js_shift with
      vregs := fun r =>
        if r = JoltISA.inlineTmp3 then
          js_shift.vregs JoltISA.inlineTmp2 ^^^ js_shift.vregs JoltISA.inlineTmp3
        else js_shift.vregs r }
  let js_and : SailJoltState :=
    { js_xor with
      vregs := fun r =>
        if r = JoltISA.inlineTmp3 then
          js_xor.vregs JoltISA.inlineTmp3 &&& js_xor.vregs JoltISA.inlineTmp0
        else js_xor.vregs r }
  let js_splice : SailJoltState :=
    { js_and with
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
    { js_lui with
      vregs := fun r =>
        if r = JoltISA.inlineTmp4 then
          jolt_virtual_pow2_value (js_lui.vregs JoltISA.inlineTmp3)
        else js_lui.vregs r }
  have hpow2_mask :
      (JoltISA.execInstr (.VirtualPow2 (.vreg JoltISA.inlineTmp4) (.vreg JoltISA.inlineTmp3) (0 : BitVec 64))).run js_lui =
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
    { js_mask with
      vregs := fun r =>
        if r = JoltISA.inlineTmp4 then
          jolt_virtual_pow2_value (js_mask.vregs JoltISA.inlineTmp3)
        else js_mask.vregs r }
  have hpow2_value :
      (JoltISA.execInstr (.VirtualPow2 (.vreg JoltISA.inlineTmp4) (.vreg JoltISA.inlineTmp3) (0 : BitVec 64))).run js_mask =
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
         .instr (JoltISA.Encoded.ORI (.vreg JoltISA.inlineTmp3) (.xreg (regidx.Regidx 0)) (-1 : BitVec 12)) <|
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
    { js_mask with
      vregs := fun r =>
        if r = JoltISA.inlineTmp0 then
          shift_bits_left rs2_val
            (Sail.BitVec.extractLsb (js_mask.vregs JoltISA.inlineTmp0) 5 0)
        else if r = JoltISA.inlineTmp4 then
          jolt_virtual_pow2_value (js_mask.vregs JoltISA.inlineTmp0)
        else js_mask.vregs r }
  let js_xor : SailJoltState :=
    { js_shift with
      vregs := fun r =>
        if r = JoltISA.inlineTmp0 then
          js_shift.vregs JoltISA.inlineTmp2 ^^^ js_shift.vregs JoltISA.inlineTmp0
        else js_shift.vregs r }
  let js_and : SailJoltState :=
    { js_xor with
      vregs := fun r =>
        if r = JoltISA.inlineTmp0 then
          js_xor.vregs JoltISA.inlineTmp0 &&& js_xor.vregs JoltISA.inlineTmp3
        else js_xor.vregs r }
  let js_splice : SailJoltState :=
    { js_and with
      vregs := fun r =>
        if r = JoltISA.inlineTmp2 then
          js_and.vregs JoltISA.inlineTmp2 ^^^ js_and.vregs JoltISA.inlineTmp0
        else js_and.vregs r }
  have hrs2_mask : rX_bits rs2 js_mask.sail = .ok rs2_val js_mask.sail := by
    simpa [hmask_sail] using hrs2
  let js_shift_pow2 : SailJoltState :=
    { js_mask with
      vregs := fun r =>
        if r = JoltISA.inlineTmp4 then
          jolt_virtual_pow2_value (js_mask.vregs JoltISA.inlineTmp0)
        else js_mask.vregs r }
  have hpow2_value :
      (JoltISA.execInstr (.VirtualPow2 (.vreg JoltISA.inlineTmp4) (.vreg JoltISA.inlineTmp0) (0 : BitVec 64))).run js_mask =
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
      .ok (Ok true) s')
    (h_ram : JoltISA.RAM_START_ADDRESS ≤ base.toNat)
    (hpriv : Assumptions.CurPrivilegeMachine js_store.sail)
    (hmprv : Assumptions.MstatusMprvZero js_store.sail)
    (hpmp : Assumptions.StorePmpOk base 8 js_store.sail)
    (hmmio : Assumptions.NotWritableMmio base 8 js_store.sail)
    (hjolt : Assumptions.JoltRamStoreOk base js_store) :
    ∃ js_write : SailJoltState,
      (JoltISA.execProgram (.instr (JoltISA.Encoded.SD (.vreg JoltISA.inlineTmp1) (.vreg JoltISA.inlineTmp2) 0) rest)).run js_store =
        (JoltISA.execProgram rest).run js_write ∧
      js_write.sail = s' ∧
      js_write.vregs = js_store.vregs := by
  let js_write : SailJoltState := { js_store with sail := s' }
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
      (JoltISA.execInstr (JoltISA.Encoded.SD (.vreg JoltISA.inlineTmp1) (.vreg JoltISA.inlineTmp2) 0)).run js_store =
        .ok RETIRE_SUCCESS js_write := by
    simpa [js_write] using
      (JoltISA.execInstr_sd_vreg_run_of_write
        JoltISA.inlineTmp1 JoltISA.inlineTmp2 (0 : BitVec 12) js_store s' hsd_align hwrite'
        (by simpa only [haddr] using h_ram)
        hpriv hmprv
        (by rw [haddr]; exact hpmp)
        (by rw [haddr]; exact hmmio)
        (by rw [haddr]; exact hjolt))
  refine ⟨js_write, ?_, rfl, rfl⟩
  rw [JoltISA.execProgram_instr_run_retire _ _ js_store js_write hsd]

end StoreProgramBlocks

end
