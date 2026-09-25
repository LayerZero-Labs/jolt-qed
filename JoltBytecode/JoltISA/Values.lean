/-
Copyright (c) 2026 Ari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ari 
-/
import JoltBytecode.JoltISA.Core
import JoltBytecode.JoltISA.semantic_helpers
import Mathlib.Tactic
import Mathlib.Data.BitVec

/-!
# Helper Functions

Often instruction execution needs helpers like `sign_extend`, 
or `ctz` (count trailing zeros of a bitstring).
This file contains commonly used values and helper methods, 
written in a way that makes Jolt CPU semantics more readable.

Proof-side characterisations of these helpers live in
`InstructionEquivalence/ValueLemmas.lean`.
-/

set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

-- ============================================================================
-- Count trailing zeros
-- ============================================================================

/-- Count trailing zeros of a natural number. Returns 0 for input 0. -/
def ctz (n : Nat) : Nat :=
  if n = 0 then 0
  else if n % 2 = 1 then 0
  else 1 + ctz (n / 2)
termination_by n

-- ============================================================================
-- Riscv pure-function reference definitions (Sail-equivalent abstractions)
-- The actual instruction will have monadic malarkey, here we find the key 
-- mathematical facts
-- ============================================================================

namespace Riscv

variable {w : Nat}

def mul (x y : BitVec w) : BitVec w := x * y
def slli (x : BitVec w) (shamt : Nat) : BitVec w := x <<< shamt
def ori (x imm : BitVec w) : BitVec w := x ||| imm
def andi (x y : BitVec w) : BitVec w := x &&& y

def sllw (rs1_val rs2_val : BitVec 64) : BitVec 64 :=
  ((rs1_val.setWidth 32) <<< (rs2_val.setWidth 5).toNat).signExtend 64

def srlw (rs1_val rs2_val : BitVec 64) : BitVec 64 :=
  ((rs1_val.setWidth 32) >>> (rs2_val.setWidth 5).toNat).signExtend 64

def sraw (rs1_val rs2_val : BitVec 64) : BitVec 64 :=
  ((rs1_val.setWidth 32).sshiftRight (rs2_val.setWidth 5).toNat).signExtend 64

def sll (x y : BitVec 64) : BitVec 64 := x <<< (y.setWidth 6).toNat
def srl (x y : BitVec 64) : BitVec 64 := x >>> (y.setWidth 6).toNat
def sra (rs1_val rs2_val : BitVec 64) : BitVec 64 :=
  rs1_val.sshiftRight (rs2_val.setWidth 6).toNat

def slli64 (rs1_val shamt : BitVec 64) : BitVec 64 := rs1_val <<< (shamt.setWidth 6).toNat
def srli64 (rs1_val shamt : BitVec 64) : BitVec 64 := rs1_val >>> (shamt.setWidth 6).toNat
def srai64 (rs1_val shamt : BitVec 64) : BitVec 64 := rs1_val.sshiftRight (shamt.setWidth 6).toNat

def slliw (rs1_val shamt : BitVec 64) : BitVec 64 :=
  ((rs1_val.setWidth 32) <<< (shamt.setWidth 5).toNat).signExtend 64

def srliw (rs1_val shamt : BitVec 64) : BitVec 64 :=
  ((rs1_val.setWidth 32) >>> (shamt.setWidth 5).toNat).signExtend 64

def sraiw (rs1_val shamt : BitVec 64) : BitVec 64 :=
  ((rs1_val.setWidth 32).sshiftRight (shamt.setWidth 5).toNat).signExtend 64

end Riscv

-- ============================================================================
-- Jolt-side value helpers
-- ============================================================================

-- Rust: [bitwise and comparison lookup outputs](/Users/ari.biswas/Work-with-A16z/jolt/crates/jolt-lookup-tables/src/instructions/riscv).
-- Transparent pure calculations shared by execInstr and witness extraction.
-- Keeping these transparent preserves the existing execution proof reductions.
abbrev jolt_xor_value (x y : BitVec 64) : BitVec 64 := x ^^^ y

abbrev jolt_andn_value (x y : BitVec 64) : BitVec 64 := x &&& Complement.complement y

abbrev jolt_slt_value (x y : BitVec 64) : BitVec 64 :=
  zero_extend (m := 64) (bool_to_bit (zopz0zI_s x y))

-- Rust: [JALR target](/Users/ari.biswas/Work-with-A16z/jolt/crates/jolt-lookup-tables/src/instructions/riscv/jalr.rs:29).
abbrev jolt_jalr_target64 (base : BitVec 64) (imm : BitVec 64) : BitVec 64 :=
  BitVec.update (BitVec.ofNat 64 (JoltISA.addWide base imm)) 0 0#1

abbrev jolt_jalr_target (base : BitVec 64) (imm : BitVec 12) : BitVec 64 :=
  BitVec.update (BitVec.ofNat 64 (JoltISA.addWide base (sign_extend (m := 64) imm))) 0 0#1

-- Rust: [AssertEq output](/Users/ari.biswas/Work-with-A16z/jolt/crates/jolt-lookup-tables/src/instructions/virt/assert_eq.rs:17).
-- Equality is still the lookup predicate when a nonzero immediate suppresses
-- the execution assertion; successful retirement alone does not imply equality.
abbrev jolt_assert_eq (x y : BitVec 64) : Prop := x = y

abbrev jolt_virtual_zero_extend_word_value (x : BitVec 64) : BitVec 64 :=
  zero_extend (m := 64) (Sail.BitVec.extractLsb x 31 0)

/-- RV64 `VirtualMovsign` value: all ones if the source sign bit is set,
otherwise zero. -/
def jolt_movsign_value (x : BitVec 64) : BitVec 64 :=
  if x.msb then (-1 : BitVec 64) else 0

/-- RV64 `MULHU` value: high 64 bits of the unsigned 64x64 product. -/
def jolt_mulhu_value (x y : BitVec 64) : BitVec 64 :=
  BitVec.ofNat 64 (JoltISA.mulWide x y / 2^64)

/-- RV64 `SLTU` value: one if `x < y` as unsigned 64-bit integers,
otherwise zero. -/
def jolt_sltu_value (x y : BitVec 64) : BitVec 64 :=
  zero_extend (m := 64) (bool_to_bit (zopz0zI_u x y))

/-- RV64 `ADDIW` value: add the sign-extended immediate, retain the low word,
then sign-extend that word. -/
abbrev jolt_addiw_value64 (x : BitVec 64) (imm : BitVec 64) : BitVec 64 :=
  ((BitVec.ofNat 64 (JoltISA.addWide x imm)).setWidth 32).signExtend 64

def jolt_addiw_value (x : BitVec 64) (imm : BitVec 12) : BitVec 64 :=
  ((BitVec.ofNat 64 (JoltISA.addWide x (sign_extend (m := 64) imm))).setWidth 32).signExtend 64

/-- Decode the source ADDIW immediate before using the final-row helper. -/
@[simp] theorem jolt_addiw_value64_encoded (x : BitVec 64) (imm : BitVec 12) :
    jolt_addiw_value64 x (sign_extend (m := 64) imm) = jolt_addiw_value x imm := rfl

/-- Rust keeps a signed branch immediate in i128 and wraps its execution to RV64. -/
@[simp] theorem encoded_branch_offset (imm : BitVec 13) :
    (sign_extend (m := 128) imm).setWidth 64 = sign_extend (m := 64) imm := by
  change (imm.signExtend 128).setWidth 64 = imm.signExtend 64
  bv_decide

/-- RV64 `ADDW` value. -/
def jolt_addw_value (x y : BitVec 64) : BitVec 64 :=
  ((BitVec.ofNat 64 (JoltISA.addWide x y)).setWidth 32).signExtend 64

/-- RV64 `SUBW` value. -/
def jolt_subw_value (x y : BitVec 64) : BitVec 64 :=
  ((BitVec.ofNat 64 (JoltISA.subWide x y)).setWidth 32).signExtend 64

/-- RV64 `MULW` value. Signed and unsigned multiplication have the same low
32-bit product, which is then sign-extended. -/
def jolt_mulw_value (x y : BitVec 64) : BitVec 64 :=
  ((BitVec.ofNat 64 (JoltISA.mulWide x y)).setWidth 32).signExtend 64

/-- RV64 `VirtualMULI` value: multiply by the immediate in the 64-bit word
ring.  In the Rust tracer this instruction writes the sign-extended machine
word after a wrapping multiply; for RV64 that is exactly the resulting
64-bit bit pattern. -/
def jolt_virtual_muli_value (x imm : BitVec 64) : BitVec 64 :=
  BitVec.ofNat 64 (JoltISA.mulWide x imm)

/-- RV64 `VirtualMULIW` value: wrapping multiplication followed by low-word
sign extension. -/
def jolt_virtual_muliw_value (x imm : BitVec 64) : BitVec 64 :=
  ((BitVec.ofNat 64 (JoltISA.mulWide x imm)).setWidth 32).signExtend 64

/-- RV64 `VirtualPow2` value: `2 ^ (x[5:0])`, used by `SLL`. -/
def jolt_virtual_pow2_value (x : BitVec 64) : BitVec 64 :=
  BitVec.ofNat 64 (2 ^ (x.setWidth 6).toNat)

/-- RV64 `VirtualPow2W` value: `2 ^ (x[4:0])`, used by `SLLW`. -/
def jolt_virtual_pow2w_value (x : BitVec 64) : BitVec 64 :=
  BitVec.ofNat 64 (2 ^ (x.setWidth 5).toNat)

/-- RV64 `VirtualPow2I` value: `2 ^ (imm % 64)`. -/
def jolt_virtual_pow2i_value (imm : Nat) : BitVec 64 :=
  BitVec.ofNat 64 (2 ^ (imm % 64))

/-- RV64 `VirtualPow2IW` value: `2 ^ (imm % 32)`. -/
def jolt_virtual_pow2iw_value (imm : Nat) : BitVec 64 :=
  BitVec.ofNat 64 (2 ^ (imm % 32))

/-- RV64 `VirtualShiftRightBitmask` value.

The tracer first masks the requested shift to six bits, then writes a word
whose trailing-zero count is exactly that shift.  Later `VirtualSRL` and
`VirtualSRA` consume this bitmask by taking `ctz`. -/
def jolt_virtual_shift_right_bitmask_value (x : BitVec 64) : BitVec 64 :=
  let shift := (x.setWidth 6).toNat
  let ones := (1 <<< (64 - shift)) - 1
  BitVec.ofNat 64 (ones <<< shift)

/-- RV64 `VirtualShiftRightBitmaskI` value. -/
def jolt_virtual_shift_right_bitmaski_value (imm : Nat) : BitVec 64 :=
  let shift := imm % 64
  let ones := (1 <<< (64 - shift)) - 1
  BitVec.ofNat 64 (ones <<< shift)

/-- RV64 `VirtualShiftRightBitmaskW` value. The low five source bits select
the shift, and the result's trailing-zero count encodes that shift. -/
def jolt_virtual_shift_right_bitmaskw_value (x : BitVec 64) : BitVec 64 :=
  let shift := (x.setWidth 5).toNat
  BitVec.ofNat 64 (2^32 - 2^shift)

/-- RV64 `VirtualSRLI` value: logical right shift by the trailing-zero count
of the encoded bitmask immediate. -/
def jolt_virtual_srli_value (x : BitVec 64) (bitmask : Nat) : BitVec 64 :=
  x >>> ctz bitmask

/-- RV64 `VirtualSRAI` value: arithmetic right shift by the trailing-zero
count of the encoded bitmask immediate. -/
def jolt_virtual_srai_value (x : BitVec 64) (bitmask : Nat) : BitVec 64 :=
  x.sshiftRight (ctz bitmask)

/-- RV64 `VirtualSRLIW` value: logically shift the low word by the encoded
mask's trailing-zero count, then sign-extend the word result.
A zero mask gives zero: Rust's `trailing_zeros` returns 64, and `checked_shr`
then yields 0, whereas `ctz 0 = 0` would leave the word unshifted.
Rust: tracer/src/instruction/virtual_srliw.rs::VirtualSRLIW::exec. -/
def jolt_virtual_srliw_value (x : BitVec 64) (bitmask : Nat) : BitVec 64 :=
  if bitmask = 0 then 0
  else ((x.setWidth 32) >>> ctz bitmask).signExtend 64

/-- RV64 `VirtualSRAIW` value: arithmetically shift the low word by the
encoded mask's trailing-zero count, then sign-extend it. -/
def jolt_virtual_sraiw_value (x : BitVec 64) (bitmask : Nat) : BitVec 64 :=
  ((x.setWidth 32).sshiftRight (ctz bitmask)).signExtend 64

/-- RV64 `VirtualSRL` value: logical right shift by `ctz` of the bitmask
stored in the second source register. -/
def jolt_virtual_srl_value (x bitmask : BitVec 64) : BitVec 64 :=
  x >>> ctz bitmask.toNat

/-- RV64 `VirtualSRA` value: arithmetic right shift by `ctz` of the bitmask
stored in the second source register. -/
def jolt_virtual_sra_value (x bitmask : BitVec 64) : BitVec 64 :=
  x.sshiftRight (ctz bitmask.toNat)

/-- RV64 `VirtualSRLW` value. -/
def jolt_virtual_srlw_value (x bitmask : BitVec 64) : BitVec 64 :=
  ((x.setWidth 32) >>> ctz bitmask.toNat).signExtend 64

/-- RV64 `VirtualSRAW` value. -/
def jolt_virtual_sraw_value (x bitmask : BitVec 64) : BitVec 64 :=
  ((x.setWidth 32).sshiftRight (ctz bitmask.toNat)).signExtend 64

/-- RV64 `VirtualROTRI` value: rotate right by the trailing-zero count of the
encoded bitmask immediate. -/
def jolt_virtual_rotri_value (x : BitVec 64) (bitmask : Nat) : BitVec 64 :=
  rotater x (ctz bitmask)

/-- RV64 `VirtualROTRIW` value: rotate the low word right, then zero-extend. -/
def jolt_virtual_rotriw_value (x : BitVec 64) (bitmask : Nat) : BitVec 64 :=
  zero_extend (m := 64) (rotater (Sail.BitVec.extractLsb x 31 0) (min (ctz bitmask) 32))

/-- RV64 `VirtualRev8W` value: reverse bytes separately in each 32-bit word. -/
def jolt_virtual_rev8w_value (x : BitVec 64) : BitVec 64 :=
  let lo : BitVec 32 := Sail.BitVec.extractLsb x 31 0
  let hi : BitVec 32 := Sail.BitVec.extractLsb x 63 32
  (rev8 hi) +++ (rev8 lo)

/-- RV64 `VirtualXORROT*` value. -/
def jolt_virtual_xorrot_value (rot : Nat) (x y : BitVec 64) : BitVec 64 :=
  rotater (x ^^^ y) rot

/-- RV64 `VirtualXORROTL1`: xor the first operand with the second rotated left once.
Rust: https://github.com/abiswas3/jolt/tree/main/tracer/src/instruction/virtual_xor_rotl1.rs -/
def jolt_virtual_xorrotl1_value (x y : BitVec 64) : BitVec 64 :=
  x ^^^ rotatel y 1

/-- RV64 `VirtualXORROTW*` value: xor low words, rotate, then zero-extend. -/
def jolt_virtual_xorrotw_value (rot : Nat) (x y : BitVec 64) : BitVec 64 :=
  zero_extend (m := 64)
    (rotater ((Sail.BitVec.extractLsb x 31 0) ^^^ (Sail.BitVec.extractLsb y 31 0)) rot)

/-- RV64 `VirtualAlignAddr` value: align `base + sext(imm)` down to its
containing doubleword. -/
abbrev jolt_virtual_align_addr_value64 (base : BitVec 64) (imm : BitVec 64) : BitVec 64 :=
  (BitVec.ofNat 64 (JoltISA.addWide base imm)) &&& ~~~(7 : BitVec 64)

def jolt_virtual_align_addr_value (base : BitVec 64) (imm : BitVec 12) : BitVec 64 :=
  (BitVec.ofNat 64 (JoltISA.addWide base (sign_extend (m := 64) imm))) &&& ~~~(7 : BitVec 64)

/-- RV64 `VirtualWindowMaskB` value. -/
abbrev jolt_virtual_window_mask_b_value64 (base : BitVec 64) (imm : BitVec 64) : BitVec 64 :=
  let ea := BitVec.ofNat 64 (JoltISA.addWide base imm)
  let offset := (ea &&& (7 : BitVec 64)).toNat
  BitVec.ofNat 64 (0xFF <<< (8 * offset))

def jolt_virtual_window_mask_b_value (base : BitVec 64) (imm : BitVec 12) : BitVec 64 :=
  let ea := BitVec.ofNat 64 (JoltISA.addWide base (sign_extend (m := 64) imm))
  let offset := (ea &&& (7 : BitVec 64)).toNat
  BitVec.ofNat 64 (0xFF <<< (8 * offset))

/-- RV64 `VirtualWindowMaskH` value. Bit zero of the effective address is
ignored, matching the tracer's `ea & 6`. -/
abbrev jolt_virtual_window_mask_h_value64 (base : BitVec 64) (imm : BitVec 64) : BitVec 64 :=
  let ea := BitVec.ofNat 64 (JoltISA.addWide base imm)
  let offset := (ea &&& (6 : BitVec 64)).toNat
  BitVec.ofNat 64 (0xFFFF <<< (8 * offset))

def jolt_virtual_window_mask_h_value (base : BitVec 64) (imm : BitVec 12) : BitVec 64 :=
  let ea := BitVec.ofNat 64 (JoltISA.addWide base (sign_extend (m := 64) imm))
  let offset := (ea &&& (6 : BitVec 64)).toNat
  BitVec.ofNat 64 (0xFFFF <<< (8 * offset))

/-- RV64 `VirtualWindowMaskW` value. Only effective-address bit two selects
the low or high word lane. -/
abbrev jolt_virtual_window_mask_w_value64 (base : BitVec 64) (imm : BitVec 64) : BitVec 64 :=
  let ea := BitVec.ofNat 64 (JoltISA.addWide base imm)
  let word := ((ea >>> 2) &&& (1 : BitVec 64)).toNat
  BitVec.ofNat 64 (0xFFFF_FFFF <<< (32 * word))

def jolt_virtual_window_mask_w_value (base : BitVec 64) (imm : BitVec 12) : BitVec 64 :=
  let ea := BitVec.ofNat 64 (JoltISA.addWide base (sign_extend (m := 64) imm))
  let word := ((ea >>> 2) &&& (1 : BitVec 64)).toNat
  BitVec.ofNat 64 (0xFFFF_FFFF <<< (32 * word))

/-- RV64 `VirtualShiftDataB` value. -/
def jolt_virtual_shift_data_b_value (value address : BitVec 64) : BitVec 64 :=
  let offset := (address &&& (7 : BitVec 64)).toNat
  (value &&& (0xFF : BitVec 64)) <<< (8 * offset)

/-- RV64 `VirtualShiftDataH` value. Bit zero of the effective address is ignored. -/
def jolt_virtual_shift_data_h_value (value address : BitVec 64) : BitVec 64 :=
  let offset := (address &&& (6 : BitVec 64)).toNat
  (value &&& (0xFFFF : BitVec 64)) <<< (8 * offset)

/-- RV64 `VirtualShiftDataW` value. Only effective-address bit two selects the lane. -/
def jolt_virtual_shift_data_w_value (value address : BitVec 64) : BitVec 64 :=
  let offset := (address &&& (4 : BitVec 64)).toNat
  (value &&& (0xFFFF_FFFF : BitVec 64)) <<< (8 * offset)

/-- Recursive implementation used by `VirtualPext`. The first argument bounds
the number of source/mask bits inspected. `execInstr` always supplies 64. -/
def jolt_pext_nat : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | fuel + 1, x, mask =>
      if mask % 2 = 1 then
        x % 2 + 2 * jolt_pext_nat fuel (x / 2) (mask / 2)
      else
        jolt_pext_nat fuel (x / 2) (mask / 2)

/-- Count the set bits in the low `fuel` positions of a natural number. -/
def jolt_popcount_nat : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, x => x % 2 + jolt_popcount_nat fuel (x / 2)

/-- RV64 `VirtualPext` value. -/
def jolt_virtual_pext_value (x mask : BitVec 64) : BitVec 64 :=
  BitVec.ofNat 64 (jolt_pext_nat 64 x.toNat mask.toNat)

/-- RV64 `VirtualPextSigned` value: parallel-extract, then sign-extend from
the highest extracted bit. -/
def jolt_virtual_pext_signed_value (x mask : BitVec 64) : BitVec 64 :=
  let width := jolt_popcount_nat 64 mask.toNat
  if width = 0 then
    0
  else
    let extracted := jolt_virtual_pext_value x mask
    if extracted.getLsbD (width - 1) then
      let lowMask : BitVec 64 := BitVec.ofNat 64 (2^width - 1)
      extracted ||| ~~~lowMask
    else
      extracted

/-- RV64 `VirtualNegateIf` value. The first operand supplies only its sign;
negation is wrapping in the 64-bit ring. -/
def jolt_virtual_negate_if_value (signSource value : BitVec 64) : BitVec 64 :=
  if signSource.msb then -value else value

/-- RV64 `VirtualSignExtendWord` value: sign-extend the low 32 bits to 64
bits. -/
def jolt_virtual_sign_extend_word_value (x : BitVec 64) : BitVec 64 :=
  (x.setWidth 32).signExtend 64

/-- Upper 64 bits of a signed 64×64 multiply. -/
def mulhs (a b : BitVec 64) : BitVec 64 :=
  BitVec.ofInt 64 ((a.toInt * b.toInt) / (2 ^ 64))

end
