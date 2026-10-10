import JoltConstraints.Constraints.LookupOperandData
import JoltConstraints.Soundness.Layer4.WordEntry
import JoltConstraints.Soundness.Layer4.BitwiseEntry
import JoltConstraints.Soundness.Layer4.ComparisonEntry
import JoltConstraints.Soundness.Layer4.ConditionalEntry
import JoltConstraints.Soundness.Layer4.RotateEntry
import JoltConstraints.Completeness.Helpers.LookupWriteProofHelpers
import JoltConstraints.Completeness.Helpers.LookupPextProofHelpers
import JoltConstraints.Completeness.Helpers.LookupShiftProofHelpers

/-!
# Per-table obligations for constraint (39)

Constraint (39) says that on an execution row the lookup output equals the
selected table entry at the honest lookup address. After the address sum and the
table sum are collapsed (see `LookupOutputEqInstructionReadRaf.lean`), what is
left is one obligation per `LookupTableKind`:

  lookupTableEntry k (rowLookupAddress row) = rowLookupOutput row.toTraceRow

whenever the row's instruction uses table `k`. This file states that obligation
as `LookupEntryCorrect` and proves it table by table as
`lookupEntryCorrect_<Table>`. `lookupEntryCorrect_of_lookupTable` dispatches on
the table.
-/

set_option autoImplicit false

namespace JoltConstraints

open TraceWitness
open Sail PreSail LeanRV64D.Functions

/-- The expanded instruction executed by a trace row. -/
abbrev rowInstruction {bytecode : Array JoltInstructionRow} (row : HonestTraceRow bytecode) : JoltISA.Instr :=
  (getElem bytecode row.rowIndex.val row.rowIndex.isLt).instruction

/-- The honest 128-bit lookup index of an execution row. -/
noncomputable def rowLookupIndex {bytecode : Array JoltInstructionRow} (row : HonestTraceRow bytecode) :
    BitVec 128 :=
  let bc := getElem bytecode row.rowIndex.val row.rowIndex.isLt
  instructionLookupIndex bc.instruction bc.address row.preState row.postState

/-- The honest lookup index as a table address. -/
noncomputable def rowLookupAddress {bytecode : Array JoltInstructionRow} (row : HonestTraceRow bytecode) :
    Fin (2 ^ 128) :=
  (rowLookupIndex row).toFin

/-- The per-table obligation of constraint (39): table `table` at the honest
address is the honest lookup output. -/
def LookupEntryCorrect (F : Type) [Field F] {bytecode : Array JoltInstructionRow}
    (table : LookupTableKind) (row : HonestTraceRow bytecode) : Prop :=
  lookupTableEntry (F := F) table (rowLookupAddress row) = ((rowLookupOutput row.toTraceRow).toNat : F)

/-! ## Wide arithmetic as bit-vector arithmetic -/

theorem ofNat128_addWide (x y : BitVec 64) :
    BitVec.ofNat 128 (JoltISA.addWide x y) = x.setWidth 128 + y.setWidth 128 := by
  apply BitVec.eq_of_toNat_eq
  have hx := x.isLt; have hy := y.isLt
  simp only [JoltISA.addWide, BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_setWidth]
  omega

theorem ofNat64_addWide (x y : BitVec 64) :
    BitVec.ofNat 64 (JoltISA.addWide x y) = x + y := by
  apply BitVec.eq_of_toNat_eq
  simp only [JoltISA.addWide, BitVec.toNat_ofNat, BitVec.toNat_add]

theorem ofNat128_mulWide (x y : BitVec 64) :
    BitVec.ofNat 128 (JoltISA.mulWide x y) = x.setWidth 128 * y.setWidth 128 := by
  apply BitVec.eq_of_toNat_eq
  have hx := x.isLt; have hy := y.isLt
  have hxy : x.toNat * y.toNat < 2 ^ 128 := by
    calc x.toNat * y.toNat < 2 ^ 64 * 2 ^ 64 := Nat.mul_lt_mul'' hx hy
      _ = 2 ^ 128 := by norm_num
  simp only [JoltISA.mulWide, BitVec.toNat_ofNat, BitVec.toNat_mul, BitVec.toNat_setWidth]
  rw [Nat.mod_eq_of_lt (a := x.toNat) (by omega), Nat.mod_eq_of_lt (a := y.toNat) (by omega),
    Nat.mod_eq_of_lt hxy]

/-! ## Table entries at honest addresses -/

section entries
variable {F : Type} [Field F]

theorem cast_ite_one_zero (c : Prop) [Decidable c] :
    (((if c then (1 : BitVec 64) else 0).toNat : F)) = if c then 1 else 0 := by
  split <;> simp

end entries

theorem jolt_slt_value_eq (x y : BitVec 64) :
    jolt_slt_value x y = if x.toInt < y.toInt then 1 else 0 := by
  unfold jolt_slt_value zopz0zI_s bool_to_bit bool_bit_forwards zero_extend Sail.BitVec.zeroExtend
  by_cases hc : x.toInt < y.toInt <;> simp [hc]

theorem toNatInt_lt (x y : BitVec 64) : (BitVec.toNatInt x < BitVec.toNatInt y) ↔ x < y := by
  simp [BitVec.toNatInt, BitVec.lt_def]

theorem toNatInt_ge (x y : BitVec 64) : (BitVec.toNatInt x ≥ BitVec.toNatInt y) ↔ x ≥ y := by
  simp [BitVec.toNatInt, BitVec.le_def]

theorem jolt_sltu_value_eq (x y : BitVec 64) :
    jolt_sltu_value x y = if x < y then 1 else 0 := by
  unfold jolt_sltu_value zopz0zI_u bool_to_bit bool_bit_forwards zero_extend Sail.BitVec.zeroExtend
  by_cases hc : x < y <;> simp [hc, toNatInt_lt]


theorem row_executes_exists {bytecode : Array JoltInstructionRow} (row : HonestTraceRow bytecode) :
    ∃ advice : (rowInstruction row).RuntimeAdvice,
      JoltISA.execInstr ((rowInstruction row).withRuntimeAdvice advice) row.preState =
        .ok (.Retire_Success ()) row.postState :=
  ⟨row.runtimeAdvice, row.executes⟩

theorem upper_zero_of_lt (n : Nat) (h : n < 2 ^ 64) : BitVec.ofNat 128 n >>> 64 = 0 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt (by omega), Nat.div_eq_of_lt h]
  rfl

/-! ## Per-table obligations -/

section tables
variable {F : Type} [Field F] {bytecode : Array JoltInstructionRow}

set_option hygiene false in
/-- Split on the row instruction, keep the instructions that use the table, and
unfold the index, output and table definitions. -/
macro "lookup_cases" : tactic => `(tactic| (
  unfold LookupEntryCorrect rowLookupAddress rowLookupIndex
  cases hi : rowInstruction row <;>
    simp only [hi, JoltMetadata.lookupTable, reduceCtorEq, Option.some.injEq] at h <;>
    simp only [lookupTableEntry, rowLookupOutput, instructionLookupIndex, hi]))

theorem lookupEntryCorrect_RangeCheck (row : HonestTraceRow bytecode)
    (h : JoltMetadata.lookupTable (rowInstruction row) = some .RangeCheck) :
    LookupEntryCorrect F .RangeCheck row := by
  lookup_cases
  all_goals simp only [rangeCheck_entry]
  all_goals simp [ BitVec.setWidth_ofNat_of_le, BitVec.setWidth_setWidth_of_le,
    jolt_virtual_muli_value]

theorem lookupEntryCorrect_And (row : HonestTraceRow bytecode)
    (h : JoltMetadata.lookupTable (rowInstruction row) = some .And) :
    LookupEntryCorrect F .And row := by
  lookup_cases
  all_goals simp only [and_entry, Riscv.andi]

theorem lookupEntryCorrect_Or (row : HonestTraceRow bytecode)
    (h : JoltMetadata.lookupTable (rowInstruction row) = some .Or) :
    LookupEntryCorrect F .Or row := by
  lookup_cases
  all_goals simp only [or_entry, Riscv.ori]

theorem lookupEntryCorrect_Xor (row : HonestTraceRow bytecode)
    (h : JoltMetadata.lookupTable (rowInstruction row) = some .Xor) :
    LookupEntryCorrect F .Xor row := by
  lookup_cases
  all_goals simp only [xor_entry, jolt_xor_value]

theorem lookupEntryCorrect_Andn (row : HonestTraceRow bytecode)
    (h : JoltMetadata.lookupTable (rowInstruction row) = some .Andn) :
    LookupEntryCorrect F .Andn row := by
  lookup_cases
  all_goals simp only [andn_entry, jolt_andn_value]

theorem lookupEntryCorrect_SignedLessThan (row : HonestTraceRow bytecode)
    (h : JoltMetadata.lookupTable (rowInstruction row) = some .SignedLessThan) :
    LookupEntryCorrect F .SignedLessThan row := by
  lookup_cases
  all_goals simp only [signedLessThan_entry, jolt_slt_value_eq, cast_ite_one_zero,
    JoltISA.branchDecisionPure, zopz0zI_s, decide_eq_true_eq]

theorem lookupEntryCorrect_UnsignedLessThan (row : HonestTraceRow bytecode)
    (h : JoltMetadata.lookupTable (rowInstruction row) = some .UnsignedLessThan) :
    LookupEntryCorrect F .UnsignedLessThan row := by
  lookup_cases
  all_goals simp only [unsignedLessThan_entry, jolt_sltu_value_eq, cast_ite_one_zero,
    JoltISA.branchDecisionPure, zopz0zI_u, decide_eq_true_eq, toNatInt_lt]

theorem lookupEntryCorrect_SignedGreaterThanEqual (row : HonestTraceRow bytecode)
    (h : JoltMetadata.lookupTable (rowInstruction row) = some .SignedGreaterThanEqual) :
    LookupEntryCorrect F .SignedGreaterThanEqual row := by
  lookup_cases
  all_goals simp only [signedGreaterThanEqual_entry, cast_ite_one_zero,
    JoltISA.branchDecisionPure, zopz0zKzJ_s, decide_eq_true_eq]

theorem lookupEntryCorrect_UnsignedGreaterThanEqual (row : HonestTraceRow bytecode)
    (h : JoltMetadata.lookupTable (rowInstruction row) = some .UnsignedGreaterThanEqual) :
    LookupEntryCorrect F .UnsignedGreaterThanEqual row := by
  lookup_cases
  all_goals simp only [unsignedGreaterThanEqual_entry, cast_ite_one_zero,
    JoltISA.branchDecisionPure, zopz0zKzJ_u, decide_eq_true_eq, toNatInt_ge]

theorem lookupEntryCorrect_Equal (row : HonestTraceRow bytecode)
    (h : JoltMetadata.lookupTable (rowInstruction row) = some .Equal) :
    LookupEntryCorrect F .Equal row := by
  lookup_cases
  all_goals simp only [equal_entry, cast_ite_one_zero, JoltISA.branchDecisionPure,
    beq_iff_eq, jolt_assert_eq]

theorem lookupEntryCorrect_NotEqual (row : HonestTraceRow bytecode)
    (h : JoltMetadata.lookupTable (rowInstruction row) = some .NotEqual) :
    LookupEntryCorrect F .NotEqual row := by
  lookup_cases
  all_goals simp only [notEqual_entry, cast_ite_one_zero, JoltISA.branchDecisionPure,
    bne_iff_ne, ne_eq]

end tables

section entries2
variable {F : Type} [Field F]

theorem shiftLeft_ofNat_eq (c k : Nat) :
    BitVec.ofNat 64 c <<< k = BitVec.ofNat 64 (c <<< k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  rw [Nat.mod_mul_mod]

theorem toNat_eq_of_setWidth (a : BitVec 128) (b : BitVec 64) (h : a = b.setWidth 128) :
    a.toNat = b.toNat := by
  rw [h, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := b.isLt; omega)]

theorem ofNat64_eq_setWidth (n : Nat) :
    BitVec.ofNat 64 n = (BitVec.ofNat 128 n).setWidth 64 := by
  rw [BitVec.setWidth_ofNat_of_le (by norm_num)]

theorem windowMaskB_entry (n : Nat) :
    windowMaskBTableEntry (F := F) (BitVec.ofNat 128 n).toFin =
      ((BitVec.ofNat 64 (0xFF <<< (8 * (BitVec.ofNat 64 n &&& 7).toNat))).toNat : F) := by
  have hm : ((1#128 <<< 8) - 1).setWidth 64 = BitVec.ofNat 64 0xFF := by decide
  have ho : (BitVec.ofNat 128 n &&& 7).toNat = (BitVec.ofNat 64 n &&& 7).toNat :=
    toNat_eq_of_setWidth _ _ (by rw [ofNat64_eq_setWidth]; bv_decide)
  simp only [windowMaskBTableEntry, BitVec.ofFin_toFin, hm, shiftLeft_ofNat_eq, ho]

theorem windowMaskH_entry (n : Nat) :
    windowMaskHTableEntry (F := F) (BitVec.ofNat 128 n).toFin =
      ((BitVec.ofNat 64 (0xFFFF <<< (8 * (BitVec.ofNat 64 n &&& 6).toNat))).toNat : F) := by
  have hm : ((1#128 <<< 16) - 1).setWidth 64 = BitVec.ofNat 64 0xFFFF := by decide
  have ho : (BitVec.ofNat 128 n &&& 6).toNat = (BitVec.ofNat 64 n &&& 6).toNat :=
    toNat_eq_of_setWidth _ _ (by rw [ofNat64_eq_setWidth]; bv_decide)
  simp only [windowMaskHTableEntry, BitVec.ofFin_toFin, hm, shiftLeft_ofNat_eq, ho]

theorem windowMaskW_entry (n : Nat) :
    windowMaskWTableEntry (F := F) (BitVec.ofNat 128 n).toFin =
      ((BitVec.ofNat 64 (0xFFFF_FFFF <<< (32 * ((BitVec.ofNat 64 n >>> 2) &&& 1).toNat))).toNat : F) := by
  have hm : ((1#128 <<< 32) - 1).setWidth 64 = BitVec.ofNat 64 0xFFFF_FFFF := by decide
  have ho : ((BitVec.ofNat 128 n >>> 2) &&& 1).toNat = ((BitVec.ofNat 64 n >>> 2) &&& 1).toNat :=
    toNat_eq_of_setWidth _ _ (by rw [ofNat64_eq_setWidth]; bv_decide)
  simp only [windowMaskWTableEntry, BitVec.ofFin_toFin, hm, shiftLeft_ofNat_eq, ho]

theorem halfword_aligned (n : Nat) (h : BitVec.ofNat 64 n &&& 1 = 0) :
    BitVec.ofNat 128 n % 2 = 0 := by
  rw [ofNat64_eq_setWidth] at h
  generalize BitVec.ofNat 128 n = v at h ⊢
  bv_decide

theorem word_aligned (n : Nat) (h : BitVec.ofNat 64 n &&& 3 = 0) :
    BitVec.ofNat 128 n % 4 = 0 := by
  rw [ofNat64_eq_setWidth] at h
  generalize BitVec.ofNat 128 n = v at h ⊢
  bv_decide

end entries2

theorem mulWide_lt (x y : BitVec 64) : JoltISA.mulWide x y < 2 ^ 128 := by
  have hx := x.isLt; have hy := y.isLt
  calc x.toNat * y.toNat < 2 ^ 64 * 2 ^ 64 := Nat.mul_lt_mul'' hx hy
    _ = 2 ^ 128 := by norm_num

section tables2
variable {F : Type} [Field F] {bytecode : Array JoltInstructionRow}

theorem lookupEntryCorrect_SignExtendWord (row : HonestTraceRow bytecode)
    (h : JoltMetadata.lookupTable (rowInstruction row) = some .SignExtendWord) :
    LookupEntryCorrect F .SignExtendWord row := by
  lookup_cases
  all_goals simp only [signExtendWord_entry]
  all_goals simp only [jolt_addiw_value64, jolt_addw_value,
    jolt_subw_value, jolt_mulw_value, jolt_virtual_muliw_value, jolt_virtual_sign_extend_word_value,
    BitVec.setWidth_ofNat_of_le (by norm_num : 32 ≤ 128), BitVec.setWidth_ofNat_of_le (by norm_num : 32 ≤ 64),
    BitVec.setWidth_setWidth_of_le _ (by norm_num : 32 ≤ 128)]

theorem lookupEntryCorrect_UpperWord (row : HonestTraceRow bytecode)
    (h : JoltMetadata.lookupTable (rowInstruction row) = some .UpperWord) :
    LookupEntryCorrect F .UpperWord row := by
  lookup_cases
  rw [upperWord_entry _ (mulWide_lt _ _)]
  rfl

theorem lookupEntryCorrect_LowerHalfWord (row : HonestTraceRow bytecode)
    (h : JoltMetadata.lookupTable (rowInstruction row) = some .LowerHalfWord) :
    LookupEntryCorrect F .LowerHalfWord row := by
  lookup_cases
  simp only [lowerHalfWord_entry, jolt_virtual_zero_extend_word_value, zero_extend,
    Sail.BitVec.zeroExtend, Sail.BitVec.extractLsb]
  congr 2

theorem lookupEntryCorrect_RangeCheckAligned (row : HonestTraceRow bytecode)
    (h : JoltMetadata.lookupTable (rowInstruction row) = some .RangeCheckAligned) :
    LookupEntryCorrect F .RangeCheckAligned row := by
  lookup_cases
  simp only [rangeCheckAligned_entry, jolt_jalr_target64, BitVec.setWidth_ofNat_of_le (by norm_num : 64 ≤ 128),
    Sail.BitVec.update, Sail.BitVec.updateSubrange']
  congr 2
  bv_decide

theorem lookupEntryCorrect_AlignAddr (row : HonestTraceRow bytecode)
    (h : JoltMetadata.lookupTable (rowInstruction row) = some .AlignAddr) :
    LookupEntryCorrect F .AlignAddr row := by
  lookup_cases
  simp only [alignAddr_entry, jolt_virtual_align_addr_value64,
    BitVec.setWidth_ofNat_of_le (by norm_num : 64 ≤ 128)]
  rfl

theorem lookupEntryCorrect_SignMask (row : HonestTraceRow bytecode)
    (h : JoltMetadata.lookupTable (rowInstruction row) = some .SignMask) :
    LookupEntryCorrect F .SignMask row := by
  lookup_cases
  simp only [signMask_entry, jolt_movsign_value]

theorem lookupEntryCorrect_VirtualNegateIf (row : HonestTraceRow bytecode)
    (h : JoltMetadata.lookupTable (rowInstruction row) = some .VirtualNegateIf) :
    LookupEntryCorrect F .VirtualNegateIf row := by
  lookup_cases
  simp only [negateIf_entry, jolt_virtual_negate_if_value]

theorem lookupEntryCorrect_Pow2 (row : HonestTraceRow bytecode)
    (h : JoltMetadata.lookupTable (rowInstruction row) = some .Pow2) :
    LookupEntryCorrect F .Pow2 row := by
  lookup_cases
  all_goals simp only [pow2_entry, jolt_virtual_pow2_value, jolt_virtual_pow2i_value]
  all_goals congr 4
  all_goals simp [BitVec.toNat_setWidth, Nat.mod_mod_of_dvd]

theorem lookupEntryCorrect_Pow2W (row : HonestTraceRow bytecode)
    (h : JoltMetadata.lookupTable (rowInstruction row) = some .Pow2W) :
    LookupEntryCorrect F .Pow2W row := by
  lookup_cases
  all_goals simp only [pow2W_entry, jolt_virtual_pow2w_value, jolt_virtual_pow2iw_value]
  all_goals congr 4
  all_goals simp [BitVec.toNat_setWidth, Nat.mod_mod_of_dvd]

theorem lookupEntryCorrect_ShiftRightBitmask (row : HonestTraceRow bytecode)
    (h : JoltMetadata.lookupTable (rowInstruction row) = some .ShiftRightBitmask) :
    LookupEntryCorrect F .ShiftRightBitmask row := by
  lookup_cases
  all_goals simp only [shiftRightBitmask_entry, jolt_virtual_shift_right_bitmask_value,
    jolt_virtual_shift_right_bitmaski_value]
  all_goals congr 4 <;> simp [BitVec.toNat_setWidth, Nat.mod_mod_of_dvd]

theorem lookupEntryCorrect_ShiftRightBitmaskW (row : HonestTraceRow bytecode)
    (h : JoltMetadata.lookupTable (rowInstruction row) = some .ShiftRightBitmaskW) :
    LookupEntryCorrect F .ShiftRightBitmaskW row := by
  lookup_cases
  simp only [shiftRightBitmaskW_entry, jolt_virtual_shift_right_bitmaskw_value]
  congr 5

theorem lookupEntryCorrect_ShiftDataB (row : HonestTraceRow bytecode)
    (h : JoltMetadata.lookupTable (rowInstruction row) = some .ShiftDataB) :
    LookupEntryCorrect F .ShiftDataB row := by
  lookup_cases
  simp only [shiftDataB_entry]

theorem lookupEntryCorrect_ShiftDataH (row : HonestTraceRow bytecode)
    (h : JoltMetadata.lookupTable (rowInstruction row) = some .ShiftDataH) :
    LookupEntryCorrect F .ShiftDataH row := by
  lookup_cases
  simp only [shiftDataH_entry]

theorem lookupEntryCorrect_ShiftDataW (row : HonestTraceRow bytecode)
    (h : JoltMetadata.lookupTable (rowInstruction row) = some .ShiftDataW) :
    LookupEntryCorrect F .ShiftDataW row := by
  lookup_cases
  simp only [shiftDataW_entry]

theorem lookupEntryCorrect_WindowMaskB (row : HonestTraceRow bytecode)
    (h : JoltMetadata.lookupTable (rowInstruction row) = some .WindowMaskB) :
    LookupEntryCorrect F .WindowMaskB row := by
  lookup_cases
  simp only [windowMaskB_entry, jolt_virtual_window_mask_b_value64]

theorem lookupEntryCorrect_WindowMaskH (row : HonestTraceRow bytecode)
    (h : JoltMetadata.lookupTable (rowInstruction row) = some .WindowMaskH) :
    LookupEntryCorrect F .WindowMaskH row := by
  lookup_cases
  simp only [windowMaskH_entry, jolt_virtual_window_mask_h_value64]

theorem lookupEntryCorrect_WindowMaskW (row : HonestTraceRow bytecode)
    (h : JoltMetadata.lookupTable (rowInstruction row) = some .WindowMaskW) :
    LookupEntryCorrect F .WindowMaskW row := by
  lookup_cases
  simp only [windowMaskW_entry, jolt_virtual_window_mask_w_value64]

theorem lookupEntryCorrect_VirtualXORROTL1 (row : HonestTraceRow bytecode)
    (h : JoltMetadata.lookupTable (rowInstruction row) = some .VirtualXORROTL1) :
    LookupEntryCorrect F .VirtualXORROTL1 row := by
  lookup_cases
  simp only [xorRotL1_entry]

theorem lookupEntryCorrect_VirtualXORROT32 (row : HonestTraceRow bytecode)
    (h : JoltMetadata.lookupTable (rowInstruction row) = some .VirtualXORROT32) :
    LookupEntryCorrect F .VirtualXORROT32 row := by
  lookup_cases
  exact xorRot_entry 32 (by decide) _ _

theorem lookupEntryCorrect_VirtualXORROT24 (row : HonestTraceRow bytecode)
    (h : JoltMetadata.lookupTable (rowInstruction row) = some .VirtualXORROT24) :
    LookupEntryCorrect F .VirtualXORROT24 row := by
  lookup_cases
  exact xorRot_entry 24 (by decide) _ _

theorem lookupEntryCorrect_VirtualXORROT16 (row : HonestTraceRow bytecode)
    (h : JoltMetadata.lookupTable (rowInstruction row) = some .VirtualXORROT16) :
    LookupEntryCorrect F .VirtualXORROT16 row := by
  lookup_cases
  exact xorRot_entry 16 (by decide) _ _

theorem lookupEntryCorrect_VirtualXORROT63 (row : HonestTraceRow bytecode)
    (h : JoltMetadata.lookupTable (rowInstruction row) = some .VirtualXORROT63) :
    LookupEntryCorrect F .VirtualXORROT63 row := by
  lookup_cases
  exact xorRot_entry 63 (by decide) _ _

theorem lookupEntryCorrect_VirtualXORROTW16 (row : HonestTraceRow bytecode)
    (h : JoltMetadata.lookupTable (rowInstruction row) = some .VirtualXORROTW16) :
    LookupEntryCorrect F .VirtualXORROTW16 row := by
  lookup_cases
  exact xorRotW_entry 16 (by decide) _ _

theorem lookupEntryCorrect_VirtualXORROTW12 (row : HonestTraceRow bytecode)
    (h : JoltMetadata.lookupTable (rowInstruction row) = some .VirtualXORROTW12) :
    LookupEntryCorrect F .VirtualXORROTW12 row := by
  lookup_cases
  exact xorRotW_entry 12 (by decide) _ _

theorem lookupEntryCorrect_VirtualXORROTW8 (row : HonestTraceRow bytecode)
    (h : JoltMetadata.lookupTable (rowInstruction row) = some .VirtualXORROTW8) :
    LookupEntryCorrect F .VirtualXORROTW8 row := by
  lookup_cases
  exact xorRotW_entry 8 (by decide) _ _

theorem lookupEntryCorrect_VirtualXORROTW7 (row : HonestTraceRow bytecode)
    (h : JoltMetadata.lookupTable (rowInstruction row) = some .VirtualXORROTW7) :
    LookupEntryCorrect F .VirtualXORROTW7 row := by
  lookup_cases
  exact xorRotW_entry 7 (by decide) _ _

theorem lookupEntryCorrect_VirtualXORROTW22 (row : HonestTraceRow bytecode)
    (h : JoltMetadata.lookupTable (rowInstruction row) = some .VirtualXORROTW22) :
    LookupEntryCorrect F .VirtualXORROTW22 row := by
  lookup_cases
  exact xorRotW_entry 22 (by decide) _ _

theorem lookupEntryCorrect_VirtualXORROTW19 (row : HonestTraceRow bytecode)
    (h : JoltMetadata.lookupTable (rowInstruction row) = some .VirtualXORROTW19) :
    LookupEntryCorrect F .VirtualXORROTW19 row := by
  lookup_cases
  exact xorRotW_entry 19 (by decide) _ _

theorem lookupEntryCorrect_VirtualXORROTW6 (row : HonestTraceRow bytecode)
    (h : JoltMetadata.lookupTable (rowInstruction row) = some .VirtualXORROTW6) :
    LookupEntryCorrect F .VirtualXORROTW6 row := by
  lookup_cases
  exact xorRotW_entry 6 (by decide) _ _

theorem rev8_32 (x : BitVec 32) : rev8 x = swapBytes32 x := by
  unfold rev8
  simp only [Id.run]
  change IntRange.forIn' _ _ _ >>= _ = _
  unfold IntRange.forIn'
  simp only [Sail.BitVec.length, BitVec.length, Nat.cast_ofNat]
  iterate 5
    rw [IntRange.forIn'.loop]
    simp (config := { decide := true }) only [Membership.mem, dite_true, dite_false, pure_bind,
      bind_pure, Int.reduceAdd, Int.reduceSub, Int.reduceToNat]
  change BitVec.updateSubrange _ _ _ _ = _
  simp only [BitVec.updateSubrange, Sail.BitVec.updateSubrange', Sail.BitVec.extractLsb,
    zeros, swapBytes32, Nat.reduceSub, Nat.reduceAdd]
  bv_decide

theorem rev8w_eq (v : BitVec 64) :
    rev8w v = swapBytes32 (v.extractLsb 63 32) +++ swapBytes32 (v.extractLsb 31 0) := by
  simp only [rev8w, swapBytes32]
  bv_decide

theorem lookupEntryCorrect_VirtualRev8W (row : HonestTraceRow bytecode)
    (h : JoltMetadata.lookupTable (rowInstruction row) = some .VirtualRev8W) :
    LookupEntryCorrect F .VirtualRev8W row := by
  lookup_cases
  simp only [virtualRev8WTableEntry, BitVec.ofFin_toFin, jolt_virtual_rev8w_value, rev8_32,
    Sail.BitVec.extractLsb, BitVec.setWidth_setWidth_of_le _ (by norm_num : 64 ≤ 128)]
  rw [BitVec.setWidth_eq, rev8w_eq]


/-! ## Shift masks

The shift tables are correct only when the shift's mask is a right-shift bitmask.
`ShiftMaskOk` says so for a row; `shiftMaskOk_of_honest` proves it for every row of
an honest trace, from the expansions: an immediate mask is a bitmask in the bytecode,
and a register mask was written by the `VirtualShiftRightBitmask(W)` row just before.
-/

/-- The mask a shift row reads is a right-shift bitmask, and no rotate runs. -/
def ShiftMaskOk (instruction : JoltISA.Instr) (state : SailJoltState) : Prop :=
  match instruction with
  | .VirtualSRLI _ _ mask | .VirtualSRAI _ _ mask =>
      ∃ s < 64, mask = ExpansionFacts.rightShiftMask s
  | .VirtualSRLIW _ _ mask | .VirtualSRAIW _ _ mask =>
      ∃ s < 32, mask = ExpansionFacts.wordShiftMask s
  | .VirtualSRL _ _ mask | .VirtualSRA _ _ mask =>
      ∃ s < 64, JoltISA.sourceValue mask state =
        BitVec.ofNat 64 (ExpansionFacts.rightShiftMask s)
  | .VirtualSRLW _ _ mask | .VirtualSRAW _ _ mask =>
      ∃ s < 32, JoltISA.sourceValue mask state =
        BitVec.ofNat 64 (ExpansionFacts.wordShiftMask s)
  | .VirtualROTRI .. | .VirtualROTRIW .. => False
  | _ => True

theorem maskOk_mask (mask : Nat) (ok : ExpansionFacts.maskOk mask = true) :
    ∃ s < 64, mask = ExpansionFacts.rightShiftMask s := by
  simp only [ExpansionFacts.maskOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at ok
  exact ⟨_, ok.2, ok.1⟩

theorem wordMaskOk_mask (mask : Nat) (ok : ExpansionFacts.wordMaskOk mask = true) :
    ∃ s < 32, mask = ExpansionFacts.wordShiftMask s := by
  simp only [ExpansionFacts.wordMaskOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at ok
  exact ⟨_, ok.2, ok.1⟩

-- A row that is not a register shift: its immediate mask, if any, is checked in the
-- bytecode.
theorem shiftMaskOk_of_immShiftOk (instruction : JoltISA.Instr) (state : SailJoltState)
    (immOk : ExpansionFacts.immShiftOk instruction = true)
    (notShift : ExpansionFacts.isRegisterShift instruction = false) :
    ShiftMaskOk instruction state := by
  unfold ShiftMaskOk
  split
  all_goals first
    | trivial
    | exact maskOk_mask _ immOk
    | exact wordMaskOk_mask _ immOk

theorem bitmask_written (written : JoltISA.VReg) (src : JoltISA.Src) (imm : BitVec 64)
    (pre post : SailJoltState)
    (runs : JoltISA.execInstr (.VirtualShiftRightBitmask (.vreg written) src imm) pre =
      .ok (.Retire_Success ()) post) :
    JoltISA.sourceValue (.vreg written) post =
      BitVec.ofNat 64 (ExpansionFacts.rightShiftMask
        ((JoltISA.sourceValue src pre).setWidth 6).toNat) := by
  simp only [JoltISA.execInstr] at runs
  exact lookup_write_retire (.vreg written) _ _ _ trivial (lookup_read_bind src _ _ _ _ runs)

theorem bitmaskW_written (written : JoltISA.VReg) (src : JoltISA.Src) (imm : BitVec 64)
    (pre post : SailJoltState)
    (runs : JoltISA.execInstr (.VirtualShiftRightBitmaskW (.vreg written) src imm) pre =
      .ok (.Retire_Success ()) post) :
    JoltISA.sourceValue (.vreg written) post =
      BitVec.ofNat 64 (ExpansionFacts.wordShiftMask
        ((JoltISA.sourceValue src pre).setWidth 5).toNat) := by
  simp only [JoltISA.execInstr] at runs
  rw [show ExpansionFacts.wordShiftMask ((JoltISA.sourceValue src pre).setWidth 5).toNat =
      2 ^ 32 - 2 ^ ((JoltISA.sourceValue src pre).setWidth 5).toNat by
    simp only [ExpansionFacts.wordShiftMask, Nat.one_shiftLeft]]
  exact lookup_write_retire (.vreg written) _ _ _ trivial (lookup_read_bind src _ _ _ _ runs)

-- Once `previous` has run, the register mask it wrote for `current` is a bitmask.
theorem fed_mask (previous current : JoltISA.Instr)
    (fed : ExpansionFacts.masksFed previous current = true) (pre post : SailJoltState)
    (runs : JoltISA.execInstr previous pre = .ok (.Retire_Success ()) post) :
    ShiftMaskOk current post := by
  unfold ExpansionFacts.masksFed at fed
  split at fed
  · next written src imm _ _ read =>
    obtain rfl : written = read := beq_iff_eq.mp fed
    exact ⟨_, BitVec.isLt _, bitmask_written written src imm pre post runs⟩
  · next written src imm _ _ read =>
    obtain rfl : written = read := beq_iff_eq.mp fed
    exact ⟨_, BitVec.isLt _, bitmask_written written src imm pre post runs⟩
  · next written src imm _ _ read =>
    obtain rfl : written = read := beq_iff_eq.mp fed
    exact ⟨_, BitVec.isLt _, bitmaskW_written written src imm pre post runs⟩
  · next written src imm _ _ read =>
    obtain rfl : written = read := beq_iff_eq.mp fed
    exact ⟨_, BitVec.isLt _, bitmaskW_written written src imm pre post runs⟩
  · cases fed

-- A bitmask row carries no runtime advice.
theorem masksFed_withRuntimeAdvice (previous current : JoltISA.Instr)
    (advice : previous.RuntimeAdvice) (fed : ExpansionFacts.masksFed previous current = true) :
    previous.withRuntimeAdvice advice = previous := by
  unfold JoltISA.Instr.withRuntimeAdvice
  split
  · simp [ExpansionFacts.masksFed] at fed
  · rfl

-- Every row of an honest trace reads a right-shift bitmask.
theorem shiftMaskOk_of_honest {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (t : Nat) (inBounds : t < trace.rows.size) :
    ShiftMaskOk (rowInstruction (trace.row t inBounds)) (trace.row t inBounds).preState := by
  cases isShift : ExpansionFacts.isRegisterShift (rowInstruction (trace.row t inBounds)) with
  | false =>
    exact shiftMaskOk_of_immShiftOk _ _ (trace.immShiftOk _) isShift
  | true =>
    obtain ⟨j, before, fed, notStart⟩ := trace.shiftPairs trace.rows[t].rowIndex isShift
    obtain ⟨m, mBefore, index, linked⟩ := trace.previous_row t inBounds notStart
    have same : trace.rows[m].rowIndex = j := Fin.ext (by omega)
    have fedPrevious : ExpansionFacts.masksFed
        trace.bytecode[trace.rows[m].rowIndex].instruction
        (rowInstruction (trace.row t inBounds)) = true := by
      have sameRow : trace.bytecode[trace.rows[m].rowIndex] = trace.bytecode[j] :=
        congrArg (fun i : Fin trace.bytecode.size => trace.bytecode[i]) same
      rw [sameRow]
      exact fed
    have runs := trace.executes trace.rows[m] (Array.getElem_mem (by omega))
    rw [masksFed_withRuntimeAdvice _ _ _ fedPrevious] at runs
    rw [show (trace.row t inBounds).preState = trace.rows[m].postState from linked]
    exact fed_mask _ _ fedPrevious _ _ runs

theorem rightShiftMask_shape (s : Nat) (sLt : s < 64) :
    ∀ i < 64, (BitVec.ofNat 64 (ExpansionFacts.rightShiftMask s)).getLsbD i =
      decide (s ≤ i) := by
  intro i iLt
  rw [BitVec.getLsbD_ofNat, ExpansionFacts.rightShiftMask_testBit s i sLt]
  simp [iLt]

theorem wordShiftMask_shape (s : Nat) (sLt : s < 32) :
    ∀ i < 32, (BitVec.ofNat 64 (ExpansionFacts.wordShiftMask s)).getLsbD i =
      decide (s ≤ i) := by
  intro i iLt
  rw [BitVec.getLsbD_ofNat, ExpansionFacts.wordShiftMask_testBit s i sLt]
  simp [iLt, show i < 64 by omega]

theorem rightShiftMask_toNat (s : Nat) (sLt : s < 64) :
    (BitVec.ofNat 64 (ExpansionFacts.rightShiftMask s)).toNat =
      ExpansionFacts.rightShiftMask s := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  apply Nat.lt_pow_two_of_testBit
  intro i iGe
  rw [ExpansionFacts.rightShiftMask_testBit s i sLt]
  simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
  omega

theorem wordShiftMask_toNat (s : Nat) (sLt : s < 32) :
    (BitVec.ofNat 64 (ExpansionFacts.wordShiftMask s)).toNat =
      ExpansionFacts.wordShiftMask s := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  apply Nat.lt_pow_two_of_testBit
  intro i iGe
  rw [ExpansionFacts.wordShiftMask_testBit s i sLt]
  simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
  omega

theorem wordShiftMask_ne_zero (s : Nat) (sLt : s < 32) : ExpansionFacts.wordShiftMask s ≠ 0 := by
  intro zero
  have bit := ExpansionFacts.wordShiftMask_testBit s s sLt
  rw [zero, Nat.zero_testBit] at bit
  simp [sLt] at bit

theorem srl_mask_entry (x : BitVec 64) (s : Nat) (sLt : s < 64) :
    virtualSRLTableEntry (F := F)
        (interleaveLookupOperands x (BitVec.ofNat 64 (ExpansionFacts.rightShiftMask s))).toFin =
      ((x >>> ctz (ExpansionFacts.rightShiftMask s)).toNat : F) := by
  rw [ExpansionFacts.ctz_rightShiftMask s sLt]
  exact ShiftTables.srl_entry _ x _ (uninterleave_interleave _ _) s (rightShiftMask_shape s sLt)

theorem sra_mask_entry (x : BitVec 64) (s : Nat) (sLt : s < 64) :
    virtualSRATableEntry (F := F)
        (interleaveLookupOperands x (BitVec.ofNat 64 (ExpansionFacts.rightShiftMask s))).toFin =
      ((x.sshiftRight (ctz (ExpansionFacts.rightShiftMask s))).toNat : F) := by
  rw [ExpansionFacts.ctz_rightShiftMask s sLt]
  exact ShiftTables.sra_entry _ x _ (uninterleave_interleave _ _) s sLt
    (rightShiftMask_shape s sLt)

theorem srlw_mask_entry (x : BitVec 64) (s : Nat) (sLt : s < 32) :
    virtualSRLWTableEntry (F := F)
        (interleaveLookupOperands x (BitVec.ofNat 64 (ExpansionFacts.wordShiftMask s))).toFin =
      ((((x.setWidth 32) >>> ctz (ExpansionFacts.wordShiftMask s)).signExtend 64).toNat : F) := by
  rw [ExpansionFacts.ctz_wordShiftMask s sLt]
  exact ShiftTables.srlw_entry _ x _ (uninterleave_interleave _ _) s sLt
    (wordShiftMask_shape s sLt)

theorem sraw_mask_entry (x : BitVec 64) (s : Nat) (sLt : s < 32) :
    virtualSRAWTableEntry (F := F)
        (interleaveLookupOperands x (BitVec.ofNat 64 (ExpansionFacts.wordShiftMask s))).toFin =
      ((((x.setWidth 32).sshiftRight (ctz (ExpansionFacts.wordShiftMask s))).signExtend
        64).toNat : F) := by
  rw [ExpansionFacts.ctz_wordShiftMask s sLt]
  exact ShiftTables.sraw_entry _ x _ (uninterleave_interleave _ _) s sLt
    (wordShiftMask_shape s sLt)

theorem lookupEntryCorrect_VirtualSRL (row : HonestTraceRow bytecode)
    (h : JoltMetadata.lookupTable (rowInstruction row) = some .VirtualSRL)
    (maskOk : ShiftMaskOk (rowInstruction row) row.preState) :
    LookupEntryCorrect F .VirtualSRL row := by
  lookup_cases
  · rw [hi] at maskOk
    obtain ⟨s, sLt, rfl⟩ := maskOk
    exact srl_mask_entry _ s sLt
  · rw [hi] at maskOk
    obtain ⟨s, sLt, maskValue⟩ := maskOk
    simp only [jolt_virtual_srl_value, maskValue, rightShiftMask_toNat s sLt]
    exact srl_mask_entry _ s sLt

theorem lookupEntryCorrect_VirtualSRA (row : HonestTraceRow bytecode)
    (h : JoltMetadata.lookupTable (rowInstruction row) = some .VirtualSRA)
    (maskOk : ShiftMaskOk (rowInstruction row) row.preState) :
    LookupEntryCorrect F .VirtualSRA row := by
  lookup_cases
  · rw [hi] at maskOk
    obtain ⟨s, sLt, rfl⟩ := maskOk
    exact sra_mask_entry _ s sLt
  · rw [hi] at maskOk
    obtain ⟨s, sLt, maskValue⟩ := maskOk
    simp only [jolt_virtual_sra_value, maskValue, rightShiftMask_toNat s sLt]
    exact sra_mask_entry _ s sLt

theorem lookupEntryCorrect_VirtualSRLW (row : HonestTraceRow bytecode)
    (h : JoltMetadata.lookupTable (rowInstruction row) = some .VirtualSRLW)
    (maskOk : ShiftMaskOk (rowInstruction row) row.preState) :
    LookupEntryCorrect F .VirtualSRLW row := by
  lookup_cases
  · rw [hi] at maskOk
    obtain ⟨s, sLt, rfl⟩ := maskOk
    simp only [jolt_virtual_srliw_value, if_neg (wordShiftMask_ne_zero s sLt)]
    exact srlw_mask_entry _ s sLt
  · rw [hi] at maskOk
    obtain ⟨s, sLt, maskValue⟩ := maskOk
    simp only [jolt_virtual_srlw_value, maskValue, wordShiftMask_toNat s sLt]
    exact srlw_mask_entry _ s sLt

theorem lookupEntryCorrect_VirtualSRAW (row : HonestTraceRow bytecode)
    (h : JoltMetadata.lookupTable (rowInstruction row) = some .VirtualSRAW)
    (maskOk : ShiftMaskOk (rowInstruction row) row.preState) :
    LookupEntryCorrect F .VirtualSRAW row := by
  lookup_cases
  · rw [hi] at maskOk
    obtain ⟨s, sLt, rfl⟩ := maskOk
    exact sraw_mask_entry _ s sLt
  · rw [hi] at maskOk
    obtain ⟨s, sLt, maskValue⟩ := maskOk
    simp only [jolt_virtual_sraw_value, maskValue, wordShiftMask_toNat s sLt]
    exact sraw_mask_entry _ s sLt

-- No expansion emits a rotate, so these tables are never used.
theorem lookupEntryCorrect_VirtualROTR (row : HonestTraceRow bytecode)
    (h : JoltMetadata.lookupTable (rowInstruction row) = some .VirtualROTR)
    (maskOk : ShiftMaskOk (rowInstruction row) row.preState) :
    LookupEntryCorrect F .VirtualROTR row := by
  lookup_cases
  rw [hi] at maskOk
  exact maskOk.elim

theorem lookupEntryCorrect_VirtualROTRW (row : HonestTraceRow bytecode)
    (h : JoltMetadata.lookupTable (rowInstruction row) = some .VirtualROTRW)
    (maskOk : ShiftMaskOk (rowInstruction row) row.preState) :
    LookupEntryCorrect F .VirtualROTRW row := by
  lookup_cases
  rw [hi] at maskOk
  exact maskOk.elim

theorem lookupEntryCorrect_Pext (row : HonestTraceRow bytecode)
    (h : JoltMetadata.lookupTable (rowInstruction row) = some .Pext) :
    LookupEntryCorrect F .Pext row := by
  lookup_cases
  all_goals simp only [pextTableEntry, uninterleave_interleave, pext_eq_jolt_virtual_pext_value]

theorem lookupEntryCorrect_PextSigned (row : HonestTraceRow bytecode)
    (h : JoltMetadata.lookupTable (rowInstruction row) = some .PextSigned) :
    LookupEntryCorrect F .PextSigned row := by
  lookup_cases
  all_goals simp only [pextSignedTableEntry, uninterleave_interleave,
    pextSigned_eq_jolt_virtual_pext_signed_value]

theorem lookupEntryCorrect_UnsignedLessThanEqual (row : HonestTraceRow bytecode)
    (h : JoltMetadata.lookupTable (rowInstruction row) = some .UnsignedLessThanEqual) :
    LookupEntryCorrect F .UnsignedLessThanEqual row := by
  have hexec := row_executes_exists row
  lookup_cases
  rw [hi] at hexec
  obtain ⟨_, hexec⟩ := hexec
  simp only [JoltISA.Instr.withRuntimeAdvice, JoltISA.execInstr] at hexec
  have h1 := lookup_read_bind _ _ _ _ _ hexec
  have h2 := lookup_read_bind _ _ _ _ _ h1
  split_ifs at h2 with hc
  · rw [unsignedLessThanEqual_entry, if_pos (BitVec.le_def.mpr hc)]
    simp
  · exact absurd h2 (by simp [throw, throwThe, MonadExceptOf.throw, EStateM.throw])

theorem lookupEntryCorrect_HalfwordAlignment (row : HonestTraceRow bytecode)
    (h : JoltMetadata.lookupTable (rowInstruction row) = some .HalfwordAlignment) :
    LookupEntryCorrect F .HalfwordAlignment row := by
  have hexec := row_executes_exists row
  lookup_cases
  rw [hi] at hexec
  obtain ⟨_, hexec⟩ := hexec
  simp only [JoltISA.Instr.withRuntimeAdvice, JoltISA.execInstr] at hexec
  have h1 := lookup_read_bind _ _ _ _ _ hexec
  split_ifs at h1 with hc
  · simp only [halfwordAlignmentTableEntry, BitVec.ofFin_toFin]
    rw [if_pos (halfword_aligned _ hc)]
    simp
  · exact absurd h1 (by simp [pure, EStateM.pure])

theorem lookupEntryCorrect_WordAlignment (row : HonestTraceRow bytecode)
    (h : JoltMetadata.lookupTable (rowInstruction row) = some .WordAlignment) :
    LookupEntryCorrect F .WordAlignment row := by
  have hexec := row_executes_exists row
  lookup_cases
  rw [hi] at hexec
  obtain ⟨_, hexec⟩ := hexec
  simp only [JoltISA.Instr.withRuntimeAdvice, JoltISA.execInstr] at hexec
  have h1 := lookup_read_bind _ _ _ _ _ hexec
  split_ifs at h1 with hc
  · simp only [wordAlignmentTableEntry, BitVec.ofFin_toFin]
    rw [if_pos (word_aligned _ hc)]
    simp
  · exact absurd h1 (by simp [pure, EStateM.pure])

theorem lookupEntryCorrect_MulUNoOverflow (row : HonestTraceRow bytecode)
    (h : JoltMetadata.lookupTable (rowInstruction row) = some .MulUNoOverflow) :
    LookupEntryCorrect F .MulUNoOverflow row := by
  have hexec := row_executes_exists row
  lookup_cases
  rw [hi] at hexec
  obtain ⟨_, hexec⟩ := hexec
  simp only [JoltISA.Instr.withRuntimeAdvice, JoltISA.execInstr] at hexec
  have h1 := lookup_read_bind _ _ _ _ _ hexec
  have h2 := lookup_read_bind _ _ _ _ _ h1
  split_ifs at h2 with hc
  · simp only [mulUNoOverflowTableEntry, BitVec.ofFin_toFin]
    rw [if_pos (upper_zero_of_lt _ hc)]
    simp
  · exact absurd h2 (by simp [throw, throwThe, MonadExceptOf.throw, EStateM.throw])

theorem lookupEntryCorrect_ValidDiv0 (row : HonestTraceRow bytecode)
    (h : JoltMetadata.lookupTable (rowInstruction row) = some .ValidDiv0) :
    LookupEntryCorrect F .ValidDiv0 row := by
  have hexec := row_executes_exists row
  lookup_cases
  rw [hi] at hexec
  obtain ⟨_, hexec⟩ := hexec
  simp only [JoltISA.Instr.withRuntimeAdvice, JoltISA.execInstr] at hexec
  have h1 := lookup_read_bind _ _ _ _ _ hexec
  have h2 := lookup_read_bind _ _ _ _ _ h1
  split_ifs at h2 with hc
  · exact absurd h2 (by simp [throw, throwThe, MonadExceptOf.throw, EStateM.throw])
  · rw [validDiv0_entry, if_neg (by simpa using hc)]
    simp

theorem lookupEntryCorrect_ValidUnsignedRemainder (row : HonestTraceRow bytecode)
    (h : JoltMetadata.lookupTable (rowInstruction row) = some .ValidUnsignedRemainder) :
    LookupEntryCorrect F .ValidUnsignedRemainder row := by
  have hexec := row_executes_exists row
  lookup_cases
  rw [hi] at hexec
  obtain ⟨_, hexec⟩ := hexec
  simp only [JoltISA.Instr.withRuntimeAdvice, JoltISA.execInstr] at hexec
  have h1 := lookup_read_bind _ _ _ _ _ hexec
  have h2 := lookup_read_bind _ _ _ _ _ h1
  split_ifs at h2 with hc
  · rw [validUnsignedRemainder_entry, if_pos (by simpa [BitVec.lt_def] using hc)]
    simp
  · exact absurd h2 (by simp [throw, throwThe, MonadExceptOf.throw, EStateM.throw])

/-- Rows whose instruction has no lookup table (`FENCE`, `LD`, `SD`,
`VirtualHostIO`) have lookup output zero. -/
theorem rowLookupOutput_eq_zero_of_lookupTable_none (row : HonestTraceRow bytecode)
    (h : JoltMetadata.lookupTable (rowInstruction row) = none) :
    rowLookupOutput row.toTraceRow = 0 := by
  unfold rowLookupOutput
  cases hi : rowInstruction row <;>
    simp only [hi, JoltMetadata.lookupTable, reduceCtorEq] at h <;>
    simp only [hi]

/-- Dispatcher: the honest entry of the row's lookup table equals the honest
lookup output. The shift tables need the row's mask to be a bitmask
(`shiftMaskOk_of_honest`). -/
theorem lookupEntryCorrect_of_lookupTable (row : HonestTraceRow bytecode) (k : LookupTableKind)
    (h : JoltMetadata.lookupTable (rowInstruction row) = some k)
    (maskOk : ShiftMaskOk (rowInstruction row) row.preState) :
    LookupEntryCorrect F k row :=
  match k with
  | .RangeCheck => lookupEntryCorrect_RangeCheck row h
  | .RangeCheckAligned => lookupEntryCorrect_RangeCheckAligned row h
  | .And => lookupEntryCorrect_And row h
  | .Andn => lookupEntryCorrect_Andn row h
  | .Or => lookupEntryCorrect_Or row h
  | .Xor => lookupEntryCorrect_Xor row h
  | .Equal => lookupEntryCorrect_Equal row h
  | .SignedGreaterThanEqual => lookupEntryCorrect_SignedGreaterThanEqual row h
  | .UnsignedGreaterThanEqual => lookupEntryCorrect_UnsignedGreaterThanEqual row h
  | .NotEqual => lookupEntryCorrect_NotEqual row h
  | .SignedLessThan => lookupEntryCorrect_SignedLessThan row h
  | .UnsignedLessThan => lookupEntryCorrect_UnsignedLessThan row h
  | .SignMask => lookupEntryCorrect_SignMask row h
  | .UpperWord => lookupEntryCorrect_UpperWord row h
  | .UnsignedLessThanEqual => lookupEntryCorrect_UnsignedLessThanEqual row h
  | .ValidUnsignedRemainder => lookupEntryCorrect_ValidUnsignedRemainder row h
  | .ValidDiv0 => lookupEntryCorrect_ValidDiv0 row h
  | .HalfwordAlignment => lookupEntryCorrect_HalfwordAlignment row h
  | .WordAlignment => lookupEntryCorrect_WordAlignment row h
  | .LowerHalfWord => lookupEntryCorrect_LowerHalfWord row h
  | .SignExtendWord => lookupEntryCorrect_SignExtendWord row h
  | .Pow2 => lookupEntryCorrect_Pow2 row h
  | .Pow2W => lookupEntryCorrect_Pow2W row h
  | .ShiftRightBitmask => lookupEntryCorrect_ShiftRightBitmask row h
  | .VirtualRev8W => lookupEntryCorrect_VirtualRev8W row h
  | .VirtualSRL => lookupEntryCorrect_VirtualSRL row h maskOk
  | .VirtualSRA => lookupEntryCorrect_VirtualSRA row h maskOk
  | .VirtualROTR => lookupEntryCorrect_VirtualROTR row h maskOk
  | .VirtualROTRW => lookupEntryCorrect_VirtualROTRW row h maskOk
  | .VirtualNegateIf => lookupEntryCorrect_VirtualNegateIf row h
  | .MulUNoOverflow => lookupEntryCorrect_MulUNoOverflow row h
  | .VirtualXORROT32 => lookupEntryCorrect_VirtualXORROT32 row h
  | .VirtualXORROT24 => lookupEntryCorrect_VirtualXORROT24 row h
  | .VirtualXORROT16 => lookupEntryCorrect_VirtualXORROT16 row h
  | .VirtualXORROT63 => lookupEntryCorrect_VirtualXORROT63 row h
  | .VirtualXORROTW16 => lookupEntryCorrect_VirtualXORROTW16 row h
  | .VirtualXORROTW12 => lookupEntryCorrect_VirtualXORROTW12 row h
  | .VirtualXORROTW8 => lookupEntryCorrect_VirtualXORROTW8 row h
  | .VirtualXORROTW7 => lookupEntryCorrect_VirtualXORROTW7 row h
  | .WindowMaskW => lookupEntryCorrect_WindowMaskW row h
  | .PextSigned => lookupEntryCorrect_PextSigned row h
  | .VirtualXORROTW22 => lookupEntryCorrect_VirtualXORROTW22 row h
  | .VirtualXORROTW19 => lookupEntryCorrect_VirtualXORROTW19 row h
  | .VirtualXORROTW6 => lookupEntryCorrect_VirtualXORROTW6 row h
  | .ShiftRightBitmaskW => lookupEntryCorrect_ShiftRightBitmaskW row h
  | .VirtualSRLW => lookupEntryCorrect_VirtualSRLW row h maskOk
  | .VirtualSRAW => lookupEntryCorrect_VirtualSRAW row h maskOk
  | .Pext => lookupEntryCorrect_Pext row h
  | .WindowMaskB => lookupEntryCorrect_WindowMaskB row h
  | .WindowMaskH => lookupEntryCorrect_WindowMaskH row h
  | .AlignAddr => lookupEntryCorrect_AlignAddr row h
  | .ShiftDataB => lookupEntryCorrect_ShiftDataB row h
  | .ShiftDataH => lookupEntryCorrect_ShiftDataH row h
  | .ShiftDataW => lookupEntryCorrect_ShiftDataW row h
  | .VirtualXORROTL1 => lookupEntryCorrect_VirtualXORROTL1 row h

end tables2

end JoltConstraints
