import JoltConstraints.Constraints.LookupOperandData
import JoltConstraints.Constraints.LookupWriteProofHelpers

/-!
# Per-table obligations for constraint (39)

Constraint (39) says that on an execution row the lookup output equals the
selected table entry at the honest lookup address. After the address sum and the
table sum are collapsed (see `LookupOutputEqInstructionReadRaf.lean`), what is
left is one obligation per `LookupTableKind`:

  lookupTableEntry k (rowLookupAddress row) = rowLookupOutput row

whenever the row's instruction uses table `k`. This file states that obligation
as `LookupEntryCorrect` and proves it table by table as
`lookupEntryCorrect_<Table>`. `lookupEntryCorrect_of_lookupTable` dispatches on
the table.
-/

set_option autoImplicit false

namespace JoltConstraints

open HonestWitness
open Sail PreSail LeanRV64D.Functions

/-- The expanded instruction executed by a trace row. -/
abbrev rowInstruction {program : JoltProgram} (row : JoltTraceRow program) : JoltISA.Instr :=
  (getElem program.expandedBytecode row.rowIndex.val row.rowIndex.isLt).expandedInstruction

/-- The honest 128-bit lookup index of an execution row. -/
noncomputable def rowLookupIndex {program : JoltProgram} (row : JoltTraceRow program) :
    BitVec 128 :=
  let bc := getElem program.expandedBytecode row.rowIndex.val row.rowIndex.isLt
  instructionLookupIndex bc.expandedInstruction bc.address row.preState row.postState

/-- The honest lookup index as a table address. -/
noncomputable def rowLookupAddress {program : JoltProgram} (row : JoltTraceRow program) :
    Fin (2 ^ 128) :=
  (rowLookupIndex row).toFin

/-- The per-table obligation of constraint (39): table `table` at the honest
address is the honest lookup output. -/
def LookupEntryCorrect (F : Type) [Field F] {program : JoltProgram}
    (table : LookupTableKind) (row : JoltTraceRow program) : Prop :=
  lookupTableEntry (F := F) table (rowLookupAddress row) = ((rowLookupOutput row).toNat : F)

/-! ## Uninterleaving -/

theorem uninterleave_fst_getLsbD (v : BitVec 128) (i : Nat) (hi : i < 64) :
    (uninterleave v.toFin).1.getLsbD i = v.getLsbD (2 * i + 1) := by
  interval_cases i <;> (simp only [uninterleave, BitVec.ofFin_toFin]; bv_decide)

theorem uninterleave_snd_getLsbD (v : BitVec 128) (i : Nat) (hi : i < 64) :
    (uninterleave v.toFin).2.getLsbD i = v.getLsbD (2 * i) := by
  interval_cases i <;> (simp only [uninterleave, BitVec.ofFin_toFin]; bv_decide)

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

theorem rangeCheck_entry (v : BitVec 128) :
    rangeCheckTableEntry (F := F) v.toFin = ((v.setWidth 64).toNat : F) := by
  unfold rangeCheckTableEntry
  have h : (v &&& ((1#128 <<< 64) - 1)).setWidth 64 = v.setWidth 64 := by bv_decide
  simp only [BitVec.ofFin_toFin, h]

theorem interleave_testBit_odd (l r : BitVec 64) (i : Nat) (hi : i < 64) :
    (interleaveLookupOperands l r).toNat.testBit (2 * i + 1) = l.getLsbD i := by
  rw [interleaveLookupOperands_testBit l r (by omega)]
  have h1 : (2 * i + 1) % 2 = 1 := by omega
  have h2 : (2 * i + 1) / 2 = i := by omega
  simp only [h1, h2, ↓reduceIte]

theorem interleave_testBit_even (l r : BitVec 64) (i : Nat) (hi : i < 64) :
    (interleaveLookupOperands l r).toNat.testBit (2 * i) = r.getLsbD i := by
  rw [interleaveLookupOperands_testBit l r (by omega)]
  have h1 : 2 * i % 2 = 0 := by omega
  have h2 : 2 * i / 2 = i := by omega
  simp only [h1, h2, Nat.zero_ne_one, ↓reduceIte]

theorem and_entry (l r : BitVec 64) :
    andTableEntry (F := F) (interleaveLookupOperands l r).toFin = ((l &&& r).toNat : F) := by
  rw [bitVec_toNat_cast_eq_sum]
  unfold andTableEntry
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [BitVec.val_toFin, interleave_testBit_odd l r i i.isLt,
    interleave_testBit_even l r i i.isLt, BitVec.getLsbD_and]

theorem or_entry (l r : BitVec 64) :
    orTableEntry (F := F) (interleaveLookupOperands l r).toFin = ((l ||| r).toNat : F) := by
  rw [bitVec_toNat_cast_eq_sum]
  unfold orTableEntry
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [BitVec.val_toFin, interleave_testBit_odd l r i i.isLt,
    interleave_testBit_even l r i i.isLt, BitVec.getLsbD_or]

theorem xor_entry (l r : BitVec 64) :
    xorTableEntry (F := F) (interleaveLookupOperands l r).toFin = ((l ^^^ r).toNat : F) := by
  rw [bitVec_toNat_cast_eq_sum]
  unfold xorTableEntry
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [BitVec.val_toFin, interleave_testBit_odd l r i i.isLt,
    interleave_testBit_even l r i i.isLt, BitVec.getLsbD_xor, bne]

theorem andn_entry (l r : BitVec 64) :
    andnTableEntry (F := F) (interleaveLookupOperands l r).toFin = ((l &&& ~~~r).toNat : F) := by
  simp only [andnTableEntry, uninterleave_interleave]

theorem equal_entry (l r : BitVec 64) :
    equalTableEntry (F := F) (interleaveLookupOperands l r).toFin = if l = r then 1 else 0 := by
  simp only [equalTableEntry, uninterleave_interleave]

theorem notEqual_entry (l r : BitVec 64) :
    notEqualTableEntry (F := F) (interleaveLookupOperands l r).toFin = if l ≠ r then 1 else 0 := by
  simp only [notEqualTableEntry, uninterleave_interleave]

theorem unsignedLessThan_entry (l r : BitVec 64) :
    unsignedLessThanTableEntry (F := F) (interleaveLookupOperands l r).toFin =
      if l < r then 1 else 0 := by
  simp only [unsignedLessThanTableEntry, uninterleave_interleave]

theorem unsignedLessThanEqual_entry (l r : BitVec 64) :
    unsignedLessThanEqualTableEntry (F := F) (interleaveLookupOperands l r).toFin =
      if l ≤ r then 1 else 0 := by
  simp only [unsignedLessThanEqualTableEntry, uninterleave_interleave]

theorem unsignedGreaterThanEqual_entry (l r : BitVec 64) :
    unsignedGreaterThanEqualTableEntry (F := F) (interleaveLookupOperands l r).toFin =
      if l ≥ r then 1 else 0 := by
  simp only [unsignedGreaterThanEqualTableEntry, uninterleave_interleave]

theorem signedLessThan_entry (l r : BitVec 64) :
    signedLessThanTableEntry (F := F) (interleaveLookupOperands l r).toFin =
      if l.toInt < r.toInt then 1 else 0 := by
  simp only [signedLessThanTableEntry, uninterleave_interleave]

theorem signedGreaterThanEqual_entry (l r : BitVec 64) :
    signedGreaterThanEqualTableEntry (F := F) (interleaveLookupOperands l r).toFin =
      if l.toInt ≥ r.toInt then 1 else 0 := by
  simp only [signedGreaterThanEqualTableEntry, uninterleave_interleave]

theorem validDiv0_entry (l r : BitVec 64) :
    validDiv0TableEntry (F := F) (interleaveLookupOperands l r).toFin =
      if l = 0 ∧ r ≠ -1 then 0 else 1 := by
  have hmax : ((1#128 <<< 64) - 1).setWidth 64 = (-1 : BitVec 64) := by decide
  simp only [validDiv0TableEntry, uninterleave_interleave, hmax]
  split_ifs <;> simp_all

theorem validUnsignedRemainder_entry (l r : BitVec 64) :
    validUnsignedRemainderTableEntry (F := F) (interleaveLookupOperands l r).toFin =
      if r = 0 ∨ l < r then 1 else 0 := by
  simp only [validUnsignedRemainderTableEntry, uninterleave_interleave]

theorem signMask_entry (l r : BitVec 64) :
    signMaskTableEntry (F := F) (interleaveLookupOperands l r).toFin =
      ((if l.msb then (-1 : BitVec 64) else 0).toNat : F) := by
  unfold signMaskTableEntry
  have hbit : (interleaveLookupOperands l r &&& 1#128 <<< 127 ≠ 0) = (l.msb = true) := by
    have h127 := interleave_testBit_odd l r 63 (by omega)
    have hiff : ∀ v : BitVec 128, (v &&& 1#128 <<< 127 ≠ 0) ↔ v.getLsbD 127 = true := by
      intro v; bv_decide
    rw [hiff, BitVec.getLsbD, h127, BitVec.msb_eq_getLsbD_last]
  have hones : ((1#128 <<< 64) - 1).setWidth 64 = (-1 : BitVec 64) := by decide
  simp only [BitVec.ofFin_toFin, hbit, hones]
  split <;> simp

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


theorem row_executes_exists {program : JoltProgram} (row : JoltTraceRow program) :
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
variable {F : Type} [Field F] {program : JoltProgram}

set_option hygiene false in
/-- Split on the row instruction, keep the instructions that use the table, and
unfold the index, output and table definitions. -/
macro "lookup_cases" : tactic => `(tactic| (
  unfold LookupEntryCorrect rowLookupAddress rowLookupIndex
  cases hi : rowInstruction row <;>
    simp only [hi, JoltMetadata.lookupTable, reduceCtorEq, Option.some.injEq] at h <;>
    simp only [lookupTableEntry, rowLookupOutput, instructionLookupIndex, hi]))

theorem lookupEntryCorrect_RangeCheck (row : JoltTraceRow program)
    (h : JoltMetadata.lookupTable (rowInstruction row) = some .RangeCheck) :
    LookupEntryCorrect F .RangeCheck row := by
  lookup_cases
  all_goals simp only [rangeCheck_entry]
  all_goals simp [ BitVec.setWidth_ofNat_of_le, BitVec.setWidth_setWidth_of_le,
    jolt_virtual_muli_value]

theorem lookupEntryCorrect_And (row : JoltTraceRow program)
    (h : JoltMetadata.lookupTable (rowInstruction row) = some .And) :
    LookupEntryCorrect F .And row := by
  lookup_cases
  all_goals simp only [and_entry, Riscv.andi]

theorem lookupEntryCorrect_Or (row : JoltTraceRow program)
    (h : JoltMetadata.lookupTable (rowInstruction row) = some .Or) :
    LookupEntryCorrect F .Or row := by
  lookup_cases
  all_goals simp only [or_entry, Riscv.ori]

theorem lookupEntryCorrect_Xor (row : JoltTraceRow program)
    (h : JoltMetadata.lookupTable (rowInstruction row) = some .Xor) :
    LookupEntryCorrect F .Xor row := by
  lookup_cases
  all_goals simp only [xor_entry, jolt_xor_value]

theorem lookupEntryCorrect_Andn (row : JoltTraceRow program)
    (h : JoltMetadata.lookupTable (rowInstruction row) = some .Andn) :
    LookupEntryCorrect F .Andn row := by
  lookup_cases
  all_goals simp only [andn_entry, jolt_andn_value]

theorem lookupEntryCorrect_SignedLessThan (row : JoltTraceRow program)
    (h : JoltMetadata.lookupTable (rowInstruction row) = some .SignedLessThan) :
    LookupEntryCorrect F .SignedLessThan row := by
  lookup_cases
  all_goals simp only [signedLessThan_entry, jolt_slt_value_eq, cast_ite_one_zero,
    JoltISA.branchDecisionPure, zopz0zI_s, decide_eq_true_eq]

theorem lookupEntryCorrect_UnsignedLessThan (row : JoltTraceRow program)
    (h : JoltMetadata.lookupTable (rowInstruction row) = some .UnsignedLessThan) :
    LookupEntryCorrect F .UnsignedLessThan row := by
  lookup_cases
  all_goals simp only [unsignedLessThan_entry, jolt_sltu_value_eq, cast_ite_one_zero,
    JoltISA.branchDecisionPure, zopz0zI_u, decide_eq_true_eq, toNatInt_lt]

theorem lookupEntryCorrect_SignedGreaterThanEqual (row : JoltTraceRow program)
    (h : JoltMetadata.lookupTable (rowInstruction row) = some .SignedGreaterThanEqual) :
    LookupEntryCorrect F .SignedGreaterThanEqual row := by
  lookup_cases
  all_goals simp only [signedGreaterThanEqual_entry, cast_ite_one_zero,
    JoltISA.branchDecisionPure, zopz0zKzJ_s, decide_eq_true_eq]

theorem lookupEntryCorrect_UnsignedGreaterThanEqual (row : JoltTraceRow program)
    (h : JoltMetadata.lookupTable (rowInstruction row) = some .UnsignedGreaterThanEqual) :
    LookupEntryCorrect F .UnsignedGreaterThanEqual row := by
  lookup_cases
  all_goals simp only [unsignedGreaterThanEqual_entry, cast_ite_one_zero,
    JoltISA.branchDecisionPure, zopz0zKzJ_u, decide_eq_true_eq, toNatInt_ge]

theorem lookupEntryCorrect_Equal (row : JoltTraceRow program)
    (h : JoltMetadata.lookupTable (rowInstruction row) = some .Equal) :
    LookupEntryCorrect F .Equal row := by
  lookup_cases
  all_goals simp only [equal_entry, cast_ite_one_zero, JoltISA.branchDecisionPure,
    beq_iff_eq, jolt_assert_eq]

theorem lookupEntryCorrect_NotEqual (row : JoltTraceRow program)
    (h : JoltMetadata.lookupTable (rowInstruction row) = some .NotEqual) :
    LookupEntryCorrect F .NotEqual row := by
  lookup_cases
  all_goals simp only [notEqual_entry, cast_ite_one_zero, JoltISA.branchDecisionPure,
    bne_iff_ne, ne_eq]

end tables

section entries2
variable {F : Type} [Field F]

theorem signExtendWord_entry (v : BitVec 128) :
    signExtendWordTableEntry (F := F) v.toFin =
      (((v.setWidth 32).signExtend 64).toNat : F) := by
  unfold signExtendWordTableEntry
  simp only [BitVec.ofFin_toFin]
  split
  · rename_i hs
    congr 2
    bv_decide
  · rename_i hs
    congr 2
    bv_decide

theorem upperWord_entry (n : Nat) (hn : n < 2 ^ 128) :
    upperWordTableEntry (F := F) (BitVec.ofNat 128 n).toFin =
      ((BitVec.ofNat 64 (n / 2 ^ 64)).toNat : F) := by
  unfold upperWordTableEntry
  simp only [BitVec.ofFin_toFin]
  congr 2
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt hn]

theorem lowerHalfWord_entry (v : BitVec 128) :
    lowerHalfWordTableEntry (F := F) v.toFin = (((v.setWidth 32).setWidth 64).toNat : F) := by
  unfold lowerHalfWordTableEntry
  simp only [BitVec.ofFin_toFin]
  congr 2
  bv_decide

theorem rangeCheckAligned_entry (v : BitVec 128) :
    rangeCheckAlignedTableEntry (F := F) v.toFin =
      ((v.setWidth 64 &&& ~~~1#64).toNat : F) := by
  unfold rangeCheckAlignedTableEntry
  have h : (v &&& ((1#128 <<< 64) - 1)).setWidth 64 = v.setWidth 64 := by bv_decide
  simp only [BitVec.ofFin_toFin, h]

theorem alignAddr_entry (v : BitVec 128) :
    alignAddrTableEntry (F := F) v.toFin =
      ((v.setWidth 64 &&& ~~~7#64).toNat : F) := by
  unfold alignAddrTableEntry
  have h : (v &&& ((1#128 <<< 64) - 1)).setWidth 64 = v.setWidth 64 := by bv_decide
  simp only [BitVec.ofFin_toFin, h]

theorem umod_toNat (v : BitVec 128) (m : Nat) (hm : m < 2 ^ 128) :
    (v % BitVec.ofNat 128 m).toNat = v.toNat % m := by
  simp only [BitVec.toNat_umod, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm]

theorem one_shiftLeft_eq (k : Nat) : 1#64 <<< k = BitVec.ofNat 64 (2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  norm_num

theorem pow2_entry (v : BitVec 128) :
    pow2TableEntry (F := F) v.toFin = ((BitVec.ofNat 64 (2 ^ (v.toNat % 64))).toNat : F) := by
  unfold pow2TableEntry
  simp only [BitVec.ofFin_toFin, one_shiftLeft_eq]
  rw [show (64 : BitVec 128) = BitVec.ofNat 128 64 from rfl, umod_toNat _ _ (by norm_num)]

theorem pow2W_entry (v : BitVec 128) :
    pow2WTableEntry (F := F) v.toFin = ((BitVec.ofNat 64 (2 ^ (v.toNat % 32))).toNat : F) := by
  unfold pow2WTableEntry
  simp only [BitVec.ofFin_toFin, one_shiftLeft_eq]
  rw [show (32 : BitVec 128) = BitVec.ofNat 128 32 from rfl, umod_toNat _ _ (by norm_num)]

theorem shiftRightBitmask_value (s : Nat) (hs : s < 64) :
    ((1#128 <<< (64 - s)) - 1).setWidth 64 <<< s =
      BitVec.ofNat 64 (((1 <<< (64 - s)) - 1) <<< s) := by
  interval_cases s <;> decide

theorem shiftRightBitmask_entry (v : BitVec 128) :
    shiftRightBitmaskTableEntry (F := F) v.toFin =
      ((BitVec.ofNat 64 (((1 <<< (64 - v.toNat % 64)) - 1) <<< (v.toNat % 64))).toNat : F) := by
  unfold shiftRightBitmaskTableEntry
  simp only [BitVec.ofFin_toFin]
  rw [show (64 : BitVec 128) = BitVec.ofNat 128 64 from rfl, umod_toNat _ _ (by norm_num),
    shiftRightBitmask_value _ (Nat.mod_lt _ (by norm_num))]

theorem shiftRightBitmaskW_value (s : Nat) (hs : s < 32) :
    ((1#128 <<< 32) - (1#128 <<< s)).setWidth 64 = BitVec.ofNat 64 (2 ^ 32 - 2 ^ s) := by
  interval_cases s <;> decide

theorem shiftRightBitmaskW_entry (v : BitVec 128) :
    shiftRightBitmaskWTableEntry (F := F) v.toFin =
      ((BitVec.ofNat 64 (2 ^ 32 - 2 ^ (v.toNat % 32))).toNat : F) := by
  unfold shiftRightBitmaskWTableEntry
  simp only [BitVec.ofFin_toFin]
  rw [show (32 : BitVec 128) = BitVec.ofNat 128 32 from rfl, umod_toNat _ _ (by norm_num),
    shiftRightBitmaskW_value _ (Nat.mod_lt _ (by norm_num))]

theorem negateIf_entry (l r : BitVec 64) :
    virtualNegateIfTableEntry (F := F) (interleaveLookupOperands l r).toFin =
      ((if l.msb then -r else r).toNat : F) := by
  have hmask : ((1#128 <<< 64) - 1).setWidth 64 = (-1 : BitVec 64) := by decide
  have h1 : r &&& -1 = r := by bv_decide
  have h2 : -r &&& -1 = -r := by bv_decide
  simp only [virtualNegateIfTableEntry, uninterleave_interleave, hmask, h1, h2]
  have hsign : (l &&& 1#64 <<< 63 = 0) ↔ l.msb = false := by bv_decide
  by_cases hm : l.msb
  · have : ¬ (l &&& 1#64 <<< 63 = 0) := by rw [hsign, hm]; simp
    simp only [this, hm, ↓reduceIte]
  · have : l &&& 1#64 <<< 63 = 0 := by rw [hsign]; simpa using hm
    simp only [this, hm, ↓reduceIte, Bool.false_eq_true]

theorem shiftDataB_entry (l r : BitVec 64) :
    shiftDataBTableEntry (F := F) (interleaveLookupOperands l r).toFin =
      ((jolt_virtual_shift_data_b_value l r).toNat : F) := by
  have hm : ((1#128 <<< 8) - 1).setWidth 64 = (0xFF : BitVec 64) := by decide
  simp only [shiftDataBTableEntry, uninterleave_interleave, hm, jolt_virtual_shift_data_b_value]

theorem shiftDataH_entry (l r : BitVec 64) :
    shiftDataHTableEntry (F := F) (interleaveLookupOperands l r).toFin =
      ((jolt_virtual_shift_data_h_value l r).toNat : F) := by
  have hm : ((1#128 <<< 16) - 1).setWidth 64 = (0xFFFF : BitVec 64) := by decide
  simp only [shiftDataHTableEntry, uninterleave_interleave, hm, jolt_virtual_shift_data_h_value]

theorem shiftDataW_entry (l r : BitVec 64) :
    shiftDataWTableEntry (F := F) (interleaveLookupOperands l r).toFin =
      ((jolt_virtual_shift_data_w_value l r).toNat : F) := by
  have hm : ((1#128 <<< 32) - 1).setWidth 64 = (0xFFFF_FFFF : BitVec 64) := by decide
  simp only [shiftDataWTableEntry, uninterleave_interleave, hm, jolt_virtual_shift_data_w_value]

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

theorem rotater_eq {n : Nat} (z : BitVec n) (s : Nat) (hs : s ≤ n) :
    rotater z s = (z >>> s) ||| (z <<< (n - s)) := by
  unfold rotater
  have : (Sail.BitVec.length z -i (s : Int)) = ((n - s : Nat) : Int) := by
    simp only [Sail.BitVec.length]; omega
  rw [this]
  rfl

theorem rotatel_one (z : BitVec 64) : rotatel z 1 = (z <<< 1) ||| (z >>> 63) := rfl

theorem xorRotL1_getLsbD (x y : BitVec 64) (i : Nat) (hi : i < 64) :
    (x ^^^ ((y <<< 1) ||| (y >>> 63))).getLsbD i = (x.getLsbD i != y.getLsbD ((i + 63) % 64)) := by
  interval_cases i <;> bv_decide

theorem xorRotL1_entry (l r : BitVec 64) :
    virtualXorRotL1TableEntry (F := F) (interleaveLookupOperands l r).toFin =
      ((jolt_virtual_xorrotl1_value l r).toNat : F) := by
  rw [jolt_virtual_xorrotl1_value, rotatel_one, bitVec_toNat_cast_eq_sum]
  unfold virtualXorRotL1TableEntry
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [BitVec.val_toFin, interleave_testBit_odd l r i i.isLt,
    interleave_testBit_even l r _ (Nat.mod_lt _ (by omega)), xorRotL1_getLsbD l r i i.isLt]

theorem xorRot_entry (r : Nat) (hr : r = 32 ∨ r = 24 ∨ r = 16 ∨ r = 63) (l y : BitVec 64) :
    virtualXorRotTableEntry (F := F) r (interleaveLookupOperands l y).toFin =
      ((jolt_virtual_xorrot_value r l y).toNat : F) := by
  have hr64 : r < 64 := by omega
  simp only [virtualXorRotTableEntry, uninterleave_interleave, jolt_virtual_xorrot_value,
    rotater_eq _ r hr64.le, Nat.mod_eq_of_lt hr64]
  congr 2
  rcases hr with rfl | rfl | rfl | rfl <;> bv_decide

theorem xorRotW_entry (r : Nat)
    (hr : r = 16 ∨ r = 12 ∨ r = 8 ∨ r = 7 ∨ r = 22 ∨ r = 19 ∨ r = 6) (l y : BitVec 64) :
    virtualXorRotWTableEntry (F := F) r (interleaveLookupOperands l y).toFin =
      ((jolt_virtual_xorrotw_value r l y).toNat : F) := by
  have hr32 : r < 32 := by omega
  simp only [virtualXorRotWTableEntry, uninterleave_interleave, jolt_virtual_xorrotw_value,
    rotater_eq _ r hr32.le, Nat.mod_eq_of_lt hr32, zero_extend, Sail.BitVec.zeroExtend,
    Sail.BitVec.extractLsb]
  congr 2
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> bv_decide

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
variable {F : Type} [Field F] {program : JoltProgram}

theorem lookupEntryCorrect_SignExtendWord (row : JoltTraceRow program)
    (h : JoltMetadata.lookupTable (rowInstruction row) = some .SignExtendWord) :
    LookupEntryCorrect F .SignExtendWord row := by
  lookup_cases
  all_goals simp only [signExtendWord_entry]
  all_goals simp only [jolt_addiw_value64, jolt_addw_value,
    jolt_subw_value, jolt_mulw_value, jolt_virtual_muliw_value, jolt_virtual_sign_extend_word_value,
    BitVec.setWidth_ofNat_of_le (by norm_num : 32 ≤ 128), BitVec.setWidth_ofNat_of_le (by norm_num : 32 ≤ 64),
    BitVec.setWidth_setWidth_of_le _ (by norm_num : 32 ≤ 128)]

theorem lookupEntryCorrect_UpperWord (row : JoltTraceRow program)
    (h : JoltMetadata.lookupTable (rowInstruction row) = some .UpperWord) :
    LookupEntryCorrect F .UpperWord row := by
  lookup_cases
  rw [upperWord_entry _ (mulWide_lt _ _)]
  rfl

theorem lookupEntryCorrect_LowerHalfWord (row : JoltTraceRow program)
    (h : JoltMetadata.lookupTable (rowInstruction row) = some .LowerHalfWord) :
    LookupEntryCorrect F .LowerHalfWord row := by
  lookup_cases
  simp only [lowerHalfWord_entry, jolt_virtual_zero_extend_word_value, zero_extend,
    Sail.BitVec.zeroExtend, Sail.BitVec.extractLsb]
  congr 2

theorem lookupEntryCorrect_RangeCheckAligned (row : JoltTraceRow program)
    (h : JoltMetadata.lookupTable (rowInstruction row) = some .RangeCheckAligned) :
    LookupEntryCorrect F .RangeCheckAligned row := by
  lookup_cases
  simp only [rangeCheckAligned_entry, jolt_jalr_target64, BitVec.setWidth_ofNat_of_le (by norm_num : 64 ≤ 128),
    Sail.BitVec.update, Sail.BitVec.updateSubrange']
  congr 2
  bv_decide

theorem lookupEntryCorrect_AlignAddr (row : JoltTraceRow program)
    (h : JoltMetadata.lookupTable (rowInstruction row) = some .AlignAddr) :
    LookupEntryCorrect F .AlignAddr row := by
  lookup_cases
  simp only [alignAddr_entry, jolt_virtual_align_addr_value64,
    BitVec.setWidth_ofNat_of_le (by norm_num : 64 ≤ 128)]
  rfl

theorem lookupEntryCorrect_SignMask (row : JoltTraceRow program)
    (h : JoltMetadata.lookupTable (rowInstruction row) = some .SignMask) :
    LookupEntryCorrect F .SignMask row := by
  lookup_cases
  simp only [signMask_entry, jolt_movsign_value]

theorem lookupEntryCorrect_VirtualNegateIf (row : JoltTraceRow program)
    (h : JoltMetadata.lookupTable (rowInstruction row) = some .VirtualNegateIf) :
    LookupEntryCorrect F .VirtualNegateIf row := by
  lookup_cases
  simp only [negateIf_entry, jolt_virtual_negate_if_value]

theorem lookupEntryCorrect_Pow2 (row : JoltTraceRow program)
    (h : JoltMetadata.lookupTable (rowInstruction row) = some .Pow2) :
    LookupEntryCorrect F .Pow2 row := by
  lookup_cases
  all_goals simp only [pow2_entry, jolt_virtual_pow2_value, jolt_virtual_pow2i_value]
  all_goals congr 4
  all_goals simp [BitVec.toNat_setWidth, Nat.mod_mod_of_dvd]

theorem lookupEntryCorrect_Pow2W (row : JoltTraceRow program)
    (h : JoltMetadata.lookupTable (rowInstruction row) = some .Pow2W) :
    LookupEntryCorrect F .Pow2W row := by
  lookup_cases
  all_goals simp only [pow2W_entry, jolt_virtual_pow2w_value, jolt_virtual_pow2iw_value]
  all_goals congr 4
  all_goals simp [BitVec.toNat_setWidth, Nat.mod_mod_of_dvd]

theorem lookupEntryCorrect_ShiftRightBitmask (row : JoltTraceRow program)
    (h : JoltMetadata.lookupTable (rowInstruction row) = some .ShiftRightBitmask) :
    LookupEntryCorrect F .ShiftRightBitmask row := by
  lookup_cases
  all_goals simp only [shiftRightBitmask_entry, jolt_virtual_shift_right_bitmask_value,
    jolt_virtual_shift_right_bitmaski_value]
  all_goals congr 4 <;> simp [BitVec.toNat_setWidth, Nat.mod_mod_of_dvd]

theorem lookupEntryCorrect_ShiftRightBitmaskW (row : JoltTraceRow program)
    (h : JoltMetadata.lookupTable (rowInstruction row) = some .ShiftRightBitmaskW) :
    LookupEntryCorrect F .ShiftRightBitmaskW row := by
  lookup_cases
  simp only [shiftRightBitmaskW_entry, jolt_virtual_shift_right_bitmaskw_value]
  congr 5

theorem lookupEntryCorrect_ShiftDataB (row : JoltTraceRow program)
    (h : JoltMetadata.lookupTable (rowInstruction row) = some .ShiftDataB) :
    LookupEntryCorrect F .ShiftDataB row := by
  lookup_cases
  simp only [shiftDataB_entry]

theorem lookupEntryCorrect_ShiftDataH (row : JoltTraceRow program)
    (h : JoltMetadata.lookupTable (rowInstruction row) = some .ShiftDataH) :
    LookupEntryCorrect F .ShiftDataH row := by
  lookup_cases
  simp only [shiftDataH_entry]

theorem lookupEntryCorrect_ShiftDataW (row : JoltTraceRow program)
    (h : JoltMetadata.lookupTable (rowInstruction row) = some .ShiftDataW) :
    LookupEntryCorrect F .ShiftDataW row := by
  lookup_cases
  simp only [shiftDataW_entry]

theorem lookupEntryCorrect_WindowMaskB (row : JoltTraceRow program)
    (h : JoltMetadata.lookupTable (rowInstruction row) = some .WindowMaskB) :
    LookupEntryCorrect F .WindowMaskB row := by
  lookup_cases
  simp only [windowMaskB_entry, jolt_virtual_window_mask_b_value64]

theorem lookupEntryCorrect_WindowMaskH (row : JoltTraceRow program)
    (h : JoltMetadata.lookupTable (rowInstruction row) = some .WindowMaskH) :
    LookupEntryCorrect F .WindowMaskH row := by
  lookup_cases
  simp only [windowMaskH_entry, jolt_virtual_window_mask_h_value64]

theorem lookupEntryCorrect_WindowMaskW (row : JoltTraceRow program)
    (h : JoltMetadata.lookupTable (rowInstruction row) = some .WindowMaskW) :
    LookupEntryCorrect F .WindowMaskW row := by
  lookup_cases
  simp only [windowMaskW_entry, jolt_virtual_window_mask_w_value64]

theorem lookupEntryCorrect_VirtualXORROTL1 (row : JoltTraceRow program)
    (h : JoltMetadata.lookupTable (rowInstruction row) = some .VirtualXORROTL1) :
    LookupEntryCorrect F .VirtualXORROTL1 row := by
  lookup_cases
  simp only [xorRotL1_entry]

theorem lookupEntryCorrect_VirtualXORROT32 (row : JoltTraceRow program)
    (h : JoltMetadata.lookupTable (rowInstruction row) = some .VirtualXORROT32) :
    LookupEntryCorrect F .VirtualXORROT32 row := by
  lookup_cases
  exact xorRot_entry 32 (by decide) _ _

theorem lookupEntryCorrect_VirtualXORROT24 (row : JoltTraceRow program)
    (h : JoltMetadata.lookupTable (rowInstruction row) = some .VirtualXORROT24) :
    LookupEntryCorrect F .VirtualXORROT24 row := by
  lookup_cases
  exact xorRot_entry 24 (by decide) _ _

theorem lookupEntryCorrect_VirtualXORROT16 (row : JoltTraceRow program)
    (h : JoltMetadata.lookupTable (rowInstruction row) = some .VirtualXORROT16) :
    LookupEntryCorrect F .VirtualXORROT16 row := by
  lookup_cases
  exact xorRot_entry 16 (by decide) _ _

theorem lookupEntryCorrect_VirtualXORROT63 (row : JoltTraceRow program)
    (h : JoltMetadata.lookupTable (rowInstruction row) = some .VirtualXORROT63) :
    LookupEntryCorrect F .VirtualXORROT63 row := by
  lookup_cases
  exact xorRot_entry 63 (by decide) _ _

theorem lookupEntryCorrect_VirtualXORROTW16 (row : JoltTraceRow program)
    (h : JoltMetadata.lookupTable (rowInstruction row) = some .VirtualXORROTW16) :
    LookupEntryCorrect F .VirtualXORROTW16 row := by
  lookup_cases
  exact xorRotW_entry 16 (by decide) _ _

theorem lookupEntryCorrect_VirtualXORROTW12 (row : JoltTraceRow program)
    (h : JoltMetadata.lookupTable (rowInstruction row) = some .VirtualXORROTW12) :
    LookupEntryCorrect F .VirtualXORROTW12 row := by
  lookup_cases
  exact xorRotW_entry 12 (by decide) _ _

theorem lookupEntryCorrect_VirtualXORROTW8 (row : JoltTraceRow program)
    (h : JoltMetadata.lookupTable (rowInstruction row) = some .VirtualXORROTW8) :
    LookupEntryCorrect F .VirtualXORROTW8 row := by
  lookup_cases
  exact xorRotW_entry 8 (by decide) _ _

theorem lookupEntryCorrect_VirtualXORROTW7 (row : JoltTraceRow program)
    (h : JoltMetadata.lookupTable (rowInstruction row) = some .VirtualXORROTW7) :
    LookupEntryCorrect F .VirtualXORROTW7 row := by
  lookup_cases
  exact xorRotW_entry 7 (by decide) _ _

theorem lookupEntryCorrect_VirtualXORROTW22 (row : JoltTraceRow program)
    (h : JoltMetadata.lookupTable (rowInstruction row) = some .VirtualXORROTW22) :
    LookupEntryCorrect F .VirtualXORROTW22 row := by
  lookup_cases
  exact xorRotW_entry 22 (by decide) _ _

theorem lookupEntryCorrect_VirtualXORROTW19 (row : JoltTraceRow program)
    (h : JoltMetadata.lookupTable (rowInstruction row) = some .VirtualXORROTW19) :
    LookupEntryCorrect F .VirtualXORROTW19 row := by
  lookup_cases
  exact xorRotW_entry 19 (by decide) _ _

theorem lookupEntryCorrect_VirtualXORROTW6 (row : JoltTraceRow program)
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

theorem lookupEntryCorrect_VirtualRev8W (row : JoltTraceRow program)
    (h : JoltMetadata.lookupTable (rowInstruction row) = some .VirtualRev8W) :
    LookupEntryCorrect F .VirtualRev8W row := by
  lookup_cases
  simp only [virtualRev8WTableEntry, BitVec.ofFin_toFin, jolt_virtual_rev8w_value, rev8_32,
    Sail.BitVec.extractLsb, BitVec.setWidth_setWidth_of_le _ (by norm_num : 64 ≤ 128)]
  rw [BitVec.setWidth_eq, rev8w_eq]


-- FIXME: the six shift/rotate lemmas below are false while
-- `JoltProgram.expandedBytecode` is an arbitrary array: a `VirtualSRLI` row with
-- mask immediate `2` (or a `VirtualSRL` row whose mask register holds `2`) is
-- accepted, and its entry differs from its output. Rust's expander only emits
-- right-shift bitmasks here. Once `JoltProgram` records that construction,
-- prove these for bitmask-shaped masks. `Pext`/`PextSigned` are open (no
-- counterexample known).
/-- FALSE for arbitrary programs; left as `sorry`.
The table reads the right operand as a right-shift bitmask (ones from bit
`s` upward) and is correct only for such masks, while the honest output of
`VirtualSRL`/`VirtualSRLI` shifts by `ctz` of whatever mask the row carries.
`JoltProgram.expandedBytecode` is an arbitrary array (see the FIXME on
`JoltProgram.rowValid`), so nothing constrains the mask shape.
Counterexample: source `4`, mask `2`: entry `0`, output `4 >>> ctz 2 = 2`.
See `JoltConstraints/Tests/LookupShiftMask.lean`. -/
theorem lookupEntryCorrect_VirtualSRL (row : JoltTraceRow program)
    (h : JoltMetadata.lookupTable (rowInstruction row) = some .VirtualSRL) :
    LookupEntryCorrect F .VirtualSRL row := by
  sorry

/-- FALSE for arbitrary programs; left as `sorry`.
The table reads the right operand as a right-shift bitmask (ones from bit
`s` upward) and is correct only for such masks, while the honest output of
`VirtualSRA`/`VirtualSRAI` shifts by `ctz` of whatever mask the row carries.
`JoltProgram.expandedBytecode` is an arbitrary array (see the FIXME on
`JoltProgram.rowValid`), so nothing constrains the mask shape.
Counterexample: source `4`, mask `2`: entry `0`, output `4.sshiftRight 1 = 2`.
See `JoltConstraints/Tests/LookupShiftMask.lean`. -/
theorem lookupEntryCorrect_VirtualSRA (row : JoltTraceRow program)
    (h : JoltMetadata.lookupTable (rowInstruction row) = some .VirtualSRA) :
    LookupEntryCorrect F .VirtualSRA row := by
  sorry

/-- FALSE for arbitrary programs; left as `sorry`.
The table reads the right operand as a right-shift bitmask (ones from bit
`s` upward) and is correct only for such masks, while the honest output of
`VirtualSRLW`/`VirtualSRLIW` shifts by `ctz` of whatever mask the row carries.
`JoltProgram.expandedBytecode` is an arbitrary array (see the FIXME on
`JoltProgram.rowValid`), so nothing constrains the mask shape.
Counterexample: source `4`, mask `2`: entry `0`, output `2`. Also mask `0` for `VirtualSRLW`: entry `0`, output the sign-extended low word.
See `JoltConstraints/Tests/LookupShiftMask.lean`. -/
theorem lookupEntryCorrect_VirtualSRLW (row : JoltTraceRow program)
    (h : JoltMetadata.lookupTable (rowInstruction row) = some .VirtualSRLW) :
    LookupEntryCorrect F .VirtualSRLW row := by
  sorry

/-- FALSE for arbitrary programs; left as `sorry`.
The table reads the right operand as a right-shift bitmask (ones from bit
`s` upward) and is correct only for such masks, while the honest output of
`VirtualSRAW`/`VirtualSRAIW` shifts by `ctz` of whatever mask the row carries.
`JoltProgram.expandedBytecode` is an arbitrary array (see the FIXME on
`JoltProgram.rowValid`), so nothing constrains the mask shape.
Counterexample: source `4`, mask `2`: entry `0`, output `2`.
See `JoltConstraints/Tests/LookupShiftMask.lean`. -/
theorem lookupEntryCorrect_VirtualSRAW (row : JoltTraceRow program)
    (h : JoltMetadata.lookupTable (rowInstruction row) = some .VirtualSRAW) :
    LookupEntryCorrect F .VirtualSRAW row := by
  sorry

/-- FALSE for arbitrary programs; left as `sorry`.
The table reads the right operand as a right-shift bitmask (ones from bit
`s` upward) and is correct only for such masks, while the honest output of
`VirtualROTRI` shifts by `ctz` of whatever mask the row carries.
`JoltProgram.expandedBytecode` is an arbitrary array (see the FIXME on
`JoltProgram.rowValid`), so nothing constrains the mask shape.
Counterexample: source `4`, mask `2`: entry `4`, output `rotater 4 1 = 2`.
See `JoltConstraints/Tests/LookupShiftMask.lean`. -/
theorem lookupEntryCorrect_VirtualROTR (row : JoltTraceRow program)
    (h : JoltMetadata.lookupTable (rowInstruction row) = some .VirtualROTR) :
    LookupEntryCorrect F .VirtualROTR row := by
  sorry

/-- FALSE for arbitrary programs; left as `sorry`.
The table reads the right operand as a right-shift bitmask (ones from bit
`s` upward) and is correct only for such masks, while the honest output of
`VirtualROTRIW` shifts by `ctz` of whatever mask the row carries.
`JoltProgram.expandedBytecode` is an arbitrary array (see the FIXME on
`JoltProgram.rowValid`), so nothing constrains the mask shape.
Counterexample: source `4`, mask `2`: entry `4`, output `2`.
See `JoltConstraints/Tests/LookupShiftMask.lean`. -/
theorem lookupEntryCorrect_VirtualROTRW (row : JoltTraceRow program)
    (h : JoltMetadata.lookupTable (rowInstruction row) = some .VirtualROTRW) :
    LookupEntryCorrect F .VirtualROTRW row := by
  sorry

/-- Open: the table's `pext` (contiguous fast path plus a clear-lowest-bit
loop) against `jolt_pext_nat 64`. They agree on 20000 random operand pairs
(`JoltConstraints/Tests/LookupShiftMask.lean`), but no proof yet. -/
theorem lookupEntryCorrect_Pext (row : JoltTraceRow program)
    (h : JoltMetadata.lookupTable (rowInstruction row) = some .Pext) :
    LookupEntryCorrect F .Pext row := by
  sorry

/-- Open: as `lookupEntryCorrect_Pext`, plus the sign-extension step
(`windowSignBit` versus bit `popcount - 1` of the extracted value). -/
theorem lookupEntryCorrect_PextSigned (row : JoltTraceRow program)
    (h : JoltMetadata.lookupTable (rowInstruction row) = some .PextSigned) :
    LookupEntryCorrect F .PextSigned row := by
  sorry

theorem lookupEntryCorrect_UnsignedLessThanEqual (row : JoltTraceRow program)
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

theorem lookupEntryCorrect_HalfwordAlignment (row : JoltTraceRow program)
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

theorem lookupEntryCorrect_WordAlignment (row : JoltTraceRow program)
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

theorem lookupEntryCorrect_MulUNoOverflow (row : JoltTraceRow program)
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

theorem lookupEntryCorrect_ValidDiv0 (row : JoltTraceRow program)
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

theorem lookupEntryCorrect_ValidUnsignedRemainder (row : JoltTraceRow program)
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
theorem rowLookupOutput_eq_zero_of_lookupTable_none (row : JoltTraceRow program)
    (h : JoltMetadata.lookupTable (rowInstruction row) = none) :
    rowLookupOutput row = 0 := by
  unfold rowLookupOutput
  cases hi : rowInstruction row <;>
    simp only [hi, JoltMetadata.lookupTable, reduceCtorEq] at h <;>
    simp only [hi]

/-- Dispatcher: the honest entry of the row's lookup table equals the honest
lookup output. Depends on every `lookupEntryCorrect_*` lemma, including the
ones left as `sorry` (`VirtualSRL`, `VirtualSRA`, `VirtualSRLW`, `VirtualSRAW`,
`VirtualROTR`, `VirtualROTRW`, `Pext`, `PextSigned`). -/
theorem lookupEntryCorrect_of_lookupTable (row : JoltTraceRow program) (k : LookupTableKind)
    (h : JoltMetadata.lookupTable (rowInstruction row) = some k) :
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
  | .VirtualSRL => lookupEntryCorrect_VirtualSRL row h
  | .VirtualSRA => lookupEntryCorrect_VirtualSRA row h
  | .VirtualROTR => lookupEntryCorrect_VirtualROTR row h
  | .VirtualROTRW => lookupEntryCorrect_VirtualROTRW row h
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
  | .VirtualSRLW => lookupEntryCorrect_VirtualSRLW row h
  | .VirtualSRAW => lookupEntryCorrect_VirtualSRAW row h
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
