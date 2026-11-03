import JoltConstraints.lookup_table
import JoltBytecode.InstructionEquivalence.ProofSupport.BitVecMasks

set_option autoImplicit false

namespace JoltConstraints

/-- The low word of a floor index is the wrapping effective address; for
example, base zero plus immediate -16 has low word `2^64 - 16`.
Jolt's prover: `crates/jolt-lookup-tables/src/instructions/virt/floor_access.rs`
(`to_lookup_index`) at `c6703570`. -/
private theorem floor_index_low (base imm : BitVec 64) :
    (BitVec.ofInt 128 (base.toNat + imm.toInt)).setWidth 64 = base + imm := by
  rw [BitVec.ofInt_add, BitVec.setWidth_add _ _ (by decide), BitVec.ofInt_natCast]
  congr 1
  · simp
  · change (imm.signExtend 128).setWidth 64 = imm
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_signExtend, hi,
      show i < 128 by omega, decide_true, Bool.true_and, if_true]

/-- AddressOffset returns the effective address masked by `8 - width`, for
any width; widths 1, 2 and 4 give masks 7, 6 and 4 respectively.
For example, width 2 at effective address 10 returns 2, even if the sum wrapped.
Jolt's prover: `crates/jolt-lookup-tables/src/tables/address_offset.rs`
(`AddressOffsetTable::materialize_entry`) at `c6703570`. -/
theorem addressOffset_entry {F : Type} [Field F] (width : Nat) (base imm : BitVec 64) :
    addressOffsetTableEntry (F := F) width
      (BitVec.ofInt 128 (base.toNat + imm.toInt)).toFin =
      (((base + imm) &&& BitVec.ofNat 64 (8 - width)).toNat : F) := by
  have masked := BitVec.ushiftRight_and_setWidth
    (BitVec.ofInt 128 (base.toNat + imm.toInt)) (8 - width) 0 4
    (by omega) (by decide : 4 + 0 ≤ 64) (by decide : 64 ≤ 128)
  simp only [BitVec.ushiftRight_zero, floor_index_low] at masked
  simp only [addressOffsetTableEntry, BitVec.ofFin_toFin, masked,
    BitVec.toNat_setWidth_of_le (by decide : 64 ≤ 128)]

end JoltConstraints
