import JoltConstraints.Soundness.Layer3.Layout
import JoltConstraints.Soundness.Layer3.Address
import JoltConstraints.Soundness.Layer1.BytecodeReads
import JoltConstraints.Soundness.Layer4.Table

open LeanRV64D

/-! Recover load/store addresses as integers before converting them to machine
words. Constraint (01) gives the field value of the integer sum of a base word
and a signed immediate, minus the lookup offset; the lemmas here recover that
sum and its machine word. `AccessRow.address_encoded` (`MemoryRows.lean`)
combines them with RAM selection and the layout premise, including the
unselected address-zero case and negative signed immediates. -/

set_option autoImplicit false

namespace JoltConstraints.Soundness

variable {F : Type} [Field F]

/-- A base word plus a signed immediate, as an integer, equals a natural number
below `2^64` whenever their field encodings agree.
For example, base 16 plus immediate -8 can only encode the address 8.
The shift by `2^63` covers a possibly negative sum. -/
theorem addressSum_eq_of_field_eq
    (charAbove2pow127 : 2 ^ 127 < ringChar F) (base imm : BitVec 64)
    (address : Nat) (addressLt : address < 2 ^ 64)
    (same : (((base.toNat : Int) + imm.toInt : Int) : F) = (address : F)) :
    (base.toNat : Int) + imm.toInt = address := by
  have baseLt := base.isLt
  have immLower := imm.le_toInt
  have immUpper := BitVec.toInt_lt (x := imm)
  have charBound : (2 : Int) ^ 127 < (ringChar F : Int) := by
    exact_mod_cast charAbove2pow127
  -- Shift both integers into [0, p). This includes a possibly negative sum;
  -- equality of their unshifted residues alone would not establish equality.
  have shifted : (base.toNat : Int) + imm.toInt + 2 ^ 63 = (address : Int) + 2 ^ 63 := by
    apply CharP.intCast_injOn_Ico F (ringChar F)
    · exact ⟨by omega, by omega⟩
    · exact ⟨by omega, by omega⟩
    · simpa only [Int.cast_add, Int.cast_pow, Int.cast_ofNat, Int.cast_natCast] using
        congrArg (fun value : F => value + (2 : F) ^ 63) same
  omega

/-- A word whose field encoding is a base plus a signed immediate is the
wrapping machine sum, since the characteristic separates the possible integer
sums from all 64-bit words.
For example, base 16 plus immediate -8 must encode word 8.
This also recovers the address operand of VirtualShiftData rows. -/
theorem word_add_eq_of_field_sum (charAbove2pow127 : 2 ^ 127 < ringChar F)
    (base imm word : BitVec 64)
    (same : (((base.toNat : Int) + imm.toInt : Int) : F) = (word.toNat : F)) :
    base + imm = word := by
  have sum := addressSum_eq_of_field_eq charAbove2pow127 base imm word.toNat word.isLt same
  calc
    base + imm = BitVec.ofInt 64 ((base.toNat : Int) + imm.toInt) := by
      simp only [BitVec.ofInt_add, BitVec.ofInt_natCast, BitVec.ofNat_toNat,
        BitVec.ofInt_toInt, BitVec.setWidth_eq]
    _ = word := by rw [sum]; simp

variable {params : WitnessParams} {witness : WitnessType F params}

/-- For an active memory cycle, constraint (01) subtracts the lookup offset
from the integer base value plus signed immediate, without assuming no wrap.
For example, a halfword row at effective address 10 subtracts offset 2.
See Jolt's verifier at c6703570, `crates/jolt-claims/src/protocols/composed/r1cs/rv64.rs`
(`rv64_eq_constraint_rows`, row 0). -/
theorem ramAddress_eq_sum (constraint : ramAddrEqRs1PlusImmMinusLookupIfLoadStore witness)
    (t : Fin params.traceLength)
    (active : witness.OpFlags .Load t + witness.OpFlags .Store t = 1)
    (base imm : BitVec 64)
    (source : witness.Rs1Value t = (base.toNat : F))
    (immediate : witness.Imm t = (imm.toInt : F)) :
    witness.RamAddress t = (((base.toNat : Int) + imm.toInt : Int) : F) -
      witness.LookupOutput t := by
  have relation := constraint t
  rw [active, one_mul, source, immediate] at relation
  push_cast
  linear_combination relation

/-- A nonwrapping integer sum of a base word and a signed immediate is the
machine sum's value; for example, base 16 plus immediate -8 is word 8. -/
theorem address_toNat_eq_sum (base imm : BitVec 64)
    (noWrap : 0 ≤ (base.toNat : Int) + imm.toInt ∧
      (base.toNat : Int) + imm.toInt < 2 ^ 64) :
    ((base + imm).toNat : Int) = (base.toNat : Int) + imm.toInt := by
  have asWord : base + imm = BitVec.ofInt 64 ((base.toNat : Int) + imm.toInt) := by
    simp only [BitVec.ofInt_add, BitVec.ofInt_natCast, BitVec.ofNat_toNat,
      BitVec.ofInt_toInt, BitVec.setWidth_eq]
  rw [asWord, BitVec.toNat_ofInt, Nat.cast_pow, Nat.cast_ofNat,
    Int.emod_eq_of_lt noWrap.1 noWrap.2,
    Int.toNat_of_nonneg noWrap.1]

end JoltConstraints.Soundness
