import JoltConstraints.Soundness.Layer3.Layout
import JoltConstraints.Soundness.Layer3.Address
import JoltConstraints.Soundness.Layer1.BytecodeReads

/-! Recover load/store addresses as integers before converting them to machine
words. The layout premise bounds the RAM domain; the operand encodings are
local agreement facts to be supplied by the execution induction. The argument
also covers the unselected address-zero case and negative signed immediates. -/

set_option autoImplicit false

namespace JoltConstraints.Soundness

variable {F : Type} [Field F]

private theorem addressSum_eq_of_field_eq
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

variable {params : WitnessParams} {witness : WitnessType F params}

/-- For an active load/store cycle, the address column is the field encoding
of the integer base value plus signed immediate. No no-wrap fact is used. -/
theorem ramAddress_eq_sum (constraint : ramAddrEqRs1PlusImmIfLoadStore witness)
    (t : Fin params.traceLength)
    (active : witness.OpFlags .Load t + witness.OpFlags .Store t = 1)
    (base imm : BitVec 64)
    (source : witness.Rs1Value t = (base.toNat : F))
    (immediate : witness.Imm t = (imm.toInt : F)) :
    witness.RamAddress t = (((base.toNat : Int) + imm.toInt : Int) : F) := by
  have relation := constraint t
  rw [active, one_mul, source, immediate] at relation
  push_cast
  linear_combination relation

variable {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
  (charAbove2pow127 : 2 ^ 127 < ringChar F)
  (context : ConstraintContext joltInstance privateInputs params)
  (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)

include charAbove2pow127 context equations

/-- Selection recovers the actual integer sum, not just its residue in the
field. In particular, a negative sum cannot select a nonnegative word address. -/
theorem addressSum_eq_of_selected (regionFits : joltInstance.RamRegionFits)
    (t : Fin params.traceLength) (base imm : BitVec 64)
    (encodedSum : witness.RamAddress t = (((base.toNat : Int) + imm.toInt : Int) : F))
    (chosen : Fin params.ramSize) (selected : witness.RamRa chosen t = 1) :
    (base.toNat : Int) + imm.toInt =
      (ramLowestAddress context.io.memory_layout + 8 * chosen.val : Nat) := by
  have addressLt := ram_word_byte_lt_two_pow_64 context regionFits chosen ⟨0, by decide⟩
  apply addressSum_eq_of_field_eq charAbove2pow127 base imm _ (by simpa using addressLt)
  exact encodedSum.symm.trans
    (ramAddress_of_selected charAbove2pow127 context equations t chosen selected)

/-- If no RAM word is selected, the integer sum is exactly zero. This rules
out both a negative sum and a nonzero multiple of the characteristic. -/
theorem addressSum_zero_of_unselected (t : Fin params.traceLength) (base imm : BitVec 64)
    (encodedSum : witness.RamAddress t = (((base.toNat : Int) + imm.toInt : Int) : F))
    (unselected : ∀ address, witness.RamRa address t = 0) :
    (base.toNat : Int) + imm.toInt = 0 := by
  have zero := (ramRa_zero_iff_address_zero charAbove2pow127 context equations t).mp unselected
  exact addressSum_eq_of_field_eq charAbove2pow127 base imm 0 (by decide)
    (by simpa using encodedSum.symm.trans zero)

/-- A constrained address sum lies in the machine range: it is zero or an
in-domain word address. This holds for either execution specification. -/
theorem addressSum_noWrap (regionFits : joltInstance.RamRegionFits)
    (t : Fin params.traceLength) (base imm : BitVec 64)
    (encodedSum : witness.RamAddress t = (((base.toNat : Int) + imm.toInt : Int) : F)) :
    0 ≤ (base.toNat : Int) + imm.toInt ∧ (base.toNat : Int) + imm.toInt < 2 ^ 64 := by
  rcases ramRa_zero_or_unique charAbove2pow127 context equations t with zero | ⟨chosen, one, _⟩
  · rw [addressSum_zero_of_unselected charAbove2pow127 context equations t base imm encodedSum zero]
    norm_num
  · rw [addressSum_eq_of_selected charAbove2pow127 context equations regionFits
      t base imm encodedSum chosen one]
    have addressLt := ram_word_byte_lt_two_pow_64 context regionFits chosen ⟨0, by decide⟩
    exact ⟨Int.natCast_nonneg _, by exact_mod_cast (by simpa using addressLt :
      ramLowestAddress context.io.memory_layout + 8 * chosen.val < 2 ^ 64)⟩

omit charAbove2pow127 context equations in
private theorem address_toNat_eq_sum (base imm : BitVec 64)
    (noWrap : 0 ≤ (base.toNat : Int) + imm.toInt ∧
      (base.toNat : Int) + imm.toInt < 2 ^ 64) :
    ((base + imm).toNat : Int) = (base.toNat : Int) + imm.toInt := by
  have asWord : base + imm = BitVec.ofInt 64 ((base.toNat : Int) + imm.toInt) := by
    simp only [BitVec.ofInt_add, BitVec.ofInt_natCast, BitVec.ofNat_toNat,
      BitVec.ofInt_toInt, BitVec.setWidth_eq]
  rw [asWord, BitVec.toNat_ofInt, Nat.cast_pow, Nat.cast_ofNat,
    Int.emod_eq_of_lt noWrap.1 noWrap.2,
    Int.toNat_of_nonneg noWrap.1]

/-- The constrained field address encodes the machine's wrapped addition,
because selection and the layout bound prove that this addition does not wrap. -/
theorem ramAddress_encoded (regionFits : joltInstance.RamRegionFits)
    (t : Fin params.traceLength) (base imm : BitVec 64)
    (encodedSum : witness.RamAddress t = (((base.toNat : Int) + imm.toInt : Int) : F)) :
    witness.RamAddress t = ((base + imm).toNat : F) := by
  have noWrap := addressSum_noWrap charAbove2pow127 context equations regionFits t base imm encodedSum
  have same := congrArg (fun value : Int => (value : F)) (address_toNat_eq_sum base imm noWrap)
  exact encodedSum.trans (by simpa only [Int.cast_natCast] using same.symm)

/-- An LD row supplies the load flag and signed immediate. Once its source
column agrees with the base word, the address is encoded without wrapping. -/
theorem ld_address_encoded (regionFits : joltInstance.RamRegionFits)
    (t : Fin params.traceLength) (slot : Fin (2 ^ params.logBytecodeK))
    (selected : bytecodeRa witness slot t = 1) (row : JoltInstructionRow)
    (present : bytecodeRow context.bytecode slot.val = some row)
    (fault : JoltISA.LoadFaultClass) (destination : JoltISA.Dst) (source : JoltISA.Src)
    (base imm : BitVec 64) (instruction : row.instruction = .LD fault destination source imm)
    (sourceValue : witness.Rs1Value t = (base.toNat : F)) :
    witness.RamAddress t = ((base + imm).toNat : F) := by
  have active : witness.OpFlags .Load t + witness.OpFlags .Store t = 1 := by
    rw [opFlag_of_selected_bytecode charAbove2pow127 context equations .Load t slot selected,
      opFlag_of_selected_bytecode charAbove2pow127 context equations .Store t slot selected]
    simp [bytecodeCircuitFlag, present, JoltMetadata.circuitFlag, instruction, JoltMetadata.opcodeFlag]
  have immediate : witness.Imm t = (imm.toInt : F) := by
    rw [imm_of_selected_bytecode charAbove2pow127 context equations t slot selected]
    simp [bytecodeImmediate, present, instruction, JoltMetadata.immediate]
  exact ramAddress_encoded charAbove2pow127 context equations regionFits t base imm
    (ramAddress_eq_sum equations.ramAddrEqRs1PlusImmIfLoadStore t active base imm sourceValue immediate)

/-- An SD row supplies the store flag and signed immediate. The same integer
argument gives its machine address, including the unselected zero case. -/
theorem sd_address_encoded (regionFits : joltInstance.RamRegionFits)
    (t : Fin params.traceLength) (slot : Fin (2 ^ params.logBytecodeK))
    (selected : bytecodeRa witness slot t = 1) (row : JoltInstructionRow)
    (present : bytecodeRow context.bytecode slot.val = some row)
    (source value : JoltISA.Src) (base imm : BitVec 64)
    (instruction : row.instruction = .SD source value imm)
    (sourceValue : witness.Rs1Value t = (base.toNat : F)) :
    witness.RamAddress t = ((base + imm).toNat : F) := by
  have active : witness.OpFlags .Load t + witness.OpFlags .Store t = 1 := by
    rw [opFlag_of_selected_bytecode charAbove2pow127 context equations .Load t slot selected,
      opFlag_of_selected_bytecode charAbove2pow127 context equations .Store t slot selected]
    simp [bytecodeCircuitFlag, present, JoltMetadata.circuitFlag, instruction, JoltMetadata.opcodeFlag]
  have immediate : witness.Imm t = (imm.toInt : F) := by
    rw [imm_of_selected_bytecode charAbove2pow127 context equations t slot selected]
    simp [bytecodeImmediate, present, instruction, JoltMetadata.immediate]
  exact ramAddress_encoded charAbove2pow127 context equations regionFits t base imm
    (ramAddress_eq_sum equations.ramAddrEqRs1PlusImmIfLoadStore t active base imm sourceValue immediate)

end JoltConstraints.Soundness
