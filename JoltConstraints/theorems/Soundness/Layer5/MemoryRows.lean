import JoltConstraints.theorems.MemoryRowExecution
import JoltConstraints.theorems.Soundness.Layer5.RamAlignment
import JoltConstraints.theorems.Soundness.Layer3.Layout
import JoltConstraints.theorems.Soundness.Layer4.Inputs
import JoltConstraints.theorems.Soundness.Layer4.Table
import JoltConstraints.theorems.Soundness.Layer5.MemoryAddress

open LeanRV64D

/-! Native and floor-addressed memory rows, classified once by their width.
A memory row is a load (LD, VirtualLoadB/H/W) or a store (SD, VirtualStoreB/H/W).
Its effective address is `ea = base + imm`.
Native rows access the doubleword at `ea`; floor rows access the containing
doubleword `ea &&& ~~~7`.
For example, VirtualLoadH at `ea = 10` loads the doubleword at 8.
The facts below are proved once over the four widths and used by every memory step.
Jolt's tracer at ff6fc6568: `tracer/src/instruction/floor_access.rs`
(`addresses`, `load`, `store`), `tracer/src/instruction/ld.rs` (`LD::exec`) and
`tracer/src/instruction/sd.rs` (`SD::exec`).
Jolt's verifier at ff6fc6568 pins the accessed doubleword with constraint (01):
`crates/jolt-claims/src/protocols/composed/r1cs/rv64.rs`
(`rv64_eq_constraint_rows`, row 0). -/

set_option autoImplicit false

namespace JoltConstraints.Soundness

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail LeanRV64D LeanRV64D.Functions JoltISA

variable {F : Type} [Field F] {params : WitnessParams} {witness : WitnessType F params}
  {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
  (charAbove2pow128Minus2pow64 : 2 ^ 128 - 2 ^ 64 < ringChar F)
  (context : ConstraintContext joltInstance privateInputs params)
  (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
  {t : Fin params.traceLength} {slot : Fin (2 ^ params.logBytecodeK)}
  (selected : bytecodeRa witness slot t = 1)
  {row : JoltInstructionRow} (rowIs : bytecodeRow context.bytecode slot.val = some row)
  {width : MemoryWidth} {base : Src} {imm : BitVec 64}
  (access : AccessRow row.instruction width base imm)

include charAbove2pow128Minus2pow64 context equations selected rowIs access

/-- The lookup output of a selected access row is a small offset: zero for a
native row, and the AddressOffset entry for a floor row.
Once `sum` is known to be the effective address's value, that offset is
`sum &&& offsetMask`. For example, a halfword row at `ea = 10` outputs 2.
Jolt's prover: `crates/jolt-lookup-tables/src/tables/address_offset.rs`
(`AddressOffsetTable::materialize_entry`) at `ff6fc6568`. -/
private theorem AccessRow.lookup_offset (baseValue : BitVec 64)
    (source : witness.Rs1Value t = (baseValue.toNat : F)) :
    ∃ offset : Nat, offset ≤ 7 ∧ witness.LookupOutput t = (offset : F) ∧
      ∀ sum : Nat, sum < 2 ^ 64 →
        ((sum : Int) : F) = (((baseValue.toNat : Int) + imm.toInt : Int) : F) →
        offset = sum &&& width.offsetMask.toNat := by
  have bound := two_pow_127_lt_char charAbove2pow128Minus2pow64
  obtain ⟨-, immediate, -, tableIs⟩ := access.metadata
  obtain ⟨chosen, lookupSelected, _⟩ := instructionLookupRa_unique bound context equations t
  have output := lookupOutput_of_selected_bytecode bound context equations t slot selected
    chosen lookupSelected
  simp only [rowIs, Option.bind_some, tableIs] at output
  by_cases native : width = .double
  · subst native
    refine ⟨0, by decide, by simpa only [MemoryWidth.table?, Nat.cast_zero] using output, ?_⟩
    intro sum _ _
    simp [MemoryWidth.offsetMask]
  obtain ⟨addFlag, inputFlags⟩ := access.floor_inputs native
  simp only [Prod.mk.injEq] at inputFlags
  obtain ⟨rs1Flag, pcFlag, rs2Flag, immFlag, rdFlag⟩ := inputFlags
  have add : witness.OpFlags .AddOperands t = 1 := by
    simpa only [bytecodeCircuitFlag, rowIs, JoltMetadata.circuitFlag, addFlag] using!
      opFlag_of_selected_bytecode bound context equations .AddOperands t slot selected
  have raf := instructionRafFlag_one_of_arithmetic bound context equations t (Or.inl add)
  have immediateIs : witness.Imm t = (imm.toInt : F) := by
    rw [imm_of_selected_bytecode bound context equations t slot selected]
    simp only [bytecodeImmediate, rowIs, immediate]
  obtain ⟨left, right⟩ :=
    instructionInputs_of_selected_bytecode bound context equations t slot selected row rowIs
  simp only [rs1Flag, pcFlag, rs2Flag, immFlag, rdFlag, Bool.false_eq_true, ↓reduceIte,
    add_zero, zero_add, source, immediateIs] at left right
  have operand := rightLookupOperand_of_selected bound context equations t chosen lookupSelected
  rw [raf, sub_self, zero_mul, zero_add, one_mul] at operand
  have addition := equations.rightLookupAdd t
  rw [add, one_mul, operand, left, right, sub_sub, sub_eq_zero] at addition
  have entry (mask : Nat) (small : mask < 2 ^ 128) :
      ((BitVec.ofFin chosen &&& BitVec.ofNat 128 mask).toNat : F) = ((chosen.val &&& mask : Nat) : F) := by
    rw [BitVec.toNat_and, BitVec.toNat_ofFin, BitVec.toNat_ofNat, Nat.mod_eq_of_lt small]
  refine ⟨chosen.val &&& width.offsetMask.toNat, ?_, ?_, ?_⟩
  · have offsetSmall : width.offsetMask.toNat ≤ 7 := by cases width <;> decide
    exact le_trans Nat.and_le_right offsetSmall
  · simp only [lookupTableEntry, addressOffsetTableEntry] at output
    cases width
    · exact False.elim (native rfl)
    · simpa only [MemoryWidth.table?, Nat.reduceSub, entry 7 (by norm_num)] using! output
    · simpa only [MemoryWidth.table?, Nat.reduceSub, entry 6 (by norm_num)] using! output
    · simpa only [MemoryWidth.table?, Nat.reduceSub, entry 4 (by norm_num)] using! output
  · intro sum sumSmall sumIs
    have same : chosen.val = sum := natCast_injective_below_char
      (identityAddress_lt_char charAbove2pow128Minus2pow64 context equations t chosen lookupSelected raf)
      (lt_trans sumSmall (two_pow_64_lt_char bound))
      (by
        rw [addition]
        push_cast at sumIs
        exact sumIs.symm)
    rw [same]

/-- A selected access row's RAM address is the doubleword it accesses, and its
effective address is naturally aligned for its width.
Constraint (01) subtracts the lookup offset from the integer sum of the base
and signed immediate, RAM selection makes the result zero or an in-domain word
address, and the layout bound rules out wrapping.
For example, VirtualStoreH with base 16 and immediate -6 has `ea = 10`, records
`10 - 2 = 8`, and accesses 8; with `ea = 11` it would record 9, which no RAM
selection allows.
Jolt's verifier at ff6fc6568: `crates/jolt-claims/src/protocols/composed/r1cs/rv64.rs`
(`rv64_eq_constraint_rows`, row 0). -/
theorem AccessRow.address_encoded (regionFits : joltInstance.RamRegionFits)
    (baseValue : BitVec 64) (source : witness.Rs1Value t = (baseValue.toNat : F)) :
    witness.RamAddress t = ((width.accessed (baseValue + imm)).toNat : F) ∧
      (baseValue + imm) &&& width.alignMask = 0 ∧
      width.recorded (baseValue + imm) = width.accessed (baseValue + imm) := by
  have bound := two_pow_127_lt_char charAbove2pow128Minus2pow64
  obtain ⟨flags, immediate, -, -⟩ := access.metadata
  have active : witness.OpFlags .Load t + witness.OpFlags .Store t = 1 := by
    rw [opFlag_of_selected_bytecode bound context equations .Load t slot selected,
      opFlag_of_selected_bytecode bound context equations .Store t slot selected]
    rcases flags with ⟨load, store⟩ | ⟨load, store⟩ <;>
      simp [bytecodeCircuitFlag, rowIs, JoltMetadata.circuitFlag, load, store]
  have immediateIs : witness.Imm t = (imm.toInt : F) := by
    rw [imm_of_selected_bytecode bound context equations t slot selected]
    simp only [bytecodeImmediate, rowIs, immediate]
  have sum := ramAddress_eq_sum equations.ramAddrEqRs1PlusImmMinusLookupIfLoadStore
    t active baseValue imm source immediateIs
  obtain ⟨offset, offsetSmall, output, offsetIs⟩ :=
    access.lookup_offset charAbove2pow128Minus2pow64 context equations selected rowIs baseValue source
  obtain ⟨word, wordIs, wordFits⟩ : ∃ word : Nat,
      witness.RamAddress t = (word : F) ∧ word + 7 < 2 ^ 64 := by
    rcases ramRa_zero_or_unique bound context equations t with zero | ⟨chosen, one, _⟩
    · exact ⟨0, by simpa using (ramRa_zero_iff_address_zero bound context equations t).mp zero,
        by norm_num⟩
    · exact ⟨_, ramAddress_of_selected bound context equations t chosen one,
        ram_word_byte_lt_two_pow_64 context regionFits chosen ⟨7, by decide⟩⟩
  have fieldSum : (((baseValue.toNat : Int) + imm.toInt : Int) : F) = ((word + offset : Nat) : F) := by
    rw [Nat.cast_add, ← wordIs, sum, output]
    ring
  have intSum := addressSum_eq_of_field_eq bound baseValue imm (word + offset) (by omega) fieldSum
  have eaValue := address_toNat_eq_sum baseValue imm (by omega)
  have offsetEq := offsetIs (baseValue + imm).toNat (baseValue + imm).isLt (by rw [eaValue])
  have recordedValue : (width.recorded (baseValue + imm)).toNat = word := by
    rw [MemoryWidth.recorded_toNat, ← offsetEq]
    omega
  have recordedEncoded : witness.RamAddress t = ((width.recorded (baseValue + imm)).toNat : F) := by
    rw [recordedValue]
    exact wordIs
  have aligned := width.aligned_of_recorded _
    (ramAddress_aligned bound context equations t _ recordedEncoded)
  have same := width.recorded_eq_accessed _ aligned
  exact ⟨same ▸ recordedEncoded, aligned, same⟩

end JoltConstraints.Soundness
