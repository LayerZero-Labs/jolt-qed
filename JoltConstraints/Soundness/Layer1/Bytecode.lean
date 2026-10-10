import JoltConstraints.Soundness.Layer0.Words
import JoltConstraints.Soundness.Layer1.Addresses
import JoltConstraints.program_facts

set_option autoImplicit false

namespace JoltConstraints.Soundness

open scoped BigOperators

variable {F : Type} [Field F]
  {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
  {params : WitnessParams} {witness : WitnessType F params}

private theorem zero_ne_four (charAbove2pow127 : 2 ^ 127 < ringChar F) : (0 : F) ≠ 4 := by
  intro same
  have words : (0 : BitVec 64) = 4 := word_eq_of_field_eq charAbove2pow127 (by simpa using same)
  exact (by decide : (0 : BitVec 64) ≠ 4) words

/-- Preprocessed bytecode has no row at address four: real rows have addresses
at or above `RAM_START_ADDRESS` (`bytecode_address_ok`), and no-op slots have
address zero. The field encoding preserves this fact. -/
private theorem bytecodeAddress_ne_four (charAbove2pow127 : 2 ^ 127 < ringChar F)
    (context : ConstraintContext joltInstance privateInputs params) (address : Nat) :
    bytecodeAddress (F := F) context.bytecode address ≠ 4 := by
  have accepted : pc_map_ok context.bytecode = true := by
    obtain ⟨slots, preprocessed, _⟩ := context.entryIsRust
    unfold preprocess at preprocessed
    split at preprocessed
    · assumption
    · cases preprocessed
  cases address with
  | zero => exact zero_ne_four charAbove2pow127
  | succ index =>
    by_cases inRange : index < context.bytecode.size
    · simp only [bytecodeAddress, bytecodeRow, Array.getElem?_eq_getElem inRange]
      intro same
      have words : context.bytecode[index].address = (4 : BitVec 64) :=
        word_eq_of_field_eq charAbove2pow127 (by simpa using same)
      have valid := pc_map_ok_addresses context.bytecode accepted index inRange
      rw [words] at valid
      exact (by decide : bytecode_address_ok (4 : BitVec 64) ≠ true) valid
    · simpa [bytecodeAddress, bytecodeRow, inRange] using zero_ne_four (F := F) charAbove2pow127

/-- Once a bytecode address is selected, every read of a fixed bytecode column
returns that address's entry. The selected address hypothesis is discharged by
`bytecodeRa_unique` below. -/
theorem bytecode_read_of_selected (charAbove2pow127 : 2 ^ 127 < ringChar F)
    (context : ConstraintContext joltInstance privateInputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
    (t : Fin params.traceLength) (value : Fin (2 ^ params.logBytecodeK) → F)
    (chosen : Fin (2 ^ params.logBytecodeK)) (one : bytecodeRa witness chosen t = 1) :
    (∑ address, value address * bytecodeRa witness address t) = value chosen := by
  apply read_eq_selected (fun address => bytecodeRa witness address t) value
  · intro address
    rcases bytecodeRa_zero_or_one context equations address t with zero | one
    · simp [zero]
    · simp [one]
  · exact one
  · exact fun address selected =>
      bytecodeRa_at_most_one charAbove2pow127 context equations t address chosen selected one

/-- The unexpanded PC cannot be four, even before ruling out an all-zero
bytecode selector. Such a selector would instead give PC zero. -/
private theorem unexpandedPC_ne_four (charAbove2pow127 : 2 ^ 127 < ringChar F)
    (context : ConstraintContext joltInstance privateInputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
    (t : Fin params.traceLength) : witness.UnexpandedPC t ≠ 4 := by
  rw [equations.unexpandedPCEqBytecodeRead t]
  rcases bytecodeRa_zero_or_unique charAbove2pow127 context equations t with zero | ⟨chosen, one, _⟩
  · simpa only [zero, mul_zero, Finset.sum_const_zero] using zero_ne_four (F := F) charAbove2pow127
  · rw [bytecode_read_of_selected charAbove2pow127 context equations t _ chosen one]
    exact bytecodeAddress_ne_four charAbove2pow127 context chosen.val

/-- If every bytecode selector entry is zero, its PC and flags vanish, so the
ordinary PC-update equation forces the next unexpanded PC to four. -/
private theorem nextUnexpandedPC_eq_four_of_bytecodeRa_zero
    (context : ConstraintContext joltInstance privateInputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
    (t : Fin params.traceLength) (zero : ∀ address, bytecodeRa witness address t = 0) :
    witness.NextUnexpandedPC t = 4 := by
  have current : witness.UnexpandedPC t = 0 := by
    rw [equations.unexpandedPCEqBytecodeRead t]
    simp [zero]
  have flags : ∀ flag, witness.OpFlags flag t = 0 := by
    intro flag
    rw [equations.opFlagsEqBytecodeRead flag t]
    simp [zero]
  have branch : witness.ShouldBranch t = 0 := by
    rw [equations.shouldBranchEqLookupOutputMulBranch t,
      equations.instructionFlagsEqBytecodeRead .Branch t]
    simp [zero]
  have update := equations.nextUnexpandedPCUpdateOtherwise t
  simp only [current, flags, branch, sub_zero, mul_zero, one_mul, add_zero] at update
  exact sub_eq_zero.mp update

/-- Every witness cycle selects exactly one in-domain bytecode slot.
An all-zero selector would force next PC four, contradicting the shifted PC
at a following cycle or the zero shift at the final cycle.
The final-cycle zero matches Jolt revision `43cc043332762034b5f65379441576e06e7a3890`:
`relations/spartan/shift.rs` weights `UnexpandedPC` by `EqPlusOneOuter`, evaluated
by `stages/stage3/spartan_shift.rs` using `crates/jolt-poly/src/eq_plus_one.rs`.
Its no-wrap successor polynomial is zero for every output at the last cycle. -/
theorem bytecodeRa_unique (charAbove2pow127 : 2 ^ 127 < ringChar F)
    (context : ConstraintContext joltInstance privateInputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
    (t : Fin params.traceLength) : ∃! address, bytecodeRa witness address t = 1 := by
  rcases bytecodeRa_zero_or_unique charAbove2pow127 context equations t with zero | selected
  · have next := nextUnexpandedPC_eq_four_of_bytecodeRa_zero context equations t zero
    rw [equations.nextUnexpandedPCEqShift t] at next
    split at next
    · exact False.elim (unexpandedPC_ne_four charAbove2pow127 context equations _ next)
    · exact False.elim (zero_ne_four charAbove2pow127 next)
  · exact selected

end JoltConstraints.Soundness
