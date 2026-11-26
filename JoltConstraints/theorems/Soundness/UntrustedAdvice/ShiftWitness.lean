import JoltConstraints.theorems.Soundness.UntrustedAdvice.RegisterWords
import JoltConstraints.theorems.Soundness.Layer3.Access
import JoltConstraints.theorems.Soundness.Layer3.History

open LeanRV64D

/-! Moving the untrusted-advice words into the 64-bit range.
Jolt's verifier adds a committed field element for each untrusted-advice word, so an
initial RAM value can lie outside the 64-bit range. No row reads or writes such a word:
`RamWriteProtected` forces a store to an advice word to keep its value, a store keeps a
register value, a load reads a range-checked doubleword, and every register value is a
64-bit word (`RegisterWords.lean`).
Subtracting the difference between two initial values from every RAM-table entry of a
word that no row selects keeps every constraint. The public I/O mask is zero on the
advice block, so the final-RAM check is unaffected.
Jolt at `ff6fc6568`: `crates/jolt-claims/src/protocols/jolt/relations/ram/read_write_checking.rs`
(the protected-increment claim) and `crates/jolt-verifier/src/stages/stage4/ram_val_check.rs`
(`ram_val_check_advice_block`). -/

set_option autoImplicit false

namespace JoltConstraints.Soundness.UntrustedAdvice

open scoped BigOperators

section Shift

variable {F : Type} [Field F] {params : WitnessParams}

/-- The witness with `gap k` subtracted from every RAM-table entry of word `k`,
including its final value. Every other column is unchanged.
For example, with `gap 5 = 3`, `RamVal 5 t` decreases by 3 at every cycle `t`. -/
def shiftRam (witness : WitnessType F params) (gap : Nat → F) : WitnessType F params :=
  { witness with
    RamVal := fun address t => witness.RamVal address t - gap address.val
    RamValFinal := fun address => witness.RamValFinal address - gap address.val }

/-- Shifting the RAM table of unselected, non-public words keeps every constraint,
with the initial values shifted by the same amounts.
`unselected` says that every row that selects a word has zero gap there, and
`nonPublic` that the public I/O mask vanishes wherever the gap does not. -/
theorem shiftRam_equations {bytecode : Array JoltInstructionRow} {io : JoltPublicIo}
    {entry : Fin (2 ^ params.logBytecodeK)} {witness : WitnessType F params}
    {initialValue : Nat → F} (gap : Nat → F)
    (equations : FieldConstraintEquations bytecode initialValue io entry witness)
    (unselected : ∀ (address : Fin params.ramSize) (t : Fin params.traceLength),
      witness.RamRa address t * gap address.val = 0)
    (nonPublic : ∀ address : Fin params.ramSize,
      ramPublicIoMask (F := F) io address.val * gap address.val = 0) :
    FieldConstraintEquations bytecode (fun address => initialValue address - gap address) io
      entry (shiftRam witness gap) := by
  refine
    { equations with
      ramReadValueEqRamRead := ?_
      ramWriteValueEqRamReadWrite := ?_
      ramOutputEqPublicIo := ?_
      ramValEqInitialPlusPrefixRamInc := ?_
      ramValFinalEqInitialPlusRamInc := ?_ }
  · intro t
    have relation := equations.ramReadValueEqRamRead t
    simp only [shiftRam]
    rw [relation]
    have zero : ∑ address : Fin params.ramSize, witness.RamRa address t * gap address.val = 0 :=
      Finset.sum_eq_zero fun address _ => unselected address t
    rw [← sub_zero (∑ address : Fin params.ramSize,
      witness.RamRa address t * witness.RamVal address t), ← zero, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun address _ => by ring
  · intro t
    have relation := equations.ramWriteValueEqRamReadWrite t
    simp only [shiftRam]
    rw [relation]
    have zero : ∑ address : Fin params.ramSize, witness.RamRa address t * gap address.val = 0 :=
      Finset.sum_eq_zero fun address _ => unselected address t
    rw [← sub_zero (∑ address : Fin params.ramSize,
      witness.RamRa address t * (witness.RamVal address t + witness.RamInc t)), ← zero,
      ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun address _ => by ring
  · intro address
    have relation := equations.ramOutputEqPublicIo address
    have masked := nonPublic address
    simp only [shiftRam]
    linear_combination relation - masked
  · intro address t
    have relation := equations.ramValEqInitialPlusPrefixRamInc address t
    simp only [shiftRam]
    rw [relation]
    ring
  · intro address
    have relation := equations.ramValFinalEqInitialPlusRamInc address
    simp only [shiftRam]
    rw [relation]
    ring

end Shift

variable {F : Type} [Field F] {params : WitnessParams} {witness : WitnessType F params}
  {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}

/-- A row's memory flags: a row that selects a RAM word is a load or a store.
For example, an ADD row selects no word. -/
theorem load_or_store_of_selected (charAbove2pow127 : 2 ^ 127 < ringChar F)
    (context : ConstraintContext joltInstance privateInputs params)
    {initialValue : Nat → F}
    (equations : FieldConstraintEquations context.bytecode initialValue context.io
      context.entry witness)
    (address : Fin params.ramSize) (t : Fin params.traceLength)
    (selected : witness.RamRa address t = 1) :
    witness.OpFlags .Load t = 1 ∨ witness.OpFlags .Store t = 1 := by
  obtain ⟨slot, chosen, _⟩ := bytecodeRa_unique charAbove2pow127 context equations t
  have flag : ∀ kind : CircuitFlags,
      witness.OpFlags kind t = 0 ∨ witness.OpFlags kind t = 1 := by
    intro kind
    rw [opFlag_of_selected_bytecode charAbove2pow127 context equations kind t slot chosen]
    unfold bytecodeCircuitFlag
    split
    · split
      · exact Or.inr rfl
      · exact Or.inl rfl
    · split
      · exact Or.inr rfl
      · exact Or.inl rfl
  rcases flag .Load with noLoad | load
  · rcases flag .Store with noStore | store
    · have zero := ramAddress_zero_of_not_load_store equations.ramAddrEqZeroIfNotLoadStore t
        noLoad noStore
      have none := (ramRa_zero_iff_address_zero charAbove2pow127 context equations t).mpr zero
        address
      rw [selected] at none
      exact False.elim (one_ne_zero none)
    · exact Or.inr store
  · exact Or.inl load

/-- A write-protected RAM word that some row selects has a 64-bit initial value.
At the first row that selects it, its table value is still its initial value.
A load there reads a range-checked doubleword, and a store there writes a register
value with zero increment.
For example, a committed untrusted-advice word equal to `2 ^ 64` is never selected. -/
theorem initialValue_word_of_selected (charAbove : 2 ^ 128 - 2 ^ 64 < ringChar F)
    (context : ConstraintContext joltInstance privateInputs params)
    {initialValue : Nat → F}
    (equations : FieldConstraintEquations context.bytecode initialValue context.io
      context.entry witness)
    (address : Fin params.ramSize)
    (protectedWord : ramWriteProtectedMask (F := F) context.bytecode
      context.io.memory_layout address.val = 1)
    (t : Fin params.traceLength) (selected : witness.RamRa address t = 1) :
    IsWord (initialValue address.val) := by
  classical
  have charAbove2pow127 := two_pow_127_lt_char charAbove
  have exists_selected : ∃ n, ∃ inRange : n < params.traceLength,
      witness.RamRa address ⟨n, inRange⟩ = 1 := ⟨t.val, t.isLt, selected⟩
  let first := Nat.find exists_selected
  obtain ⟨firstInRange, firstSelected⟩ := Nat.find_spec exists_selected
  have earlier : ∀ cycle : Fin params.traceLength, cycle.val < first →
      witness.RamRa address cycle = 0 := by
    intro cycle before
    rcases ramRa_zero_or_one context equations address cycle with zero | one
    · exact zero
    · exact False.elim (Nat.find_min exists_selected before ⟨cycle.isLt, one⟩)
  let start : Fin params.traceLength := ⟨first, firstInRange⟩
  have initial : witness.RamVal address start = initialValue address.val := by
    rw [equations.ramValEqInitialPlusPrefixRamInc address start]
    have zero : (∑ cycle : Fin params.traceLength,
        if cycle.val < start.val then witness.RamRa address cycle * witness.RamInc cycle
        else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro cycle _
      split
      · rename_i before
        rw [earlier cycle before, zero_mul]
      · rfl
    rw [zero, add_zero]
  rcases load_or_store_of_selected charAbove2pow127 context equations address start
      firstSelected with load | store
  · obtain ⟨value, read⟩ := load_ramReadValue_word charAbove2pow127 context equations start load
    rw [ramReadValue_of_selected charAbove2pow127 context equations start address
      firstSelected, initial] at read
    exact ⟨value, read⟩
  · have increment := ramInc_zero_of_selected_protected charAbove2pow127 context equations start
      address firstSelected protectedWord
    have written := ramWriteValue_of_selected charAbove2pow127 context equations start address
      firstSelected
    rw [initial, increment, add_zero] at written
    have relation := equations.rs2EqRamWriteIfStore start
    rw [store, one_mul, sub_eq_zero, written] at relation
    rw [← relation]
    exact rs2Value_word charAbove context equations start

end JoltConstraints.Soundness.UntrustedAdvice
