import JoltConstraints.Soundness.Layer1.Ram
import JoltConstraints.Soundness.UntrustedAdvice.LoadWords

open LeanRV64D

/-! Move a field-valued initial RAM word into the first write to that word.
Suppose the equations hold with initial values `initialValue`, and `byteRam` is a
64-bit initial RAM that agrees with `initialValue` wherever `initialValue` is the
cast of a 64-bit word.
Let `gap` be the difference between the two initial values.
`shiftWitness` subtracts `gap` from the word's value columns until its first access
and adds it to `RamInc` at that access, so the shifted witness satisfies the
equations with initial RAM `byteRam`.
The first access cannot be a load, because a load reads a 64-bit word
(`load_ramReadValue_word`), so the read value of a store or of no access absorbs
the change.
Only `RamVal`, `RamValFinal`, `RamReadValue` and `RamInc` change, and only
constraints 03, 04, 23, 24, 26, 37 and 38 mention them. -/

set_option autoImplicit false

namespace JoltConstraints.Soundness.UntrustedAdvice

variable {F : Type} [Field F] {params : WitnessParams}

/-- No row before cycle `bound` selects RAM word `address`.
For example, if the first access to `address` is at cycle 5, then
`Untouched witness address 5` holds and `Untouched witness address 6` does not. -/
def Untouched (witness : WitnessType F params) (address : Fin params.ramSize) (bound : Nat) :
    Prop :=
  ∀ cycle : Fin params.traceLength, cycle.val < bound → witness.RamRa address cycle = 0

open Classical in
/-- The amount subtracted from word `address` at cycle `bound`: `gap address` until the
word's first access, and zero from then on.
For example, if the word's first access is at cycle 5, then
`correction witness gap address 5 = gap address` and
`correction witness gap address 6 = 0`. -/
noncomputable def correction (witness : WitnessType F params) (gap : Fin params.ramSize → F)
    (address : Fin params.ramSize) (bound : Nat) : F :=
  if Untouched witness address bound then gap address else 0

/-- The correction of the word that cycle `t` accesses, or zero if it accesses none.
For example, if cycle 5 is the first access to `address` and selects only that word, then
`accessCorrection witness gap 5 = gap address`. -/
noncomputable def accessCorrection (witness : WitnessType F params)
    (gap : Fin params.ramSize → F) (t : Fin params.traceLength) : F :=
  ∑ address, witness.RamRa address t * correction witness gap address t.val

/-- The witness with `gap` moved from the initial RAM into each word's first access.
For example, if word `address` has gap 3 and is first accessed at cycle 5, the shifted
witness lowers its `RamVal` by 3 at cycles 0 through 5, lowers `RamReadValue` at cycle 5
by 3, and raises `RamInc` at cycle 5 by 3. -/
noncomputable def shiftWitness (witness : WitnessType F params)
    (gap : Fin params.ramSize → F) : WitnessType F params :=
  { witness with
    RamVal := fun address t => witness.RamVal address t - correction witness gap address t.val
    RamValFinal := fun address =>
      witness.RamValFinal address - correction witness gap address params.traceLength
    RamReadValue := fun t => witness.RamReadValue t - accessCorrection witness gap t
    RamInc := fun t => witness.RamInc t + accessCorrection witness gap t }

variable {witness : WitnessType F params}
  {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
  (charAbove2pow127 : 2 ^ 127 < ringChar F)
  (context : ConstraintContext joltInstance privateInputs params)
  {initialValue : Nat → F}
  (equations : FieldConstraintEquations context.bytecode initialValue context.io
    context.entry witness)

include charAbove2pow127 context equations

/-- Every circuit flag is zero or one. For example, at a row that selects an `LD`
bytecode entry, `witness.OpFlags .Load t = 1`, and at a row that selects an `ADD` entry
it is `0`. -/
theorem opFlag_zero_or_one (flag : CircuitFlags) (t : Fin params.traceLength) :
    witness.OpFlags flag t = 0 ∨ witness.OpFlags flag t = 1 := by
  obtain ⟨slot, selected, _⟩ := bytecodeRa_unique charAbove2pow127 context equations t
  rw [opFlag_of_selected_bytecode charAbove2pow127 context equations flag t slot selected]
  unfold bytecodeCircuitFlag
  split <;> split_ifs <;> simp

omit charAbove2pow127 in
/-- Before `bound`, the corrections applied at a word's accesses add up to the part of
`gap` already released: `gap` after the first access, and zero before it.
For example, if the word's first access is at cycle 5 and selects it with `RamRa = 1`, the
sum is zero for `bound ≤ 5` and `gap address` for `bound ≥ 6`. -/
theorem prefix_correction (gap : Fin params.ramSize → F) (address : Fin params.ramSize)
    (bound : Nat) :
    (∑ cycle : Fin params.traceLength,
      if cycle.val < bound then
        witness.RamRa address cycle * correction witness gap address cycle.val
      else 0) =
      gap address - correction witness gap address bound := by
  classical
  by_cases untouched : Untouched witness address bound
  · rw [correction, ite_eq_left untouched, sub_self]
    apply Finset.sum_eq_zero
    intro cycle _
    split_ifs with before
    · rw [untouched cycle before, zero_mul]
    · rfl
  · rw [correction, ite_eq_right untouched, sub_zero]
    have accessed : ∃ k, ∃ cycle : Fin params.traceLength,
        cycle.val = k ∧ k < bound ∧ witness.RamRa address cycle ≠ 0 := by
      simp only [Untouched, not_forall] at untouched
      obtain ⟨cycle, before, nonzero⟩ := untouched
      exact ⟨cycle.val, cycle, rfl, before, nonzero⟩
    obtain ⟨first, firstIs, firstBefore, firstNonzero⟩ := Nat.find_spec accessed
    have earlier : Untouched witness address first.val := by
      intro cycle before
      by_contra nonzero
      have minimal := Nat.find_min' accessed ⟨cycle, rfl, by omega, nonzero⟩
      omega
    have firstOne : witness.RamRa address first = 1 :=
      (ramRa_zero_or_one context equations address first).resolve_left firstNonzero
    rw [Finset.sum_eq_single first]
    · rw [ite_eq_left (by omega), firstOne, one_mul, correction, ite_eq_left earlier]
    · intro cycle _ other
      split_ifs with before
      · by_cases zero : witness.RamRa address cycle = 0
        · rw [zero, zero_mul]
        · have minimal := Nat.find_min' accessed ⟨cycle, rfl, before, zero⟩
          have different : cycle.val ≠ first.val := fun same => other (Fin.ext same)
          have later : first.val < cycle.val := by omega
          rw [correction, ite_eq_right (fun untouched => firstNonzero (untouched first later)),
            mul_zero]
      · rfl
    · intro absent
      exact absurd (Finset.mem_univ _) absent

/-- At a cycle that selects `address`, the access correction is that word's correction.
For example, if cycle 5 selects only `address`, both sides are
`correction witness gap address 5`. -/
theorem ramRa_mul_accessCorrection (gap : Fin params.ramSize → F)
    (address : Fin params.ramSize) (t : Fin params.traceLength) :
    witness.RamRa address t * accessCorrection witness gap t =
      witness.RamRa address t * correction witness gap address t.val := by
  rcases ramRa_zero_or_one context equations address t with zero | one
  · rw [zero, zero_mul, zero_mul]
  · rw [one, one_mul, one_mul, accessCorrection, Finset.sum_eq_single address]
    · rw [one, one_mul]
    · intro other _ different
      rcases ramRa_zero_or_one context equations other t with otherZero | otherOne
      · rw [otherZero, zero_mul]
      · exact absurd (ramRa_at_most_one charAbove2pow127 context equations t other address
          otherOne one) different
    · intro absent
      exact absurd (Finset.mem_univ _) absent

/-- A load never accesses a word before its value becomes a 64-bit word.
At a word's first access, the read value is the initial value; a load reads a
64-bit word, and `gap` is zero at every such initial value.
For example, if a load at cycle 5 is the first access to a word whose initial value is
the cast of `7`, that word's gap is zero, so the product is zero. -/
theorem load_mul_accessCorrection (gap : Fin params.ramSize → F)
    (good : ∀ address : Fin params.ramSize,
      (∃ value : BitVec 64, initialValue address.val = (value.toNat : F)) → gap address = 0)
    (t : Fin params.traceLength) :
    witness.OpFlags .Load t * accessCorrection witness gap t = 0 := by
  rcases opFlag_zero_or_one charAbove2pow127 context equations .Load t with zero | one
  · rw [zero, zero_mul]
  rw [one, one_mul]
  rcases ramRa_zero_or_unique charAbove2pow127 context equations t with
    zero | ⟨address, selected, _⟩
  · simp [accessCorrection, zero]
  have collapse := ramRa_mul_accessCorrection charAbove2pow127 context equations gap address t
  rw [selected, one_mul, one_mul] at collapse
  rw [collapse, correction]
  split_ifs with untouched
  · obtain ⟨value, read⟩ := load_ramReadValue_word charAbove2pow127 context equations t one
    have readIs : witness.RamReadValue t = witness.RamVal address t := by
      rw [equations.ramReadValueEqRamRead t]
      simpa only [mul_comm] using ram_read_of_selected charAbove2pow127 context equations t
        (fun address => witness.RamVal address t) address selected
    have initialIs : witness.RamVal address t = initialValue address.val := by
      rw [equations.ramValEqInitialPlusPrefixRamInc address t, add_eq_left]
      apply Finset.sum_eq_zero
      intro cycle _
      split_ifs with before
      · rw [untouched cycle before, zero_mul]
      · rfl
    exact good address ⟨value, by rw [← initialIs, ← readIs, read]⟩
  · rfl

/-- A word's RAM value history up to cycle `bound` carries over to the shifted witness:
subtracting the word's correction at `bound` from a value with the original history
gives the history from `byteRam` with the shifted increments.
For example, `bound = t` gives the value at cycle `t`, and `bound = traceLength` the
final value. -/
theorem shifted_history (byteRam : Nat → BitVec 64) (gap : Fin params.ramSize → F)
    (gapIs : ∀ address : Fin params.ramSize,
      gap address = initialValue address.val - ramInitialValue byteRam address.val)
    (address : Fin params.ramSize) (bound : Nat) {value : F}
    (history : value = initialValue address.val +
      ∑ cycle : Fin params.traceLength, if cycle.val < bound then
        witness.RamRa address cycle * witness.RamInc cycle else 0) :
    value - correction witness gap address bound =
      ramInitialValue byteRam address.val +
        ∑ cycle : Fin params.traceLength, if cycle.val < bound then
          witness.RamRa address cycle *
            (witness.RamInc cycle + accessCorrection witness gap cycle) else 0 := by
  have split : (∑ cycle : Fin params.traceLength, if cycle.val < bound then
        witness.RamRa address cycle *
          (witness.RamInc cycle + accessCorrection witness gap cycle) else 0) =
      (∑ cycle : Fin params.traceLength, if cycle.val < bound then
        witness.RamRa address cycle * witness.RamInc cycle else 0) +
      ∑ cycle : Fin params.traceLength, if cycle.val < bound then
        witness.RamRa address cycle * correction witness gap address cycle.val else 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro cycle _
    split_ifs
    · rw [mul_add, ramRa_mul_accessCorrection charAbove2pow127 context equations gap address
        cycle]
    · rw [add_zero]
  rw [split, prefix_correction context equations gap address bound, history, gapIs address]
  ring

/-- The shifted witness satisfies the equations with the 64-bit initial RAM `byteRam`.
`byteRam` must agree with `initialValue` wherever `initialValue` is a 64-bit word, and
the public I/O mask must vanish wherever they differ.
For example, `onBytes_of_allConstraints` applies it with `byteInitialRam`, which meets
the first condition by `byteInitialRam_good` and the second by `byteInitialRam_masked`. -/
theorem shiftWitness_equations (byteRam : Nat → BitVec 64)
    (good : ∀ address : Fin params.ramSize,
      (∃ value : BitVec 64, initialValue address.val = (value.toNat : F)) →
        ramInitialValue byteRam address.val = initialValue address.val)
    (masked : ∀ address : Fin params.ramSize,
      ramPublicIoMask context.io address.val *
        (initialValue address.val - ramInitialValue byteRam address.val) = 0) :
    ConstraintEquations context.bytecode byteRam context.io context.entry
      (shiftWitness witness
        (fun address => initialValue address.val - ramInitialValue byteRam address.val)) := by
  set gap : Fin params.ramSize → F :=
    fun address => initialValue address.val - ramInitialValue byteRam address.val with gapIs
  have gapZero : ∀ address : Fin params.ramSize,
      (∃ value : BitVec 64, initialValue address.val = (value.toNat : F)) → gap address = 0 :=
    fun address word => by rw [gapIs]; dsimp only; rw [good address word, sub_self]
  have loads := load_mul_accessCorrection charAbove2pow127 context equations gap gapZero
  have collapse := ramRa_mul_accessCorrection charAbove2pow127 context equations gap
  exact
  { equations with
    ramReadEqRamWriteIfLoad := fun t => by
      have relation := equations.ramReadEqRamWriteIfLoad t
      change witness.OpFlags .Load t *
        (witness.RamReadValue t - accessCorrection witness gap t - witness.RamWriteValue t) = 0
      linear_combination relation - loads t
    ramReadEqRdWriteIfLoad := fun t => by
      have relation := equations.ramReadEqRdWriteIfLoad t
      change witness.OpFlags .Load t *
        (witness.RamReadValue t - accessCorrection witness gap t - witness.RdWriteValue t) = 0
      linear_combination relation - loads t
    ramReadValueEqRamRead := fun t => by
      change witness.RamReadValue t - accessCorrection witness gap t =
        ∑ address, witness.RamRa address t *
          (witness.RamVal address t - correction witness gap address t.val)
      rw [equations.ramReadValueEqRamRead t, accessCorrection, ← Finset.sum_sub_distrib]
      simp only [mul_sub]
    ramWriteValueEqRamReadWrite := fun t => by
      change witness.RamWriteValue t =
        ∑ address, witness.RamRa address t *
          (witness.RamVal address t - correction witness gap address t.val +
            (witness.RamInc t + accessCorrection witness gap t))
      rw [equations.ramWriteValueEqRamReadWrite t]
      apply Finset.sum_congr rfl
      intro address _
      linear_combination (collapse address t).symm
    ramOutputEqPublicIo := fun address => by
      have relation := equations.ramOutputEqPublicIo address
      change ramPublicIoMask context.io address.val *
        (witness.RamValFinal address - correction witness gap address params.traceLength -
          ((ramPublicIoWord context.io address.val).toNat : F)) = 0
      have maskedCorrection : ramPublicIoMask context.io address.val *
          correction witness gap address params.traceLength = 0 := by
        rw [correction]
        split_ifs
        · exact masked address
        · rw [mul_zero]
      linear_combination relation - maskedCorrection
    ramValEqInitialPlusPrefixRamInc := fun address t =>
      shifted_history charAbove2pow127 context equations byteRam gap (fun _ => rfl) address
        t.val (equations.ramValEqInitialPlusPrefixRamInc address t)
    ramValFinalEqInitialPlusRamInc := fun address => by
      have history : witness.RamValFinal address = initialValue address.val +
          ∑ cycle : Fin params.traceLength, if cycle.val < params.traceLength then
            witness.RamRa address cycle * witness.RamInc cycle else 0 := by
        rw [equations.ramValFinalEqInitialPlusRamInc address]
        simp only [Fin.is_lt, ite_true]
      have shifted := shifted_history charAbove2pow127 context equations byteRam gap
        (fun _ => rfl) address params.traceLength history
      simp only [Fin.is_lt, ite_true] at shifted
      exact shifted }

end JoltConstraints.Soundness.UntrustedAdvice
