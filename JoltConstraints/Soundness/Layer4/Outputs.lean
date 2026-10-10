import JoltConstraints.Soundness.Layer4.Table

/-! How the constraints consume lookup outputs: register writes, assertions and
branches. Instruction-specific callers derive the active flags from bytecode. -/

set_option autoImplicit false

namespace JoltConstraints.Soundness

variable {F : Type} [Field F] {params : WitnessParams} {witness : WitnessType F params}

/-- A lookup-writing instruction writes exactly the lookup output. -/
theorem rdWriteValue_eq_lookupOutput
    (write : rdWriteEqLookupIfWriteLookupToRd witness) (t : Fin params.traceLength)
    (active : witness.OpFlags .WriteLookupOutputToRD t = 1) :
    witness.RdWriteValue t = witness.LookupOutput t := by
  have relation := write t
  rw [active, one_mul] at relation
  exact sub_eq_zero.mp relation

/-- An assertion row must receive the accepting table entry, one. -/
theorem lookupOutput_one_of_assert
    (assertion : assertLookupOne witness) (t : Fin params.traceLength)
    (active : witness.OpFlags .Assert t = 1) :
    witness.LookupOutput t = 1 := by
  have relation := assertion t
  rw [active, one_mul] at relation
  exact sub_eq_zero.mp relation

/-- A predicate table accepted by an assertion establishes that predicate. -/
theorem predicate_of_assert
    (assertion : assertLookupOne witness) (t : Fin params.traceLength)
    (active : witness.OpFlags .Assert t = 1) (predicate : Prop) [Decidable predicate]
    (output : witness.LookupOutput t = if predicate then 1 else 0) : predicate := by
  have accepted := lookupOutput_one_of_assert assertion t active
  by_contra rejected
  simp [rejected] at output
  exact zero_ne_one (output.symm.trans accepted)

/-- A branch uses the comparison result as its branch decision. -/
theorem shouldBranch_eq_lookupOutput
    (branch : shouldBranchEqLookupOutputMulBranch witness) (t : Fin params.traceLength)
    (active : witness.InstructionFlags .Branch t = 1) :
    witness.ShouldBranch t = witness.LookupOutput t := by
  simpa only [active, mul_one] using branch t

end JoltConstraints.Soundness
