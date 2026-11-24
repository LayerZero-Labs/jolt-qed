import JoltConstraints.theorems.Soundness.Layer1.BytecodeReads
import JoltConstraints.theorems.HaltFlags

open LeanRV64D

set_option autoImplicit false

namespace JoltConstraints.Soundness

/-- At the end of a real row, the halt lane identifies the public halt kind.
For example, a real row followed by padding under a true panic claim must be
`Panic`, rather than an ordinary jump or a success halt.
This is the row-level obligation used by the stopping proof.
Jolt at `ff6fc6568`: `rv64_trace_constraints` (`NextIsNoopEqIsNoopUnlessHalt`). -/
private theorem instruction_halt_of_end_lane {F : Type} [Field F]
    (charAbove2pow127 : 2 ^ 127 < ringChar F) (instruction : JoltISA.Instr)
    (claimedPanic : Bool)
    (lane : (2 : F) =
      (2 - if claimedPanic then 1 else 0) *
        (if JoltMetadata.opcodeFlag instruction .Halt then 1 else 0) +
        (if JoltMetadata.opcodeFlag instruction .HaltPanic then 1 else 0)) :
    instruction.haltKind? = some (if claimedPanic then .panic else .success) := by
  have twoNe : (2 : F) ≠ 0 := by
    intro same
    have word : (2 : BitVec 64) = 0 :=
      word_eq_of_field_eq charAbove2pow127 (by simpa using same)
    exact (by decide : (2 : BitVec 64) ≠ 0) word
  obtain ⟨halt, panic⟩ := JoltMetadata.haltFlags instruction
  rw [halt, panic] at lane
  cases kindIs : instruction.haltKind? with
  | none =>
    simp only [kindIs, Option.isSome_none, Bool.false_eq_true,
      ↓reduceIte, beq_iff_eq, reduceCtorEq, mul_zero, add_zero] at lane
    exact False.elim (twoNe lane)
  | some kind =>
    have claim : (if claimedPanic then (1 : F) else 0) =
        (if kind = .panic then 1 else 0) := by
      simp only [kindIs, Option.isSome_some, ↓reduceIte, beq_iff_eq, Option.some.injEq,
        mul_one] at lane
      linear_combination lane
    cases kind <;> cases claimedPanic <;>
      simp only [Bool.false_eq_true, Bool.true_eq, ↓reduceIte, reduceCtorEq,
        zero_ne_one, one_ne_zero] at claim ⊢
    all_goals exact kindIs

/-- A selected real bytecode row followed by padding is the halt of the
publicly claimed kind.
For example, the selected EBREAK expansion is a panic halt when the public
panic claim is true, even if it occupies the final domain cycle exactly.
The next-noop shift supplies the final-cycle padding value separately. -/
theorem selected_halt_of_next_padding {F : Type} [Field F]
    (charAbove2pow127 : 2 ^ 127 < ringChar F)
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    {params : WitnessParams} {witness : WitnessType F params}
    (context : ConstraintContext joltInstance privateInputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
    (t : Fin params.traceLength) (chosen : Fin (2 ^ params.logBytecodeK))
    (selected : bytecodeRa witness chosen t = 1) (row : JoltInstructionRow)
    (atRow : bytecodeRow context.bytecode chosen.val = some row)
    (nextPadding : witness.NextIsNoop t = 1) :
    row.instruction.haltKind? = some (if context.io.panic then .panic else .success) := by
  have noop := instructionFlag_of_selected_bytecode charAbove2pow127
    context equations .IsNoop t chosen selected
  have halt := opFlag_of_selected_bytecode charAbove2pow127
    context equations .Halt t chosen selected
  have panic := opFlag_of_selected_bytecode charAbove2pow127
    context equations .HaltPanic t chosen selected
  have lane := equations.haltEndRule t
  rw [nextPadding, noop, halt, panic] at lane
  simp only [bytecodeInstructionFlag, bytecodeCircuitFlag, atRow,
    JoltMetadata.instructionFlag, JoltMetadata.circuitFlag, Bool.false_eq_true,
    ↓reduceIte, sub_zero, mul_one] at lane
  exact instruction_halt_of_end_lane charAbove2pow127 row.instruction context.io.panic lane

/-- The shifted no-op column is Boolean because it reads a selected bytecode flag,
or the fixed terminal value one.
For example, the final domain cycle always has `NextIsNoop = 1`. -/
theorem nextIsNoop_zero_or_one {F : Type} [Field F]
    (charAbove2pow127 : 2 ^ 127 < ringChar F)
    {inst : JoltInstance SourceInstruction} {inputs : JoltPrivateInputs}
    {params : WitnessParams} {witness : WitnessType F params}
    (context : ConstraintContext inst inputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
    (t : Fin params.traceLength) :
    witness.NextIsNoop t = 0 ∨ witness.NextIsNoop t = 1 := by
  rw [equations.nextIsNoopEqShift t]
  split
  · rename_i next
    obtain ⟨slot, selected, _⟩ := bytecodeRa_unique charAbove2pow127 context equations
      ⟨t.val + 1, next⟩
    rw [instructionFlag_of_selected_bytecode charAbove2pow127 context equations
      .IsNoop ⟨t.val + 1, next⟩ slot selected]
    cases atRow : bytecodeRow context.bytecode slot.val <;>
      simp only [bytecodeInstructionFlag, atRow, JoltMetadata.instructionFlag,
        Bool.false_eq_true, ↓reduceIte, true_or, or_true]
  · exact Or.inr rfl

private theorem halt_lane_nonzero {F : Type} [Field F]
    (charAbove2pow127 : 2 ^ 127 < ringChar F) (instruction : JoltISA.Instr)
    (claim : Bool) (halted : instruction.haltKind?.isSome = true) :
    (2 - if claim then (1 : F) else 0) *
      (if JoltMetadata.opcodeFlag instruction .Halt then 1 else 0) +
      (if JoltMetadata.opcodeFlag instruction .HaltPanic then 1 else 0) ≠ 0 := by
  have nonzero (n : Nat) (positive : 0 < n) (small : n ≤ 3) : (n : F) ≠ 0 := by
    intro zero
    have equal := natCast_injective_below_char
      (show n < ringChar F by omega) (show 0 < ringChar F by omega)
      (b := 0) (by simpa only [Nat.cast_zero] using zero)
    omega
  obtain ⟨halt, panic⟩ := JoltMetadata.haltFlags instruction
  rw [halt, panic]
  cases kindIs : instruction.haltKind? with
  | none => simp only [kindIs, Option.isSome_none, Bool.false_eq_true] at halted
  | some kind =>
    cases kind <;> cases claim <;>
      simp only [kindIs, Option.isSome_some, beq_iff_eq, Option.some.injEq,
        reduceCtorEq, Bool.false_eq_true, Bool.true_eq, ↓reduceIte,
        sub_zero, mul_one, add_zero, sub_self]
    all_goals norm_num only [Nat.reduceAdd, zero_add, one_mul, sub_self, sub_add_cancel]
    all_goals first
      | exact one_ne_zero
      | simpa only [Nat.cast_ofNat] using nonzero 2 (by omega) (by omega)
      | simpa only [Nat.cast_ofNat] using nonzero 3 (by omega) (by omega)

/-- A selected halt must have a padding successor, including the final-domain boundary.
For example, a panic row cannot be followed by a real row under either public claim. -/
theorem selected_halt_forces_next_padding {F : Type} [Field F]
    (charAbove2pow127 : 2 ^ 127 < ringChar F)
    {inst : JoltInstance SourceInstruction} {inputs : JoltPrivateInputs}
    {params : WitnessParams} {witness : WitnessType F params}
    (context : ConstraintContext inst inputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
    (t : Fin params.traceLength) (slot : Fin (2 ^ params.logBytecodeK))
    (selected : bytecodeRa witness slot t = 1) (row : JoltInstructionRow)
    (atRow : bytecodeRow context.bytecode slot.val = some row)
    (halted : row.instruction.haltKind?.isSome = true) :
    witness.NextIsNoop t = 1 := by
  rcases nextIsNoop_zero_or_one charAbove2pow127 context equations t with zero | one
  · have noop := instructionFlag_of_selected_bytecode charAbove2pow127 context equations
      .IsNoop t slot selected
    have halt := opFlag_of_selected_bytecode charAbove2pow127 context equations .Halt t slot selected
    have panic := opFlag_of_selected_bytecode charAbove2pow127 context equations .HaltPanic t slot selected
    have lane := equations.haltEndRule t
    rw [zero, noop, halt, panic] at lane
    simp only [bytecodeInstructionFlag, bytecodeCircuitFlag, atRow,
      JoltMetadata.instructionFlag, JoltMetadata.circuitFlag,
      Bool.false_eq_true, ↓reduceIte, sub_self, mul_zero] at lane
    exact False.elim (halt_lane_nonzero charAbove2pow127 row.instruction context.io.panic halted lane.symm)
  · exact one

end JoltConstraints.Soundness
