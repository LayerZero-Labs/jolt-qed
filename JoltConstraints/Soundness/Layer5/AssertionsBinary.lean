import JoltConstraints.Soundness.Layer5.AssertLessThanEqual
import JoltConstraints.Soundness.Layer4.Conditional

/-! Three two-register assertion rows. The selected lookup and Assert flag force
each condition before execution; no successful-assertion premise is assumed.
At public pin 8bbb2357:
See : jolt/tracer/src/instruction/virtual_assert_eq.rs:17-34
See : jolt/tracer/src/instruction/virtual_assert_valid_div0.rs:17-25
See : jolt/tracer/src/instruction/virtual_assert_valid_unsigned_remainder.rs:17-27 -/

set_option autoImplicit false

namespace JoltConstraints.Soundness

open Sail PreSail LeanRV64D.Functions JoltISA

/-- The equality and division/remainder guard rows. -/
inductive BinaryAssertion where
  | eq | div0 | remainder

/-- Build the row instruction. -/
def BinaryAssertion.instruction (kind : BinaryAssertion) (lhs rhs : Src)
    (imm : BitVec 128) : Instr :=
  match kind with
  | .eq => .VirtualAssertEQ lhs rhs imm
  | .div0 => .VirtualAssertValidDiv0 lhs rhs imm
  | .remainder => .VirtualAssertValidUnsignedRemainder lhs rhs imm

/-- The condition needed by the interpreter to retire successfully. -/
def BinaryAssertion.Passes (kind : BinaryAssertion) (lhs rhs : BitVec 64) : Prop :=
  match kind with
  | .eq => lhs = rhs
  | .div0 => ¬ (lhs = 0 ∧ rhs ≠ -1)
  | .remainder => rhs = 0 ∨ lhs < rhs

variable {F : Type} [Field F] {params : WitnessParams} {live : Fin 128 → Prop} {witness : WitnessType F params}
  {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
  (charAbove2pow128 : 2 ^ 128 < ringChar F)
  (context : ConstraintContext joltInstance privateInputs params)
  (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
  {t : Fin params.traceLength} {slot : Fin (2 ^ params.logBytecodeK)}
  (selected : bytecodeRa witness slot t = 1)
  {row : JoltInstructionRow} (rowIs : bytecodeRow context.bytecode slot.val = some row)
  (kind : BinaryAssertion) {lhs rhs : Src} {imm : BitVec 128}
  (instructionIs : row.instruction = kind.instruction lhs rhs imm)

include context rowIs instructionIs in
private theorem binaryAssertion_canonical :
    JoltRegisterEncoding.sourceIsCanonical lhs = true ∧
    JoltRegisterEncoding.sourceIsCanonical rhs = true := by
  cases kind <;>
    simpa only [instructionIs, BinaryAssertion.instruction,
      JoltRegisterEncoding.instructionIsCanonical, Bool.and_eq_true] using
      (bytecodeRow_rowOk context rowIs).canonical

include charAbove2pow128 context equations selected rowIs instructionIs

private theorem binaryAssertion_passes {pre : SailJoltState}
    (agrees : RegisterAgreementOn live witness t pre)
    (leftLive : live (TraceWitness.sourceRegisterAddress lhs))
    (rightLive : live (TraceWitness.sourceRegisterAddress rhs)) :
    kind.Passes (sourceValue lhs pre) (sourceValue rhs pre) := by
  have bound := two_pow_127_lt_char charAbove2pow128
  have canonical := binaryAssertion_canonical context rowIs kind instructionIs
  obtain ⟨left, right⟩ := agrees.registerInputs bound context equations selected rowIs
    lhs rhs canonical.1 canonical.2
    (by cases kind <;> rw [instructionIs] <;> rfl)
    (by cases kind <;> rw [instructionIs] <;> rfl)
    (by cases kind <;> rw [instructionIs] <;> rfl) leftLive rightLive
  have raf : witness.InstructionRafFlag t = 0 := by
    have flag := instructionRafFlag_of_selected_bytecode bound context equations t slot selected
    cases kind <;>
      simpa only [bytecodeRafFlag, rowIs, instructionIs, BinaryAssertion.instruction,
        JoltMetadata.instructionRafFlag, JoltMetadata.opcodeFlag, Bool.or_self] using flag
  have active : witness.OpFlags .Assert t = 1 := by
    have flag := opFlag_of_selected_bytecode bound context equations .Assert t slot selected
    cases kind <;>
      simpa only [bytecodeCircuitFlag, rowIs, instructionIs, BinaryAssertion.instruction,
        JoltMetadata.circuitFlag, JoltMetadata.opcodeFlag] using flag
  obtain ⟨leftLookup, rightLookup⟩ :=
    lookupOperands_eq_inputs_of_raf_zero bound context equations t raf
  have accepted := lookupOutput_one_of_assert equations.assertLookupOne t active
  cases kind with
  | eq =>
    have output := lookupOutput_equal bound context equations t slot selected
      (sourceValue lhs pre) (sourceValue rhs pre) raf
      (leftLookup.trans left) (rightLookup.trans right)
      (by simp only [rowIs, Option.bind_some, instructionIs,
        BinaryAssertion.instruction, JoltMetadata.lookupTable])
    change sourceValue lhs pre = sourceValue rhs pre
    exact predicate_of_assert equations.assertLookupOne t active _ output
  | div0 =>
    have output := lookupOutput_validDiv0 bound context equations t slot selected
      (sourceValue lhs pre) (sourceValue rhs pre) raf
      (leftLookup.trans left) (rightLookup.trans right)
      (by simp only [rowIs, Option.bind_some, instructionIs,
        BinaryAssertion.instruction, JoltMetadata.lookupTable])
    change ¬ (sourceValue lhs pre = 0 ∧ sourceValue rhs pre ≠ -1)
    intro bad
    rw [if_pos bad] at output
    exact zero_ne_one (output.symm.trans accepted)
  | remainder =>
    have output := lookupOutput_validUnsignedRemainder bound context equations t slot selected
      (sourceValue lhs pre) (sourceValue rhs pre) raf
      (leftLookup.trans left) (rightLookup.trans right)
      (by simp only [rowIs, Option.bind_some, instructionIs,
        BinaryAssertion.instruction, JoltMetadata.lookupTable])
    change sourceValue rhs pre = 0 ∨ sourceValue lhs pre < sourceValue rhs pre
    exact predicate_of_assert equations.assertLookupOne t active _ output

/-- All three assertion rows retire with no state change and preserve register
agreement, including at the final cycle.
Both source registers must be live; the live set is unchanged.
For example, a division guard retains agreement on its initialized temporaries. -/
theorem binaryAssertion_step {pre : SailJoltState}
    (agrees : RegisterAgreementOn live witness t pre)
    (leftLive : live (TraceWitness.sourceRegisterAddress lhs))
    (rightLive : live (TraceWitness.sourceRegisterAddress rhs))
    (answer : BitVec 64) (advice : row.instruction.RuntimeAdvice) :
    kind.Passes (sourceValue lhs pre) (sourceValue rhs pre) ∧
    execWithTapeAnswer (row.instruction.withRuntimeAdvice advice) answer pre =
      .ok RETIRE_SUCCESS pre ∧
    ∀ next : t.val + 1 < params.traceLength,
      RegisterAgreementOn live witness ⟨t.val + 1, next⟩ pre := by
  have canonical := binaryAssertion_canonical context rowIs kind instructionIs
  have leftRead := (agrees.read lhs canonical.1 leftLive).1
  have rightRead := (agrees.read rhs canonical.2 rightLive).1
  have passes := binaryAssertion_passes charAbove2pow128 context equations
    selected rowIs kind instructionIs agrees leftLive rightLive
  refine ⟨passes, ?_, ?_⟩
  · rw [withRuntimeAdvice_eq_of_noAdvice _ advice
      (by cases kind <;> rw [instructionIs] <;> rfl), instructionIs]
    cases kind with
    | eq =>
      by_cases zero : imm = 0#128
      · simp only [BinaryAssertion.instruction, BinaryAssertion.Passes] at passes ⊢
        simp only [execWithTapeAnswer, execInstr, bind, EStateM.bind, zero,
          ↓reduceIte, leftRead, rightRead, jolt_assert_eq, passes, pure, EStateM.pure]
      · simp only [BinaryAssertion.instruction, execWithTapeAnswer, execInstr,
          zero, ↓reduceIte, pure, EStateM.pure]
    | div0 =>
      simp only [BinaryAssertion.instruction, BinaryAssertion.Passes] at passes ⊢
      have noBad : ¬ (sourceValue lhs pre = 0#64 ∧ sourceValue rhs pre ≠ -1) := by
        simpa only using passes
      simp only [execWithTapeAnswer, execInstr, bind, EStateM.bind,
        leftRead, rightRead, if_neg noBad, pure, EStateM.pure]
    | remainder =>
      simp only [BinaryAssertion.instruction, BinaryAssertion.Passes] at passes ⊢
      have succeeds : sourceValue rhs pre = 0#64 ∨
          (sourceValue lhs pre).toNat < (sourceValue rhs pre).toNat := by
        simpa only [BitVec.lt_def] using passes
      simp only [execWithTapeAnswer, execInstr, bind, EStateM.bind,
        leftRead, rightRead, if_pos succeeds, pure, EStateM.pure]
  · intro next
    exact agrees.noWrite (two_pow_127_lt_char charAbove2pow128) context equations
      next slot selected rowIs (by cases kind <;> rw [instructionIs] <;> rfl)

end JoltConstraints.Soundness
