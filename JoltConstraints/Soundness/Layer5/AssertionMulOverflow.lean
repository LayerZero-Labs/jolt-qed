import JoltConstraints.Soundness.Layer5.AssertLessThanEqual
import JoltConstraints.Soundness.Layer4.Assertions
import JoltConstraints.Soundness.Layer4.Arithmetic

/-! The unsigned-multiplication guard uses the full 128-bit product lookup.
At public pin 8bbb2357:
See : jolt/tracer/src/instruction/virtual_assert_mulu_no_overflow.rs:16-26 -/

set_option autoImplicit false

namespace JoltConstraints.Soundness

open Sail PreSail LeanRV64D.Functions JoltISA

private theorem mulWide_lt_128 (lhs rhs : BitVec 64) : mulWide lhs rhs < 2 ^ 128 := by
  have bound := Nat.mul_lt_mul'' lhs.isLt rhs.isLt
  simpa only [mulWide, ← pow_add] using bound

variable {F : Type} [Field F] {params : WitnessParams} {live : Fin 128 → Prop} {witness : WitnessType F params}
  {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
  (charAbove2pow128 : 2 ^ 128 < ringChar F)
  (context : ConstraintContext joltInstance privateInputs params)
  (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
  {t : Fin params.traceLength} {slot : Fin (2 ^ params.logBytecodeK)}
  (selected : bytecodeRa witness slot t = 1)
  {row : JoltInstructionRow} (rowIs : bytecodeRow context.bytecode slot.val = some row)
  {lhs rhs : Src} {imm : BitVec 128}
  (instructionIs : row.instruction = .VirtualAssertMulUNoOverflow lhs rhs imm)

include context rowIs instructionIs in
private theorem mulAssertion_canonical :
    JoltRegisterEncoding.sourceIsCanonical lhs = true ∧
    JoltRegisterEncoding.sourceIsCanonical rhs = true := by
  simpa only [instructionIs, JoltRegisterEncoding.instructionIsCanonical,
    Bool.and_eq_true] using (bytecodeRow_rowOk context rowIs).canonical

include charAbove2pow128 context equations selected rowIs instructionIs

private theorem mulAssertion_passes {pre : SailJoltState}
    (agrees : RegisterAgreementOn live witness t pre)
    (leftLive : live (TraceWitness.sourceRegisterAddress lhs))
    (rightLive : live (TraceWitness.sourceRegisterAddress rhs)) :
    mulWide (sourceValue lhs pre) (sourceValue rhs pre) < 2 ^ 64 := by
  have bound := two_pow_127_lt_char charAbove2pow128
  have canonical := mulAssertion_canonical context rowIs instructionIs
  obtain ⟨left, right⟩ := agrees.registerInputs bound context equations selected rowIs
    lhs rhs canonical.1 canonical.2
    (by rw [instructionIs]; rfl) (by rw [instructionIs]; rfl)
    (by rw [instructionIs]; rfl) leftLive rightLive
  have active : witness.OpFlags .MultiplyOperands t = 1 := by
    simpa only [bytecodeCircuitFlag, rowIs, instructionIs,
      JoltMetadata.circuitFlag, JoltMetadata.opcodeFlag] using
      opFlag_of_selected_bytecode bound context equations .MultiplyOperands t slot selected
  have assertion : witness.OpFlags .Assert t = 1 := by
    simpa only [bytecodeCircuitFlag, rowIs, instructionIs,
      JoltMetadata.circuitFlag, JoltMetadata.opcodeFlag] using
      opFlag_of_selected_bytecode bound context equations .Assert t slot selected
  have raf := instructionRafFlag_one_of_arithmetic bound context equations t
    (Or.inr (Or.inr active))
  have encoded := rightLookupOperand_mul equations.rightLookupEqProductIfMul
    equations.productEqLeftInputMulRightInput t active
    (sourceValue lhs pre) (sourceValue rhs pre) left right
  have output := lookupOutput_mulUNoOverflow_of_identity charAbove2pow128
    context equations t slot selected _ raf encoded
    (by simp only [rowIs, Option.bind_some, instructionIs, JoltMetadata.lookupTable])
  have passes := predicate_of_assert equations.assertLookupOne t assertion _ output
  simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt
    (mulWide_lt_128 (sourceValue lhs pre) (sourceValue rhs pre))] using passes

/-- The multiplication guard's lookup forces its successful, state-preserving
execution, including at the final cycle.
Both source registers must be live; the live set is unchanged.
For example, a division guard retains agreement on its initialized temporaries. -/
theorem mulAssertion_step {pre : SailJoltState}
    (agrees : RegisterAgreementOn live witness t pre)
    (leftLive : live (TraceWitness.sourceRegisterAddress lhs))
    (rightLive : live (TraceWitness.sourceRegisterAddress rhs))
    (answer : BitVec 64) (advice : row.instruction.RuntimeAdvice) :
    mulWide (sourceValue lhs pre) (sourceValue rhs pre) < 2 ^ 64 ∧
    execWithTapeAnswer (row.instruction.withRuntimeAdvice advice) answer pre =
      .ok RETIRE_SUCCESS pre ∧
    ∀ next : t.val + 1 < params.traceLength,
      RegisterAgreementOn live witness ⟨t.val + 1, next⟩ pre := by
  have canonical := mulAssertion_canonical context rowIs instructionIs
  have leftRead := (agrees.read lhs canonical.1 leftLive).1
  have rightRead := (agrees.read rhs canonical.2 rightLive).1
  have passes := mulAssertion_passes charAbove2pow128 context equations
    selected rowIs instructionIs agrees leftLive rightLive
  refine ⟨passes, ?_, ?_⟩
  · rw [withRuntimeAdvice_eq_of_noAdvice _ advice (by rw [instructionIs]; rfl),
      instructionIs]
    simp only [execWithTapeAnswer, execInstr, bind, EStateM.bind,
      leftRead, rightRead, if_pos passes, pure, EStateM.pure]
  · intro next
    exact agrees.noWrite (two_pow_127_lt_char charAbove2pow128) context equations
      next slot selected rowIs (by rw [instructionIs]; rfl)

end JoltConstraints.Soundness
