import JoltConstraints.Soundness.Layer5.AssertLessThanEqual
import JoltConstraints.Soundness.Layer4.Assertions
import JoltConstraints.Soundness.Layer4.Arithmetic

/-! Halfword and word alignment assertions. Their AddOperands lookup uses the
full 128-bit base-plus-immediate; the low machine word has the same low bits.
At public pin 8bbb2357:
See : jolt/tracer/src/instruction/virtual_assert_halfword_alignment.rs:17-29
See : jolt/tracer/src/instruction/virtual_assert_word_alignment.rs:17-29 -/

set_option autoImplicit false

namespace JoltConstraints.Soundness

open Sail PreSail LeanRV64D.Functions JoltISA

/-- The two alignment assertion widths. -/
inductive AlignmentAssertion where
  | halfword | word

/-- Build the alignment assertion row. -/
def AlignmentAssertion.instruction (kind : AlignmentAssertion)
    (base : Src) (imm : BitVec 64) (fault : ExceptionType) : Instr :=
  match kind with
  | .halfword => .VirtualAssertHalfwordAlignment base imm fault
  | .word => .VirtualAssertWordAlignment base imm fault

/-- The byte multiple required by the selected lookup. -/
def AlignmentAssertion.modulus : AlignmentAssertion → Nat
  | .halfword => 2
  | .word => 4

private theorem low_word_aligned (value : Nat) (bits : Nat)
    (bitsIs : bits = 1 ∨ bits = 2)
    (aligned : (BitVec.ofNat 128 value).toNat % 2 ^ bits = 0) :
    (BitVec.ofNat 64 value) &&& (BitVec.ofNat 64 (2 ^ bits - 1)) = 0 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
  have divisor : 2 ^ bits ∣ 2 ^ 64 := by rcases bitsIs with rfl | rfl <;> decide
  have wideDivisor : 2 ^ bits ∣ 2 ^ 128 := by rcases bitsIs with rfl | rfl <;> decide
  rw [Nat.mod_eq_of_lt (by rcases bitsIs with rfl | rfl <;> decide :
    2 ^ bits - 1 < 2 ^ 64)]
  rw [Nat.and_two_pow_sub_one_eq_mod]
  simpa only [BitVec.toNat_ofNat, Nat.mod_mod_of_dvd _ divisor,
    Nat.mod_mod_of_dvd _ wideDivisor] using aligned

variable {F : Type} [Field F] {params : WitnessParams} {witness : WitnessType F params}
  {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
  (charAbove2pow128 : 2 ^ 128 < ringChar F)
  (context : ConstraintContext joltInstance privateInputs params)
  (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
  {live : Fin 128 → Prop} {t : Fin params.traceLength} {slot : Fin (2 ^ params.logBytecodeK)}
  (selected : bytecodeRa witness slot t = 1)
  {row : JoltInstructionRow} (rowIs : bytecodeRow context.bytecode slot.val = some row)
  (kind : AlignmentAssertion) {base : Src} {imm : BitVec 64} {fault : ExceptionType}
  (instructionIs : row.instruction = kind.instruction base imm fault)

include context rowIs instructionIs in
private theorem alignmentAssertion_canonical :
    JoltRegisterEncoding.sourceIsCanonical base = true := by
  cases kind <;>
    simpa only [instructionIs, AlignmentAssertion.instruction,
      JoltRegisterEncoding.instructionIsCanonical, Bool.and_eq_true] using
      (bytecodeRow_rowOk context rowIs).canonical

include charAbove2pow128 context equations selected rowIs instructionIs

private theorem alignmentAssertion_passes {pre : SailJoltState}
    (agrees : RegisterAgreementOn live witness t pre)
    (sourceLive : live (TraceWitness.sourceRegisterAddress base)) :
    (BitVec.ofNat 128 (addWide (sourceValue base pre) imm)).toNat % kind.modulus = 0 := by
  have bound := two_pow_127_lt_char charAbove2pow128
  obtain ⟨left, right⟩ := agrees.immediateInputs bound context equations selected rowIs
    base imm (alignmentAssertion_canonical context rowIs kind instructionIs)
    (by cases kind <;> rw [instructionIs] <;> rfl)
    (by cases kind <;> rw [instructionIs] <;> rfl)
    (by cases kind <;> rw [instructionIs] <;> rfl) sourceLive
  have active : witness.OpFlags .AddOperands t = 1 := by
    have flag := opFlag_of_selected_bytecode bound context equations .AddOperands t slot selected
    cases kind <;>
      simpa only [bytecodeCircuitFlag, rowIs, instructionIs,
        AlignmentAssertion.instruction, JoltMetadata.circuitFlag,
        JoltMetadata.opcodeFlag] using flag
  have assertion : witness.OpFlags .Assert t = 1 := by
    have flag := opFlag_of_selected_bytecode bound context equations .Assert t slot selected
    cases kind <;>
      simpa only [bytecodeCircuitFlag, rowIs, instructionIs,
        AlignmentAssertion.instruction, JoltMetadata.circuitFlag,
        JoltMetadata.opcodeFlag] using flag
  have raf := instructionRafFlag_one_of_arithmetic bound context equations t (Or.inl active)
  have encoded := rightLookupOperand_add equations.rightLookupAdd t active
    (sourceValue base pre) imm left right
  cases kind with
  | halfword =>
    have output := lookupOutput_halfwordAlignment_of_identity charAbove2pow128
      context equations t slot selected _ raf encoded
      (by simp only [rowIs, Option.bind_some, instructionIs,
        AlignmentAssertion.instruction, JoltMetadata.lookupTable])
    exact predicate_of_assert equations.assertLookupOne t assertion _ output
  | word =>
    have output := lookupOutput_wordAlignment_of_identity charAbove2pow128
      context equations t slot selected _ raf encoded
      (by simp only [rowIs, Option.bind_some, instructionIs,
        AlignmentAssertion.instruction, JoltMetadata.lookupTable])
    exact predicate_of_assert equations.assertLookupOne t assertion _ output

/-- The selected alignment lookup forces successful, state-preserving execution.
The base register is live, and this assertion preserves the live set.
For example, a halfword alignment check reads a live base and writes no register. -/
theorem alignmentAssertion_step {pre : SailJoltState}
    (agrees : RegisterAgreementOn live witness t pre)
    (sourceLive : live (TraceWitness.sourceRegisterAddress base))
    (answer : BitVec 64) (advice : row.instruction.RuntimeAdvice) :
    (BitVec.ofNat 128 (addWide (sourceValue base pre) imm)).toNat % kind.modulus = 0 ∧
    execWithTapeAnswer (row.instruction.withRuntimeAdvice advice) answer pre =
      .ok RETIRE_SUCCESS pre ∧
    ∀ next : t.val + 1 < params.traceLength,
      RegisterAgreementOn live witness ⟨t.val + 1, next⟩ pre := by
  have canonical := alignmentAssertion_canonical context rowIs kind instructionIs
  have read := (agrees.read base canonical sourceLive).1
  have passes := alignmentAssertion_passes charAbove2pow128 context equations
    selected rowIs kind instructionIs agrees sourceLive
  refine ⟨passes, ?_, ?_⟩
  · rw [withRuntimeAdvice_eq_of_noAdvice _ advice
      (by cases kind <;> rw [instructionIs] <;> rfl), instructionIs]
    cases kind with
    | halfword =>
      have aligned := low_word_aligned (addWide (sourceValue base pre) imm) 1
        (Or.inl rfl) passes
      have aligned1 : BitVec.ofNat 64 (addWide (sourceValue base pre) imm) &&&
          (1 : BitVec 64) = 0 := by simpa only using aligned
      simp only [AlignmentAssertion.instruction, execWithTapeAnswer, execInstr,
        bind, EStateM.bind, read, if_pos aligned1, pure, EStateM.pure]
    | word =>
      have aligned := low_word_aligned (addWide (sourceValue base pre) imm) 2
        (Or.inr rfl) passes
      have aligned3 : BitVec.ofNat 64 (addWide (sourceValue base pre) imm) &&&
          (3 : BitVec 64) = 0 := by simpa only using aligned
      simp only [AlignmentAssertion.instruction, execWithTapeAnswer, execInstr,
        bind, EStateM.bind, read, if_pos aligned3, pure, EStateM.pure]
  · intro next
    exact agrees.noWrite (two_pow_127_lt_char charAbove2pow128) context equations
      next slot selected rowIs (by cases kind <;> rw [instructionIs] <;> rfl)

end JoltConstraints.Soundness
