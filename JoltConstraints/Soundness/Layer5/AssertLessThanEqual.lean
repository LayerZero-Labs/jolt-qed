import JoltConstraints.Soundness.Layer5.LookupWrite
import JoltConstraints.Soundness.Layer4.Comparison

/-! Execute the unsigned assertion used by DIV, DIVU, DIVW, DIVUW, REM, REMU,
REMW, REMUW, LR.W, LR.D, SC.W and SC.D expansions.
Acceptance is derived from the selected comparison table and Assert constraint;
it is not an execution premise. The entire state is preserved.
At public pin 8bbb2357:
See : jolt/tracer/src/instruction/virtual_assert_lte.rs:17-23
See : jolt/crates/jolt-riscv/src/instructions/assert/assert_lte.rs:3-8
See : jolt/crates/jolt-lookup-tables/src/instructions/virt/assert_lte.rs:6-21 -/

set_option autoImplicit false

namespace JoltConstraints.Soundness

open Sail PreSail LeanRV64D.Functions JoltISA

variable {F : Type} [Field F] {params : WitnessParams} {witness : WitnessType F params}
  {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
  (charAbove2pow128 : 2 ^ 128 < ringChar F)
  (context : ConstraintContext joltInstance privateInputs params)
  (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
  {t : Fin params.traceLength} {slot : Fin (2 ^ params.logBytecodeK)}
  (selected : bytecodeRa witness slot t = 1)
  {row : JoltInstructionRow} (rowIs : bytecodeRow context.bytecode slot.val = some row)
  {lhs rhs : Src} {imm : BitVec 128}
  (instructionIs : row.instruction = .VirtualAssertLTE lhs rhs imm)

include context rowIs instructionIs in
private theorem assertLTE_canonical :
    JoltRegisterEncoding.sourceIsCanonical lhs = true ∧
    JoltRegisterEncoding.sourceIsCanonical rhs = true := by
  simpa only [instructionIs, JoltRegisterEncoding.instructionIsCanonical,
    Bool.and_eq_true] using (bytecodeRow_rowOk context rowIs).canonical

include charAbove2pow128 context equations selected rowIs instructionIs

private theorem assertLTE_passes {pre : SailJoltState}
    (agrees : RegisterAgreement witness t pre) :
    (sourceValue lhs pre).toNat ≤ (sourceValue rhs pre).toNat := by
  have bound := two_pow_127_lt_char charAbove2pow128
  have canonical := assertLTE_canonical context rowIs instructionIs
  obtain ⟨left, right⟩ := agrees.registerInputs bound context equations selected rowIs
    lhs rhs canonical.1 canonical.2
    (by rw [instructionIs]; rfl) (by rw [instructionIs]; rfl)
    (by rw [instructionIs]; rfl)
  have raf : witness.InstructionRafFlag t = 0 := by
    simpa only [bytecodeRafFlag, rowIs, instructionIs, JoltMetadata.instructionRafFlag,
      JoltMetadata.opcodeFlag, Bool.or_self] using
      instructionRafFlag_of_selected_bytecode bound context equations t slot selected
  have active : witness.OpFlags .Assert t = 1 := by
    simpa only [bytecodeCircuitFlag, rowIs, instructionIs, JoltMetadata.circuitFlag,
      JoltMetadata.opcodeFlag] using
      opFlag_of_selected_bytecode bound context equations .Assert t slot selected
  obtain ⟨leftLookup, rightLookup⟩ :=
    lookupOperands_eq_inputs_of_raf_zero bound context equations t raf
  have output := lookupOutput_unsignedLessThanEqual bound context equations t slot selected
    (sourceValue lhs pre) (sourceValue rhs pre) raf (leftLookup.trans left) (rightLookup.trans right)
    (by simp only [rowIs, Option.bind_some, instructionIs, JoltMetadata.lookupTable])
  exact predicate_of_assert equations.assertLookupOne t active _ output

/-- The lookup and assertion constraints force the unsigned comparison to pass.
The row executes without changing any state, and preserves register agreement.
The comparison and execution also hold at the last cycle. -/
theorem assertLTE_step {pre : SailJoltState} (agrees : RegisterAgreement witness t pre)
    (answer : BitVec 64) (advice : row.instruction.RuntimeAdvice) :
    (sourceValue lhs pre).toNat ≤ (sourceValue rhs pre).toNat ∧
    execWithTapeAnswer (row.instruction.withRuntimeAdvice advice) answer pre =
      .ok RETIRE_SUCCESS pre ∧
    ∀ next : t.val + 1 < params.traceLength,
      RegisterAgreement witness ⟨t.val + 1, next⟩ pre := by
  have canonical := assertLTE_canonical context rowIs instructionIs
  have leftRead := (agrees.read lhs canonical.1).1
  have rightRead := (agrees.read rhs canonical.2).1
  have passes := assertLTE_passes charAbove2pow128 context equations selected rowIs instructionIs agrees
  refine ⟨passes, ?_, ?_⟩
  · rw [withRuntimeAdvice_eq_of_noAdvice _ advice (by rw [instructionIs]; rfl), instructionIs]
    simp only [execWithTapeAnswer, execInstr, bind, EStateM.bind, leftRead, rightRead,
      passes, ↓reduceIte, pure, EStateM.pure]
  · intro next
    exact agrees.noWrite (two_pow_127_lt_char charAbove2pow128) context equations next slot selected
      rowIs (by rw [instructionIs]; rfl)

end JoltConstraints.Soundness
