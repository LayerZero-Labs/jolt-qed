import JoltConstraints.Soundness.Layer5.LookupWrite
import JoltConstraints.Soundness.Layer4.Comparison
import JoltBytecode.InstructionEquivalence.ProofSupport.ValueLemmas

/-! Execute a selected SLTIU row from the unsigned comparison lookup.
The immediate is the row's decoded 64-bit word. In particular, immediate one
tests for zero after the XOR in SC's expansion. -/

set_option autoImplicit false

namespace JoltConstraints.Soundness

open Sail PreSail LeanRV64D.Functions JoltISA

variable {F : Type} [Field F] {params : WitnessParams} {witness : WitnessType F params}
  {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
  (charAbove2pow128 : 2 ^ 128 < ringChar F)
  (context : ConstraintContext joltInstance privateInputs params)
  (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
  {live : Fin 128 → Prop} {t : Fin params.traceLength} {slot : Fin (2 ^ params.logBytecodeK)}
  (selected : bytecodeRa witness slot t = 1)
  {row : JoltInstructionRow} (rowIs : bytecodeRow context.bytecode slot.val = some row)
  {destination : Dst} {source : Src} {imm : BitVec 64}
  (instructionIs : row.instruction = .SLTIU destination source imm)

include context rowIs instructionIs in
private theorem sltiu_canonical :
    JoltRegisterEncoding.destinationIsCanonical destination = true ∧
    JoltRegisterEncoding.sourceIsCanonical source = true := by
  simpa only [instructionIs, JoltRegisterEncoding.instructionIsCanonical,
    Bool.and_eq_true] using (bytecodeRow_rowOk context rowIs).canonical

include charAbove2pow128 context equations selected rowIs instructionIs

private theorem sltiu_inputs {pre : SailJoltState}
    (agrees : RegisterAgreementOn live witness t pre)
    (sourceLive : live (TraceWitness.sourceRegisterAddress source)) :
    witness.LeftInstructionInput t = ((sourceValue source pre).toNat : F) ∧
    witness.RightInstructionInput t = (imm.toNat : F) := by
  exact agrees.immediateInputs (two_pow_127_lt_char charAbove2pow128)
    context equations selected rowIs source imm
    (sltiu_canonical context rowIs instructionIs).2
    (by rw [instructionIs]; rfl) (by rw [instructionIs]; rfl)
    (by rw [instructionIs]; rfl) sourceLive

private theorem sltiu_write_value {pre : SailJoltState}
    (agrees : RegisterAgreementOn live witness t pre)
    (sourceLive : live (TraceWitness.sourceRegisterAddress source)) :
    witness.RdWriteValue t = ((jolt_sltu_value (sourceValue source pre) imm).toNat : F) := by
  obtain ⟨left, right⟩ :=
    sltiu_inputs charAbove2pow128 context equations selected rowIs instructionIs agrees sourceLive
  apply lookupWrite_value_of_raf_zero (two_pow_127_lt_char charAbove2pow128)
    context equations selected rowIs (sourceValue source pre) imm _ .UnsignedLessThan
    (by rw [instructionIs]; rfl) (by rw [instructionIs]; rfl)
    (by rw [instructionIs]; rfl) left right
  intro raf leftLookup rightLookup table
  have output := lookupOutput_unsignedLessThan (two_pow_127_lt_char charAbove2pow128)
    context equations t slot selected (sourceValue source pre) imm raf
    leftLookup rightLookup table
  simpa only [jolt_sltu_value_toNat, BitVec.lt_def, Nat.cast_ite, Nat.cast_one,
    Nat.cast_zero] using output

/-- A selected SLTIU row writes its constrained unsigned comparison, executes,
and preserves register agreement at the next cycle. This also covers the
in-place zero test in SC; no source/destination inequality is assumed.
Runtime advice is applied exactly as in the trace definition.
The source is live; the destination joins the live set after the row.
For example, SLTIU can test a live source and write the comparison to a temporary. -/
theorem sltiu_step {pre : SailJoltState} (agrees : RegisterAgreementOn live witness t pre)
    (sourceLive : live (TraceWitness.sourceRegisterAddress source))
    (answer : BitVec 64) (advice : row.instruction.RuntimeAdvice) :
    let value := jolt_sltu_value (sourceValue source pre) imm
    witness.RdWriteValue t = (value.toNat : F) ∧
    execWithTapeAnswer (row.instruction.withRuntimeAdvice advice) answer pre =
      .ok RETIRE_SUCCESS (afterWriteDst destination value pre) ∧
    ∀ next : t.val + 1 < params.traceLength,
      RegisterAgreementOn
        (fun register => live register ∨ register = TraceWitness.destinationRegisterAddress destination)
        witness ⟨t.val + 1, next⟩ (afterWriteDst destination value pre) := by
  dsimp only
  have sourceCanonical := (sltiu_canonical context rowIs instructionIs).2
  have encoded := sltiu_write_value charAbove2pow128 context equations
    selected rowIs instructionIs agrees sourceLive
  have read := (agrees.read source sourceCanonical sourceLive).1
  apply registerWriteOn_step context equations selected rowIs charAbove2pow128 agrees
    destination (by rw [instructionIs]; rfl) _ encoded answer advice
  rw [withRuntimeAdvice_eq_of_noAdvice _ advice
    (by rw [instructionIs]; rfl)]
  rw [instructionIs]
  simp only [execWithTapeAnswer, execInstr, bind, EStateM.bind, read]

end JoltConstraints.Soundness
