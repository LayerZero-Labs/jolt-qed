import JoltConstraints.Soundness.Layer5.LookupWrite
import JoltConstraints.Soundness.Layer4.Arithmetic

/-! A selected ADDI row executes with the wrapped sum required by its lookup
constraints and preserves register agreement. All operand, metadata and write
facts are derived here from the selected row and the induction invariant.
The immediate is the row's already-decoded 64-bit word. No nonwrapping
assumption is needed for this arithmetic operation. -/

set_option autoImplicit false

namespace JoltConstraints.Soundness

open Sail PreSail LeanRV64D.Functions JoltISA

variable {F : Type} [Field F] {params : WitnessParams} {live : Fin 128 → Prop} {witness : WitnessType F params}
  {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
  (charAbove2pow128 : 2 ^ 128 < ringChar F)
  (context : ConstraintContext joltInstance privateInputs params)
  (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
  {t : Fin params.traceLength} {slot : Fin (2 ^ params.logBytecodeK)}
  (selected : bytecodeRa witness slot t = 1)
  {row : JoltInstructionRow} (rowIs : bytecodeRow context.bytecode slot.val = some row)
  {destination : Dst} {source : Src} {imm : BitVec 64}
  (instructionIs : row.instruction = .ADDI destination source imm)

include context rowIs instructionIs in
private theorem addi_canonical :
    JoltRegisterEncoding.destinationIsCanonical destination = true ∧
    JoltRegisterEncoding.sourceIsCanonical source = true := by
  simpa only [instructionIs, JoltRegisterEncoding.instructionIsCanonical,
    Bool.and_eq_true] using (bytecodeRow_rowOk context rowIs).canonical

include charAbove2pow128 context equations selected rowIs instructionIs

private theorem addi_metadata :
    witness.OpFlags .AddOperands t = 1 ∧
    witness.OpFlags .WriteLookupOutputToRD t = 1 ∧
    (bytecodeRow context.bytecode slot.val).bind
      (fun row => JoltMetadata.lookupTable row.instruction) = some .RangeCheck := by
  have flags := opFlag_of_selected_bytecode (two_pow_127_lt_char charAbove2pow128)
    context equations
  refine ⟨?_, ?_, ?_⟩
  · simpa only [bytecodeCircuitFlag, rowIs, JoltMetadata.circuitFlag, instructionIs,
      JoltMetadata.opcodeFlag] using flags .AddOperands t slot selected
  · simpa only [bytecodeCircuitFlag, rowIs, JoltMetadata.circuitFlag, instructionIs,
      JoltMetadata.opcodeFlag] using flags .WriteLookupOutputToRD t slot selected
  · simp only [rowIs, Option.bind_some, instructionIs, JoltMetadata.lookupTable]

private theorem addi_inputs {pre : SailJoltState}
    (agrees : RegisterAgreementOn live witness t pre)
    (sourceLive : live (TraceWitness.sourceRegisterAddress source)) :
    witness.LeftInstructionInput t = ((sourceValue source pre).toNat : F) ∧
    witness.RightInstructionInput t = (imm.toNat : F) := by
  exact agrees.immediateInputs (two_pow_127_lt_char charAbove2pow128)
    context equations selected rowIs source imm
    (addi_canonical context rowIs instructionIs).2
    (by rw [instructionIs]; rfl) (by rw [instructionIs]; rfl)
    (by rw [instructionIs]; rfl) sourceLive

private theorem addi_write_value {pre : SailJoltState}
    (agrees : RegisterAgreementOn live witness t pre)
    (sourceLive : live (TraceWitness.sourceRegisterAddress source)) :
    witness.RdWriteValue t = ((sourceValue source pre + imm).toNat : F) := by
  obtain ⟨addFlag, writeFlag, table⟩ :=
    addi_metadata charAbove2pow128 context equations selected rowIs instructionIs
  obtain ⟨left, right⟩ :=
    addi_inputs charAbove2pow128 context equations selected rowIs instructionIs agrees sourceLive
  rw [rdWriteValue_eq_lookupOutput equations.rdWriteEqLookupIfWriteLookupToRd t writeFlag]
  exact lookupOutput_rangeCheck_add charAbove2pow128 context equations t slot
    selected table addFlag (sourceValue source pre) imm left right

/-- A selected ADDI row writes the constrained wrapped sum and executes to the
concrete destination-write state. Register agreement holds at the next cycle
whenever that column exists. Execution and the write value also cover the last
cycle. Runtime advice is applied exactly as in the trace definition; both
internal advice and the arbitrary tape answer are ignored by ADDI.
The source register must be live, and the destination is added to the live set.
For example, a division row can initialize a dead temporary from live operands. -/
theorem addi_step {pre : SailJoltState} (agrees : RegisterAgreementOn live witness t pre)
    (sourceLive : live (TraceWitness.sourceRegisterAddress source))
    (answer : BitVec 64) (advice : row.instruction.RuntimeAdvice) :
    let value := sourceValue source pre + imm
    witness.RdWriteValue t = (value.toNat : F) ∧
    execWithTapeAnswer (row.instruction.withRuntimeAdvice advice) answer pre =
      .ok RETIRE_SUCCESS (afterWriteDst destination value pre) ∧
    ∀ next : t.val + 1 < params.traceLength,
      RegisterAgreementOn
        (fun register => live register ∨ register = TraceWitness.destinationRegisterAddress destination)
        witness ⟨t.val + 1, next⟩ (afterWriteDst destination value pre) := by
  dsimp only
  have sourceCanonical := (addi_canonical context rowIs instructionIs).2
  have encoded := addi_write_value charAbove2pow128 context equations
    selected rowIs instructionIs agrees sourceLive
  have read := (agrees.read source sourceCanonical sourceLive).1
  apply registerWriteOn_step context equations selected rowIs charAbove2pow128 agrees
    destination (by rw [instructionIs]; rfl) _ encoded answer advice
  rw [withRuntimeAdvice_eq_of_noAdvice _ advice (by rw [instructionIs]; rfl)]
  rw [instructionIs]
  simp only [execWithTapeAnswer, execInstr, bind, EStateM.bind, read, addWide_low]

end JoltConstraints.Soundness
