import JoltConstraints.Soundness.Layer5.Registers
import JoltConstraints.Soundness.Layer5.RegisterWrite
import JoltConstraints.Soundness.Layer5.TapeSemantics
import JoltConstraints.Soundness.Layer4.Arithmetic
import JoltConstraints.Soundness.Layer4.Inputs
import JoltConstraints.Soundness.Layer4.Outputs

/-! A selected ADDI row executes with the wrapped sum required by its lookup
constraints and preserves register agreement. All operand, metadata and write
facts are derived here from the selected row and the induction invariant.
The immediate is the row's already-decoded 64-bit word. No nonwrapping
assumption is needed for this arithmetic operation. -/

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
    (agrees : RegisterAgreement witness t pre) :
    witness.LeftInstructionInput t = ((sourceValue source pre).toNat : F) ∧
    witness.RightInstructionInput t = (imm.toNat : F) := by
  have charAbove2pow127 := two_pow_127_lt_char charAbove2pow128
  have canonical := (addi_canonical context rowIs instructionIs).2
  have sourceTable : witness.Rs1Value t =
      witness.RegistersVal (TraceWitness.sourceRegisterAddress source) t := by
    simpa only [rowIs, Option.bind_some, instructionIs, bytecodeRs1Register] using
      rs1Value_of_selected_bytecode charAbove2pow127 context equations t slot selected
  have sourceValueIs := sourceTable.trans (agrees.read source canonical).2
  have immediate : witness.Imm t = (imm.toNat : F) := by
    simpa only [bytecodeImmediate, rowIs, instructionIs, JoltMetadata.immediate,
      Int.cast_natCast] using
      imm_of_selected_bytecode charAbove2pow127 context equations t slot selected
  simpa only [instructionIs, JoltMetadata.instructionFlag, Bool.false_eq_true, ↓reduceIte,
    add_zero, zero_add, sourceValueIs, immediate] using
    instructionInputs_of_selected_bytecode charAbove2pow127 context equations
      t slot selected row rowIs

private theorem addi_write_value {pre : SailJoltState}
    (agrees : RegisterAgreement witness t pre) :
    witness.RdWriteValue t = ((sourceValue source pre + imm).toNat : F) := by
  obtain ⟨addFlag, writeFlag, table⟩ :=
    addi_metadata charAbove2pow128 context equations selected rowIs instructionIs
  obtain ⟨left, right⟩ :=
    addi_inputs charAbove2pow128 context equations selected rowIs instructionIs agrees
  rw [rdWriteValue_eq_lookupOutput equations.rdWriteEqLookupIfWriteLookupToRd t writeFlag]
  exact lookupOutput_rangeCheck_add charAbove2pow128 context equations t slot
    selected table addFlag (sourceValue source pre) imm left right

/-- A selected ADDI row writes the constrained wrapped sum and executes to the
concrete destination-write state. Register agreement holds at the next cycle
whenever that column exists. Execution and the write value also cover the last
cycle. The arbitrary tape answer is ignored by ADDI. -/
theorem addi_step {pre : SailJoltState} (agrees : RegisterAgreement witness t pre)
    (answer : BitVec 64) :
    let value := sourceValue source pre + imm
    witness.RdWriteValue t = (value.toNat : F) ∧
    execWithTapeAnswer row.instruction answer pre =
      .ok RETIRE_SUCCESS (afterWriteDst destination value pre) ∧
    ∀ next : t.val + 1 < params.traceLength,
      RegisterAgreement witness ⟨t.val + 1, next⟩ (afterWriteDst destination value pre) := by
  dsimp only
  obtain ⟨destinationCanonical, sourceCanonical⟩ := addi_canonical context rowIs instructionIs
  have encoded := addi_write_value charAbove2pow128 context equations
    selected rowIs instructionIs agrees
  have read := (agrees.read source sourceCanonical).1
  have written := writeDst_afterWriteDst destination destinationCanonical
    (sourceValue source pre + imm) pre
  refine ⟨encoded, ?_, ?_⟩
  · rw [instructionIs]
    simp only [execWithTapeAnswer, execInstr, bind, EStateM.bind, read,
      addWide_low, written, pure, EStateM.pure]
  · intro next
    exact agrees.write charAbove2pow128 context equations next slot selected rowIs
      (by rw [instructionIs]; rfl) _ encoded written

end JoltConstraints.Soundness
