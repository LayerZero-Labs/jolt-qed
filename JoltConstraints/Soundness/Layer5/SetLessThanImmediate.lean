import JoltConstraints.Soundness.Layer5.Registers
import JoltConstraints.Soundness.Layer5.RegisterWrite
import JoltConstraints.Soundness.Layer5.TapeSemantics
import JoltConstraints.Soundness.Layer4.Comparison
import JoltConstraints.Soundness.Layer4.Inputs
import JoltConstraints.Soundness.Layer4.Outputs
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
  {t : Fin params.traceLength} {slot : Fin (2 ^ params.logBytecodeK)}
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

private theorem sltiu_metadata :
    witness.InstructionRafFlag t = 0 ∧
    witness.OpFlags .WriteLookupOutputToRD t = 1 ∧
    (bytecodeRow context.bytecode slot.val).bind
      (fun row => JoltMetadata.lookupTable row.instruction) = some .UnsignedLessThan := by
  have bound := two_pow_127_lt_char charAbove2pow128
  refine ⟨?_, ?_, ?_⟩
  · simpa only [bytecodeRafFlag, rowIs, instructionIs, JoltMetadata.instructionRafFlag,
      JoltMetadata.opcodeFlag, Bool.or_self] using
      instructionRafFlag_of_selected_bytecode bound context equations t slot selected
  · simpa only [bytecodeCircuitFlag, rowIs, JoltMetadata.circuitFlag, instructionIs,
      JoltMetadata.opcodeFlag] using
      opFlag_of_selected_bytecode bound context equations .WriteLookupOutputToRD t slot selected
  · simp only [rowIs, Option.bind_some, instructionIs, JoltMetadata.lookupTable]

private theorem sltiu_inputs {pre : SailJoltState}
    (agrees : RegisterAgreement witness t pre) :
    witness.LeftInstructionInput t = ((sourceValue source pre).toNat : F) ∧
    witness.RightInstructionInput t = (imm.toNat : F) := by
  have bound := two_pow_127_lt_char charAbove2pow128
  have canonical := (sltiu_canonical context rowIs instructionIs).2
  have sourceTable : witness.Rs1Value t =
      witness.RegistersVal (TraceWitness.sourceRegisterAddress source) t := by
    simpa only [rowIs, Option.bind_some, instructionIs, bytecodeRs1Register] using
      rs1Value_of_selected_bytecode bound context equations t slot selected
  have sourceValueIs := sourceTable.trans (agrees.read source canonical).2
  have immediate : witness.Imm t = (imm.toNat : F) := by
    simpa only [bytecodeImmediate, rowIs, instructionIs, JoltMetadata.immediate,
      Int.cast_natCast] using imm_of_selected_bytecode bound context equations t slot selected
  simpa only [instructionIs, JoltMetadata.instructionFlag, Bool.false_eq_true, ↓reduceIte,
    add_zero, zero_add, sourceValueIs, immediate] using
    instructionInputs_of_selected_bytecode bound context equations t slot selected row rowIs

private theorem sltiu_write_value {pre : SailJoltState}
    (agrees : RegisterAgreement witness t pre) :
    witness.RdWriteValue t = ((jolt_sltu_value (sourceValue source pre) imm).toNat : F) := by
  obtain ⟨raf, writeFlag, table⟩ :=
    sltiu_metadata charAbove2pow128 context equations selected rowIs instructionIs
  obtain ⟨left, right⟩ :=
    sltiu_inputs charAbove2pow128 context equations selected rowIs instructionIs agrees
  obtain ⟨leftLookup, rightLookup⟩ := lookupOperands_eq_inputs_of_raf_zero
    (two_pow_127_lt_char charAbove2pow128) context equations t raf
  rw [rdWriteValue_eq_lookupOutput equations.rdWriteEqLookupIfWriteLookupToRd t writeFlag]
  have output := lookupOutput_unsignedLessThan (two_pow_127_lt_char charAbove2pow128)
    context equations t slot selected (sourceValue source pre) imm raf
    (leftLookup.trans left) (rightLookup.trans right) table
  simpa only [jolt_sltu_value_toNat, BitVec.lt_def, Nat.cast_ite, Nat.cast_one,
    Nat.cast_zero] using output

/-- A selected SLTIU row writes its constrained unsigned comparison, executes,
and preserves register agreement at the next cycle. This also covers the
in-place zero test in SC; no source/destination inequality is assumed. -/
theorem sltiu_step {pre : SailJoltState} (agrees : RegisterAgreement witness t pre)
    (answer : BitVec 64) :
    let value := jolt_sltu_value (sourceValue source pre) imm
    witness.RdWriteValue t = (value.toNat : F) ∧
    execWithTapeAnswer row.instruction answer pre =
      .ok RETIRE_SUCCESS (afterWriteDst destination value pre) ∧
    ∀ next : t.val + 1 < params.traceLength,
      RegisterAgreement witness ⟨t.val + 1, next⟩ (afterWriteDst destination value pre) := by
  dsimp only
  obtain ⟨destinationCanonical, sourceCanonical⟩ := sltiu_canonical context rowIs instructionIs
  have encoded := sltiu_write_value charAbove2pow128 context equations
    selected rowIs instructionIs agrees
  have read := (agrees.read source sourceCanonical).1
  have written := writeDst_afterWriteDst destination destinationCanonical
    (jolt_sltu_value (sourceValue source pre) imm) pre
  refine ⟨encoded, ?_, ?_⟩
  · rw [instructionIs]
    simp only [execWithTapeAnswer, execInstr, bind, EStateM.bind, read,
      written, pure, EStateM.pure]
  · intro next
    exact agrees.write charAbove2pow128 context equations next slot selected rowIs
      (by rw [instructionIs]; rfl) _ encoded written

end JoltConstraints.Soundness
