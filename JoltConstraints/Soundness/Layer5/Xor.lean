import JoltConstraints.Soundness.Layer5.Registers
import JoltConstraints.Soundness.Layer5.RegisterWrite
import JoltConstraints.Soundness.Layer5.TapeSemantics
import JoltConstraints.Soundness.Layer4.Bitwise
import JoltConstraints.Soundness.Layer4.Inputs
import JoltConstraints.Soundness.Layer4.Outputs

/-! Execute a selected XOR row using its constrained register operands and
lookup output. This includes the virtual-register comparison in SC's expansion;
no interpretation of those registers as a reservation is needed. -/

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
  {destination : Dst} {lhs rhs : Src}
  (instructionIs : row.instruction = .XOR destination lhs rhs)

include context rowIs instructionIs in
private theorem xor_canonical :
    (JoltRegisterEncoding.destinationIsCanonical destination = true ∧
      JoltRegisterEncoding.sourceIsCanonical lhs = true) ∧
    JoltRegisterEncoding.sourceIsCanonical rhs = true := by
  simpa only [instructionIs, JoltRegisterEncoding.instructionIsCanonical,
    Bool.and_eq_true] using (bytecodeRow_rowOk context rowIs).canonical

include charAbove2pow128 context equations selected rowIs instructionIs

private theorem xor_metadata :
    witness.InstructionRafFlag t = 0 ∧
    witness.OpFlags .WriteLookupOutputToRD t = 1 ∧
    (bytecodeRow context.bytecode slot.val).bind
      (fun row => JoltMetadata.lookupTable row.instruction) = some .Xor := by
  have bound := two_pow_127_lt_char charAbove2pow128
  refine ⟨?_, ?_, ?_⟩
  · simpa only [bytecodeRafFlag, rowIs, instructionIs, JoltMetadata.instructionRafFlag,
      JoltMetadata.opcodeFlag, Bool.or_self] using
      instructionRafFlag_of_selected_bytecode bound context equations t slot selected
  · simpa only [bytecodeCircuitFlag, rowIs, JoltMetadata.circuitFlag, instructionIs,
      JoltMetadata.opcodeFlag] using
      opFlag_of_selected_bytecode bound context equations .WriteLookupOutputToRD t slot selected
  · simp only [rowIs, Option.bind_some, instructionIs, JoltMetadata.lookupTable]

private theorem xor_inputs {pre : SailJoltState}
    (agrees : RegisterAgreement witness t pre) :
    witness.LeftInstructionInput t = ((sourceValue lhs pre).toNat : F) ∧
    witness.RightInstructionInput t = ((sourceValue rhs pre).toNat : F) := by
  have bound := two_pow_127_lt_char charAbove2pow128
  have canonical := xor_canonical context rowIs instructionIs
  have leftSource : witness.Rs1Value t = ((sourceValue lhs pre).toNat : F) := by
    have sourceTable := rs1Value_of_selected_bytecode bound context equations t slot selected
    simp only [rowIs, Option.bind_some, instructionIs, bytecodeRs1Register] at sourceTable
    exact sourceTable.trans (agrees.read lhs canonical.1.2).2
  have rightSource : witness.Rs2Value t = ((sourceValue rhs pre).toNat : F) := by
    have sourceTable := rs2Value_of_selected_bytecode bound context equations t slot selected
    simp only [rowIs, Option.bind_some, instructionIs, bytecodeRs2Register] at sourceTable
    exact sourceTable.trans (agrees.read rhs canonical.2).2
  simpa only [instructionIs, JoltMetadata.instructionFlag, Bool.false_eq_true, ↓reduceIte,
    add_zero, zero_add, leftSource, rightSource] using
    instructionInputs_of_selected_bytecode bound context equations t slot selected row rowIs

private theorem xor_write_value {pre : SailJoltState}
    (agrees : RegisterAgreement witness t pre) :
    witness.RdWriteValue t = (((sourceValue lhs pre ^^^ sourceValue rhs pre).toNat : F)) := by
  obtain ⟨raf, writeFlag, table⟩ :=
    xor_metadata charAbove2pow128 context equations selected rowIs instructionIs
  obtain ⟨left, right⟩ :=
    xor_inputs charAbove2pow128 context equations selected rowIs instructionIs agrees
  obtain ⟨leftLookup, rightLookup⟩ := lookupOperands_eq_inputs_of_raf_zero
    (two_pow_127_lt_char charAbove2pow128) context equations t raf
  rw [rdWriteValue_eq_lookupOutput equations.rdWriteEqLookupIfWriteLookupToRd t writeFlag]
  exact lookupOutput_xor (two_pow_127_lt_char charAbove2pow128) context equations t slot
    selected (sourceValue lhs pre) (sourceValue rhs pre) raf
    (leftLookup.trans left) (rightLookup.trans right) table

/-- A selected XOR row executes with its constrained result and preserves
register agreement at the next cycle. Both operands are read before the write,
so source/destination aliases and virtual registers need no extra premises.
Execution and the result also cover the last cycle, which has no next column. -/
theorem xor_step {pre : SailJoltState} (agrees : RegisterAgreement witness t pre)
    (answer : BitVec 64) :
    let value := sourceValue lhs pre ^^^ sourceValue rhs pre
    witness.RdWriteValue t = (value.toNat : F) ∧
    execWithTapeAnswer row.instruction answer pre =
      .ok RETIRE_SUCCESS (afterWriteDst destination value pre) ∧
    ∀ next : t.val + 1 < params.traceLength,
      RegisterAgreement witness ⟨t.val + 1, next⟩ (afterWriteDst destination value pre) := by
  dsimp only
  obtain ⟨⟨destinationCanonical, leftCanonical⟩, rightCanonical⟩ :=
    xor_canonical context rowIs instructionIs
  have encoded := xor_write_value charAbove2pow128 context equations
    selected rowIs instructionIs agrees
  have leftRead := (agrees.read lhs leftCanonical).1
  have rightRead := (agrees.read rhs rightCanonical).1
  have written := writeDst_afterWriteDst destination destinationCanonical
    (sourceValue lhs pre ^^^ sourceValue rhs pre) pre
  refine ⟨encoded, ?_, ?_⟩
  · rw [instructionIs]
    simp only [execWithTapeAnswer, execInstr, bind, EStateM.bind, leftRead, rightRead,
      jolt_xor_value, written, pure, EStateM.pure]
  · intro next
    exact agrees.write charAbove2pow128 context equations next slot selected rowIs
      (by rw [instructionIs]; rfl) _ encoded written

end JoltConstraints.Soundness
