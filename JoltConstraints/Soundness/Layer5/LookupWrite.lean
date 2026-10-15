import JoltConstraints.Soundness.Layer5.Registers
import JoltConstraints.Soundness.Layer5.RegisterWrite
import JoltConstraints.Soundness.Layer5.RuntimeAdvice
import JoltConstraints.Soundness.Layer5.TapeSemantics
import JoltConstraints.Soundness.Layer4.Inputs
import JoltConstraints.Soundness.Layer4.Outputs

/-! Shared steps for instructions that write a lookup result to a register.
Instruction families prove their operand selection, metadata, table meaning and
read/write equation. These local facts are discharged by each caller; none is
an additional premise of the soundness theorem. Successful writes follow from
bytecode canonicality, including x0, and execution retains the full post-state. -/

set_option autoImplicit false

namespace JoltConstraints.Soundness

open Sail PreSail LeanRV64D.Functions JoltISA

variable {F : Type} [Field F] {params : WitnessParams} {witness : WitnessType F params}
  {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
  (charAbove2pow127 : 2 ^ 127 < ringChar F)
  (context : ConstraintContext joltInstance privateInputs params)
  (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
  {t : Fin params.traceLength} {slot : Fin (2 ^ params.logBytecodeK)}
  (selected : bytecodeRa witness slot t = 1)
  {row : JoltInstructionRow} (rowIs : bytecodeRow context.bytecode slot.val = some row)

include charAbove2pow127 context equations selected rowIs

/-- A selected canonical first source has the value supplied by register agreement. -/
theorem RegisterAgreement.rs1Value {pre : SailJoltState}
    (agrees : RegisterAgreement witness t pre) (source : Src)
    (canonical : JoltRegisterEncoding.sourceIsCanonical source = true)
    (operand : bytecodeRs1Register row.instruction =
      some (TraceWitness.sourceRegisterAddress source)) :
    witness.Rs1Value t = ((sourceValue source pre).toNat : F) := by
  have table := rs1Value_of_selected_bytecode
    charAbove2pow127 context equations t slot selected
  simp only [rowIs, Option.bind_some, operand] at table
  exact table.trans (agrees.read source canonical).2

/-- A selected canonical second source has the value supplied by register agreement. -/
theorem RegisterAgreement.rs2Value {pre : SailJoltState}
    (agrees : RegisterAgreement witness t pre) (source : Src)
    (canonical : JoltRegisterEncoding.sourceIsCanonical source = true)
    (operand : bytecodeRs2Register row.instruction =
      some (TraceWitness.sourceRegisterAddress source)) :
    witness.Rs2Value t = ((sourceValue source pre).toNat : F) := by
  have table := rs2Value_of_selected_bytecode
    charAbove2pow127 context equations t slot selected
  simp only [rowIs, Option.bind_some, operand] at table
  exact table.trans (agrees.read source canonical).2

/-- For an interleaved lookup-writing row, transfer its inputs through the
lookup and into RdWriteValue. The caller supplies the proved Layer 4 table rule. -/
theorem lookupWrite_value_of_raf_zero (lhs rhs value : BitVec 64) (table : LookupTableKind)
    (rafFlag : JoltMetadata.instructionRafFlag row.instruction = false)
    (writeFlag : JoltMetadata.opcodeFlag row.instruction .WriteLookupOutputToRD = true)
    (tableIs : JoltMetadata.lookupTable row.instruction = some table)
    (left : witness.LeftInstructionInput t = (lhs.toNat : F))
    (right : witness.RightInstructionInput t = (rhs.toNat : F))
    (meaning : witness.InstructionRafFlag t = 0 →
      witness.LeftLookupOperand t = (lhs.toNat : F) →
      witness.RightLookupOperand t = (rhs.toNat : F) →
      (bytecodeRow context.bytecode slot.val).bind
        (fun row => JoltMetadata.lookupTable row.instruction) = some table →
      witness.LookupOutput t = (value.toNat : F)) :
    witness.RdWriteValue t = (value.toNat : F) := by
  have raf : witness.InstructionRafFlag t = 0 := by
    simpa only [bytecodeRafFlag, rowIs, rafFlag] using
      instructionRafFlag_of_selected_bytecode charAbove2pow127 context equations t slot selected
  have writes : witness.OpFlags .WriteLookupOutputToRD t = 1 := by
    simpa only [bytecodeCircuitFlag, rowIs, JoltMetadata.circuitFlag, writeFlag] using
      opFlag_of_selected_bytecode charAbove2pow127 context equations
        .WriteLookupOutputToRD t slot selected
  have selectedTable : (bytecodeRow context.bytecode slot.val).bind
      (fun row => JoltMetadata.lookupTable row.instruction) = some table := by
    simp only [rowIs, Option.bind_some, tableIs]
  obtain ⟨leftLookup, rightLookup⟩ :=
    lookupOperands_eq_inputs_of_raf_zero charAbove2pow127 context equations t raf
  rw [rdWriteValue_eq_lookupOutput equations.rdWriteEqLookupIfWriteLookupToRd t writes]
  exact meaning raf (leftLookup.trans left) (rightLookup.trans right) selectedTable

omit charAbove2pow127 in
/-- Finish a register-writing step from its constrained value and read/write
equation. Canonicality proves that the write succeeds; no successful execution
is assumed. Runtime advice is applied exactly as in UntrustedAnswerRun.executes.
The write and execution conclusions also cover the last cycle. -/
theorem registerWrite_step (charAbove2pow128 : 2 ^ 128 < ringChar F)
    {pre : SailJoltState} (agrees : RegisterAgreement witness t pre)
    (destination : Dst) (destinationIs : row.instruction.destination? = some destination)
    (value : BitVec 64) (encoded : witness.RdWriteValue t = (value.toNat : F))
    (answer : BitVec 64) (advice : row.instruction.RuntimeAdvice)
    (absent : row.instruction.adviceValue? = none)
    (rule : execWithTapeAnswer row.instruction answer pre =
      (do writeDst destination value; pure RETIRE_SUCCESS) pre) :
    witness.RdWriteValue t = (value.toNat : F) ∧
    execWithTapeAnswer (row.instruction.withRuntimeAdvice advice) answer pre =
      .ok RETIRE_SUCCESS (afterWriteDst destination value pre) ∧
    ∀ next : t.val + 1 < params.traceLength,
      RegisterAgreement witness ⟨t.val + 1, next⟩ (afterWriteDst destination value pre) := by
  have canonical := instruction_destination_canonical _ _
    (bytecodeRow_rowOk context rowIs).canonical destinationIs
  have written := writeDst_afterWriteDst destination canonical value pre
  refine ⟨encoded, ?_, ?_⟩
  · rw [withRuntimeAdvice_eq_of_noAdvice _ advice absent, rule]
    simp only [bind, EStateM.bind, written, pure, EStateM.pure]
  · intro next
    exact agrees.write charAbove2pow128 context equations next slot selected rowIs
      destinationIs value encoded written

end JoltConstraints.Soundness
