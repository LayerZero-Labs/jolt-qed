import JoltConstraints.Soundness.Layer5.Registers
import JoltConstraints.Soundness.Layer4.Inputs

/-! Recover register and immediate inputs from the selected row and register
agreement. Instruction families discharge the syntactic operand, canonicality
and selection facts; the same proofs serve arithmetic, bitwise and assertion rows. -/

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

/-- A selected canonical first source has the value supplied by register agreement.
For example, a live architectural register or initialized division temporary
supplies its operand without agreement on any other temporary. -/
theorem RegisterAgreementOn.rs1Value {live : Fin 128 → Prop} {pre : SailJoltState}
    (agrees : RegisterAgreementOn live witness t pre) (source : Src)
    (canonical : JoltRegisterEncoding.sourceIsCanonical source = true)
    (operand : bytecodeRs1Register row.instruction =
      some (TraceWitness.sourceRegisterAddress source))
    (sourceLive : live (TraceWitness.sourceRegisterAddress source)) :
    witness.Rs1Value t = ((sourceValue source pre).toNat : F) := by
  have table := rs1Value_of_selected_bytecode
    charAbove2pow127 context equations t slot selected
  simp only [rowIs, Option.bind_some, operand] at table
  exact table.trans (agrees.read source canonical sourceLive).2

/-- A selected canonical first source has the value supplied by register agreement.
For example, an LD reads its base register from the witness table. -/
theorem RegisterAgreement.rs1Value {pre : SailJoltState}
    (agrees : RegisterAgreement witness t pre) (source : Src)
    (canonical : JoltRegisterEncoding.sourceIsCanonical source = true)
    (operand : bytecodeRs1Register row.instruction =
      some (TraceWitness.sourceRegisterAddress source)) :
    witness.Rs1Value t = ((sourceValue source pre).toNat : F) := by
  exact (agrees.toOn (fun _ => True)).rs1Value charAbove2pow127 context equations
    selected rowIs source canonical operand True.intro

/-- A selected canonical second source has the value supplied by register agreement.
For example, a live architectural register or initialized division temporary
supplies its operand without agreement on any other temporary. -/
theorem RegisterAgreementOn.rs2Value {live : Fin 128 → Prop} {pre : SailJoltState}
    (agrees : RegisterAgreementOn live witness t pre) (source : Src)
    (canonical : JoltRegisterEncoding.sourceIsCanonical source = true)
    (operand : bytecodeRs2Register row.instruction =
      some (TraceWitness.sourceRegisterAddress source))
    (sourceLive : live (TraceWitness.sourceRegisterAddress source)) :
    witness.Rs2Value t = ((sourceValue source pre).toNat : F) := by
  have table := rs2Value_of_selected_bytecode
    charAbove2pow127 context equations t slot selected
  simp only [rowIs, Option.bind_some, operand] at table
  exact table.trans (agrees.read source canonical sourceLive).2

/-- A selected canonical second source has the value supplied by register agreement.
For example, an SD reads its stored value from the witness table. -/
theorem RegisterAgreement.rs2Value {pre : SailJoltState}
    (agrees : RegisterAgreement witness t pre) (source : Src)
    (canonical : JoltRegisterEncoding.sourceIsCanonical source = true)
    (operand : bytecodeRs2Register row.instruction =
      some (TraceWitness.sourceRegisterAddress source)) :
    witness.Rs2Value t = ((sourceValue source pre).toNat : F) := by
  exact (agrees.toOn (fun _ => True)).rs2Value charAbove2pow127 context equations
    selected rowIs source canonical operand True.intro

/-- Two selected register operands supply both instruction inputs.
For example, a live architectural register or initialized division temporary
supplies its operand without agreement on any other temporary. -/
theorem RegisterAgreementOn.registerInputs {live : Fin 128 → Prop} {pre : SailJoltState}
    (agrees : RegisterAgreementOn live witness t pre) (lhs rhs : Src)
    (leftCanonical : JoltRegisterEncoding.sourceIsCanonical lhs = true)
    (rightCanonical : JoltRegisterEncoding.sourceIsCanonical rhs = true)
    (leftOperand : bytecodeRs1Register row.instruction =
      some (TraceWitness.sourceRegisterAddress lhs))
    (rightOperand : bytecodeRs2Register row.instruction =
      some (TraceWitness.sourceRegisterAddress rhs))
    (selection : (JoltMetadata.instructionFlag row.instruction .LeftOperandIsRs1Value,
      JoltMetadata.instructionFlag row.instruction .LeftOperandIsPC,
      JoltMetadata.instructionFlag row.instruction .RightOperandIsRs2Value,
      JoltMetadata.instructionFlag row.instruction .RightOperandIsImm) =
        (true, false, true, false))
    (leftLive : live (TraceWitness.sourceRegisterAddress lhs))
    (rightLive : live (TraceWitness.sourceRegisterAddress rhs)) :
    witness.LeftInstructionInput t = ((sourceValue lhs pre).toNat : F) ∧
    witness.RightInstructionInput t = ((sourceValue rhs pre).toNat : F) := by
  have left := agrees.rs1Value charAbove2pow127 context equations selected rowIs
    lhs leftCanonical leftOperand leftLive
  have right := agrees.rs2Value charAbove2pow127 context equations selected rowIs
    rhs rightCanonical rightOperand rightLive
  simp only [Prod.mk.injEq] at selection
  obtain ⟨rs1, pc, rs2, imm⟩ := selection
  simpa only [rs1, pc, rs2, imm, Bool.false_eq_true, ↓reduceIte, add_zero, left, right] using
    instructionInputs_of_selected_bytecode charAbove2pow127 context equations t slot selected row rowIs

/-- Two selected register operands supply both instruction inputs.
For example, AND reads both operands from the witness table. -/
theorem RegisterAgreement.registerInputs {pre : SailJoltState}
    (agrees : RegisterAgreement witness t pre) (lhs rhs : Src)
    (leftCanonical : JoltRegisterEncoding.sourceIsCanonical lhs = true)
    (rightCanonical : JoltRegisterEncoding.sourceIsCanonical rhs = true)
    (leftOperand : bytecodeRs1Register row.instruction =
      some (TraceWitness.sourceRegisterAddress lhs))
    (rightOperand : bytecodeRs2Register row.instruction =
      some (TraceWitness.sourceRegisterAddress rhs))
    (selection : (JoltMetadata.instructionFlag row.instruction .LeftOperandIsRs1Value,
      JoltMetadata.instructionFlag row.instruction .LeftOperandIsPC,
      JoltMetadata.instructionFlag row.instruction .RightOperandIsRs2Value,
      JoltMetadata.instructionFlag row.instruction .RightOperandIsImm) =
        (true, false, true, false)) :
    witness.LeftInstructionInput t = ((sourceValue lhs pre).toNat : F) ∧
    witness.RightInstructionInput t = ((sourceValue rhs pre).toNat : F) := by
  exact (agrees.toOn (fun _ => True)).registerInputs charAbove2pow127 context equations
    selected rowIs lhs rhs leftCanonical rightCanonical leftOperand rightOperand selection
    True.intro True.intro

/-- A selected register and decoded immediate supply both instruction inputs.
For example, a live architectural register or initialized division temporary
supplies its operand without agreement on any other temporary. -/
theorem RegisterAgreementOn.immediateInputs {live : Fin 128 → Prop} {pre : SailJoltState}
    (agrees : RegisterAgreementOn live witness t pre) (source : Src) (imm : BitVec 64)
    (canonical : JoltRegisterEncoding.sourceIsCanonical source = true)
    (operand : bytecodeRs1Register row.instruction =
      some (TraceWitness.sourceRegisterAddress source))
    (immediateIs : JoltMetadata.immediate row.instruction = (imm.toNat : Int))
    (selection : (JoltMetadata.instructionFlag row.instruction .LeftOperandIsRs1Value,
      JoltMetadata.instructionFlag row.instruction .LeftOperandIsPC,
      JoltMetadata.instructionFlag row.instruction .RightOperandIsRs2Value,
      JoltMetadata.instructionFlag row.instruction .RightOperandIsImm) =
        (true, false, false, true))
    (sourceLive : live (TraceWitness.sourceRegisterAddress source)) :
    witness.LeftInstructionInput t = ((sourceValue source pre).toNat : F) ∧
    witness.RightInstructionInput t = (imm.toNat : F) := by
  have left := agrees.rs1Value charAbove2pow127 context equations selected rowIs
    source canonical operand sourceLive
  have immediate : witness.Imm t = (imm.toNat : F) := by
    simpa only [bytecodeImmediate, rowIs, immediateIs, Int.cast_natCast] using
      imm_of_selected_bytecode charAbove2pow127 context equations t slot selected
  simp only [Prod.mk.injEq] at selection
  obtain ⟨rs1, pc, rs2, immFlag⟩ := selection
  simpa only [rs1, pc, rs2, immFlag, Bool.false_eq_true, ↓reduceIte,
    add_zero, zero_add, left, immediate] using
    instructionInputs_of_selected_bytecode charAbove2pow127 context equations t slot selected row rowIs

/-- A selected register and decoded immediate supply both instruction inputs.
For example, XORI combines a witness register value and its decoded immediate. -/
theorem RegisterAgreement.immediateInputs {pre : SailJoltState}
    (agrees : RegisterAgreement witness t pre) (source : Src) (imm : BitVec 64)
    (canonical : JoltRegisterEncoding.sourceIsCanonical source = true)
    (operand : bytecodeRs1Register row.instruction =
      some (TraceWitness.sourceRegisterAddress source))
    (immediateIs : JoltMetadata.immediate row.instruction = (imm.toNat : Int))
    (selection : (JoltMetadata.instructionFlag row.instruction .LeftOperandIsRs1Value,
      JoltMetadata.instructionFlag row.instruction .LeftOperandIsPC,
      JoltMetadata.instructionFlag row.instruction .RightOperandIsRs2Value,
      JoltMetadata.instructionFlag row.instruction .RightOperandIsImm) =
        (true, false, false, true)) :
    witness.LeftInstructionInput t = ((sourceValue source pre).toNat : F) ∧
    witness.RightInstructionInput t = (imm.toNat : F) := by
  exact (agrees.toOn (fun _ => True)).immediateInputs charAbove2pow127 context equations
    selected rowIs source imm canonical operand immediateIs selection True.intro

end JoltConstraints.Soundness
