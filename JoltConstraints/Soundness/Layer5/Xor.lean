import JoltConstraints.Soundness.Layer5.LookupWrite
import JoltConstraints.Soundness.Layer4.Bitwise

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

private theorem xor_inputs {pre : SailJoltState}
    (agrees : RegisterAgreement witness t pre) :
    witness.LeftInstructionInput t = ((sourceValue lhs pre).toNat : F) ∧
    witness.RightInstructionInput t = ((sourceValue rhs pre).toNat : F) := by
  have bound := two_pow_127_lt_char charAbove2pow128
  have canonical := xor_canonical context rowIs instructionIs
  have leftSource := agrees.rs1Value bound context equations selected rowIs lhs canonical.1.2
    (by rw [instructionIs]; rfl)
  have rightSource := agrees.rs2Value bound context equations selected rowIs rhs canonical.2
    (by rw [instructionIs]; rfl)
  simpa only [instructionIs, JoltMetadata.instructionFlag, Bool.false_eq_true, ↓reduceIte,
    add_zero, zero_add, leftSource, rightSource] using
    instructionInputs_of_selected_bytecode bound context equations t slot selected row rowIs

private theorem xor_write_value {pre : SailJoltState}
    (agrees : RegisterAgreement witness t pre) :
    witness.RdWriteValue t = (((sourceValue lhs pre ^^^ sourceValue rhs pre).toNat : F)) := by
  obtain ⟨left, right⟩ :=
    xor_inputs charAbove2pow128 context equations selected rowIs instructionIs agrees
  exact lookupWrite_value_of_raf_zero (two_pow_127_lt_char charAbove2pow128)
    context equations selected rowIs (sourceValue lhs pre) (sourceValue rhs pre) _ .Xor
    (by rw [instructionIs]; rfl) (by rw [instructionIs]; rfl)
    (by rw [instructionIs]; rfl) left right
    (lookupOutput_xor (two_pow_127_lt_char charAbove2pow128) context equations t slot
      selected (sourceValue lhs pre) (sourceValue rhs pre))

/-- A selected XOR row executes with its constrained result and preserves
register agreement at the next cycle. Both operands are read before the write,
so source/destination aliases and virtual registers need no extra premises.
Execution applies runtime advice as in the trace definition. Execution and the
result also cover the last cycle, which has no next column. -/
theorem xor_step {pre : SailJoltState} (agrees : RegisterAgreement witness t pre)
    (answer : BitVec 64) (advice : row.instruction.RuntimeAdvice) :
    let value := sourceValue lhs pre ^^^ sourceValue rhs pre
    witness.RdWriteValue t = (value.toNat : F) ∧
    execWithTapeAnswer (row.instruction.withRuntimeAdvice advice) answer pre =
      .ok RETIRE_SUCCESS (afterWriteDst destination value pre) ∧
    ∀ next : t.val + 1 < params.traceLength,
      RegisterAgreement witness ⟨t.val + 1, next⟩ (afterWriteDst destination value pre) := by
  dsimp only
  have canonical := xor_canonical context rowIs instructionIs
  have encoded := xor_write_value charAbove2pow128 context equations
    selected rowIs instructionIs agrees
  have leftRead := (agrees.read lhs canonical.1.2).1
  have rightRead := (agrees.read rhs canonical.2).1
  apply registerWrite_step context equations selected rowIs charAbove2pow128 agrees
    destination (by rw [instructionIs]; rfl) _ encoded answer advice
    (by rw [instructionIs]; rfl)
  rw [instructionIs]
  simp only [execWithTapeAnswer, execInstr, bind, EStateM.bind, leftRead, rightRead,
    jolt_xor_value]

end JoltConstraints.Soundness
