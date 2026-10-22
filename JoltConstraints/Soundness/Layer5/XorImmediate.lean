import JoltConstraints.Soundness.Layer5.LookupWrite
import JoltConstraints.Soundness.Layer4.Bitwise

/-! Execute a selected XORI row using the shared register/immediate inputs,
XOR lookup and register write. The immediate is already decoded to 64 bits.
At public pin 8bbb2357:
See : jolt/tracer/src/instruction/xori.rs:20-27
See : jolt/crates/jolt-lookup-tables/src/instructions/riscv/xori.rs:6-24 -/

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
  (instructionIs : row.instruction = .XORI destination source imm)

include context rowIs instructionIs in
private theorem xori_canonical :
    JoltRegisterEncoding.destinationIsCanonical destination = true ∧
    JoltRegisterEncoding.sourceIsCanonical source = true := by
  simpa only [instructionIs, JoltRegisterEncoding.instructionIsCanonical,
    Bool.and_eq_true] using (bytecodeRow_rowOk context rowIs).canonical

include charAbove2pow128 context equations selected rowIs instructionIs

private theorem xori_inputs {pre : SailJoltState}
    (agrees : RegisterAgreement witness t pre) :
    witness.LeftInstructionInput t = ((sourceValue source pre).toNat : F) ∧
    witness.RightInstructionInput t = (imm.toNat : F) := by
  exact agrees.immediateInputs (two_pow_127_lt_char charAbove2pow128)
    context equations selected rowIs source imm
    (xori_canonical context rowIs instructionIs).2
    (by rw [instructionIs]; rfl) (by rw [instructionIs]; rfl)
    (by rw [instructionIs]; rfl)

private theorem xori_write_value {pre : SailJoltState}
    (agrees : RegisterAgreement witness t pre) :
    witness.RdWriteValue t = ((sourceValue source pre ^^^ imm).toNat : F) := by
  obtain ⟨left, right⟩ :=
    xori_inputs charAbove2pow128 context equations selected rowIs instructionIs agrees
  exact lookupWrite_value_of_raf_zero (two_pow_127_lt_char charAbove2pow128)
    context equations selected rowIs (sourceValue source pre) imm _ .Xor
    (by rw [instructionIs]; rfl) (by rw [instructionIs]; rfl)
    (by rw [instructionIs]; rfl) left right
    (lookupOutput_xor (two_pow_127_lt_char charAbove2pow128) context equations t slot
      selected (sourceValue source pre) imm)

/-- XORI writes its constrained bitwise result and preserves register agreement.
Source/destination aliases are allowed; execution also covers the final cycle. -/
theorem xori_step {pre : SailJoltState} (agrees : RegisterAgreement witness t pre)
    (answer : BitVec 64) (advice : row.instruction.RuntimeAdvice) :
    let value := sourceValue source pre ^^^ imm
    witness.RdWriteValue t = (value.toNat : F) ∧
    execWithTapeAnswer (row.instruction.withRuntimeAdvice advice) answer pre =
      .ok RETIRE_SUCCESS (afterWriteDst destination value pre) ∧
    ∀ next : t.val + 1 < params.traceLength,
      RegisterAgreement witness ⟨t.val + 1, next⟩ (afterWriteDst destination value pre) := by
  dsimp only
  have sourceCanonical := (xori_canonical context rowIs instructionIs).2
  have encoded := xori_write_value charAbove2pow128 context equations
    selected rowIs instructionIs agrees
  have read := (agrees.read source sourceCanonical).1
  apply registerWrite_step context equations selected rowIs charAbove2pow128 agrees
    destination (by rw [instructionIs]; rfl) _ encoded answer advice
    (by rw [instructionIs]; rfl)
  rw [instructionIs]
  simp only [execWithTapeAnswer, execInstr, bind, EStateM.bind, read, jolt_xor_value]

end JoltConstraints.Soundness
