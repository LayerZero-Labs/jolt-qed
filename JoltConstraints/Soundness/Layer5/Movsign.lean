import JoltConstraints.Soundness.Layer5.LookupWrite
import JoltConstraints.Soundness.Layer4.Conditional

/-! VirtualMovsign writes an all-ones or zero mask according to its source
sign bit. Its decoded immediate is a lookup input but does not affect the
SignMask table result or the interpreter's write.
At public pin 8bbb2357:
See : jolt/tracer/src/instruction/virtual_movsign.rs:20-32 -/

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
  (instructionIs : row.instruction = .VirtualMovsign destination source imm)

include context rowIs instructionIs in
private theorem movsign_canonical :
    JoltRegisterEncoding.destinationIsCanonical destination = true ∧
    JoltRegisterEncoding.sourceIsCanonical source = true := by
  simpa only [instructionIs, JoltRegisterEncoding.instructionIsCanonical,
    Bool.and_eq_true] using (bytecodeRow_rowOk context rowIs).canonical

include charAbove2pow128 context equations selected rowIs instructionIs

private theorem movsign_write_value {pre : SailJoltState}
    (agrees : RegisterAgreement witness t pre) :
    witness.RdWriteValue t = ((jolt_movsign_value (sourceValue source pre)).toNat : F) := by
  have bound := two_pow_127_lt_char charAbove2pow128
  obtain ⟨left, right⟩ := agrees.immediateInputs bound context equations selected rowIs
    source imm (movsign_canonical context rowIs instructionIs).2
    (by rw [instructionIs]; rfl) (by rw [instructionIs]; rfl)
    (by rw [instructionIs]; rfl)
  apply lookupWrite_value_of_raf_zero bound context equations selected rowIs
    (sourceValue source pre) imm _ .SignMask
    (by rw [instructionIs]; rfl) (by rw [instructionIs]; rfl)
    (by rw [instructionIs]; rfl) left right
  intro raf leftLookup rightLookup table
  simpa only [jolt_movsign_value] using
    (lookupOutput_signMask bound context equations t slot selected
      (sourceValue source pre) imm raf leftLookup rightLookup table)

/-- VirtualMovsign executes with its constrained sign mask and preserves
register agreement at the next cycle. -/
theorem movsign_step {pre : SailJoltState}
    (agrees : RegisterAgreement witness t pre)
    (answer : BitVec 64) (advice : row.instruction.RuntimeAdvice) :
    let value := jolt_movsign_value (sourceValue source pre)
    witness.RdWriteValue t = (value.toNat : F) ∧
    execWithTapeAnswer (row.instruction.withRuntimeAdvice advice) answer pre =
      .ok RETIRE_SUCCESS (afterWriteDst destination value pre) ∧
    ∀ next : t.val + 1 < params.traceLength,
      RegisterAgreement witness ⟨t.val + 1, next⟩ (afterWriteDst destination value pre) := by
  dsimp only
  have sourceRead := (agrees.read source (movsign_canonical context rowIs instructionIs).2).1
  have encoded := movsign_write_value charAbove2pow128 context equations
    selected rowIs instructionIs agrees
  apply registerWrite_step context equations selected rowIs charAbove2pow128 agrees
    destination (by rw [instructionIs]; rfl) _ encoded answer advice
    (by rw [instructionIs]; rfl)
  rw [instructionIs]
  simp only [execWithTapeAnswer, execInstr, bind, EStateM.bind, sourceRead]

end JoltConstraints.Soundness
