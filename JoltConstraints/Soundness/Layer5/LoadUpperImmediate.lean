import JoltConstraints.Soundness.Layer5.LookupWrite
import JoltConstraints.Soundness.Layer4.Arithmetic

/-! A selected LUI row writes its already-decoded immediate. The lookup
checks the sum of zero and that word; no source register is read. This covers
a LUI row of the expanded bytecode, whether it represents a source instruction
directly or was emitted inside an expansion.
At public pin 8bbb2357:
See : jolt/tracer/src/instruction/lui.rs:20-24
See : jolt/crates/jolt-riscv/src/instructions/i/lui.rs:3-8
See : jolt/crates/jolt-lookup-tables/src/instructions/riscv/lui.rs:6-31 -/

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
  {destination : Dst} {imm : BitVec 64}
  (instructionIs : row.instruction = .LUI destination imm)

include charAbove2pow128 context equations selected rowIs instructionIs

private theorem lui_write_value : witness.RdWriteValue t = (imm.toNat : F) := by
  have bound := two_pow_127_lt_char charAbove2pow128
  have flags := opFlag_of_selected_bytecode bound context equations
  have addFlag : witness.OpFlags .AddOperands t = 1 := by
    simpa only [bytecodeCircuitFlag, rowIs, JoltMetadata.circuitFlag, instructionIs,
      JoltMetadata.opcodeFlag] using flags .AddOperands t slot selected
  have writeFlag : witness.OpFlags .WriteLookupOutputToRD t = 1 := by
    simpa only [bytecodeCircuitFlag, rowIs, JoltMetadata.circuitFlag, instructionIs,
      JoltMetadata.opcodeFlag] using flags .WriteLookupOutputToRD t slot selected
  have immediate : witness.Imm t = (imm.toNat : F) := by
    simpa only [bytecodeImmediate, rowIs, instructionIs, JoltMetadata.immediate,
      Int.cast_natCast] using imm_of_selected_bytecode bound context equations t slot selected
  have inputs : witness.LeftInstructionInput t = 0 ∧
      witness.RightInstructionInput t = (imm.toNat : F) := by
    simpa only [instructionIs, JoltMetadata.instructionFlag, Bool.false_eq_true,
      ↓reduceIte, zero_add, immediate] using
      instructionInputs_of_selected_bytecode bound context equations t slot selected row rowIs
  rw [rdWriteValue_eq_lookupOutput equations.rdWriteEqLookupIfWriteLookupToRd t writeFlag]
  have output := lookupOutput_rangeCheck_add charAbove2pow128 context equations t slot
    selected (by simp only [rowIs, Option.bind_some, instructionIs, JoltMetadata.lookupTable])
    addFlag 0 imm (by simpa only [BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat,
      Nat.reducePow, Nat.zero_mod, Nat.cast_zero] using inputs.1) inputs.2
  simpa only [zero_add] using output

/-- LUI writes its immediate to the destination register.
Runtime advice is applied as in the trace; execution includes the last cycle. -/
theorem lui_step {pre : SailJoltState} (agrees : RegisterAgreement witness t pre)
    (answer : BitVec 64) (advice : row.instruction.RuntimeAdvice) :
    witness.RdWriteValue t = (imm.toNat : F) ∧
    execWithTapeAnswer (row.instruction.withRuntimeAdvice advice) answer pre =
      .ok RETIRE_SUCCESS (afterWriteDst destination imm pre) ∧
    ∀ next : t.val + 1 < params.traceLength,
      RegisterAgreement witness ⟨t.val + 1, next⟩ (afterWriteDst destination imm pre) := by
  apply registerWrite_step context equations selected rowIs charAbove2pow128 agrees
    destination (by rw [instructionIs]; rfl) imm
    (lui_write_value charAbove2pow128 context equations selected rowIs instructionIs)
    answer advice (by rw [instructionIs]; rfl)
  rw [instructionIs]
  rfl

end JoltConstraints.Soundness
