import JoltConstraints.Soundness.Layer5.RegisterComparison
import JoltConstraints.Soundness.Layer4.Bitwise

/-! Shared register step for the ANDI, ORI and SLTI immediate rows. The
selected row supplies the decoded 64-bit immediate to the lookup table.
At public pin 8bbb2357:
See : jolt/tracer/src/instruction/andi.rs:20-27
See : jolt/tracer/src/instruction/ori.rs:20-27
See : jolt/tracer/src/instruction/slti.rs:20-30 -/

set_option autoImplicit false

namespace JoltConstraints.Soundness

open Sail PreSail LeanRV64D.Functions JoltISA

/-- Immediate AND, OR and signed comparison rows. -/
inductive ImmediateLogic where
  | andi | ori | slti

/-- Construct the selected immediate-logic instruction. -/
def ImmediateLogic.instruction (operation : ImmediateLogic)
    (destination : Dst) (source : Src) (imm : BitVec 64) : Instr :=
  match operation with
  | .andi => .ANDI destination source imm
  | .ori => .ORI destination source imm
  | .slti => .SLTI destination source imm

/-- Interpreter value of an immediate-logic instruction. -/
def ImmediateLogic.value (operation : ImmediateLogic) (source imm : BitVec 64) : BitVec 64 :=
  match operation with
  | .andi => Riscv.andi source imm
  | .ori => Riscv.ori source imm
  | .slti => jolt_slt_value source imm

private def ImmediateLogic.table : ImmediateLogic → LookupTableKind
  | .andi => .And
  | .ori => .Or
  | .slti => .SignedLessThan

variable {F : Type} [Field F] {params : WitnessParams} {witness : WitnessType F params}
  {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
  (charAbove2pow128 : 2 ^ 128 < ringChar F)
  (context : ConstraintContext joltInstance privateInputs params)
  (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
  {t : Fin params.traceLength} {slot : Fin (2 ^ params.logBytecodeK)}
  (selected : bytecodeRa witness slot t = 1)
  {row : JoltInstructionRow} (rowIs : bytecodeRow context.bytecode slot.val = some row)
  (operation : ImmediateLogic) {destination : Dst} {source : Src} {imm : BitVec 64}
  (instructionIs : row.instruction = operation.instruction destination source imm)

include context rowIs instructionIs in
private theorem immediateLogic_canonical :
    JoltRegisterEncoding.destinationIsCanonical destination = true ∧
    JoltRegisterEncoding.sourceIsCanonical source = true := by
  cases operation <;>
    simpa only [instructionIs, ImmediateLogic.instruction,
      JoltRegisterEncoding.instructionIsCanonical, Bool.and_eq_true] using
      (bytecodeRow_rowOk context rowIs).canonical

include charAbove2pow128 context equations selected rowIs instructionIs

private theorem immediateLogic_write_value {pre : SailJoltState}
    (agrees : RegisterAgreement witness t pre) :
    witness.RdWriteValue t =
      ((operation.value (sourceValue source pre) imm).toNat : F) := by
  have bound := two_pow_127_lt_char charAbove2pow128
  obtain ⟨left, right⟩ := agrees.immediateInputs bound context equations selected rowIs
    source imm (immediateLogic_canonical context rowIs operation instructionIs).2
    (by cases operation <;> rw [instructionIs] <;> rfl)
    (by cases operation <;> rw [instructionIs] <;> rfl)
    (by cases operation <;> rw [instructionIs] <;> rfl)
  apply lookupWrite_value_of_raf_zero bound context equations selected rowIs
    (sourceValue source pre) imm _ operation.table
    (by cases operation <;> rw [instructionIs] <;> rfl)
    (by cases operation <;> rw [instructionIs] <;> rfl)
    (by cases operation <;> rw [instructionIs] <;> rfl)
    left right
  intro raf leftLookup rightLookup table
  cases operation with
  | andi =>
    simpa only [ImmediateLogic.value, Riscv.andi] using
      (lookupOutput_and bound context equations t slot selected
        (sourceValue source pre) imm raf leftLookup rightLookup table)
  | ori =>
    simpa only [ImmediateLogic.value, Riscv.ori] using
      (lookupOutput_or bound context equations t slot selected
        (sourceValue source pre) imm raf leftLookup rightLookup table)
  | slti =>
    have output := lookupOutput_signedLessThan bound context equations t slot selected
      (sourceValue source pre) imm raf leftLookup rightLookup table
    simpa only [ImmediateLogic.value, slt_value_toNat_eq] using output

/-- ANDI, ORI and SLTI execute with their constrained result and preserve
register agreement at the next cycle. -/
theorem immediateLogic_step {pre : SailJoltState}
    (agrees : RegisterAgreement witness t pre)
    (answer : BitVec 64) (advice : row.instruction.RuntimeAdvice) :
    let value := operation.value (sourceValue source pre) imm
    witness.RdWriteValue t = (value.toNat : F) ∧
    execWithTapeAnswer (row.instruction.withRuntimeAdvice advice) answer pre =
      .ok RETIRE_SUCCESS (afterWriteDst destination value pre) ∧
    ∀ next : t.val + 1 < params.traceLength,
      RegisterAgreement witness ⟨t.val + 1, next⟩ (afterWriteDst destination value pre) := by
  dsimp only
  have sourceRead := (agrees.read source
    (immediateLogic_canonical context rowIs operation instructionIs).2).1
  have encoded := immediateLogic_write_value charAbove2pow128 context equations
    selected rowIs operation instructionIs agrees
  apply registerWrite_step context equations selected rowIs charAbove2pow128 agrees
    destination (by cases operation <;> rw [instructionIs] <;> rfl) _ encoded answer advice
    (by cases operation <;> rw [instructionIs] <;> rfl)
  cases operation <;> rw [instructionIs] <;>
    simp only [ImmediateLogic.instruction, ImmediateLogic.value,
      execWithTapeAnswer, execInstr, bind, EStateM.bind, sourceRead]

end JoltConstraints.Soundness
