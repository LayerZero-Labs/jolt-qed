import JoltConstraints.Soundness.Layer5.LookupWrite
import JoltConstraints.Soundness.Layer4.WordArithmetic

/-! Shared register step for ADDIW, VirtualMULI and VirtualMULIW. The decoded
immediate is the second arithmetic operand; word rows sign-extend the low word.
At public pin 8bbb2357:
See : jolt/tracer/src/instruction/addiw.rs:20-28
See : jolt/tracer/src/instruction/virtual_muli.rs:19-28
See : jolt/tracer/src/instruction/virtual_muliw.rs:19-24 -/

set_option autoImplicit false

namespace JoltConstraints.Soundness

open Sail PreSail LeanRV64D.Functions JoltISA

/-- ADDIW and virtual immediate-multiply row kinds. -/
inductive ImmediateArithmetic where
  | addiw | muli | muliw

/-- Construct the selected immediate-arithmetic instruction. -/
def ImmediateArithmetic.instruction (operation : ImmediateArithmetic)
    (destination : Dst) (source : Src) (imm : BitVec 64) : Instr :=
  match operation with
  | .addiw => .ADDIW destination source imm
  | .muli => .VirtualMULI destination source imm
  | .muliw => .VirtualMULIW destination source imm

/-- Interpreter value of an immediate-arithmetic instruction. -/
def ImmediateArithmetic.value (operation : ImmediateArithmetic)
    (source imm : BitVec 64) : BitVec 64 :=
  match operation with
  | .addiw => jolt_addiw_value64 source imm
  | .muli => jolt_virtual_muli_value source imm
  | .muliw => jolt_virtual_muliw_value source imm

private def ImmediateArithmetic.flag : ImmediateArithmetic → CircuitFlags
  | .addiw => .AddOperands
  | .muli | .muliw => .MultiplyOperands

private def ImmediateArithmetic.table : ImmediateArithmetic → LookupTableKind
  | .addiw | .muliw => .SignExtendWord
  | .muli => .RangeCheck

variable {F : Type} [Field F] {params : WitnessParams} {witness : WitnessType F params}
  {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
  (charAbove2pow128 : 2 ^ 128 < ringChar F)
  (context : ConstraintContext joltInstance privateInputs params)
  (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
  {live : Fin 128 → Prop} {t : Fin params.traceLength} {slot : Fin (2 ^ params.logBytecodeK)}
  (selected : bytecodeRa witness slot t = 1)
  {row : JoltInstructionRow} (rowIs : bytecodeRow context.bytecode slot.val = some row)
  (operation : ImmediateArithmetic) {destination : Dst} {source : Src} {imm : BitVec 64}
  (instructionIs : row.instruction = operation.instruction destination source imm)

include context rowIs instructionIs in
private theorem immediateArithmetic_canonical :
    JoltRegisterEncoding.destinationIsCanonical destination = true ∧
    JoltRegisterEncoding.sourceIsCanonical source = true := by
  cases operation <;>
    simpa only [instructionIs, ImmediateArithmetic.instruction,
      JoltRegisterEncoding.instructionIsCanonical, Bool.and_eq_true] using
      (bytecodeRow_rowOk context rowIs).canonical

include charAbove2pow128 context equations selected rowIs instructionIs

private theorem immediateArithmetic_write_value {pre : SailJoltState}
    (agrees : RegisterAgreementOn live witness t pre)
    (sourceLive : live (TraceWitness.sourceRegisterAddress source)) :
    witness.RdWriteValue t =
      ((operation.value (sourceValue source pre) imm).toNat : F) := by
  have bound := two_pow_127_lt_char charAbove2pow128
  obtain ⟨left, right⟩ := agrees.immediateInputs bound context equations selected rowIs
    source imm (immediateArithmetic_canonical context rowIs operation instructionIs).2
    (by cases operation <;> rw [instructionIs] <;> rfl)
    (by cases operation <;> rw [instructionIs] <;> rfl)
    (by cases operation <;> rw [instructionIs] <;> rfl) sourceLive
  have writeFlag : witness.OpFlags .WriteLookupOutputToRD t = 1 := by
    have flag := opFlag_of_selected_bytecode bound context equations
      .WriteLookupOutputToRD t slot selected
    cases operation <;>
      simpa only [bytecodeCircuitFlag, rowIs, instructionIs,
        ImmediateArithmetic.instruction, JoltMetadata.circuitFlag,
        JoltMetadata.opcodeFlag] using flag
  have active : witness.OpFlags operation.flag t = 1 := by
    have flag := opFlag_of_selected_bytecode bound context equations operation.flag t slot selected
    cases operation <;>
      simpa only [bytecodeCircuitFlag, rowIs, instructionIs,
        ImmediateArithmetic.instruction, ImmediateArithmetic.flag,
        JoltMetadata.circuitFlag, JoltMetadata.opcodeFlag] using flag
  have table : (bytecodeRow context.bytecode slot.val).bind
      (fun row => JoltMetadata.lookupTable row.instruction) = some operation.table := by
    cases operation <;>
      simp only [rowIs, Option.bind_some, instructionIs, ImmediateArithmetic.instruction,
        ImmediateArithmetic.table, JoltMetadata.lookupTable]
  rw [rdWriteValue_eq_lookupOutput equations.rdWriteEqLookupIfWriteLookupToRd t writeFlag]
  cases operation with
  | addiw =>
    have output := lookupOutput_signExtendWord_add charAbove2pow128 context equations
      t slot selected table active _ _ left right
    simpa only [ImmediateArithmetic.value, jolt_addiw_value64, addWide_low] using output
  | muli =>
    have output := lookupOutput_rangeCheck_mul charAbove2pow128 context equations
      t slot selected table active _ _ left right
    simpa only [ImmediateArithmetic.value, jolt_virtual_muli_value, mulWide_low] using output
  | muliw =>
    have output := lookupOutput_signExtendWord_mul charAbove2pow128 context equations
      t slot selected table active _ _ left right
    simpa only [ImmediateArithmetic.value, jolt_virtual_muliw_value, mulWide_low] using output

/-- ADDIW and both immediate multiplications execute with their constrained
result and preserve register agreement at the next cycle.
The source is live; the destination joins the live set after the row.
For example, ADDIW can read a live source and initialize a temporary. -/
theorem immediateArithmetic_step {pre : SailJoltState}
    (agrees : RegisterAgreementOn live witness t pre)
    (sourceLive : live (TraceWitness.sourceRegisterAddress source))
    (answer : BitVec 64) (advice : row.instruction.RuntimeAdvice) :
    let value := operation.value (sourceValue source pre) imm
    witness.RdWriteValue t = (value.toNat : F) ∧
    execWithTapeAnswer (row.instruction.withRuntimeAdvice advice) answer pre =
      .ok RETIRE_SUCCESS (afterWriteDst destination value pre) ∧
    ∀ next : t.val + 1 < params.traceLength,
      RegisterAgreementOn
        (fun register => live register ∨ register = TraceWitness.destinationRegisterAddress destination)
        witness ⟨t.val + 1, next⟩ (afterWriteDst destination value pre) := by
  dsimp only
  have sourceRead := (agrees.read source
    (immediateArithmetic_canonical context rowIs operation instructionIs).2 sourceLive).1
  have encoded := immediateArithmetic_write_value charAbove2pow128 context equations
    selected rowIs operation instructionIs agrees sourceLive
  apply registerWriteOn_step context equations selected rowIs charAbove2pow128 agrees
    destination (by cases operation <;> rw [instructionIs] <;> rfl) _ encoded answer advice
  rw [withRuntimeAdvice_eq_of_noAdvice _ advice
    (by cases operation <;> rw [instructionIs] <;> rfl)]
  cases operation <;> rw [instructionIs] <;>
    simp only [ImmediateArithmetic.instruction, ImmediateArithmetic.value,
      execWithTapeAnswer, execInstr, bind, EStateM.bind, sourceRead]

end JoltConstraints.Soundness
