import JoltConstraints.Soundness.Layer5.LookupWrite
import JoltConstraints.Soundness.Layer4.WordArithmetic

/-! Shared register step for ADDW, SUBW, MULW and MULHU. The arithmetic
flags produce a wide lookup operand; the existing word-table rules truncate
or select the high word exactly as the interpreter does.
At public pin 8bbb2357:
See : jolt/tracer/src/instruction/addw.rs:17-27
See : jolt/tracer/src/instruction/subw.rs:16-30
See : jolt/tracer/src/instruction/mulw.rs:17-28
See : jolt/tracer/src/instruction/mulhu.rs:17-28 -/

set_option autoImplicit false

namespace JoltConstraints.Soundness

open Sail PreSail LeanRV64D.Functions JoltISA

inductive WordArithmetic where
  | addw | subw | mulw | mulhu

def WordArithmetic.instruction (operation : WordArithmetic)
    (destination : Dst) (lhs rhs : Src) : Instr :=
  match operation with
  | .addw => .ADDW destination lhs rhs
  | .subw => .SUBW destination lhs rhs
  | .mulw => .MULW destination lhs rhs
  | .mulhu => .MULHU destination lhs rhs

def WordArithmetic.value (operation : WordArithmetic) (lhs rhs : BitVec 64) : BitVec 64 :=
  match operation with
  | .addw => jolt_addw_value lhs rhs
  | .subw => jolt_subw_value lhs rhs
  | .mulw => jolt_mulw_value lhs rhs
  | .mulhu => jolt_mulhu_value lhs rhs

private def WordArithmetic.flag : WordArithmetic → CircuitFlags
  | .addw => .AddOperands
  | .subw => .SubtractOperands
  | .mulw | .mulhu => .MultiplyOperands

private def WordArithmetic.table : WordArithmetic → LookupTableKind
  | .addw | .subw | .mulw => .SignExtendWord
  | .mulhu => .UpperWord

variable {F : Type} [Field F] {params : WitnessParams} {witness : WitnessType F params}
  {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
  (charAbove2pow128 : 2 ^ 128 < ringChar F)
  (context : ConstraintContext joltInstance privateInputs params)
  (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
  {t : Fin params.traceLength} {slot : Fin (2 ^ params.logBytecodeK)}
  (selected : bytecodeRa witness slot t = 1)
  {row : JoltInstructionRow} (rowIs : bytecodeRow context.bytecode slot.val = some row)
  (operation : WordArithmetic) {destination : Dst} {lhs rhs : Src}
  (instructionIs : row.instruction = operation.instruction destination lhs rhs)

include context rowIs instructionIs in
private theorem wordArithmetic_canonical :
    (JoltRegisterEncoding.destinationIsCanonical destination = true ∧
      JoltRegisterEncoding.sourceIsCanonical lhs = true) ∧
    JoltRegisterEncoding.sourceIsCanonical rhs = true := by
  cases operation <;>
    simpa only [instructionIs, WordArithmetic.instruction,
      JoltRegisterEncoding.instructionIsCanonical, Bool.and_eq_true] using
      (bytecodeRow_rowOk context rowIs).canonical

include charAbove2pow128 context equations selected rowIs instructionIs

private theorem wordArithmetic_write_value {pre : SailJoltState}
    (agrees : RegisterAgreement witness t pre) :
    witness.RdWriteValue t =
      ((operation.value (sourceValue lhs pre) (sourceValue rhs pre)).toNat : F) := by
  have bound := two_pow_127_lt_char charAbove2pow128
  have canonical := wordArithmetic_canonical context rowIs operation instructionIs
  obtain ⟨left, right⟩ := agrees.registerInputs bound context equations selected rowIs
    lhs rhs canonical.1.2 canonical.2
    (by cases operation <;> rw [instructionIs] <;> rfl)
    (by cases operation <;> rw [instructionIs] <;> rfl)
    (by cases operation <;> rw [instructionIs] <;> rfl)
  have writeFlag : witness.OpFlags .WriteLookupOutputToRD t = 1 := by
    cases operation <;>
      simpa only [bytecodeCircuitFlag, rowIs, instructionIs, WordArithmetic.instruction,
        JoltMetadata.circuitFlag, JoltMetadata.opcodeFlag] using
        opFlag_of_selected_bytecode bound context equations .WriteLookupOutputToRD t slot selected
  have table : (bytecodeRow context.bytecode slot.val).bind
      (fun row => JoltMetadata.lookupTable row.instruction) = some operation.table := by
    cases operation <;>
      simp only [rowIs, Option.bind_some, instructionIs, WordArithmetic.instruction,
        WordArithmetic.table, JoltMetadata.lookupTable]
  have active : witness.OpFlags operation.flag t = 1 := by
    have flag := opFlag_of_selected_bytecode bound context equations operation.flag t slot selected
    cases operation <;>
      simpa only [bytecodeCircuitFlag, rowIs, instructionIs, WordArithmetic.instruction,
        WordArithmetic.flag, JoltMetadata.circuitFlag, JoltMetadata.opcodeFlag] using flag
  rw [rdWriteValue_eq_lookupOutput equations.rdWriteEqLookupIfWriteLookupToRd t writeFlag]
  cases operation with
  | addw =>
    have output := lookupOutput_signExtendWord_add charAbove2pow128 context equations
      t slot selected table active _ _ left right
    simpa only [WordArithmetic.value, jolt_addw_value, addWide_low] using output
  | subw =>
    have output := lookupOutput_signExtendWord_sub charAbove2pow128 context equations
      t slot selected table active _ _ left right
    simpa only [WordArithmetic.value, jolt_subw_value, subWide_low] using output
  | mulw =>
    have output := lookupOutput_signExtendWord_mul charAbove2pow128 context equations
      t slot selected table active _ _ left right
    simpa only [WordArithmetic.value, jolt_mulw_value, mulWide_low] using output
  | mulhu =>
    have output := lookupOutput_upperWord_mul charAbove2pow128 context equations
      t slot selected table active _ _ left right
    simpa only [WordArithmetic.value, jolt_mulhu_value, JoltISA.mulWide] using output

/-- All four word-arithmetic rows execute with their constrained result and
preserve register agreement at the next cycle. -/
theorem wordArithmetic_step {pre : SailJoltState} (agrees : RegisterAgreement witness t pre)
    (answer : BitVec 64) (advice : row.instruction.RuntimeAdvice) :
    let value := operation.value (sourceValue lhs pre) (sourceValue rhs pre)
    witness.RdWriteValue t = (value.toNat : F) ∧
    execWithTapeAnswer (row.instruction.withRuntimeAdvice advice) answer pre =
      .ok RETIRE_SUCCESS (afterWriteDst destination value pre) ∧
    ∀ next : t.val + 1 < params.traceLength,
      RegisterAgreement witness ⟨t.val + 1, next⟩ (afterWriteDst destination value pre) := by
  dsimp only
  have canonical := wordArithmetic_canonical context rowIs operation instructionIs
  have leftRead := (agrees.read lhs canonical.1.2).1
  have rightRead := (agrees.read rhs canonical.2).1
  have encoded := wordArithmetic_write_value charAbove2pow128 context equations selected rowIs
    operation instructionIs agrees
  apply registerWrite_step context equations selected rowIs charAbove2pow128 agrees
    destination (by cases operation <;> rw [instructionIs] <;> rfl) _ encoded answer advice
    (by cases operation <;> rw [instructionIs] <;> rfl)
  cases operation <;> rw [instructionIs] <;>
    simp only [WordArithmetic.instruction, WordArithmetic.value,
      execWithTapeAnswer, execInstr, bind, EStateM.bind, leftRead, rightRead]

end JoltConstraints.Soundness
