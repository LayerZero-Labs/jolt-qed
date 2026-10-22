import JoltConstraints.Soundness.Layer5.LookupWrite
import JoltConstraints.Soundness.Layer4.Arithmetic

/-! One register-step proof for ADD, SUB and MUL. They share source recovery,
RangeCheck lookup consumption and register updates. Only the arithmetic flag,
the existing Layer 4 rule and the interpreter's operation vary.
At public pin 8bbb2357:
See : jolt/tracer/src/instruction/add.rs:17-26
See : jolt/tracer/src/instruction/sub.rs:17-26
See : jolt/tracer/src/instruction/mul.rs:17-26
See : jolt/crates/jolt-lookup-tables/src/instructions/riscv/add.rs:6-31
See : jolt/crates/jolt-lookup-tables/src/instructions/riscv/sub.rs:6-33
See : jolt/crates/jolt-lookup-tables/src/instructions/riscv/mul.rs:6-31 -/

set_option autoImplicit false

namespace JoltConstraints.Soundness

open Sail PreSail LeanRV64D.Functions JoltISA

/-- The three full-word arithmetic operations with two register operands. -/
inductive RegisterArithmetic where
  | add | sub | mul

/-- Select an existing ISA constructor; this does not define a new interpreter. -/
def RegisterArithmetic.instruction (operation : RegisterArithmetic)
    (destination : Dst) (lhs rhs : Src) : Instr :=
  match operation with
  | .add => .ADD destination lhs rhs
  | .sub => .SUB destination lhs rhs
  | .mul => .MUL destination lhs rhs

/-- The wrapped result stated by the shared step theorem. -/
def RegisterArithmetic.value (operation : RegisterArithmetic) (lhs rhs : BitVec 64) : BitVec 64 :=
  match operation with
  | .add => lhs + rhs
  | .sub => lhs - rhs
  | .mul => lhs * rhs

private def RegisterArithmetic.flag : RegisterArithmetic → CircuitFlags
  | .add => .AddOperands
  | .sub => .SubtractOperands
  | .mul => .MultiplyOperands

variable {F : Type} [Field F] {params : WitnessParams} {witness : WitnessType F params}
  {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
  (charAbove2pow128 : 2 ^ 128 < ringChar F)
  (context : ConstraintContext joltInstance privateInputs params)
  (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
  {t : Fin params.traceLength} {slot : Fin (2 ^ params.logBytecodeK)}
  (selected : bytecodeRa witness slot t = 1)
  {row : JoltInstructionRow} (rowIs : bytecodeRow context.bytecode slot.val = some row)
  (operation : RegisterArithmetic) {destination : Dst} {lhs rhs : Src}
  (instructionIs : row.instruction = operation.instruction destination lhs rhs)

include context rowIs instructionIs in
private theorem arithmetic_canonical :
    (JoltRegisterEncoding.destinationIsCanonical destination = true ∧
      JoltRegisterEncoding.sourceIsCanonical lhs = true) ∧
    JoltRegisterEncoding.sourceIsCanonical rhs = true := by
  cases operation <;>
    simpa only [instructionIs, RegisterArithmetic.instruction,
      JoltRegisterEncoding.instructionIsCanonical, Bool.and_eq_true] using
      (bytecodeRow_rowOk context rowIs).canonical

include charAbove2pow128 context equations selected rowIs instructionIs

private theorem arithmetic_write_value {pre : SailJoltState}
    (agrees : RegisterAgreement witness t pre) :
    witness.RdWriteValue t =
      ((operation.value (sourceValue lhs pre) (sourceValue rhs pre)).toNat : F) := by
  have bound := two_pow_127_lt_char charAbove2pow128
  have canonical := arithmetic_canonical context rowIs operation instructionIs
  obtain ⟨left, right⟩ := agrees.registerInputs bound context equations selected rowIs
    lhs rhs canonical.1.2 canonical.2
    (by cases operation <;> rw [instructionIs] <;> rfl)
    (by cases operation <;> rw [instructionIs] <;> rfl)
    (by cases operation <;> rw [instructionIs] <;> rfl)
  have writeFlag : witness.OpFlags .WriteLookupOutputToRD t = 1 := by
    cases operation <;>
      simpa only [bytecodeCircuitFlag, rowIs, instructionIs, RegisterArithmetic.instruction,
        JoltMetadata.circuitFlag, JoltMetadata.opcodeFlag] using
        opFlag_of_selected_bytecode bound context equations .WriteLookupOutputToRD t slot selected
  have table : (bytecodeRow context.bytecode slot.val).bind
      (fun row => JoltMetadata.lookupTable row.instruction) = some .RangeCheck := by
    cases operation <;>
      simp only [rowIs, Option.bind_some, instructionIs, RegisterArithmetic.instruction,
        JoltMetadata.lookupTable]
  have active : witness.OpFlags operation.flag t = 1 := by
    have flag := opFlag_of_selected_bytecode bound context equations operation.flag t slot selected
    cases operation <;>
      simpa only [bytecodeCircuitFlag, rowIs, instructionIs, RegisterArithmetic.instruction,
        RegisterArithmetic.flag, JoltMetadata.circuitFlag, JoltMetadata.opcodeFlag] using flag
  rw [rdWriteValue_eq_lookupOutput equations.rdWriteEqLookupIfWriteLookupToRd t writeFlag]
  cases operation with
  | add =>
    exact lookupOutput_rangeCheck_add charAbove2pow128 context equations t slot
      selected table active _ _ left right
  | sub =>
    exact lookupOutput_rangeCheck_sub charAbove2pow128 context equations t slot
      selected table active _ _ left right
  | mul =>
    exact lookupOutput_rangeCheck_mul charAbove2pow128 context equations t slot
      selected table active _ _ left right

/-- ADD, SUB and MUL execute with their constrained wrapped result and preserve
register agreement. All source/destination aliases are allowed, and the write
and execution conclusions also cover the final cycle. -/
theorem arithmetic_step {pre : SailJoltState} (agrees : RegisterAgreement witness t pre)
    (answer : BitVec 64) (advice : row.instruction.RuntimeAdvice) :
    let value := operation.value (sourceValue lhs pre) (sourceValue rhs pre)
    witness.RdWriteValue t = (value.toNat : F) ∧
    execWithTapeAnswer (row.instruction.withRuntimeAdvice advice) answer pre =
      .ok RETIRE_SUCCESS (afterWriteDst destination value pre) ∧
    ∀ next : t.val + 1 < params.traceLength,
      RegisterAgreement witness ⟨t.val + 1, next⟩ (afterWriteDst destination value pre) := by
  dsimp only
  have canonical := arithmetic_canonical context rowIs operation instructionIs
  have leftRead := (agrees.read lhs canonical.1.2).1
  have rightRead := (agrees.read rhs canonical.2).1
  have encoded := arithmetic_write_value charAbove2pow128 context equations selected rowIs
    operation instructionIs agrees
  apply registerWrite_step context equations selected rowIs charAbove2pow128 agrees
    destination (by cases operation <;> rw [instructionIs] <;> rfl) _ encoded answer advice
    (by cases operation <;> rw [instructionIs] <;> rfl)
  cases operation <;> rw [instructionIs] <;>
    simp only [RegisterArithmetic.instruction, RegisterArithmetic.value,
      execWithTapeAnswer, execInstr, bind, EStateM.bind, leftRead, rightRead,
      addWide_low, subWide_low, mulWide_low]

end JoltConstraints.Soundness
