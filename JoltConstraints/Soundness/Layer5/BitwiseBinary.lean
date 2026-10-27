import JoltConstraints.Soundness.Layer5.LookupWrite
import JoltConstraints.Soundness.Layer4.Bitwise

/-! Shared execution proof for two-register AND, OR and ANDN. Each consumes
the existing interleaved lookup-table rule and the common destination write.
At public pin 8bbb2357:
See : jolt/tracer/src/instruction/and.rs:17-26
See : jolt/tracer/src/instruction/or.rs:17-26
See : jolt/tracer/src/instruction/andn.rs:17-26 -/

set_option autoImplicit false

namespace JoltConstraints.Soundness

open Sail PreSail LeanRV64D.Functions JoltISA

/-- Two-register bitwise row kinds covered by the shared step. -/
inductive BitwiseBinary where
  | and | or | andn

/-- Construct the selected bitwise instruction. -/
def BitwiseBinary.instruction (operation : BitwiseBinary)
    (destination : Dst) (lhs rhs : Src) : Instr :=
  match operation with
  | .and => .AND destination lhs rhs
  | .or => .OR destination lhs rhs
  | .andn => .ANDN destination lhs rhs

/-- Interpreter value of a bitwise instruction. -/
def BitwiseBinary.value (operation : BitwiseBinary) (lhs rhs : BitVec 64) : BitVec 64 :=
  match operation with
  | .and => lhs &&& rhs
  | .or => lhs ||| rhs
  | .andn => lhs &&& ~~~rhs

private def BitwiseBinary.table : BitwiseBinary → LookupTableKind
  | .and => .And
  | .or => .Or
  | .andn => .Andn

variable {F : Type} [Field F] {params : WitnessParams} {witness : WitnessType F params}
  {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
  (charAbove2pow128 : 2 ^ 128 < ringChar F)
  (context : ConstraintContext joltInstance privateInputs params)
  (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
  {live : Fin 128 → Prop} {t : Fin params.traceLength} {slot : Fin (2 ^ params.logBytecodeK)}
  (selected : bytecodeRa witness slot t = 1)
  {row : JoltInstructionRow} (rowIs : bytecodeRow context.bytecode slot.val = some row)
  (operation : BitwiseBinary) {destination : Dst} {lhs rhs : Src}
  (instructionIs : row.instruction = operation.instruction destination lhs rhs)

include context rowIs instructionIs in
private theorem bitwise_canonical :
    (JoltRegisterEncoding.destinationIsCanonical destination = true ∧
      JoltRegisterEncoding.sourceIsCanonical lhs = true) ∧
    JoltRegisterEncoding.sourceIsCanonical rhs = true := by
  cases operation <;>
    simpa only [instructionIs, BitwiseBinary.instruction,
      JoltRegisterEncoding.instructionIsCanonical, Bool.and_eq_true] using
      (bytecodeRow_rowOk context rowIs).canonical

include charAbove2pow128 context equations selected rowIs instructionIs

private theorem bitwise_write_value {pre : SailJoltState}
    (agrees : RegisterAgreementOn live witness t pre)
    (lhsLive : live (TraceWitness.sourceRegisterAddress lhs))
    (rhsLive : live (TraceWitness.sourceRegisterAddress rhs)) :
    witness.RdWriteValue t =
      ((operation.value (sourceValue lhs pre) (sourceValue rhs pre)).toNat : F) := by
  have bound := two_pow_127_lt_char charAbove2pow128
  have canonical := bitwise_canonical context rowIs operation instructionIs
  obtain ⟨left, right⟩ := agrees.registerInputs bound context equations selected rowIs
    lhs rhs canonical.1.2 canonical.2
    (by cases operation <;> rw [instructionIs] <;> rfl)
    (by cases operation <;> rw [instructionIs] <;> rfl)
    (by cases operation <;> rw [instructionIs] <;> rfl) lhsLive rhsLive
  apply lookupWrite_value_of_raf_zero bound context equations selected rowIs
    (sourceValue lhs pre) (sourceValue rhs pre) _ operation.table
    (by cases operation <;> rw [instructionIs] <;> rfl)
    (by cases operation <;> rw [instructionIs] <;> rfl)
    (by cases operation <;> rw [instructionIs] <;> rfl)
    left right
  intro raf leftLookup rightLookup table
  cases operation with
  | and =>
    exact lookupOutput_and bound context equations t slot selected
      (sourceValue lhs pre) (sourceValue rhs pre) raf leftLookup rightLookup table
  | or =>
    exact lookupOutput_or bound context equations t slot selected
      (sourceValue lhs pre) (sourceValue rhs pre) raf leftLookup rightLookup table
  | andn =>
    exact lookupOutput_andn bound context equations t slot selected
      (sourceValue lhs pre) (sourceValue rhs pre) raf leftLookup rightLookup table

/-- AND, OR and ANDN write the table-constrained bitwise result and preserve
register agreement, including when operands and destination alias.
Both sources are live; the destination joins the live set after the row.
For example, AND can read two live operands and initialize a temporary. -/
theorem bitwise_step {pre : SailJoltState} (agrees : RegisterAgreementOn live witness t pre)
    (lhsLive : live (TraceWitness.sourceRegisterAddress lhs))
    (rhsLive : live (TraceWitness.sourceRegisterAddress rhs))
    (answer : BitVec 64) (advice : row.instruction.RuntimeAdvice) :
    let value := operation.value (sourceValue lhs pre) (sourceValue rhs pre)
    witness.RdWriteValue t = (value.toNat : F) ∧
    execWithTapeAnswer (row.instruction.withRuntimeAdvice advice) answer pre =
      .ok RETIRE_SUCCESS (afterWriteDst destination value pre) ∧
    ∀ next : t.val + 1 < params.traceLength,
      RegisterAgreementOn
        (fun register => live register ∨ register = TraceWitness.destinationRegisterAddress destination)
        witness ⟨t.val + 1, next⟩ (afterWriteDst destination value pre) := by
  dsimp only
  have canonical := bitwise_canonical context rowIs operation instructionIs
  have leftRead := (agrees.read lhs canonical.1.2 lhsLive).1
  have rightRead := (agrees.read rhs canonical.2 rhsLive).1
  have encoded := bitwise_write_value charAbove2pow128 context equations selected rowIs
    operation instructionIs agrees lhsLive rhsLive
  apply registerWriteOn_step context equations selected rowIs charAbove2pow128 agrees
    destination (by cases operation <;> rw [instructionIs] <;> rfl) _ encoded answer advice
  rw [withRuntimeAdvice_eq_of_noAdvice _ advice
    (by cases operation <;> rw [instructionIs] <;> rfl)]
  cases operation <;> rw [instructionIs] <;>
    simp only [BitwiseBinary.instruction, BitwiseBinary.value,
      execWithTapeAnswer, execInstr, bind, EStateM.bind, leftRead, rightRead,
      Riscv.andi, Riscv.ori, jolt_andn_value]

end JoltConstraints.Soundness
