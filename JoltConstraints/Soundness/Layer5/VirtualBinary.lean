import JoltConstraints.Soundness.Layer5.LookupWrite
import JoltConstraints.Soundness.Layer4.Pext
import JoltConstraints.Soundness.Layer4.Conditional

/-! Shared step for extraction, store-lane shifting and conditional negation.
Their existing interleaved table rules give the interpreter value for arbitrary
source words, so no lane-mask shape is assumed by these row proofs.
At public pin 8bbb2357:
See : jolt/tracer/src/instruction/virtual_pext.rs:18-26
See : jolt/tracer/src/instruction/virtual_pext_signed.rs:17-70
See : jolt/tracer/src/instruction/virtual_shift_data_b.rs:17-28
See : jolt/tracer/src/instruction/virtual_shift_data_h.rs:17-28
See : jolt/tracer/src/instruction/virtual_shift_data_w.rs:17-28
See : jolt/tracer/src/instruction/virtual_negate_if.rs:17-32 -/

set_option autoImplicit false

namespace JoltConstraints.Soundness

open Sail PreSail LeanRV64D.Functions JoltISA

inductive VirtualBinary where
  | pext | pextSigned | shiftDataB | shiftDataH | shiftDataW | negateIf

def VirtualBinary.instruction (operation : VirtualBinary)
    (destination : Dst) (lhs rhs : Src) : Instr :=
  match operation with
  | .pext => .VirtualPext destination lhs rhs
  | .pextSigned => .VirtualPextSigned destination lhs rhs
  | .shiftDataB => .VirtualShiftDataB destination lhs rhs
  | .shiftDataH => .VirtualShiftDataH destination lhs rhs
  | .shiftDataW => .VirtualShiftDataW destination lhs rhs
  | .negateIf => .VirtualNegateIf destination lhs rhs

def VirtualBinary.value (operation : VirtualBinary) (lhs rhs : BitVec 64) : BitVec 64 :=
  match operation with
  | .pext => jolt_virtual_pext_value lhs rhs
  | .pextSigned => jolt_virtual_pext_signed_value lhs rhs
  | .shiftDataB => jolt_virtual_shift_data_b_value lhs rhs
  | .shiftDataH => jolt_virtual_shift_data_h_value lhs rhs
  | .shiftDataW => jolt_virtual_shift_data_w_value lhs rhs
  | .negateIf => jolt_virtual_negate_if_value lhs rhs

private def VirtualBinary.table : VirtualBinary → LookupTableKind
  | .pext => .Pext
  | .pextSigned => .PextSigned
  | .shiftDataB => .ShiftDataB
  | .shiftDataH => .ShiftDataH
  | .shiftDataW => .ShiftDataW
  | .negateIf => .VirtualNegateIf

variable {F : Type} [Field F] {params : WitnessParams} {live : Fin 128 → Prop} {witness : WitnessType F params}
  {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
  (charAbove2pow128 : 2 ^ 128 < ringChar F)
  (context : ConstraintContext joltInstance privateInputs params)
  (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
  {t : Fin params.traceLength} {slot : Fin (2 ^ params.logBytecodeK)}
  (selected : bytecodeRa witness slot t = 1)
  {row : JoltInstructionRow} (rowIs : bytecodeRow context.bytecode slot.val = some row)
  (operation : VirtualBinary) {destination : Dst} {lhs rhs : Src}
  (instructionIs : row.instruction = operation.instruction destination lhs rhs)

include context rowIs instructionIs in
private theorem virtualBinary_canonical :
    (JoltRegisterEncoding.destinationIsCanonical destination = true ∧
      JoltRegisterEncoding.sourceIsCanonical lhs = true) ∧
    JoltRegisterEncoding.sourceIsCanonical rhs = true := by
  cases operation <;>
    simpa only [instructionIs, VirtualBinary.instruction,
      JoltRegisterEncoding.instructionIsCanonical, Bool.and_eq_true] using
      (bytecodeRow_rowOk context rowIs).canonical

include charAbove2pow128 context equations selected rowIs instructionIs

private theorem virtualBinary_write_value {pre : SailJoltState}
    (agrees : RegisterAgreementOn live witness t pre)
    (leftLive : live (TraceWitness.sourceRegisterAddress lhs))
    (rightLive : live (TraceWitness.sourceRegisterAddress rhs)) :
    witness.RdWriteValue t =
      ((operation.value (sourceValue lhs pre) (sourceValue rhs pre)).toNat : F) := by
  have bound := two_pow_127_lt_char charAbove2pow128
  have canonical := virtualBinary_canonical context rowIs operation instructionIs
  obtain ⟨left, right⟩ := agrees.registerInputs bound context equations selected rowIs
    lhs rhs canonical.1.2 canonical.2
    (by cases operation <;> rw [instructionIs] <;> rfl)
    (by cases operation <;> rw [instructionIs] <;> rfl)
    (by cases operation <;> rw [instructionIs] <;> rfl) leftLive rightLive
  apply lookupWrite_value_of_raf_zero bound context equations selected rowIs
    (sourceValue lhs pre) (sourceValue rhs pre) _ operation.table
    (by cases operation <;> rw [instructionIs] <;> rfl)
    (by cases operation <;> rw [instructionIs] <;> rfl)
    (by cases operation <;> rw [instructionIs] <;> rfl)
    left right
  intro raf leftLookup rightLookup table
  cases operation with
  | pext =>
    exact lookupOutput_pext bound context equations t slot selected
      (sourceValue lhs pre) (sourceValue rhs pre) raf leftLookup rightLookup table
  | pextSigned =>
    exact lookupOutput_pextSigned bound context equations t slot selected
      (sourceValue lhs pre) (sourceValue rhs pre) raf leftLookup rightLookup table
  | shiftDataB =>
    exact lookupOutput_shiftDataB bound context equations t slot selected
      (sourceValue lhs pre) (sourceValue rhs pre) raf leftLookup rightLookup table
  | shiftDataH =>
    exact lookupOutput_shiftDataH bound context equations t slot selected
      (sourceValue lhs pre) (sourceValue rhs pre) raf leftLookup rightLookup table
  | shiftDataW =>
    exact lookupOutput_shiftDataW bound context equations t slot selected
      (sourceValue lhs pre) (sourceValue rhs pre) raf leftLookup rightLookup table
  | negateIf =>
    simpa only [VirtualBinary.value, jolt_virtual_negate_if_value] using
      (lookupOutput_negateIf bound context equations t slot selected
        (sourceValue lhs pre) (sourceValue rhs pre) raf
        leftLookup rightLookup table)

/-- These six virtual rows execute with their table-constrained result and
preserve register agreement at the next cycle.
The source registers must be live, and the destination is added to the live set.
For example, a division row can initialize a dead temporary from live operands. -/
theorem virtualBinary_step {pre : SailJoltState} (agrees : RegisterAgreementOn live witness t pre)
    (leftLive : live (TraceWitness.sourceRegisterAddress lhs))
    (rightLive : live (TraceWitness.sourceRegisterAddress rhs))
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
  have canonical := virtualBinary_canonical context rowIs operation instructionIs
  have leftRead := (agrees.read lhs canonical.1.2 leftLive).1
  have rightRead := (agrees.read rhs canonical.2 rightLive).1
  have encoded := virtualBinary_write_value charAbove2pow128 context equations selected rowIs
    operation instructionIs agrees leftLive rightLive
  apply registerWriteOn_step context equations selected rowIs charAbove2pow128 agrees
    destination (by cases operation <;> rw [instructionIs] <;> rfl) _ encoded answer advice
  rw [withRuntimeAdvice_eq_of_noAdvice _ advice (by cases operation <;> rw [instructionIs] <;> rfl)]
  cases operation <;> rw [instructionIs] <;>
    simp only [VirtualBinary.instruction, VirtualBinary.value,
      execWithTapeAnswer, execInstr, bind, EStateM.bind, leftRead, rightRead]

end JoltConstraints.Soundness
