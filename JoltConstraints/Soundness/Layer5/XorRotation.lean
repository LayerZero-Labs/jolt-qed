import JoltConstraints.Soundness.Layer5.LookupWrite
import JoltConstraints.Soundness.Layer4.Rotate

/-! One execution argument for the twelve XOR-rotation rows. Their lookup
tables already give the exact interpreter values at the recovered operands.
At public pin 8bbb2357:
See : jolt/tracer/src/instruction/virtual_xor_rot.rs:8-33
See : jolt/tracer/src/instruction/virtual_xor_rotw.rs:8-39
See : jolt/tracer/src/instruction/virtual_xor_rotl1.rs:8-25 -/

set_option autoImplicit false

namespace JoltConstraints.Soundness

open Sail PreSail LeanRV64D.Functions JoltISA

inductive XorRotation where
  | r32 | r24 | r16 | r63 | l1
  | w16 | w12 | w8 | w7 | w22 | w19 | w6

def XorRotation.instruction (operation : XorRotation)
    (destination : Dst) (lhs rhs : Src) : Instr :=
  match operation with
  | .r32 => .VirtualXORROT32 destination lhs rhs
  | .r24 => .VirtualXORROT24 destination lhs rhs
  | .r16 => .VirtualXORROT16 destination lhs rhs
  | .r63 => .VirtualXORROT63 destination lhs rhs
  | .l1 => .VirtualXORROTL1 destination lhs rhs
  | .w16 => .VirtualXORROTW16 destination lhs rhs
  | .w12 => .VirtualXORROTW12 destination lhs rhs
  | .w8 => .VirtualXORROTW8 destination lhs rhs
  | .w7 => .VirtualXORROTW7 destination lhs rhs
  | .w22 => .VirtualXORROTW22 destination lhs rhs
  | .w19 => .VirtualXORROTW19 destination lhs rhs
  | .w6 => .VirtualXORROTW6 destination lhs rhs

def XorRotation.value (operation : XorRotation) (lhs rhs : BitVec 64) : BitVec 64 :=
  match operation with
  | .r32 => jolt_virtual_xorrot_value 32 lhs rhs
  | .r24 => jolt_virtual_xorrot_value 24 lhs rhs
  | .r16 => jolt_virtual_xorrot_value 16 lhs rhs
  | .r63 => jolt_virtual_xorrot_value 63 lhs rhs
  | .l1 => jolt_virtual_xorrotl1_value lhs rhs
  | .w16 => jolt_virtual_xorrotw_value 16 lhs rhs
  | .w12 => jolt_virtual_xorrotw_value 12 lhs rhs
  | .w8 => jolt_virtual_xorrotw_value 8 lhs rhs
  | .w7 => jolt_virtual_xorrotw_value 7 lhs rhs
  | .w22 => jolt_virtual_xorrotw_value 22 lhs rhs
  | .w19 => jolt_virtual_xorrotw_value 19 lhs rhs
  | .w6 => jolt_virtual_xorrotw_value 6 lhs rhs

private def XorRotation.table : XorRotation → LookupTableKind
  | .r32 => .VirtualXORROT32
  | .r24 => .VirtualXORROT24
  | .r16 => .VirtualXORROT16
  | .r63 => .VirtualXORROT63
  | .l1 => .VirtualXORROTL1
  | .w16 => .VirtualXORROTW16
  | .w12 => .VirtualXORROTW12
  | .w8 => .VirtualXORROTW8
  | .w7 => .VirtualXORROTW7
  | .w22 => .VirtualXORROTW22
  | .w19 => .VirtualXORROTW19
  | .w6 => .VirtualXORROTW6

variable {F : Type} [Field F] {params : WitnessParams} {live : Fin 128 → Prop} {witness : WitnessType F params}
  {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
  (charAbove2pow128 : 2 ^ 128 < ringChar F)
  (context : ConstraintContext joltInstance privateInputs params)
  (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
  {t : Fin params.traceLength} {slot : Fin (2 ^ params.logBytecodeK)}
  (selected : bytecodeRa witness slot t = 1)
  {row : JoltInstructionRow} (rowIs : bytecodeRow context.bytecode slot.val = some row)
  (operation : XorRotation) {destination : Dst} {lhs rhs : Src}
  (instructionIs : row.instruction = operation.instruction destination lhs rhs)

include context rowIs instructionIs in
private theorem xorRotation_canonical :
    (JoltRegisterEncoding.destinationIsCanonical destination = true ∧
      JoltRegisterEncoding.sourceIsCanonical lhs = true) ∧
    JoltRegisterEncoding.sourceIsCanonical rhs = true := by
  cases operation <;>
    simpa only [instructionIs, XorRotation.instruction,
      JoltRegisterEncoding.instructionIsCanonical, Bool.and_eq_true] using
      (bytecodeRow_rowOk context rowIs).canonical

include charAbove2pow128 context equations selected rowIs instructionIs

private theorem xorRotation_write_value {pre : SailJoltState}
    (agrees : RegisterAgreementOn live witness t pre)
    (lhsLive : live (TraceWitness.sourceRegisterAddress lhs))
    (rhsLive : live (TraceWitness.sourceRegisterAddress rhs)) :
    witness.RdWriteValue t =
      ((operation.value (sourceValue lhs pre) (sourceValue rhs pre)).toNat : F) := by
  have bound := two_pow_127_lt_char charAbove2pow128
  have canonical := xorRotation_canonical context rowIs operation instructionIs
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
  | r32 => exact lookupOutput_xorRot32 bound context equations t slot selected _ _ raf leftLookup rightLookup table
  | r24 => exact lookupOutput_xorRot24 bound context equations t slot selected _ _ raf leftLookup rightLookup table
  | r16 => exact lookupOutput_xorRot16 bound context equations t slot selected _ _ raf leftLookup rightLookup table
  | r63 => exact lookupOutput_xorRot63 bound context equations t slot selected _ _ raf leftLookup rightLookup table
  | l1 => exact lookupOutput_xorRotL1 bound context equations t slot selected _ _ raf leftLookup rightLookup table
  | w16 => exact lookupOutput_xorRotW16 bound context equations t slot selected _ _ raf leftLookup rightLookup table
  | w12 => exact lookupOutput_xorRotW12 bound context equations t slot selected _ _ raf leftLookup rightLookup table
  | w8 => exact lookupOutput_xorRotW8 bound context equations t slot selected _ _ raf leftLookup rightLookup table
  | w7 => exact lookupOutput_xorRotW7 bound context equations t slot selected _ _ raf leftLookup rightLookup table
  | w22 => exact lookupOutput_xorRotW22 bound context equations t slot selected _ _ raf leftLookup rightLookup table
  | w19 => exact lookupOutput_xorRotW19 bound context equations t slot selected _ _ raf leftLookup rightLookup table
  | w6 => exact lookupOutput_xorRotW6 bound context equations t slot selected _ _ raf leftLookup rightLookup table

/-- Both sources are live, and the destination joins the live set.
For example, VirtualXORROT32 can write a fresh temporary.
All twelve XOR-rotation rows write their constrained table result, execute,
and preserve register agreement at the next cycle. -/
theorem xorRotation_step {pre : SailJoltState} (agrees : RegisterAgreementOn live witness t pre)
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
  have canonical := xorRotation_canonical context rowIs operation instructionIs
  have leftRead := (agrees.read lhs canonical.1.2 lhsLive).1
  have rightRead := (agrees.read rhs canonical.2 rhsLive).1
  have encoded := xorRotation_write_value charAbove2pow128 context equations selected rowIs
    operation instructionIs agrees lhsLive rhsLive
  apply registerWriteOn_step context equations selected rowIs charAbove2pow128 agrees
    destination (by cases operation <;> rw [instructionIs] <;> rfl) _ encoded answer advice
  rw [withRuntimeAdvice_eq_of_noAdvice _ advice
    (by cases operation <;> rw [instructionIs] <;> rfl)]
  cases operation <;> rw [instructionIs] <;>
    simp only [XorRotation.instruction, XorRotation.value,
      execWithTapeAnswer, execInstr, bind, EStateM.bind, leftRead, rightRead]

end JoltConstraints.Soundness
