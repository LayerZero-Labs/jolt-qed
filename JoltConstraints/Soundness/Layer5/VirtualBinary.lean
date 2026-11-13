import JoltConstraints.Soundness.Layer5.LookupWrite
import JoltConstraints.Soundness.Layer4.Pext
import JoltConstraints.Soundness.Layer4.Conditional
import JoltConstraints.Soundness.Layer5.MemoryAddress

open LeanRV64D

/-! Shared step for extraction, store-lane shifting and conditional negation.
Their existing interleaved table rules give the interpreter value for arbitrary
source words, so no lane-mask shape is assumed by these row proofs.
At public pin 8bbb2357:
See : jolt/tracer/src/instruction/virtual_pext.rs:18-26
See : jolt/tracer/src/instruction/virtual_pext_signed.rs:17-70
See : jolt/tracer/src/instruction/virtual_negate_if.rs:17-32
ShiftData uses address plus signed immediate at c6703570:
`tracer/src/instruction/virtual_shift_data_{b,h,w}.rs` (`VirtualShiftDataB/H/W::exec`). -/

set_option autoImplicit false

namespace JoltConstraints.Soundness

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail LeanRV64D LeanRV64D.Functions JoltISA

/-- Extraction and conditional-negation operations, and lane shifts carrying
their signed address immediate; for example, `shiftDataH 2` shifts using address + 2. -/
inductive VirtualBinary where
  | pext | pextSigned | negateIf
  | shiftDataB (imm : BitVec 64)
  | shiftDataH (imm : BitVec 64)
  | shiftDataW (imm : BitVec 64)

/-- Build the selected virtual row; for example, `shiftDataB 2` builds a
VirtualShiftDataB that adds immediate 2 to its second register operand. -/
def VirtualBinary.instruction (operation : VirtualBinary)
    (destination : Dst) (lhs rhs : Src) : Instr :=
  match operation with
  | .pext => .VirtualPext destination lhs rhs
  | .pextSigned => .VirtualPextSigned destination lhs rhs
  | .shiftDataB imm => .VirtualShiftDataB destination lhs rhs imm
  | .shiftDataH imm => .VirtualShiftDataH destination lhs rhs imm
  | .shiftDataW imm => .VirtualShiftDataW destination lhs rhs imm
  | .negateIf => .VirtualNegateIf destination lhs rhs

/-- Compute the row's result from its two register values.
For example, `shiftDataB 1` with value 1 and address 0 produces 256. -/
def VirtualBinary.value (operation : VirtualBinary) (lhs rhs : BitVec 64) : BitVec 64 :=
  match operation with
  | .pext => jolt_virtual_pext_value lhs rhs
  | .pextSigned => jolt_virtual_pext_signed_value lhs rhs
  | .shiftDataB imm => jolt_virtual_shift_data_b_value lhs (rhs + imm)
  | .shiftDataH imm => jolt_virtual_shift_data_h_value lhs (rhs + imm)
  | .shiftDataW imm => jolt_virtual_shift_data_w_value lhs (rhs + imm)
  | .negateIf => jolt_virtual_negate_if_value lhs rhs

/-- The operation's lookup table; for example, `shiftDataH 2` uses ShiftDataH. -/
private def VirtualBinary.table : VirtualBinary → LookupTableKind
  | .pext => .Pext
  | .pextSigned => .PextSigned
  | .shiftDataB _ => .ShiftDataB
  | .shiftDataH _ => .ShiftDataH
  | .shiftDataW _ => .ShiftDataW
  | .negateIf => .VirtualNegateIf

/-- The immediate added to the second register, or zero for extraction and
negation; for example, `shiftDataW 4` adds 4 to the address. -/
private def VirtualBinary.offset : VirtualBinary → BitVec 64
  | .shiftDataB imm | .shiftDataH imm | .shiftDataW imm => imm
  | _ => 0

variable {F : Type} [Field F] {params : WitnessParams} {live : Fin 128 → Prop} {witness : WitnessType F params}
  {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
  (charAbove2pow128Minus2pow64 : 2 ^ 128 - 2 ^ 64 < ringChar F)
  (context : ConstraintContext joltInstance privateInputs params)
  (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
  {t : Fin params.traceLength} {slot : Fin (2 ^ params.logBytecodeK)}
  (selected : bytecodeRa witness slot t = 1)
  {row : JoltInstructionRow} (rowIs : bytecodeRow context.bytecode slot.val = some row)
  (operation : VirtualBinary) {destination : Dst} {lhs rhs : Src}
  (instructionIs : row.instruction = operation.instruction destination lhs rhs)

include context rowIs instructionIs in
/-- The selected virtual row has canonical destination and source registers;
for example, architectural x1 and temporary 41 use valid register indices. -/
private theorem virtualBinary_canonical :
    (JoltRegisterEncoding.destinationIsCanonical destination = true ∧
      JoltRegisterEncoding.sourceIsCanonical lhs = true) ∧
    JoltRegisterEncoding.sourceIsCanonical rhs = true := by
  cases operation <;>
    simpa only [instructionIs, VirtualBinary.instruction,
      JoltRegisterEncoding.instructionIsCanonical, Bool.and_eq_true] using
      (bytecodeRow_rowOk context rowIs).canonical

include charAbove2pow128Minus2pow64 context equations selected rowIs instructionIs

/-- The virtual row's inputs encode its first register and its second register
plus the signed address immediate (zero for extraction and negation).
The interleaved lookup bounds the latter as a 64-bit word, so no new no-wrap
premise is needed; for example, address 8 plus immediate -2 encodes 6. -/
private theorem virtualBinary_inputs {pre : SailJoltState}
    (agrees : RegisterAgreementOn live witness t pre)
    (leftLive : live (TraceWitness.sourceRegisterAddress lhs))
    (rightLive : live (TraceWitness.sourceRegisterAddress rhs)) :
    witness.LeftInstructionInput t = ((sourceValue lhs pre).toNat : F) ∧
    witness.RightInstructionInput t =
      ((sourceValue rhs pre + operation.offset).toNat : F) := by
  have bound := two_pow_127_lt_char charAbove2pow128Minus2pow64
  have canonical := virtualBinary_canonical context rowIs operation instructionIs
  have sourceLeft := agrees.rs1Value bound context equations selected rowIs lhs
    canonical.1.2 (by cases operation <;> rw [instructionIs] <;> rfl) leftLive
  have sourceRight := agrees.rs2Value bound context equations selected rowIs rhs
    canonical.2 (by cases operation <;> rw [instructionIs] <;> rfl) rightLive
  have inputs := instructionInputs_of_selected_bytecode bound context equations t slot selected _ rowIs
  have immediate := imm_of_selected_bytecode bound context equations t slot selected
  have left : witness.LeftInstructionInput t = ((sourceValue lhs pre).toNat : F) := by
    cases operation <;> simpa only [instructionIs, VirtualBinary.instruction,
      JoltMetadata.instructionFlag, Bool.false_eq_true, ↓reduceIte, add_zero,
      sourceLeft] using inputs.1
  have rightSum : witness.RightInstructionInput t =
      ((((sourceValue rhs pre).toNat : Int) + operation.offset.toInt : Int) : F) := by
    cases operation <;>
      simp only [bytecodeImmediate, rowIs, instructionIs, VirtualBinary.instruction,
        JoltMetadata.immediate] at immediate <;>
      simpa [instructionIs, VirtualBinary.instruction, VirtualBinary.offset,
        JoltMetadata.instructionFlag, sourceRight, immediate] using inputs.2
  have raf : witness.InstructionRafFlag t = 0 := by
    rw [instructionRafFlag_of_selected_bytecode bound context equations t slot selected]
    cases operation <;> simp [bytecodeRafFlag, rowIs, instructionIs,
      VirtualBinary.instruction, JoltMetadata.instructionRafFlag, JoltMetadata.opcodeFlag]
  have operand := (lookupOperands_eq_inputs_of_raf_zero bound context equations t raf).2
  obtain ⟨address, addressSelected, _⟩ := instructionLookupRa_unique bound context equations t
  have encoded := rightLookupOperand_of_selected bound context equations t address addressSelected
  have sumWord : sourceValue rhs pre + operation.offset = (uninterleave address).2 := by
    apply word_add_eq_of_field_sum bound
    simpa only [raf, sub_zero, one_mul, zero_mul, add_zero,
      lookupAddressRight_eq_uninterleave, operand, rightSum] using encoded
  have right : witness.RightInstructionInput t =
      ((sourceValue rhs pre + operation.offset).toNat : F) := by
    rw [sumWord]
    simpa only [raf, sub_zero, one_mul, zero_mul, add_zero,
      lookupAddressRight_eq_uninterleave, operand] using encoded
  exact ⟨left, right⟩

/-- The lookup fixes the virtual row's destination value, including its signed
address immediate; for example, shifting byte 1 at address 0 with immediate 1 writes 256. -/
private theorem virtualBinary_write_value {pre : SailJoltState}
    (agrees : RegisterAgreementOn live witness t pre)
    (leftLive : live (TraceWitness.sourceRegisterAddress lhs))
    (rightLive : live (TraceWitness.sourceRegisterAddress rhs)) :
    witness.RdWriteValue t =
      ((operation.value (sourceValue lhs pre) (sourceValue rhs pre)).toNat : F) := by
  have bound := two_pow_127_lt_char charAbove2pow128Minus2pow64
  obtain ⟨left, right⟩ := virtualBinary_inputs charAbove2pow128Minus2pow64 context equations
    selected rowIs operation instructionIs agrees leftLive rightLive
  apply lookupWrite_value_of_raf_zero bound context equations selected rowIs
    (sourceValue lhs pre) (sourceValue rhs pre + operation.offset) _ operation.table
    (by cases operation <;> rw [instructionIs] <;> rfl)
    (by cases operation <;> rw [instructionIs] <;> rfl)
    (by cases operation <;> rw [instructionIs] <;> rfl)
    left right
  intro raf leftLookup rightLookup table
  cases operation <;> simp only [VirtualBinary.offset, add_zero] at rightLookup
  case pext =>
    simpa only [VirtualBinary.value, VirtualBinary.offset, add_zero] using
      lookupOutput_pext bound context equations t slot selected
      (sourceValue lhs pre) (sourceValue rhs pre) raf leftLookup rightLookup table
  case pextSigned =>
    simpa only [VirtualBinary.value, VirtualBinary.offset, add_zero] using
      lookupOutput_pextSigned bound context equations t slot selected
      (sourceValue lhs pre) (sourceValue rhs pre) raf leftLookup rightLookup table
  case shiftDataB imm =>
    simpa only [VirtualBinary.value, VirtualBinary.offset, add_zero] using
      lookupOutput_shiftDataB bound context equations t slot selected
      (sourceValue lhs pre) (sourceValue rhs pre + imm) raf leftLookup rightLookup table
  case shiftDataH imm =>
    simpa only [VirtualBinary.value, VirtualBinary.offset, add_zero] using
      lookupOutput_shiftDataH bound context equations t slot selected
      (sourceValue lhs pre) (sourceValue rhs pre + imm) raf leftLookup rightLookup table
  case shiftDataW imm =>
    simpa only [VirtualBinary.value, VirtualBinary.offset, add_zero] using
      lookupOutput_shiftDataW bound context equations t slot selected
      (sourceValue lhs pre) (sourceValue rhs pre + imm) raf leftLookup rightLookup table
  case negateIf =>
    simpa only [VirtualBinary.value, VirtualBinary.offset, add_zero, jolt_virtual_negate_if_value] using
      (lookupOutput_negateIf bound context equations t slot selected
        (sourceValue lhs pre) (sourceValue rhs pre) raf
        leftLookup rightLookup table)

/-- These six virtual rows execute with their table-constrained result and
preserve register agreement at the next cycle.
The source registers must be live, and the destination is added to the live set.
ShiftData's second register is an address to which its signed immediate is added.
For example, shifting byte 1 at address 0 with immediate 1 writes 256 to the destination. -/
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
  have encoded := virtualBinary_write_value charAbove2pow128Minus2pow64 context equations selected rowIs
    operation instructionIs agrees leftLive rightLive
  apply registerWriteOn_step context equations selected rowIs charAbove2pow128Minus2pow64 agrees
    destination (by cases operation <;> rw [instructionIs] <;> rfl) _ encoded answer advice
  rw [withRuntimeAdvice_eq_of_noAdvice _ advice (by cases operation <;> rw [instructionIs] <;> rfl)]
  cases operation <;> rw [instructionIs] <;>
    simp only [VirtualBinary.instruction, VirtualBinary.value,
      execWithTapeAnswer, execInstr, bind, EStateM.bind, leftRead, rightRead]

end JoltConstraints.Soundness
