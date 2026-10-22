import JoltConstraints.Soundness.Layer5.LookupWrite
import JoltConstraints.Soundness.Layer4.Word
import JoltConstraints.Soundness.Layer4.Arithmetic

/-! Shared step for unary word operations whose AddOperands flag uses the
source value as the lookup index, without interleaving. The row immediate is ignored by both
the circuit's operand selection and the interpreter.
At public pin 8bbb2357:
See : jolt/tracer/src/instruction/virtual_sign_extend_word.rs:17-24
See : jolt/tracer/src/instruction/virtual_zero_extend_word.rs:17-24
See : jolt/tracer/src/instruction/virtual_pow2.rs:17-24
See : jolt/tracer/src/instruction/virtual_pow2_w.rs:17-24
See : jolt/tracer/src/instruction/virtual_shift_right_bitmask.rs:17-27
See : jolt/tracer/src/instruction/virtual_shift_right_bitmask_w.rs:17-27
See : jolt/tracer/src/instruction/virtual_rev8w.rs:17-32 -/

set_option autoImplicit false

namespace JoltConstraints.Soundness

open Sail PreSail LeanRV64D.Functions JoltISA

/-- Unary word operations whose lookup index is the source value. -/
inductive UnaryWord where
  | signExtend | zeroExtend | pow2 | pow2W | shiftMask | shiftMaskW | rev8w

/-- Construct the selected unary-word instruction. -/
def UnaryWord.instruction (operation : UnaryWord)
    (destination : Dst) (source : Src) (imm : BitVec 64) : Instr :=
  match operation with
  | .signExtend => .VirtualSignExtendWord destination source imm
  | .zeroExtend => .VirtualZeroExtendWord destination source imm
  | .pow2 => .VirtualPow2 destination source imm
  | .pow2W => .VirtualPow2W destination source imm
  | .shiftMask => .VirtualShiftRightBitmask destination source imm
  | .shiftMaskW => .VirtualShiftRightBitmaskW destination source imm
  | .rev8w => .VirtualRev8W destination source imm

/-- Interpreter value of a unary-word instruction. -/
def UnaryWord.value (operation : UnaryWord) (source : BitVec 64) : BitVec 64 :=
  match operation with
  | .signExtend => jolt_virtual_sign_extend_word_value source
  | .zeroExtend => jolt_virtual_zero_extend_word_value source
  | .pow2 => jolt_virtual_pow2_value source
  | .pow2W => jolt_virtual_pow2w_value source
  | .shiftMask => jolt_virtual_shift_right_bitmask_value source
  | .shiftMaskW => jolt_virtual_shift_right_bitmaskw_value source
  | .rev8w => jolt_virtual_rev8w_value source

private def UnaryWord.table : UnaryWord → LookupTableKind
  | .signExtend => .SignExtendWord
  | .zeroExtend => .LowerHalfWord
  | .pow2 => .Pow2
  | .pow2W => .Pow2W
  | .shiftMask => .ShiftRightBitmask
  | .shiftMaskW => .ShiftRightBitmaskW
  | .rev8w => .VirtualRev8W

private theorem append32_eq_add (hi lo : BitVec 32) :
    hi +++ lo = lo.setWidth 64 + (hi.setWidth 64 <<< 32) := by
  apply BitVec.eq_of_toNat_eq
  have hhi := hi.isLt
  have hlo := lo.isLt
  have sumLt : hi.toNat * 2 ^ 32 + lo.toNat < 2 ^ 64 := by omega
  simp only [BitVec.toNat_append, BitVec.toNat_add,
    BitVec.toNat_setWidth_of_le (by norm_num : 32 ≤ 64),
    BitVec.toNat_shiftLeft]
  rw [← Nat.shiftLeft_add_eq_or_of_lt hlo]
  simp only [Nat.shiftLeft_eq]
  omega

private theorem rev8w_eq_kernel (v : BitVec 64) :
    rev8w v = swapBytes32 (v.extractLsb 63 32) +++ swapBytes32 (v.extractLsb 31 0) := by
  simp only [rev8w]
  rw [show v.setWidth 32 = v.extractLsb 31 0 by rfl]
  rw [show (v >>> 32).setWidth 32 = v.extractLsb 63 32 by rfl]
  exact (append32_eq_add _ _).symm

private theorem rev8_32_kernel (x : BitVec 32) : rev8 x = swapBytes32 x := by
  unfold rev8
  simp only [Id.run]
  change IntRange.forIn' _ _ _ >>= _ = _
  unfold IntRange.forIn'
  simp only [Sail.BitVec.length, BitVec.length, Nat.cast_ofNat]
  iterate 5
    rw [IntRange.forIn'.loop]
    simp (config := { decide := true }) only [Membership.mem, dite_true, dite_false, pure_bind,
      bind_pure, Int.reduceAdd, Int.reduceSub, Int.reduceToNat]
  change BitVec.updateSubrange _ _ _ _ = _
  simp only [BitVec.updateSubrange, Sail.BitVec.updateSubrange', Sail.BitVec.extractLsb,
    zeros, swapBytes32, Nat.reduceSub, Nat.reduceAdd]
  apply BitVec.eq_of_getLsbD_eq
  intro i
  simp [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_ushiftRight]
  intro hi
  interval_cases i <;> simp (config := { decide := true }) at *

variable {F : Type} [Field F] {params : WitnessParams} {live : Fin 128 → Prop} {witness : WitnessType F params}
  {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
  (charAbove2pow128 : 2 ^ 128 < ringChar F)
  (context : ConstraintContext joltInstance privateInputs params)
  (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
  {t : Fin params.traceLength} {slot : Fin (2 ^ params.logBytecodeK)}
  (selected : bytecodeRa witness slot t = 1)
  {row : JoltInstructionRow} (rowIs : bytecodeRow context.bytecode slot.val = some row)
  (operation : UnaryWord) {destination : Dst} {source : Src} {imm : BitVec 64}
  (instructionIs : row.instruction = operation.instruction destination source imm)

include context rowIs instructionIs in
private theorem unaryWord_canonical :
    JoltRegisterEncoding.destinationIsCanonical destination = true ∧
    JoltRegisterEncoding.sourceIsCanonical source = true := by
  cases operation <;>
    simpa only [instructionIs, UnaryWord.instruction,
      JoltRegisterEncoding.instructionIsCanonical, Bool.and_eq_true] using
      (bytecodeRow_rowOk context rowIs).canonical

include charAbove2pow128 context equations selected rowIs instructionIs

private theorem unaryWord_inputs {pre : SailJoltState}
    (agrees : RegisterAgreementOn live witness t pre)
    (sourceLive : live (TraceWitness.sourceRegisterAddress source)) :
    witness.LeftInstructionInput t = ((sourceValue source pre).toNat : F) ∧
    witness.RightInstructionInput t = 0 := by
  have sourceRead := agrees.rs1Value (two_pow_127_lt_char charAbove2pow128)
    context equations selected rowIs source
    (unaryWord_canonical context rowIs operation instructionIs).2
    (by cases operation <;> rw [instructionIs] <;> rfl) sourceLive
  have inputs := instructionInputs_of_selected_bytecode
    (two_pow_127_lt_char charAbove2pow128) context equations t slot selected row rowIs
  cases operation <;>
    simpa only [instructionIs, UnaryWord.instruction, JoltMetadata.instructionFlag,
      Bool.false_eq_true, ↓reduceIte, sourceRead, add_zero,
      zero_add] using inputs

private theorem unaryWord_write_value {pre : SailJoltState}
    (agrees : RegisterAgreementOn live witness t pre)
    (sourceLive : live (TraceWitness.sourceRegisterAddress source)) :
    witness.RdWriteValue t =
      ((operation.value (sourceValue source pre)).toNat : F) := by
  have bound := two_pow_127_lt_char charAbove2pow128
  obtain ⟨left, right⟩ := unaryWord_inputs charAbove2pow128 context equations
    selected rowIs operation instructionIs agrees sourceLive
  have writeFlag : witness.OpFlags .WriteLookupOutputToRD t = 1 := by
    have flag := opFlag_of_selected_bytecode bound context equations
      .WriteLookupOutputToRD t slot selected
    cases operation <;>
      simpa only [bytecodeCircuitFlag, rowIs, instructionIs, UnaryWord.instruction,
        JoltMetadata.circuitFlag, JoltMetadata.opcodeFlag] using flag
  have active : witness.OpFlags .AddOperands t = 1 := by
    have flag := opFlag_of_selected_bytecode bound context equations
      .AddOperands t slot selected
    cases operation <;>
      simpa only [bytecodeCircuitFlag, rowIs, instructionIs, UnaryWord.instruction,
        JoltMetadata.circuitFlag, JoltMetadata.opcodeFlag] using flag
  have table : (bytecodeRow context.bytecode slot.val).bind
      (fun row => JoltMetadata.lookupTable row.instruction) = some operation.table := by
    cases operation <;>
      simp only [rowIs, Option.bind_some, instructionIs, UnaryWord.instruction,
        UnaryWord.table, JoltMetadata.lookupTable]
  have raf := instructionRafFlag_one_of_arithmetic bound context equations t (Or.inl active)
  have encoded := rightLookupOperand_add equations.rightLookupAdd t active
    (sourceValue source pre) (0#64) left
    (by simpa only [BitVec.toNat_zero, Nat.cast_zero] using right)
  have sourceBelow128 : (sourceValue source pre).toNat < 2 ^ 128 :=
    lt_trans (sourceValue source pre).isLt (by norm_num)
  rw [rdWriteValue_eq_lookupOutput equations.rdWriteEqLookupIfWriteLookupToRd t writeFlag]
  cases operation with
  | signExtend =>
    have output := lookupOutput_signExtendWord_of_identity charAbove2pow128 context equations
      t slot selected _ raf encoded table
    simpa only [UnaryWord.value, jolt_virtual_sign_extend_word_value,
      JoltISA.addWide, BitVec.toNat_zero, Nat.add_zero, BitVec.setWidth_ofNat_of_le
        (by decide : 32 ≤ 128)] using output
  | zeroExtend =>
    have output := lookupOutput_lowerHalfWord_of_identity charAbove2pow128 context equations
      t slot selected _ raf encoded table
    simpa only [UnaryWord.value, jolt_virtual_zero_extend_word_value,
      JoltISA.addWide, BitVec.toNat_zero, Nat.add_zero, BitVec.setWidth_ofNat_of_le
        (by decide : 32 ≤ 128)] using output
  | pow2 =>
    have output := lookupOutput_pow2_of_identity charAbove2pow128 context equations
      t slot selected _ raf encoded table
    simpa only [UnaryWord.value, jolt_virtual_pow2_value,
      JoltISA.addWide, BitVec.toNat_zero, Nat.zero_mod, Nat.add_zero,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt sourceBelow128,
      BitVec.toNat_setWidth, show 2 ^ 6 = 64 by norm_num] using output
  | pow2W =>
    have output := lookupOutput_pow2W_of_identity charAbove2pow128 context equations
      t slot selected _ raf encoded table
    simpa only [UnaryWord.value, jolt_virtual_pow2w_value,
      JoltISA.addWide, BitVec.toNat_zero, Nat.zero_mod, Nat.add_zero,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt sourceBelow128,
      BitVec.toNat_setWidth, show 2 ^ 5 = 32 by norm_num] using output
  | shiftMask =>
    have output := lookupOutput_shiftRightBitmask_of_identity
      charAbove2pow128 context equations t slot selected _ raf encoded table
    simpa only [UnaryWord.value, jolt_virtual_shift_right_bitmask_value,
      JoltISA.addWide, BitVec.toNat_zero, Nat.zero_mod, Nat.add_zero,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt sourceBelow128,
      BitVec.toNat_setWidth, show 2 ^ 6 = 64 by norm_num] using output
  | shiftMaskW =>
    have output := lookupOutput_shiftRightBitmaskW_of_identity
      charAbove2pow128 context equations t slot selected _ raf encoded table
    simpa only [UnaryWord.value, jolt_virtual_shift_right_bitmaskw_value,
      JoltISA.addWide, BitVec.toNat_zero, Nat.zero_mod, Nat.add_zero,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt sourceBelow128,
      BitVec.toNat_setWidth, show 2 ^ 5 = 32 by norm_num] using output
  | rev8w =>
    have output := lookupOutput_rev8w_of_identity
      charAbove2pow128 context equations t slot selected _ raf encoded table
    have indexEq :
        (BitVec.ofNat 128 (JoltISA.addWide (sourceValue source pre) (0#64))).setWidth 64 =
          sourceValue source pre := by
      simp only [JoltISA.addWide, BitVec.toNat_zero, Nat.add_zero,
        BitVec.ofNat_toNat, BitVec.setWidth_setWidth_of_le _
          (by norm_num : 64 ≤ 128), BitVec.setWidth_eq]
    rw [indexEq] at output
    rw [rev8w_eq_kernel] at output
    simpa only [UnaryWord.value, jolt_virtual_rev8w_value, rev8_32_kernel]
      using output

/-- Seven unary word and mask rows write their
constrained result and preserve register agreement at the next cycle.
The source register must be live, and the destination is added to the live set.
For example, a division row can initialize a dead temporary from live operands. -/
theorem unaryWord_step {pre : SailJoltState}
    (agrees : RegisterAgreementOn live witness t pre)
    (sourceLive : live (TraceWitness.sourceRegisterAddress source))
    (answer : BitVec 64) (advice : row.instruction.RuntimeAdvice) :
    let value := operation.value (sourceValue source pre)
    witness.RdWriteValue t = (value.toNat : F) ∧
    execWithTapeAnswer (row.instruction.withRuntimeAdvice advice) answer pre =
      .ok RETIRE_SUCCESS (afterWriteDst destination value pre) ∧
    ∀ next : t.val + 1 < params.traceLength,
      RegisterAgreementOn
        (fun register => live register ∨ register = TraceWitness.destinationRegisterAddress destination)
        witness ⟨t.val + 1, next⟩ (afterWriteDst destination value pre) := by
  dsimp only
  have sourceRead := (agrees.read source
    (unaryWord_canonical context rowIs operation instructionIs).2 sourceLive).1
  have encoded := unaryWord_write_value charAbove2pow128 context equations
    selected rowIs operation instructionIs agrees sourceLive
  apply registerWriteOn_step context equations selected rowIs charAbove2pow128 agrees
    destination (by cases operation <;> rw [instructionIs] <;> rfl) _ encoded answer advice
  rw [withRuntimeAdvice_eq_of_noAdvice _ advice (by cases operation <;> rw [instructionIs] <;> rfl)]
  cases operation <;> rw [instructionIs] <;>
    simp only [UnaryWord.instruction, UnaryWord.value,
      execWithTapeAnswer, execInstr, bind, EStateM.bind, sourceRead]

end JoltConstraints.Soundness
