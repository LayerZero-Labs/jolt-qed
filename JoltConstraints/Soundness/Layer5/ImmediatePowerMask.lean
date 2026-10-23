import JoltConstraints.Soundness.Layer5.LookupWrite
import JoltConstraints.Soundness.Layer4.Word
import JoltConstraints.Soundness.Layer4.Arithmetic

/-! Immediate powers of two and right-shift masks use a zero left arithmetic
input and the normalized 64-bit immediate as the right input.
At public pin 8bbb2357:
See : jolt/tracer/src/instruction/virtual_pow2i.rs:17-21
See : jolt/tracer/src/instruction/virtual_pow2i_w.rs:17-21
See : jolt/tracer/src/instruction/virtual_shift_right_bitmaski.rs:17-27 -/

set_option autoImplicit false

namespace JoltConstraints.Soundness

open Sail PreSail LeanRV64D.Functions JoltISA

inductive ImmediatePowerMask where
  | pow2I | pow2IW | shiftMaskI

def ImmediatePowerMask.instruction (operation : ImmediatePowerMask)
    (destination : Dst) (imm : Nat) : Instr :=
  match operation with
  | .pow2I => .VirtualPow2I destination imm
  | .pow2IW => .VirtualPow2IW destination imm
  | .shiftMaskI => .VirtualShiftRightBitmaskI destination imm

def ImmediatePowerMask.value (operation : ImmediatePowerMask) (imm : Nat) : BitVec 64 :=
  match operation with
  | .pow2I => jolt_virtual_pow2i_value imm
  | .pow2IW => jolt_virtual_pow2iw_value imm
  | .shiftMaskI => jolt_virtual_shift_right_bitmaski_value imm

private def ImmediatePowerMask.table : ImmediatePowerMask → LookupTableKind
  | .pow2I => .Pow2
  | .pow2IW => .Pow2W
  | .shiftMaskI => .ShiftRightBitmask

private theorem normalized_mod (imm modulus : Nat) (divides : modulus ∣ 2 ^ 64) :
    (BitVec.ofNat 64 imm).toNat % modulus = imm % modulus := by
  simpa only [BitVec.toNat_ofNat] using Nat.mod_mod_of_dvd imm divides

private theorem index_mod (imm modulus : Nat) (divides : modulus ∣ 2 ^ 64) :
    (BitVec.ofNat 128 (JoltISA.addWide (0#64) (BitVec.ofNat 64 imm))).toNat % modulus =
      imm % modulus := by
  have small : (BitVec.ofNat 64 imm).toNat < 2 ^ 128 :=
    lt_trans (BitVec.ofNat 64 imm).isLt (by norm_num)
  change (JoltISA.addWide (0#64) (BitVec.ofNat 64 imm) % 2 ^ 128) % modulus =
    imm % modulus
  rw [JoltISA.addWide, BitVec.toNat_zero, Nat.zero_add,
    Nat.mod_eq_of_lt small]
  exact normalized_mod imm modulus divides

variable {F : Type} [Field F] {params : WitnessParams} {live : Fin 128 → Prop} {witness : WitnessType F params}
  {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
  (charAbove2pow128 : 2 ^ 128 < ringChar F)
  (context : ConstraintContext joltInstance privateInputs params)
  (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
  {t : Fin params.traceLength} {slot : Fin (2 ^ params.logBytecodeK)}
  (selected : bytecodeRa witness slot t = 1)
  {row : JoltInstructionRow} (rowIs : bytecodeRow context.bytecode slot.val = some row)
  (operation : ImmediatePowerMask) {destination : Dst} {imm : Nat}
  (instructionIs : row.instruction = operation.instruction destination imm)

include context rowIs instructionIs in
private theorem immediatePowerMask_canonical :
    JoltRegisterEncoding.destinationIsCanonical destination = true := by
  cases operation <;>
    simpa only [instructionIs, ImmediatePowerMask.instruction,
      JoltRegisterEncoding.instructionIsCanonical] using
      (bytecodeRow_rowOk context rowIs).canonical

include charAbove2pow128 context equations selected rowIs instructionIs

private theorem immediatePowerMask_write_value :
    witness.RdWriteValue t = ((operation.value imm).toNat : F) := by
  have bound := two_pow_127_lt_char charAbove2pow128
  have normalized : witness.Imm t = (((BitVec.ofNat 64 imm).toNat : Nat) : F) := by
    have fact := imm_of_selected_bytecode bound context equations t slot selected
    cases operation <;>
      simpa only [bytecodeImmediate, rowIs, instructionIs,
        ImmediatePowerMask.instruction, JoltMetadata.immediate,
        Int.cast_natCast] using fact
  have inputs := instructionInputs_of_selected_bytecode bound context equations
    t slot selected row rowIs
  have left : witness.LeftInstructionInput t = (0 : F) := by
    cases operation <;>
      simpa only [instructionIs, ImmediatePowerMask.instruction,
        JoltMetadata.instructionFlag, Bool.false_eq_true,
        ↓reduceIte, add_zero, zero_add] using inputs.1
  have right : witness.RightInstructionInput t =
      ((BitVec.ofNat 64 imm).toNat : F) := by
    cases operation <;>
      simpa only [instructionIs, ImmediatePowerMask.instruction,
        JoltMetadata.instructionFlag, Bool.false_eq_true,
        ↓reduceIte, add_zero, zero_add, normalized] using inputs.2
  have writeFlag : witness.OpFlags .WriteLookupOutputToRD t = 1 := by
    have flag := opFlag_of_selected_bytecode bound context equations
      .WriteLookupOutputToRD t slot selected
    cases operation <;>
      simpa only [bytecodeCircuitFlag, rowIs, instructionIs,
        ImmediatePowerMask.instruction, JoltMetadata.circuitFlag,
        JoltMetadata.opcodeFlag] using flag
  have active : witness.OpFlags .AddOperands t = 1 := by
    have flag := opFlag_of_selected_bytecode bound context equations
      .AddOperands t slot selected
    cases operation <;>
      simpa only [bytecodeCircuitFlag, rowIs, instructionIs,
        ImmediatePowerMask.instruction, JoltMetadata.circuitFlag,
        JoltMetadata.opcodeFlag] using flag
  have table : (bytecodeRow context.bytecode slot.val).bind
      (fun row => JoltMetadata.lookupTable row.instruction) = some operation.table := by
    cases operation <;>
      simp only [rowIs, Option.bind_some, instructionIs,
        ImmediatePowerMask.instruction, ImmediatePowerMask.table, JoltMetadata.lookupTable]
  have raf := instructionRafFlag_one_of_arithmetic bound context equations t (Or.inl active)
  have encoded := rightLookupOperand_add equations.rightLookupAdd t active
    (0#64) (BitVec.ofNat 64 imm)
    (by simpa only [BitVec.toNat_zero, Nat.cast_zero] using left) right
  rw [rdWriteValue_eq_lookupOutput equations.rdWriteEqLookupIfWriteLookupToRd t writeFlag]
  cases operation with
  | pow2I =>
    have output := lookupOutput_pow2_of_identity charAbove2pow128 context equations
      t slot selected _ raf encoded table
    simpa only [ImmediatePowerMask.value, jolt_virtual_pow2i_value,
      index_mod imm 64 (by norm_num : 64 ∣ 2 ^ 64)] using output
  | pow2IW =>
    have output := lookupOutput_pow2W_of_identity charAbove2pow128 context equations
      t slot selected _ raf encoded table
    simpa only [ImmediatePowerMask.value, jolt_virtual_pow2iw_value,
      index_mod imm 32 (by norm_num : 32 ∣ 2 ^ 64)] using output
  | shiftMaskI =>
    have output := lookupOutput_shiftRightBitmask_of_identity
      charAbove2pow128 context equations t slot selected _ raf encoded table
    simpa only [ImmediatePowerMask.value, jolt_virtual_shift_right_bitmaski_value,
      index_mod imm 64 (by norm_num : 64 ∣ 2 ^ 64)] using output

/-- Three immediate-only rows execute with their constrained values and
preserve agreement on the live registers and the destination.
For example, VirtualPow2I can initialize a previously uninitialized temporary. -/
theorem immediatePowerMask_step {pre : SailJoltState}
    (agrees : RegisterAgreementOn live witness t pre)
    (answer : BitVec 64) (advice : row.instruction.RuntimeAdvice) :
    let value := operation.value imm
    witness.RdWriteValue t = (value.toNat : F) ∧
    execWithTapeAnswer (row.instruction.withRuntimeAdvice advice) answer pre =
      .ok RETIRE_SUCCESS (afterWriteDst destination value pre) ∧
    ∀ next : t.val + 1 < params.traceLength,
      RegisterAgreementOn
        (fun register => live register ∨ register = TraceWitness.destinationRegisterAddress destination)
        witness ⟨t.val + 1, next⟩ (afterWriteDst destination value pre) := by
  dsimp only
  have encoded := immediatePowerMask_write_value charAbove2pow128 context equations
    selected rowIs operation instructionIs
  apply registerWriteOn_step context equations selected rowIs charAbove2pow128 agrees
    destination (by cases operation <;> rw [instructionIs] <;> rfl) _ encoded answer advice
  rw [withRuntimeAdvice_eq_of_noAdvice _ advice
    (by cases operation <;> rw [instructionIs] <;> rfl)]
  cases operation <;> rw [instructionIs] <;>
    simp only [ImmediatePowerMask.instruction, ImmediatePowerMask.value,
      execWithTapeAnswer, execInstr, bind, EStateM.bind]

end JoltConstraints.Soundness
