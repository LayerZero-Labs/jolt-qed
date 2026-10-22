import JoltConstraints.Soundness.Layer5.LookupWrite
import JoltConstraints.Soundness.Layer4.Word
import JoltConstraints.Soundness.Layer4.Arithmetic

/-! Address alignment and byte, halfword, and word lane-mask rows use the
checked wide sum of the base register and decoded immediate as the lookup index.
At public pin 8bbb2357:
See : jolt/tracer/src/instruction/virtual_align_addr.rs:20-28
See : jolt/tracer/src/instruction/virtual_window_mask_b.rs:20-27
See : jolt/tracer/src/instruction/virtual_window_mask_h.rs:20-31
See : jolt/tracer/src/instruction/virtual_window_mask_w.rs:20-31 -/

set_option autoImplicit false

namespace JoltConstraints.Soundness

open Sail PreSail LeanRV64D.Functions JoltISA

inductive AddressMask where
  | align | byte | halfword | word

def AddressMask.instruction (operation : AddressMask)
    (destination : Dst) (source : Src) (imm : BitVec 64) : Instr :=
  match operation with
  | .align => .VirtualAlignAddr destination source imm
  | .byte => .VirtualWindowMaskB destination source imm
  | .halfword => .VirtualWindowMaskH destination source imm
  | .word => .VirtualWindowMaskW destination source imm

def AddressMask.value (operation : AddressMask) (source imm : BitVec 64) : BitVec 64 :=
  match operation with
  | .align => jolt_virtual_align_addr_value64 source imm
  | .byte => jolt_virtual_window_mask_b_value64 source imm
  | .halfword => jolt_virtual_window_mask_h_value64 source imm
  | .word => jolt_virtual_window_mask_w_value64 source imm

private def AddressMask.table : AddressMask → LookupTableKind
  | .align => .AlignAddr
  | .byte => .WindowMaskB
  | .halfword => .WindowMaskH
  | .word => .WindowMaskW

private theorem masked_low (value : BitVec 128) (mask : Nat)
    (small : mask < 2 ^ 64) :
    (value &&& BitVec.ofNat 128 mask).toNat =
      (value.setWidth 64 &&& BitVec.ofNat 64 mask).toNat := by
  have bounded : value.toNat &&& mask < 2 ^ 64 := Nat.and_lt_two_pow _ small
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (lt_trans small (by norm_num : 2 ^ 64 < 2 ^ 128)),
    Nat.mod_eq_of_lt small, BitVec.toNat_setWidth]
  calc
    value.toNat &&& mask = (value.toNat &&& mask) % 2 ^ 64 :=
      (Nat.mod_eq_of_lt bounded).symm
    _ = value.toNat % 2 ^ 64 &&& mask % 2 ^ 64 := Nat.and_mod_two_pow
    _ = value.toNat % 2 ^ 64 &&& mask := by rw [Nat.mod_eq_of_lt small]

private theorem word_lane_low (value : BitVec 128) :
    ((value >>> 2) &&& (1 : BitVec 128)).toNat =
      (((value.setWidth 64) >>> 2) &&& (1 : BitVec 64)).toNat := by
  simp only [BitVec.toNat_and, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow, BitVec.toNat_setWidth]
  change (value.toNat / 4 &&& 1) = ((value.toNat % 2 ^ 64) / 4 &&& 1)
  rw [Nat.and_one_is_mod, Nat.and_one_is_mod]
  norm_num at *
  omega

variable {F : Type} [Field F] {params : WitnessParams} {witness : WitnessType F params}
  {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
  (charAbove2pow128 : 2 ^ 128 < ringChar F)
  (context : ConstraintContext joltInstance privateInputs params)
  (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
  {t : Fin params.traceLength} {slot : Fin (2 ^ params.logBytecodeK)}
  (selected : bytecodeRa witness slot t = 1)
  {row : JoltInstructionRow} (rowIs : bytecodeRow context.bytecode slot.val = some row)
  (operation : AddressMask) {destination : Dst} {source : Src} {imm : BitVec 64}
  (instructionIs : row.instruction = operation.instruction destination source imm)

include context rowIs instructionIs in
private theorem addressMask_canonical :
    JoltRegisterEncoding.destinationIsCanonical destination = true ∧
    JoltRegisterEncoding.sourceIsCanonical source = true := by
  cases operation <;>
    simpa only [instructionIs, AddressMask.instruction,
      JoltRegisterEncoding.instructionIsCanonical, Bool.and_eq_true] using
      (bytecodeRow_rowOk context rowIs).canonical

include charAbove2pow128 context equations selected rowIs instructionIs

private theorem addressMask_write_value {pre : SailJoltState}
    (agrees : RegisterAgreement witness t pre) :
    witness.RdWriteValue t =
      ((operation.value (sourceValue source pre) imm).toNat : F) := by
  have bound := two_pow_127_lt_char charAbove2pow128
  obtain ⟨left, right⟩ := agrees.immediateInputs bound context equations selected rowIs
    source imm (addressMask_canonical context rowIs operation instructionIs).2
    (by cases operation <;> rw [instructionIs] <;> rfl)
    (by cases operation <;> rw [instructionIs] <;> rfl)
    (by cases operation <;> rw [instructionIs] <;> rfl)
  have writeFlag : witness.OpFlags .WriteLookupOutputToRD t = 1 := by
    have flag := opFlag_of_selected_bytecode bound context equations
      .WriteLookupOutputToRD t slot selected
    cases operation <;>
      simpa only [bytecodeCircuitFlag, rowIs, instructionIs,
        AddressMask.instruction, JoltMetadata.circuitFlag, JoltMetadata.opcodeFlag] using flag
  have active : witness.OpFlags .AddOperands t = 1 := by
    have flag := opFlag_of_selected_bytecode bound context equations .AddOperands t slot selected
    cases operation <;>
      simpa only [bytecodeCircuitFlag, rowIs, instructionIs,
        AddressMask.instruction, JoltMetadata.circuitFlag, JoltMetadata.opcodeFlag] using flag
  have table : (bytecodeRow context.bytecode slot.val).bind
      (fun row => JoltMetadata.lookupTable row.instruction) = some operation.table := by
    cases operation <;>
      simp only [rowIs, Option.bind_some, instructionIs, AddressMask.instruction,
        AddressMask.table, JoltMetadata.lookupTable]
  have raf := instructionRafFlag_one_of_arithmetic bound context equations t (Or.inl active)
  have encoded := rightLookupOperand_add equations.rightLookupAdd t active
    (sourceValue source pre) imm left right
  rw [rdWriteValue_eq_lookupOutput equations.rdWriteEqLookupIfWriteLookupToRd t writeFlag]
  cases operation with
  | align =>
    have output := lookupOutput_alignAddr_of_identity charAbove2pow128 context equations
      t slot selected _ raf encoded table
    simpa only [AddressMask.value, jolt_virtual_align_addr_value64,
      BitVec.setWidth_ofNat_of_le (by decide : 64 ≤ 128)] using output
  | byte =>
    have output := lookupOutput_windowMaskB_of_identity charAbove2pow128 context equations
      t slot selected _ raf encoded table
    have lane := masked_low (BitVec.ofNat 128 (JoltISA.addWide (sourceValue source pre) imm))
      7 (by norm_num : 7 < 2 ^ 64)
    simp only [BitVec.ofNat_eq_ofNat] at output
    rw [lane] at output
    simpa only [AddressMask.value, jolt_virtual_window_mask_b_value64,
      BitVec.setWidth_ofNat_of_le (by decide : 64 ≤ 128)] using output
  | halfword =>
    have output := lookupOutput_windowMaskH_of_identity charAbove2pow128 context equations
      t slot selected _ raf encoded table
    have lane := masked_low (BitVec.ofNat 128 (JoltISA.addWide (sourceValue source pre) imm))
      6 (by norm_num : 6 < 2 ^ 64)
    simp only [BitVec.ofNat_eq_ofNat] at output
    rw [lane] at output
    simpa only [AddressMask.value, jolt_virtual_window_mask_h_value64,
      BitVec.setWidth_ofNat_of_le (by decide : 64 ≤ 128)] using output
  | word =>
    have output := lookupOutput_windowMaskW_of_identity charAbove2pow128 context equations
      t slot selected _ raf encoded table
    have lane := word_lane_low
      (BitVec.ofNat 128 (JoltISA.addWide (sourceValue source pre) imm))
    simp only [BitVec.ofNat_eq_ofNat] at lane output
    rw [lane] at output
    simpa only [AddressMask.value, jolt_virtual_window_mask_w_value64,
      BitVec.setWidth_ofNat_of_le (by decide : 64 ≤ 128)] using output

/-- Alignment and byte/halfword/word masks execute with their constrained values
and preserve register agreement at the next cycle. -/
theorem addressMask_step {pre : SailJoltState}
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
    (addressMask_canonical context rowIs operation instructionIs).2).1
  have encoded := addressMask_write_value charAbove2pow128 context equations
    selected rowIs operation instructionIs agrees
  apply registerWrite_step context equations selected rowIs charAbove2pow128 agrees
    destination (by cases operation <;> rw [instructionIs] <;> rfl) _ encoded answer advice
    (by cases operation <;> rw [instructionIs] <;> rfl)
  cases operation <;> rw [instructionIs] <;>
    simp only [AddressMask.instruction, AddressMask.value,
      execWithTapeAnswer, execInstr, bind, EStateM.bind, sourceRead]

end JoltConstraints.Soundness
