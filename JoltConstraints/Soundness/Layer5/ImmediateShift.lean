import JoltConstraints.Soundness.Layer5.LookupWrite
import JoltConstraints.Soundness.Layer4.Shift

/-! Immediate right shifts use a checked bitmask in their bytecode row. The
expansion's `immShiftOk` fact supplies the mask shape required by Layer 4.
At public pin 8bbb2357:
See : jolt/tracer/src/instruction/virtual_srli.rs:20-31
See : jolt/tracer/src/instruction/virtual_srai.rs:20-28
See : jolt/tracer/src/instruction/virtual_srliw.rs:19-27
See : jolt/tracer/src/instruction/virtual_sraiw.rs:19-25 -/

set_option autoImplicit false

namespace JoltConstraints.Soundness

open Sail PreSail LeanRV64D.Functions JoltISA

inductive ImmediateShift where
  | srl | sra | srlw | sraw

def ImmediateShift.instruction (operation : ImmediateShift)
    (destination : Dst) (source : Src) (mask : Nat) : Instr :=
  match operation with
  | .srl => .VirtualSRLI destination source mask
  | .sra => .VirtualSRAI destination source mask
  | .srlw => .VirtualSRLIW destination source mask
  | .sraw => .VirtualSRAIW destination source mask

def ImmediateShift.value (operation : ImmediateShift)
    (source : BitVec 64) (mask : Nat) : BitVec 64 :=
  match operation with
  | .srl => jolt_virtual_srli_value source mask
  | .sra => jolt_virtual_srai_value source mask
  | .srlw => jolt_virtual_srliw_value source mask
  | .sraw => jolt_virtual_sraiw_value source mask

private def ImmediateShift.table : ImmediateShift → LookupTableKind
  | .srl => .VirtualSRL
  | .sra => .VirtualSRA
  | .srlw => .VirtualSRLW
  | .sraw => .VirtualSRAW

private theorem mask64_bits (mask : Nat) (ok : ExpansionFacts.maskOk mask = true) :
    ∀ i < 64, (BitVec.ofNat 64 mask).getLsbD i = decide (ctz mask ≤ i) := by
  simp only [ExpansionFacts.maskOk, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq] at ok
  intro i below
  rw [ok.1, BitVec.getLsbD_ofNat,
    ExpansionFacts.rightShiftMask_testBit _ _ ok.2]
  simp only [ExpansionFacts.ctz_rightShiftMask _ ok.2,
    below, decide_true, Bool.and_true, Bool.true_and]

private theorem mask32_bits (mask : Nat) (ok : ExpansionFacts.wordMaskOk mask = true) :
    ∀ i < 32, (BitVec.ofNat 64 mask).getLsbD i = decide (ctz mask ≤ i) := by
  simp only [ExpansionFacts.wordMaskOk, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq] at ok
  intro i below
  rw [ok.1, BitVec.getLsbD_ofNat,
    ExpansionFacts.wordShiftMask_testBit _ _ ok.2]
  simp only [ExpansionFacts.ctz_wordShiftMask _ ok.2,
    show i < 64 by omega, below, decide_true, Bool.and_true, Bool.true_and]

private theorem mask64_shift_lt (mask : Nat)
    (ok : ExpansionFacts.maskOk mask = true) : ctz mask < 64 := by
  simp only [ExpansionFacts.maskOk, Bool.and_eq_true, decide_eq_true_eq] at ok
  exact ok.2

private theorem mask32_shift_lt (mask : Nat)
    (ok : ExpansionFacts.wordMaskOk mask = true) : ctz mask < 32 := by
  simp only [ExpansionFacts.wordMaskOk, Bool.and_eq_true, decide_eq_true_eq] at ok
  exact ok.2

private theorem wordMask_ne_zero (mask : Nat)
    (ok : ExpansionFacts.wordMaskOk mask = true) : mask ≠ 0 := by
  intro zero
  have falseAtZero : ExpansionFacts.wordMaskOk 0 = false := by
    change ((0 == ExpansionFacts.wordShiftMask (ctz 0)) &&
      decide (ctz 0 < 32)) = false
    rw [show ctz 0 = 0 by unfold ctz; exact if_pos rfl]
    decide
  rw [zero, falseAtZero] at ok
  cases ok

variable {F : Type} [Field F] {params : WitnessParams} {witness : WitnessType F params}
  {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
  (charAbove2pow128 : 2 ^ 128 < ringChar F)
  (context : ConstraintContext joltInstance privateInputs params)
  (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
  {live : Fin 128 → Prop} {t : Fin params.traceLength} {slot : Fin (2 ^ params.logBytecodeK)}
  (selected : bytecodeRa witness slot t = 1)
  {row : JoltInstructionRow} (rowIs : bytecodeRow context.bytecode slot.val = some row)
  (operation : ImmediateShift) {destination : Dst} {source : Src} {mask : Nat}
  (instructionIs : row.instruction = operation.instruction destination source mask)

include context rowIs instructionIs in
private theorem immediateShift_canonical :
    JoltRegisterEncoding.destinationIsCanonical destination = true ∧
    JoltRegisterEncoding.sourceIsCanonical source = true := by
  cases operation <;>
    simpa only [instructionIs, ImmediateShift.instruction,
      JoltRegisterEncoding.instructionIsCanonical, Bool.and_eq_true] using
      (bytecodeRow_rowOk context rowIs).canonical

include charAbove2pow128 context equations selected rowIs instructionIs

private theorem immediateShift_write_value {pre : SailJoltState}
    (agrees : RegisterAgreementOn live witness t pre)
    (sourceLive : live (TraceWitness.sourceRegisterAddress source)) :
    witness.RdWriteValue t =
      ((operation.value (sourceValue source pre) mask).toNat : F) := by
  have bound := two_pow_127_lt_char charAbove2pow128
  obtain ⟨left, right⟩ := agrees.immediateInputs bound context equations selected rowIs
    source (BitVec.ofNat 64 mask)
    (immediateShift_canonical context rowIs operation instructionIs).2
    (by cases operation <;> rw [instructionIs] <;> rfl)
    (by cases operation <;> rw [instructionIs] <;> rfl)
    (by cases operation <;> rw [instructionIs] <;> rfl) sourceLive
  have valid : ExpansionFacts.immShiftOk row.instruction = true :=
    (bytecodeRow_rowOk context rowIs).immShift
  apply lookupWrite_value_of_raf_zero bound context equations selected rowIs
    (sourceValue source pre) (BitVec.ofNat 64 mask) _ operation.table
    (by cases operation <;> rw [instructionIs] <;> rfl)
    (by cases operation <;> rw [instructionIs] <;> rfl)
    (by cases operation <;> rw [instructionIs] <;> rfl)
    left right
  intro raf leftLookup rightLookup table
  cases operation with
  | srl =>
    have ok : ExpansionFacts.maskOk mask = true := by
      simpa only [instructionIs, ImmediateShift.instruction, ExpansionFacts.immShiftOk] using valid
    have output := lookupOutput_srl bound context equations t slot selected
      (sourceValue source pre) (BitVec.ofNat 64 mask) raf leftLookup rightLookup
      table (ctz mask) (mask64_bits mask ok)
    simpa only [ImmediateShift.value, jolt_virtual_srli_value] using output
  | sra =>
    have ok : ExpansionFacts.maskOk mask = true := by
      simpa only [instructionIs, ImmediateShift.instruction, ExpansionFacts.immShiftOk] using valid
    have shiftLt := mask64_shift_lt mask ok
    have output := lookupOutput_sra bound context equations t slot selected
      (sourceValue source pre) (BitVec.ofNat 64 mask) raf leftLookup rightLookup
      table (ctz mask) shiftLt (mask64_bits mask ok)
    simpa only [ImmediateShift.value, jolt_virtual_srai_value] using output
  | srlw =>
    have ok : ExpansionFacts.wordMaskOk mask = true := by
      simpa only [instructionIs, ImmediateShift.instruction, ExpansionFacts.immShiftOk] using valid
    have shiftLt := mask32_shift_lt mask ok
    have output := lookupOutput_srlw bound context equations t slot selected
      (sourceValue source pre) (BitVec.ofNat 64 mask) raf leftLookup rightLookup
      table (ctz mask) shiftLt (mask32_bits mask ok)
    simpa only [ImmediateShift.value, jolt_virtual_srliw_value,
      wordMask_ne_zero mask ok, ↓reduceIte] using output
  | sraw =>
    have ok : ExpansionFacts.wordMaskOk mask = true := by
      simpa only [instructionIs, ImmediateShift.instruction, ExpansionFacts.immShiftOk] using valid
    have shiftLt := mask32_shift_lt mask ok
    have output := lookupOutput_sraw bound context equations t slot selected
      (sourceValue source pre) (BitVec.ofNat 64 mask) raf leftLookup rightLookup
      table (ctz mask) shiftLt (mask32_bits mask ok)
    simpa only [ImmediateShift.value, jolt_virtual_sraiw_value] using output

/-- All four immediate right-shift rows execute with their checked bitmask
result and preserve register agreement at the next cycle.
The source is live; the destination joins the live set after the row.
For example, VirtualSRLI can read a live source and initialize a temporary. -/
theorem immediateShift_step {pre : SailJoltState}
    (agrees : RegisterAgreementOn live witness t pre)
    (sourceLive : live (TraceWitness.sourceRegisterAddress source))
    (answer : BitVec 64) (advice : row.instruction.RuntimeAdvice) :
    let value := operation.value (sourceValue source pre) mask
    witness.RdWriteValue t = (value.toNat : F) ∧
    execWithTapeAnswer (row.instruction.withRuntimeAdvice advice) answer pre =
      .ok RETIRE_SUCCESS (afterWriteDst destination value pre) ∧
    ∀ next : t.val + 1 < params.traceLength,
      RegisterAgreementOn
        (fun register => live register ∨ register = TraceWitness.destinationRegisterAddress destination)
        witness ⟨t.val + 1, next⟩ (afterWriteDst destination value pre) := by
  dsimp only
  have sourceRead := (agrees.read source
    (immediateShift_canonical context rowIs operation instructionIs).2 sourceLive).1
  have encoded := immediateShift_write_value charAbove2pow128 context equations
    selected rowIs operation instructionIs agrees sourceLive
  apply registerWriteOn_step context equations selected rowIs charAbove2pow128 agrees
    destination (by cases operation <;> rw [instructionIs] <;> rfl) _ encoded answer advice
  rw [withRuntimeAdvice_eq_of_noAdvice _ advice
    (by cases operation <;> rw [instructionIs] <;> rfl)]
  cases operation <;> rw [instructionIs] <;>
    simp only [ImmediateShift.instruction, ImmediateShift.value,
      execWithTapeAnswer, execInstr, bind, EStateM.bind, sourceRead]

end JoltConstraints.Soundness
