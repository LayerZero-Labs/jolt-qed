import JoltConstraints.Soundness.Layer5.LookupWrite
import JoltConstraints.Soundness.Layer5.UnaryWord
import JoltConstraints.Soundness.Layer4.Shift

/-! Register-fed right shifts use a mask written by the immediately preceding
VirtualShiftRightBitmask(W) row. The local step below consumes that derived mask
shape; the producer bridge supplies it from the actual prior write.
At public pin 8bbb2357:
See : jolt/tracer/src/instruction/virtual_srl.rs:19-30
See : jolt/tracer/src/instruction/virtual_sra.rs:19-27
See : jolt/tracer/src/instruction/virtual_srlw.rs:19-25
See : jolt/tracer/src/instruction/virtual_sraw.rs:19-25 -/

set_option autoImplicit false

namespace JoltConstraints.Soundness

open Sail PreSail LeanRV64D.Functions JoltISA

/-- The four register-fed right-shift row kinds. -/
inductive RegisterShift where
  | srl | sra | srlw | sraw

/-- Build the row instruction for a right-shift kind. -/
def RegisterShift.instruction (operation : RegisterShift)
    (destination : Dst) (lhs rhs : Src) : Instr :=
  match operation with
  | .srl => .VirtualSRL destination lhs rhs
  | .sra => .VirtualSRA destination lhs rhs
  | .srlw => .VirtualSRLW destination lhs rhs
  | .sraw => .VirtualSRAW destination lhs rhs

/-- Interpreter value of a right-shift row. -/
def RegisterShift.value (operation : RegisterShift) (lhs rhs : BitVec 64) : BitVec 64 :=
  match operation with
  | .srl => jolt_virtual_srl_value lhs rhs
  | .sra => jolt_virtual_sra_value lhs rhs
  | .srlw => jolt_virtual_srlw_value lhs rhs
  | .sraw => jolt_virtual_sraw_value lhs rhs

private def RegisterShift.table : RegisterShift → LookupTableKind
  | .srl => .VirtualSRL
  | .sra => .VirtualSRA
  | .srlw => .VirtualSRLW
  | .sraw => .VirtualSRAW

/-- The mask shape established by the row immediately before a register shift. -/
def RegisterShift.Mask (operation : RegisterShift) (rhs : BitVec 64) : Prop :=
  match operation with
  | .srl | .sra =>
      ∃ s < 64, rhs = BitVec.ofNat 64 (ExpansionFacts.rightShiftMask s)
  | .srlw | .sraw =>
      ∃ s < 32, rhs = BitVec.ofNat 64 (ExpansionFacts.wordShiftMask s)

private theorem rightShiftMask_bits (s : Nat) (sLt : s < 64) :
    ∀ i < 64, (BitVec.ofNat 64 (ExpansionFacts.rightShiftMask s)).getLsbD i =
      decide (s ≤ i) := by
  intro i iLt
  rw [BitVec.getLsbD_ofNat, ExpansionFacts.rightShiftMask_testBit s i sLt]
  simp only [iLt, decide_true, Bool.and_true, Bool.true_and]

private theorem wordShiftMask_bits (s : Nat) (sLt : s < 32) :
    ∀ i < 32, (BitVec.ofNat 64 (ExpansionFacts.wordShiftMask s)).getLsbD i =
      decide (s ≤ i) := by
  intro i iLt
  rw [BitVec.getLsbD_ofNat, ExpansionFacts.wordShiftMask_testBit s i sLt]
  simp only [iLt, show i < 64 by omega, decide_true, Bool.and_true, Bool.true_and]

private theorem rightShiftMask_toNat (s : Nat) (sLt : s < 64) :
    (BitVec.ofNat 64 (ExpansionFacts.rightShiftMask s)).toNat =
      ExpansionFacts.rightShiftMask s := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  apply Nat.lt_pow_two_of_testBit
  intro i iGe
  rw [ExpansionFacts.rightShiftMask_testBit s i sLt]
  simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
  omega

private theorem wordShiftMask_toNat (s : Nat) (sLt : s < 32) :
    (BitVec.ofNat 64 (ExpansionFacts.wordShiftMask s)).toNat =
      ExpansionFacts.wordShiftMask s := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  apply Nat.lt_pow_two_of_testBit
  intro i iGe
  rw [ExpansionFacts.wordShiftMask_testBit s i sLt]
  simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
  omega

variable {F : Type} [Field F] {params : WitnessParams} {live : Fin 128 → Prop}
  {witness : WitnessType F params}
  {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
  (charAbove2pow128 : 2 ^ 128 < ringChar F)
  (context : ConstraintContext joltInstance privateInputs params)
  (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
  {t : Fin params.traceLength} {slot : Fin (2 ^ params.logBytecodeK)}
  (selected : bytecodeRa witness slot t = 1)
  {row : JoltInstructionRow} (rowIs : bytecodeRow context.bytecode slot.val = some row)
  (operation : RegisterShift) {destination : Dst} {lhs rhs : Src}
  (instructionIs : row.instruction = operation.instruction destination lhs rhs)

include context rowIs instructionIs in
private theorem registerShift_canonical :
    (JoltRegisterEncoding.destinationIsCanonical destination = true ∧
      JoltRegisterEncoding.sourceIsCanonical lhs = true) ∧
    JoltRegisterEncoding.sourceIsCanonical rhs = true := by
  cases operation <;>
    simpa only [instructionIs, RegisterShift.instruction,
      JoltRegisterEncoding.instructionIsCanonical, Bool.and_eq_true] using
      (bytecodeRow_rowOk context rowIs).canonical

include charAbove2pow128 context equations selected rowIs instructionIs

private theorem registerShift_write_value {pre : SailJoltState}
    (agrees : RegisterAgreementOn live witness t pre)
    (lhsLive : live (TraceWitness.sourceRegisterAddress lhs))
    (rhsLive : live (TraceWitness.sourceRegisterAddress rhs))
    (mask : operation.Mask (sourceValue rhs pre)) :
    witness.RdWriteValue t =
      ((operation.value (sourceValue lhs pre) (sourceValue rhs pre)).toNat : F) := by
  have bound := two_pow_127_lt_char charAbove2pow128
  have canonical := registerShift_canonical context rowIs operation instructionIs
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
  | srl =>
    obtain ⟨s, sLt, value⟩ := mask
    rw [value] at rightLookup
    have output := lookupOutput_srl bound context equations t slot selected
      (sourceValue lhs pre) (BitVec.ofNat 64 (ExpansionFacts.rightShiftMask s))
      raf leftLookup rightLookup table s (rightShiftMask_bits s sLt)
    simpa only [RegisterShift.value, jolt_virtual_srl_value, value,
      rightShiftMask_toNat s sLt, ExpansionFacts.ctz_rightShiftMask s sLt] using output
  | sra =>
    obtain ⟨s, sLt, value⟩ := mask
    rw [value] at rightLookup
    have output := lookupOutput_sra bound context equations t slot selected
      (sourceValue lhs pre) (BitVec.ofNat 64 (ExpansionFacts.rightShiftMask s))
      raf leftLookup rightLookup table s sLt (rightShiftMask_bits s sLt)
    simpa only [RegisterShift.value, jolt_virtual_sra_value, value,
      rightShiftMask_toNat s sLt, ExpansionFacts.ctz_rightShiftMask s sLt] using output
  | srlw =>
    obtain ⟨s, sLt, value⟩ := mask
    rw [value] at rightLookup
    have output := lookupOutput_srlw bound context equations t slot selected
      (sourceValue lhs pre) (BitVec.ofNat 64 (ExpansionFacts.wordShiftMask s))
      raf leftLookup rightLookup table s sLt (wordShiftMask_bits s sLt)
    simpa only [RegisterShift.value, jolt_virtual_srlw_value, value,
      wordShiftMask_toNat s sLt, ExpansionFacts.ctz_wordShiftMask s sLt] using output
  | sraw =>
    obtain ⟨s, sLt, value⟩ := mask
    rw [value] at rightLookup
    have output := lookupOutput_sraw bound context equations t slot selected
      (sourceValue lhs pre) (BitVec.ofNat 64 (ExpansionFacts.wordShiftMask s))
      raf leftLookup rightLookup table s sLt (wordShiftMask_bits s sLt)
    simpa only [RegisterShift.value, jolt_virtual_sraw_value, value,
      wordShiftMask_toNat s sLt, ExpansionFacts.ctz_wordShiftMask s sLt] using output

/-- A register-fed shift executes with its table-constrained result once its
immediately preceding mask producer has established the mask shape.
Both sources are live; the destination joins the live set after the row.
For example, VirtualSRL reads a live value and a live mask temporary. -/
theorem registerShift_step {pre : SailJoltState}
    (agrees : RegisterAgreementOn live witness t pre)
    (lhsLive : live (TraceWitness.sourceRegisterAddress lhs))
    (rhsLive : live (TraceWitness.sourceRegisterAddress rhs))
    (mask : operation.Mask (sourceValue rhs pre))
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
  have canonical := registerShift_canonical context rowIs operation instructionIs
  have lhsRead := (agrees.read lhs canonical.1.2 lhsLive).1
  have rhsRead := (agrees.read rhs canonical.2 rhsLive).1
  have encoded := registerShift_write_value charAbove2pow128 context equations
    selected rowIs operation instructionIs agrees lhsLive rhsLive mask
  apply registerWriteOn_step context equations selected rowIs charAbove2pow128 agrees
    destination (by cases operation <;> rw [instructionIs] <;> rfl) _ encoded answer advice
  rw [withRuntimeAdvice_eq_of_noAdvice _ advice
    (by cases operation <;> rw [instructionIs] <;> rfl)]
  cases operation <;> rw [instructionIs] <;>
    simp only [RegisterShift.instruction, RegisterShift.value,
      execWithTapeAnswer, execInstr, bind, EStateM.bind, lhsRead, rhsRead]

omit [Field F] charAbove2pow128 context equations selected rowIs instructionIs in
/-- The 64-bit mask-producing write gives both SRL and SRA their required
mask shape in its concrete post-state. -/
theorem registerShift_mask64_after_producer (written : JoltISA.VReg)
    (producerSource : Src) (pre : SailJoltState) :
    RegisterShift.srl.Mask (sourceValue (.vreg written)
      (afterWriteDst (.vreg written)
        (jolt_virtual_shift_right_bitmask_value (sourceValue producerSource pre)) pre)) ∧
    RegisterShift.sra.Mask (sourceValue (.vreg written)
      (afterWriteDst (.vreg written)
        (jolt_virtual_shift_right_bitmask_value (sourceValue producerSource pre)) pre)) := by
  have shape : sourceValue (.vreg written)
      (afterWriteDst (.vreg written)
        (jolt_virtual_shift_right_bitmask_value (sourceValue producerSource pre)) pre) =
      BitVec.ofNat 64 (ExpansionFacts.rightShiftMask
        ((sourceValue producerSource pre).setWidth 6).toNat) := by
    change (if written = written then
        jolt_virtual_shift_right_bitmask_value (sourceValue producerSource pre)
      else pre.vregs written) = _
    simp only [ite_true, jolt_virtual_shift_right_bitmask_value,
      ExpansionFacts.rightShiftMask]
  constructor <;>
    exact ⟨_, ((sourceValue producerSource pre).setWidth 6).isLt, shape⟩

omit [Field F] charAbove2pow128 context equations selected rowIs instructionIs in
/-- The word mask-producing write gives both SRLW and SRAW their required
mask shape in its concrete post-state. -/
theorem registerShift_mask32_after_producer (written : JoltISA.VReg)
    (producerSource : Src) (pre : SailJoltState) :
    RegisterShift.srlw.Mask (sourceValue (.vreg written)
      (afterWriteDst (.vreg written)
        (jolt_virtual_shift_right_bitmaskw_value (sourceValue producerSource pre)) pre)) ∧
    RegisterShift.sraw.Mask (sourceValue (.vreg written)
      (afterWriteDst (.vreg written)
        (jolt_virtual_shift_right_bitmaskw_value (sourceValue producerSource pre)) pre)) := by
  have shape : sourceValue (.vreg written)
      (afterWriteDst (.vreg written)
        (jolt_virtual_shift_right_bitmaskw_value (sourceValue producerSource pre)) pre) =
      BitVec.ofNat 64 (ExpansionFacts.wordShiftMask
        ((sourceValue producerSource pre).setWidth 5).toNat) := by
    change (if written = written then
        jolt_virtual_shift_right_bitmaskw_value (sourceValue producerSource pre)
      else pre.vregs written) = _
    simp only [ite_true, jolt_virtual_shift_right_bitmaskw_value,
      ExpansionFacts.wordShiftMask, Nat.one_shiftLeft]
  constructor <;>
    exact ⟨_, ((sourceValue producerSource pre).setWidth 5).isLt, shape⟩

omit [Field F] charAbove2pow128 context equations selected rowIs instructionIs in
/-- An expansion's adjacent producer/shift pairing supplies the exact mask
shape required by `registerShift_step`, from the producer's concrete write. -/
theorem registerShift_mask_after_producer (producer : UnaryWord)
    (written : JoltISA.VReg) (producerSource : Src) (producerImm : BitVec 64)
    (destination : Dst) (lhs : Src) (operation : RegisterShift)
    (fed : ExpansionFacts.masksFed
      (producer.instruction (.vreg written) producerSource producerImm)
      (operation.instruction destination lhs (.vreg written)) = true)
    (pre : SailJoltState) :
    operation.Mask (sourceValue (.vreg written)
      (afterWriteDst (.vreg written) (producer.value (sourceValue producerSource pre)) pre)) := by
  cases producer with
  | shiftMask =>
    cases operation with
    | srl => exact (registerShift_mask64_after_producer written producerSource pre).1
    | sra => exact (registerShift_mask64_after_producer written producerSource pre).2
    | srlw => simp only [ExpansionFacts.masksFed, UnaryWord.instruction,
        RegisterShift.instruction, Bool.false_eq_true] at fed
    | sraw => simp only [ExpansionFacts.masksFed, UnaryWord.instruction,
        RegisterShift.instruction, Bool.false_eq_true] at fed
  | shiftMaskW =>
    cases operation with
    | srl => simp only [ExpansionFacts.masksFed, UnaryWord.instruction,
        RegisterShift.instruction, Bool.false_eq_true] at fed
    | sra => simp only [ExpansionFacts.masksFed, UnaryWord.instruction,
        RegisterShift.instruction, Bool.false_eq_true] at fed
    | srlw => exact (registerShift_mask32_after_producer written producerSource pre).1
    | sraw => exact (registerShift_mask32_after_producer written producerSource pre).2
  | signExtend => cases operation <;> simp only [ExpansionFacts.masksFed,
      UnaryWord.instruction, RegisterShift.instruction, Bool.false_eq_true] at fed
  | zeroExtend => cases operation <;> simp only [ExpansionFacts.masksFed,
      UnaryWord.instruction, RegisterShift.instruction, Bool.false_eq_true] at fed
  | pow2 => cases operation <;> simp only [ExpansionFacts.masksFed,
      UnaryWord.instruction, RegisterShift.instruction, Bool.false_eq_true] at fed
  | pow2W => cases operation <;> simp only [ExpansionFacts.masksFed,
      UnaryWord.instruction, RegisterShift.instruction, Bool.false_eq_true] at fed
  | rev8w => cases operation <;> simp only [ExpansionFacts.masksFed,
      UnaryWord.instruction, RegisterShift.instruction, Bool.false_eq_true] at fed

/-- Apply the shift step directly after its paired mask producer, using the
post-state supplied by the producer step. No mask-shape assumption is added.
The producer adds its written mask register to the live set, so the shift
can read it without an extra liveness premise.
For example, VirtualShiftRightBitmask can feed VirtualSRL through one live temporary. -/
theorem registerShift_step_after_producer (producer : UnaryWord)
    (written : JoltISA.VReg) (producerSource : Src) (producerImm : BitVec 64)
    (rhsIs : rhs = .vreg written)
    (fed : ExpansionFacts.masksFed
      (producer.instruction (.vreg written) producerSource producerImm)
      (operation.instruction destination lhs rhs) = true)
    (before : SailJoltState)
    (agrees : RegisterAgreementOn
      (fun register => live register ∨
        register = TraceWitness.destinationRegisterAddress (.vreg written)) witness t
      (afterWriteDst (.vreg written) (producer.value (sourceValue producerSource before)) before))
    (lhsLive : live (TraceWitness.sourceRegisterAddress lhs) ∨
      TraceWitness.sourceRegisterAddress lhs =
        TraceWitness.destinationRegisterAddress (.vreg written))
    (answer : BitVec 64) (advice : row.instruction.RuntimeAdvice) :
    let pre := afterWriteDst (.vreg written)
      (producer.value (sourceValue producerSource before)) before
    let value := operation.value (sourceValue lhs pre) (sourceValue rhs pre)
    witness.RdWriteValue t = (value.toNat : F) ∧
    execWithTapeAnswer (row.instruction.withRuntimeAdvice advice) answer pre =
      .ok RETIRE_SUCCESS (afterWriteDst destination value pre) ∧
    ∀ next : t.val + 1 < params.traceLength,
      RegisterAgreementOn
        (fun register => (live register ∨
          register = TraceWitness.destinationRegisterAddress (.vreg written)) ∨
          register = TraceWitness.destinationRegisterAddress destination)
        witness ⟨t.val + 1, next⟩ (afterWriteDst destination value pre) := by
  subst rhs
  have mask := registerShift_mask_after_producer producer written producerSource
    producerImm destination lhs operation fed before
  have rhsLive : (fun register => live register ∨
      register = TraceWitness.destinationRegisterAddress (.vreg written))
      (TraceWitness.sourceRegisterAddress (.vreg written)) := Or.inr rfl
  exact registerShift_step charAbove2pow128 context equations selected rowIs
    operation instructionIs agrees lhsLive rhsLive mask answer advice

end JoltConstraints.Soundness
