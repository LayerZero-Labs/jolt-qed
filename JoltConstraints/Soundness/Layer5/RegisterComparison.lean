import JoltConstraints.Soundness.Layer5.LookupWrite
import JoltConstraints.Soundness.Layer4.Comparison

/-! Shared step for signed and unsigned register comparisons. Both tables
return the exact 0/1 word written by the instruction interpreter.
At public pin 8bbb2357:
See : jolt/tracer/src/instruction/slt.rs:17-27
See : jolt/tracer/src/instruction/sltu.rs:17-29 -/

set_option autoImplicit false

namespace JoltConstraints.Soundness

open Sail PreSail LeanRV64D.Functions JoltISA

/-- Signed and unsigned two-register comparison rows. -/
inductive RegisterComparison where
  | signed | unsigned

/-- Construct the selected comparison instruction. -/
def RegisterComparison.instruction (operation : RegisterComparison)
    (destination : Dst) (lhs rhs : Src) : Instr :=
  match operation with
  | .signed => .SLT destination lhs rhs
  | .unsigned => .SLTU destination lhs rhs

/-- Interpreter value of a comparison instruction. -/
def RegisterComparison.value (operation : RegisterComparison)
    (lhs rhs : BitVec 64) : BitVec 64 :=
  match operation with
  | .signed => jolt_slt_value lhs rhs
  | .unsigned => jolt_sltu_value lhs rhs

private def RegisterComparison.table : RegisterComparison → LookupTableKind
  | .signed => .SignedLessThan
  | .unsigned => .UnsignedLessThan

theorem slt_value_eq (lhs rhs : BitVec 64) :
    jolt_slt_value lhs rhs = if lhs.toInt < rhs.toInt then 1 else 0 := by
  unfold jolt_slt_value zopz0zI_s bool_to_bit bool_bit_forwards
    zero_extend Sail.BitVec.zeroExtend
  by_cases smaller : lhs.toInt < rhs.toInt <;>
    simp only [smaller, decide_true, decide_false, ↓reduceIte] <;> rfl

/-- The signed comparison's encoded word is the lookup table's field bit. -/
theorem slt_value_toNat_eq {F : Type} [Field F] (lhs rhs : BitVec 64) :
    ((jolt_slt_value lhs rhs).toNat : F) =
      (if lhs.toInt < rhs.toInt then 1 else 0) := by
  rw [slt_value_eq]
  split_ifs
  · change ((1#64).toNat : F) = 1
    simp only [BitVec.toNat_one (by decide : 0 < 64), Nat.cast_one]
  · change ((0#64).toNat : F) = 0
    simp only [BitVec.toNat_zero, Nat.cast_zero]

private theorem sltu_value_eq (lhs rhs : BitVec 64) :
    jolt_sltu_value lhs rhs = if lhs < rhs then 1 else 0 := by
  have toNatInt_lt : (BitVec.toNatInt lhs < BitVec.toNatInt rhs) ↔ lhs < rhs := by
    change (Int.ofNat lhs.toNat < Int.ofNat rhs.toNat) ↔ lhs.toNat < rhs.toNat
    exact Int.ofNat_lt
  unfold jolt_sltu_value zopz0zI_u bool_to_bit bool_bit_forwards
    zero_extend Sail.BitVec.zeroExtend
  by_cases smaller : lhs < rhs <;>
    simp only [smaller, toNatInt_lt, decide_true, decide_false, ↓reduceIte] <;> rfl

variable {F : Type} [Field F] {params : WitnessParams} {witness : WitnessType F params}
  {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
  (charAbove2pow128 : 2 ^ 128 < ringChar F)
  (context : ConstraintContext joltInstance privateInputs params)
  (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
  {live : Fin 128 → Prop} {t : Fin params.traceLength} {slot : Fin (2 ^ params.logBytecodeK)}
  (selected : bytecodeRa witness slot t = 1)
  {row : JoltInstructionRow} (rowIs : bytecodeRow context.bytecode slot.val = some row)
  (operation : RegisterComparison) {destination : Dst} {lhs rhs : Src}
  (instructionIs : row.instruction = operation.instruction destination lhs rhs)

include context rowIs instructionIs in
private theorem comparison_canonical :
    (JoltRegisterEncoding.destinationIsCanonical destination = true ∧
      JoltRegisterEncoding.sourceIsCanonical lhs = true) ∧
    JoltRegisterEncoding.sourceIsCanonical rhs = true := by
  cases operation <;>
    simpa only [instructionIs, RegisterComparison.instruction,
      JoltRegisterEncoding.instructionIsCanonical, Bool.and_eq_true] using
      (bytecodeRow_rowOk context rowIs).canonical

include charAbove2pow128 context equations selected rowIs instructionIs

private theorem comparison_write_value {pre : SailJoltState}
    (agrees : RegisterAgreementOn live witness t pre)
    (lhsLive : live (TraceWitness.sourceRegisterAddress lhs))
    (rhsLive : live (TraceWitness.sourceRegisterAddress rhs)) :
    witness.RdWriteValue t =
      ((operation.value (sourceValue lhs pre) (sourceValue rhs pre)).toNat : F) := by
  have bound := two_pow_127_lt_char charAbove2pow128
  have canonical := comparison_canonical context rowIs operation instructionIs
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
  | signed =>
    have output := lookupOutput_signedLessThan bound context equations t slot selected
      (sourceValue lhs pre) (sourceValue rhs pre) raf leftLookup rightLookup table
    simpa only [RegisterComparison.value, slt_value_toNat_eq] using output
  | unsigned =>
    have output := lookupOutput_unsignedLessThan bound context equations t slot selected
      (sourceValue lhs pre) (sourceValue rhs pre) raf leftLookup rightLookup table
    have valueEq : ((jolt_sltu_value (sourceValue lhs pre) (sourceValue rhs pre)).toNat : F) =
        (if sourceValue lhs pre < sourceValue rhs pre then 1 else 0) := by
      rw [sltu_value_eq]
      split_ifs
      · change ((1#64).toNat : F) = 1
        simp only [BitVec.toNat_one (by decide : 0 < 64), Nat.cast_one]
      · change ((0#64).toNat : F) = 0
        simp only [BitVec.toNat_zero, Nat.cast_zero]
    simpa only [RegisterComparison.value, valueEq] using output

/-- SLT and SLTU execute with their constrained comparison bit and preserve
register agreement at the next cycle.
Both sources are live; the destination joins the live set after the row.
For example, SLTU can compare two live sources and initialize a temporary. -/
theorem comparison_step {pre : SailJoltState} (agrees : RegisterAgreementOn live witness t pre)
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
  have canonical := comparison_canonical context rowIs operation instructionIs
  have leftRead := (agrees.read lhs canonical.1.2 lhsLive).1
  have rightRead := (agrees.read rhs canonical.2 rhsLive).1
  have encoded := comparison_write_value charAbove2pow128 context equations selected rowIs
    operation instructionIs agrees lhsLive rhsLive
  apply registerWriteOn_step context equations selected rowIs charAbove2pow128 agrees
    destination (by cases operation <;> rw [instructionIs] <;> rfl) _ encoded answer advice
  rw [withRuntimeAdvice_eq_of_noAdvice _ advice
    (by cases operation <;> rw [instructionIs] <;> rfl)]
  cases operation <;> rw [instructionIs] <;>
    simp only [RegisterComparison.instruction, RegisterComparison.value,
      execWithTapeAnswer, execInstr, bind, EStateM.bind, leftRead, rightRead]

end JoltConstraints.Soundness
