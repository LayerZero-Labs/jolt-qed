import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.honest_witness

set_option autoImplicit false

namespace JoltConstraints

private theorem addWide_mod (left right : BitVec 64) :
    JoltISA.addWide left right % 340282366920938463463374607431768211456 =
      JoltISA.addWide left right := by
  have hl := left.isLt
  have hr := right.isLt
  apply Nat.mod_eq_of_lt
  dsimp [JoltISA.addWide]
  omega

private theorem addWide_cast {F : Type} [Field F] (left right : BitVec 64) :
    (JoltISA.addWide left right : F) = (left.toNat : F) + (right.toNat : F) := by
  simp [JoltISA.addWide]

private theorem narrow_mod_128 (value : BitVec 64) :
    value.toNat % 340282366920938463463374607431768211456 = value.toNat :=
  Nat.mod_eq_of_lt (value.isLt.trans (by norm_num))

private theorem masked_mod_128 (value : Nat) :
    value % 18446744073709551616 % 340282366920938463463374607431768211456 =
      value % 18446744073709551616 := by
  apply Nat.mod_eq_of_lt
  exact (Nat.mod_lt _ (by norm_num)).trans (by norm_num)

/-- Constraint (08) in `constraints.md` (stage 1):
addition places the sum of the instruction inputs in the right lookup operand.
Rust: https://github.com/abiswas3/jolt/tree/main/crates/jolt-r1cs/src/constraints/rv64.rs -/
def rightLookupAdd {F : Type} [Field F] {params : WitnessParams}
    (witness : WitnessType F params) : Prop :=
  ∀ t : Fin params.traceLength,
    witness.OpFlags .AddOperands t *
      (witness.RightLookupOperand t - witness.LeftInstructionInput t -
        witness.RightInstructionInput t) = 0

/-- Completeness target for the honest witness. -/
theorem honestWitness_rightLookupAdd
    {F : Type} [Field F] (params : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program)
    (ramFits : params.RamFits trace)
    (traceFits : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor program.expandedBytecode.size) :
    rightLookupAdd
      (JoltProgram.honestWitness (F := F) params trace ramFits traceFits bytecodeDomain) := by
  intro t
  by_cases h : t.val < trace.rows.size
  · let row := getElem trace.rows t.val h
    let bytecodeRow := getElem program.expandedBytecode row.rowIndex.val row.rowIndex.isLt
    by_cases ha : JoltMetadata.opcodeFlag bytecodeRow.instruction .AddOperands = true
    · have heq : HonestWitness.RightLookupOperand (F := F) params trace t =
          HonestWitness.LeftInstructionInput (F := F) params trace t +
          HonestWitness.RightInstructionInput (F := F) params trace t := by
        cases hi : bytecodeRow.instruction
        all_goals simp [JoltMetadata.opcodeFlag, hi] at ha
        all_goals simp only [bytecodeRow, row] at hi
        all_goals
          simp [HonestWitness.RightLookupOperand, HonestWitness.lookupIndex,
            HonestWitness.instructionLookupIndex, HonestWitness.LeftInstructionInput,
            HonestWitness.RightInstructionInput, HonestWitness.Rs1Value,
            HonestWitness.Rs2Value, HonestWitness.Imm, HonestWitness.UnexpandedPC,
            JoltMetadata.hasCombinedLookupOperands, JoltMetadata.opcodeFlag,
            JoltMetadata.instructionFlag, addWide_mod, hi, h]
        all_goals (try simp [addWide_cast, narrow_mod_128, JoltMetadata.immediate])
        all_goals simp [masked_mod_128]
        all_goals norm_cast
      simp [JoltProgram.honestWitness, HonestWitness.OpFlags,
        JoltMetadata.circuitFlag, h, ha, heq]
    · simp [JoltProgram.honestWitness,
        HonestWitness.OpFlags, JoltMetadata.circuitFlag, h, ha, bytecodeRow, row]
  · simp [JoltProgram.honestWitness, HonestWitness.OpFlags, h]

end JoltConstraints
