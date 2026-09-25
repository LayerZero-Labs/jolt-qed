import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.honest_witness

set_option autoImplicit false

namespace JoltConstraints

private theorem subWide_mod (left right : BitVec 64) :
    JoltISA.subWide left right % 340282366920938463463374607431768211456 =
      JoltISA.subWide left right := by
  have hl := left.isLt
  have hr := right.isLt
  apply Nat.mod_eq_of_lt
  dsimp [JoltISA.subWide]
  omega

private theorem subWide_cast {F : Type} [Field F] (left right : BitVec 64) :
    (JoltISA.subWide left right : F) =
      (left.toNat : F) - (right.toNat : F) + (2 : F) ^ 64 := by
  have hr := right.isLt
  dsimp [JoltISA.subWide]
  rw [Nat.cast_add, Nat.cast_sub (Nat.le_of_lt hr)]
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  ring

/-- Constraint (09) in `constraints.md` (stage 1):
subtraction places the biased difference of the inputs in the right lookup operand.
Rust: https://github.com/abiswas3/jolt/tree/main/crates/jolt-r1cs/src/constraints/rv64.rs -/
def rightLookupSub {F : Type} [Field F] {params : WitnessParams}
    (witness : WitnessType F params) : Prop :=
  ∀ t : Fin params.traceLength,
    witness.OpFlags .SubtractOperands t *
      (witness.RightLookupOperand t - witness.LeftInstructionInput t +
        witness.RightInstructionInput t - (2 : F) ^ 64) = 0

/-- Completeness target for the honest witness. -/
theorem honestWitness_rightLookupSub
    {F : Type} [Field F] (params : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program)
    (ramFits : params.RamFits trace)
    (traceFits : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor program.expandedBytecode.size) :
    rightLookupSub
      (JoltProgram.honestWitness (F := F) params trace ramFits traceFits bytecodeDomain) := by
  intro t
  by_cases h : t.val < trace.rows.size
  · let row := getElem trace.rows t.val h
    let bytecodeRow := getElem program.expandedBytecode row.rowIndex.val row.rowIndex.isLt
    by_cases hs : JoltMetadata.opcodeFlag bytecodeRow.instruction .SubtractOperands = true
    · have heq : HonestWitness.RightLookupOperand (F := F) params trace t =
          HonestWitness.LeftInstructionInput (F := F) params trace t -
          HonestWitness.RightInstructionInput (F := F) params trace t + (2 : F) ^ 64 := by
        cases hi : bytecodeRow.instruction
        all_goals simp [JoltMetadata.opcodeFlag, hi] at hs
        all_goals simp only [bytecodeRow, row] at hi
        all_goals
          simp [HonestWitness.RightLookupOperand, HonestWitness.lookupIndex,
            HonestWitness.instructionLookupIndex, HonestWitness.LeftInstructionInput,
            HonestWitness.RightInstructionInput, HonestWitness.Rs1Value,
            HonestWitness.Rs2Value, JoltMetadata.hasCombinedLookupOperands,
            JoltMetadata.opcodeFlag, JoltMetadata.instructionFlag,
            subWide_mod, hi, h]
        all_goals simp [subWide_cast]
      simp [JoltProgram.honestWitness, HonestWitness.OpFlags,
        JoltMetadata.circuitFlag, h, heq]
      exact fun _ => by ring
    · simp [JoltProgram.honestWitness,
        HonestWitness.OpFlags, JoltMetadata.circuitFlag, h, hs, bytecodeRow, row]
  · simp [JoltProgram.honestWitness, HonestWitness.OpFlags, h]

end JoltConstraints
