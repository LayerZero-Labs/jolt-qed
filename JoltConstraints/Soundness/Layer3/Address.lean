import JoltConstraints.Soundness.Layer1.RamReads
import JoltConstraints.Soundness.Layer0.Words

/-! Relate a selected RAM index to an actual 64-bit byte address. A witness
address column is a field element; the `encoded` hypothesis identifies it with
a machine address when applying these lemmas during the execution proof.
The Layer 5b address lemmas in Layer5/MemoryAddress.lean derive `encoded` from
the instance's `RamRegionFits` premise and the verifier's RAM-size check.
Selection recovers the integer base-plus-signed-immediate sum as a word address;
with no selected word the sum is zero. The layout bound then excludes 64-bit
wraparound in both cases. These facts apply independently of tape semantics;
the execution induction must still supply source-register agreement.
NOTE: to confirm with a16z: the maximum padded RAM region fits below 2^64. -/

set_option autoImplicit false

namespace JoltConstraints.Soundness

variable {F : Type} [Field F] {params : WitnessParams} {witness : WitnessType F params}
  {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
  (charAbove2pow127 : 2 ^ 127 < ringChar F)
  (context : ConstraintContext joltInstance privateInputs params)
  (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)

include charAbove2pow127 context equations

/-- A selected word's byte address equals the remapping base plus eight times
its index as natural numbers, without field wraparound. -/
theorem ramAddress_eq_of_selected (t : Fin params.traceLength)
    (chosen : Fin params.ramSize) (selected : witness.RamRa chosen t = 1)
    (raw : BitVec 64) (encoded : witness.RamAddress t = (raw.toNat : F)) :
    raw.toNat = ramLowestAddress context.io.memory_layout + 8 * chosen.val := by
  exact natCast_injective_below_char
    (word_toNat_lt_char charAbove2pow127 raw)
    (ram_address_value_lt_char charAbove2pow127 context.io.memory_layout chosen)
    (encoded.symm.trans (ramAddress_of_selected charAbove2pow127 context equations t chosen selected))

/-- The actual byte address remaps to the selected RAM index. Address zero
and addresses below the base are excluded by selection and the constraints. -/
theorem remapRamAddress_of_selected (t : Fin params.traceLength)
    (chosen : Fin params.ramSize) (selected : witness.RamRa chosen t = 1)
    (raw : BitVec 64) (encoded : witness.RamAddress t = (raw.toNat : F)) :
    TraceWitness.remapRamAddress context.io.memory_layout raw = some chosen.val := by
  have address := ramAddress_eq_of_selected charAbove2pow127 context equations t chosen selected raw encoded
  have nonzero : raw.toNat ≠ 0 := by
    intro zero
    have addressZero : witness.RamAddress t = 0 := by simpa [zero] using encoded
    have allZero := (ramRa_zero_iff_address_zero charAbove2pow127 context equations t).mpr addressZero
    exact zero_ne_one ((allZero chosen).symm.trans selected)
  have above : ¬ raw.toNat < ramLowestAddress context.io.memory_layout := by omega
  change (if raw.toNat = 0 ∨ raw.toNat < ramLowestAddress context.io.memory_layout then none
    else some ((raw.toNat - ramLowestAddress context.io.memory_layout) / 8)) = _
  rw [if_neg (by simp [nonzero, above]), address]
  simp

end JoltConstraints.Soundness
