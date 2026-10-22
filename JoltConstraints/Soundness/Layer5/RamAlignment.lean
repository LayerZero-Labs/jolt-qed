import JoltConstraints.Soundness.Layer5.MemoryAddress
import JoltConstraints.Soundness.Layer3.State

/-! RAM selection forces doubleword alignment; an encoded address is either
zero or an aligned layout base plus eight times an index. LD/SD therefore need
no additional alignment premise. This does not establish address legality or
agreement with the value read by a device.
At public pin 8bbb2357:
See : jolt/tracer/src/emulator/mmu.rs:321-329
See : jolt/tracer/src/emulator/mmu.rs:429-435 -/

set_option autoImplicit false

namespace JoltConstraints.Soundness

open JoltISA

variable {F : Type} [Field F] {params : WitnessParams} {witness : WitnessType F params}
  {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
  (charAbove2pow127 : 2 ^ 127 < ringChar F)
  (context : ConstraintContext joltInstance privateInputs params)
  (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)

include context in
private theorem ramLowestAddress_aligned : ramLowestAddress context.io.memory_layout % 8 = 0 := by
  obtain ⟨initial, built, _⟩ := context.initialized
  have aligned := initial_state_lowest_address_aligned joltInstance privateInputs initial built
  rw [initial_state_memory_layout context built] at aligned
  unfold MemoryLayout.get_lowest_address at aligned
  unfold ramLowestAddress
  split at aligned <;> omega

include charAbove2pow127

/-- An encoded ordinary-RAM address cannot be the unselected zero address. -/
theorem ramAddress_nonzero_of_inRam (t : Fin params.traceLength) (raw : BitVec 64)
    (encoded : witness.RamAddress t = (raw.toNat : F))
    (inRam : RAM_START_ADDRESS ≤ raw.toNat) : witness.RamAddress t ≠ 0 := by
  intro zero
  have same : raw.toNat = 0 := natCast_injective_below_char
    (word_toNat_lt_char charAbove2pow127 raw)
    (lt_trans (by decide) charAbove2pow127)
    (encoded.symm.trans (zero.trans Nat.cast_zero.symm))
  rw [same] at inRam
  norm_num [RAM_START_ADDRESS] at inRam

include context equations

/-- Every machine address encoded by the RAM address column is eight-byte
aligned, including address zero where no RAM word is selected. -/
theorem ramAddress_aligned (t : Fin params.traceLength) (raw : BitVec 64)
    (encoded : witness.RamAddress t = (raw.toNat : F)) : raw.toNat % 8 = 0 := by
  rcases ramRa_zero_or_unique charAbove2pow127 context equations t with zero | ⟨chosen, one, _⟩
  · have addressZero := (ramRa_zero_iff_address_zero charAbove2pow127 context equations t).mp zero
    have same : raw.toNat = 0 := natCast_injective_below_char
      (word_toNat_lt_char charAbove2pow127 raw)
      (lt_trans (by decide) charAbove2pow127)
      (encoded.symm.trans (addressZero.trans (Nat.cast_zero.symm)))
    rw [same]
  · rw [ramAddress_eq_of_selected charAbove2pow127 context equations t chosen one raw encoded]
    have aligned := ramLowestAddress_aligned context
    omega

/-- The bit-mask alignment check in the instruction interpreter follows from
the selected RAM address, rather than an assumed successful memory access. -/
theorem ramAddress_mask_aligned (t : Fin params.traceLength) (raw : BitVec 64)
    (encoded : witness.RamAddress t = (raw.toNat : F)) : raw &&& (7 : BitVec 64) = 0 := by
  apply BitVec.eq_of_toNat_eq
  have aligned := ramAddress_aligned charAbove2pow127 context equations t raw encoded
  change raw.toNat &&& (2 ^ 3 - 1) = 0
  rw [Nat.and_two_pow_sub_one_eq_mod]
  exact aligned

end JoltConstraints.Soundness
