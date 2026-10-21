import JoltConstraints.constraint_context
import JoltConstraints.Constraints.RamReadData
import JoltConstraints.layout_facts
import JoltConstraints.witness_domain

/-! The approved layout restriction and its consequence for a witness's RAM
domain. These facts depend only on the instance and verifier size checks. -/

set_option autoImplicit false

/-- The maximum padded RAM region fits in the machine's 64-bit address space.
NOTE: to confirm with a16z. Approved by Ari on 2026-10-10 as a replacement for
the run-based no-wrap assumption. This is a theorem premise, not a modeled
verifier check. Failed layout or maximum-size computations admit no constraint
context, so the restriction is stated for their successful results. -/
def JoltInstance.RamRegionFits {Source : Type} (joltInstance : JoltInstance Source) : Prop :=
  ∀ (layout : MemoryLayout) (maximum : Nat),
    joltInstance.memory_layout = some layout →
    JoltConstraints.VerifierSizes.maxRamSize layout = some maximum →
      layout.get_lowest_address.toNat + 8 * maximum ≤ 2 ^ 64

namespace JoltConstraints.Soundness

variable {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
  {params : WitnessParams}

/-- The verifier's upper size check transfers the instance's region bound to
the witness's RAM domain, using the same layout as its public I/O. -/
theorem ram_domain_fits (context : ConstraintContext joltInstance privateInputs params)
    (regionFits : joltInstance.RamRegionFits) :
    ramLowestAddress context.io.memory_layout + 8 * params.ramSize ≤ 2 ^ 64 := by
  have publicIo := context.publicIo
  unfold JoltInstance.public_io at publicIo
  obtain ⟨layout, hasLayout, sameIo⟩ := Option.bind_eq_some_iff.mp publicIo
  have layoutEq : layout = context.io.memory_layout :=
    congrArg JoltDevice.memory_layout (Option.some.inj sameIo)
  have sizes := context.ramSizeBounds
  unfold JoltInstance.ram_size_in_bounds JoltInstance.verifier_ram_bounds at sizes
  rw [hasLayout] at sizes
  cases minimumIs : VerifierSizes.minRamSize joltInstance.program layout with
  | none => simp [minimumIs] at sizes
  | some minimum =>
    cases maximumIs : VerifierSizes.maxRamSize layout with
    | none => simp [minimumIs, maximumIs] at sizes
    | some maximum =>
      have bounds : minimum ≤ params.ramSize ∧ params.ramSize ≤ maximum := by
        simpa [minimumIs, maximumIs] using sizes
      have upper := bounds.2
      have bound := regionFits layout maximum hasLayout maximumIs
      rw [← layoutEq]
      unfold ramLowestAddress MemoryLayout.get_lowest_address at *
      split at bound <;> omega

/-- The word index `(RAM_START_ADDRESS - lowest) / 8` is the first word after
the public I/O range, and the verifier's RAM minimum places it within the
witness's RAM domain. -/
theorem public_io_words_fit_ram
    (context : ConstraintContext joltInstance privateInputs params) :
    (JoltISA.RAM_START_ADDRESS - ramLowestAddress context.io.memory_layout) / 8 ≤
      params.ramSize := by
  have publicIo := context.publicIo
  unfold JoltInstance.public_io at publicIo
  obtain ⟨layout, hasLayout, sameIo⟩ := Option.bind_eq_some_iff.mp publicIo
  have layoutEq : layout = context.io.memory_layout :=
    congrArg JoltDevice.memory_layout (Option.some.inj sameIo)
  have sizes := context.ramSizeBounds
  unfold JoltInstance.ram_size_in_bounds JoltInstance.verifier_ram_bounds at sizes
  rw [hasLayout] at sizes
  cases minimumIs : VerifierSizes.minRamSize joltInstance.program layout with
  | none => simp [minimumIs] at sizes
  | some minimum =>
    cases maximumIs : VerifierSizes.maxRamSize layout with
    | none => simp [minimumIs, maximumIs] at sizes
    | some maximum =>
      have minimumBound : minimum ≤ params.ramSize := by
        have h : minimum ≤ params.ramSize ∧ params.ramSize ≤ maximum := by
          simpa [minimumIs, maximumIs] using sizes
        exact h.1
      unfold VerifierSizes.minRamSize at minimumIs
      rw [bind_some_iff] at minimumIs
      obtain ⟨bytecodeStart, _, minimumIs⟩ := minimumIs
      rw [bind_some_iff] at minimumIs
      obtain ⟨bytecodeEnd, _, minimumIs⟩ := minimumIs
      rw [bind_some_iff] at minimumIs
      obtain ⟨ioEnd?, remappedIo, minimumIs⟩ := minimumIs
      cases ioEnd? with
      | none => simp at minimumIs
      | some ioEnd =>
        have ioEndBound : ioEnd ≤ minimum := by
          unfold VerifierSizes.checkedNextPowerOfTwo at minimumIs
          dsimp only at minimumIs
          split at minimumIs
          · have minimumEq := Option.some.inj minimumIs.symm
            rw [minimumEq]
            exact (Nat.le_max_right _ _).trans
              (Nat.le_pow_clog (by decide : 1 < 2) _)
          · cases minimumIs
        unfold VerifierSizes.remapWordAddress at remappedIo
        simp only [if_neg (by decide : JoltISA.RAM_START_ADDRESS ≠ 0)] at remappedIo
        cases subtracted : MemoryLayout.checkedSub JoltISA.RAM_START_ADDRESS
            layout.get_lowest_address.toNat with
        | none => simp [subtracted] at remappedIo
        | some offset =>
          have ioEndEq : offset / 8 = ioEnd := by simpa [subtracted] using remappedIo
          obtain ⟨offsetIs, _⟩ := checkedSub_some subtracted
          rw [MemoryLayout.get_lowest_address_toNat] at offsetIs
          rw [← layoutEq]
          simpa [← ioEndEq, offsetIs] using ioEndBound.trans minimumBound

/-- All eight bytes of every in-domain word fit below `2^64`, including the
last word when the region's exclusive endpoint equals `2^64`. -/
theorem ram_word_byte_lt_two_pow_64
    (context : ConstraintContext joltInstance privateInputs params)
    (regionFits : joltInstance.RamRegionFits) (address : Fin params.ramSize)
    (offset : Fin 8) :
    ramLowestAddress context.io.memory_layout + 8 * address.val + offset.val < 2 ^ 64 := by
  have bound := ram_domain_fits context regionFits
  have addressLt := address.isLt
  have offsetLt := offset.isLt
  omega

end JoltConstraints.Soundness
