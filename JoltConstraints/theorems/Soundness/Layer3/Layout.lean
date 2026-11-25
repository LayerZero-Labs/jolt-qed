import JoltConstraints.translation.constraint_context
import JoltConstraints.translation.Constraints.RamReadData
import JoltConstraints.theorems.witness_domain

open LeanRV64D

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
    congrArg JoltPublicIo.memory_layout (Option.some.inj sameIo)
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
    congrArg JoltPublicIo.memory_layout (Option.some.inj sameIo)
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
        simp only [ite_eq_right (by decide : JoltISA.RAM_START_ADDRESS ≠ 0)] at remappedIo
        cases subtracted : MemoryLayout.checkedSub JoltISA.RAM_START_ADDRESS
            layout.get_lowest_address.toNat with
        | none => simp [subtracted] at remappedIo
        | some offset =>
          have ioEndEq : offset / 8 = ioEnd := by simpa [subtracted] using remappedIo
          obtain ⟨offsetIs, _⟩ := checkedSub_some subtracted
          rw [MemoryLayout.get_lowest_address_toNat] at offsetIs
          rw [← layoutEq]
          simpa [← ioEndEq, offsetIs] using! ioEndBound.trans minimumBound

private theorem domain_reaches_ram (low size maximum : Nat)
    (aligned : low % 8 = 0) (below : low ≤ JoltISA.RAM_START_ADDRESS)
    (covers : (JoltISA.RAM_START_ADDRESS - low) / 8 ≤ size) (upper : size ≤ maximum) :
    JoltISA.RAM_START_ADDRESS ≤ low + 8 * maximum := by
  simp only [JoltISA.RAM_START_ADDRESS] at *
  omega

private theorem backing_covers_words (base low size maximum : Nat) (domain : Option Nat)
    (computed : domain = some maximum) (above : base ≤ low + 8 * maximum)
    (upper : size ≤ maximum) :
    low + 8 * size ≤ base + (domain.map fun k => low + 8 * k - base).getD 0 := by
  rw [computed]
  simp only [Option.map_some, Option.getD_some]
  omega

/-- The verifier's admitted RAM domain fits in the tracer's padded backing.
For example, the last witness word may be in heap padding beyond `heap_end`.
Jolt at `ff6fc6568`: `common/src/jolt_device.rs` (`MemoryLayout::ram_size`). -/
theorem ram_domain_within_backing (context : ConstraintContext joltInstance privateInputs params) :
    ramLowestAddress context.io.memory_layout + 8 * params.ramSize ≤
      JoltISA.RAM_START_ADDRESS + context.io.memory_layout.ram_size := by
  have publicIo := context.publicIo
  unfold JoltInstance.public_io at publicIo
  obtain ⟨layout, hasLayout, sameIo⟩ := Option.bind_eq_some_iff.mp publicIo
  have layoutEq : layout = context.io.memory_layout :=
    congrArg JoltPublicIo.memory_layout (Option.some.inj sameIo)
  have built := hasLayout
  unfold JoltInstance.memory_layout at built
  have lowestAligned := new_lowest_address_aligned _ _ built
  have order := new_io_ordered _ _ built
  have ioFits := public_io_words_fit_ram context
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
      rw [← layoutEq] at ioFits ⊢
      rw [MemoryLayout.get_lowest_address_toNat] at lowestAligned order
      have lowBelow : ramLowestAddress layout ≤ JoltISA.RAM_START_ADDRESS :=
        order.1.trans (order.2.1.trans (order.2.2.1.trans (by
          rw [order.2.2.2.1]; exact order.2.2.2.2)))
      have reaches := domain_reaches_ram (ramLowestAddress layout) params.ramSize maximum
        lowestAligned lowBelow ioFits bounds.2
      change layout.max_ram_k? = some maximum at maximumIs
      have result := backing_covers_words JoltISA.RAM_START_ADDRESS
        layout.get_lowest_address.toNat params.ramSize maximum layout.max_ram_k? maximumIs
        (by simpa only [MemoryLayout.get_lowest_address_toNat, ramLowestAddress] using reaches) bounds.2
      simpa only [MemoryLayout.ram_size, MemoryLayout.get_lowest_address_toNat,
        ramLowestAddress] using result

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
