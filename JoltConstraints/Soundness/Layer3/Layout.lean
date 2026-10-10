import JoltConstraints.constraint_context
import JoltConstraints.Constraints.RamReadData

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
