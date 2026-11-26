import JoltConstraints.translation.constraint_context
import Mathlib.Algebra.CharP.Defs

open LeanRV64D

set_option autoImplicit false

namespace JoltConstraints

/-- A 64-bit advice byte count needs at most 64 polynomial variables.
This loose bound suffices for the field-characteristic argument. -/
theorem VerifierSizes.adviceVars_le_64 (bytes : Nat) (fits : bytes < 2 ^ 64) :
    VerifierSizes.adviceVars bytes ≤ 64 := by
  have divided := Nat.div_le_self bytes 8
  have smaller : max (bytes / 8) 1 - 1 < 2 ^ 64 := by omega
  have logBound := Nat.log_lt_of_lt_pow' (b := 2) (by decide : (64 : Nat) ≠ 0) smaller
  dsimp only [VerifierSizes.adviceVars]
  split <;> omega

/-- The modeled Dory setup needs at most 72 variables: at most 64 for `maxLogT`,
the base-two logarithm of the maximum padded trace length rounded up to a power of
two below `2^64`; eight for the honest prover's one-hot chunk width
(`committedLogKChunk`); and at most 64 for either advice region.
Rounding the maximum up to an even number preserves the bound of 72.
This uses the setup definition in `verifier_sizes.lean`; precommitted program
tables (`extra_candidates`) are outside that model. Revisit 72 if they are added. -/
theorem VerifierSizes.dorySetupLogN_le_72 (layout : MemoryLayout) (maxLength setupLogN : Nat)
    (computed : VerifierSizes.dorySetupLogN layout maxLength = some setupLogN) :
    setupLogN ≤ 72 := by
  unfold VerifierSizes.dorySetupLogN at computed
  cases rounding : VerifierSizes.checkedNextPowerOfTwo maxLength with
  | none => simp [rounding] at computed
  | some rounded =>
    rw [rounding] at computed
    have roundedLt : rounded < 2 ^ 64 := by
      unfold VerifierSizes.checkedNextPowerOfTwo at rounding
      dsimp only at rounding
      split at rounding
      · cases rounding
        assumption
      · contradiction
    have logBound : Nat.log 2 rounded ≤ 64 :=
      (Nat.log_mono_right roundedLt.le).trans (Nat.log_pow (by decide) 64).le
    have chunkBound : VerifierSizes.committedLogKChunk (Nat.log 2 rounded) ≤ 8 := by
      unfold VerifierSizes.committedLogKChunk
      split <;> omega
    have trusted := VerifierSizes.adviceVars_le_64 _ layout.max_trusted_advice_size.isLt
    have untrusted := VerifierSizes.adviceVars_le_64 _ layout.max_untrusted_advice_size.isLt
    have value := Option.some.inj computed
    subst value
    split <;> omega

/-- The verifier's setup check bounds the prover-chosen one-hot chunk width.
No honest-prover `ProverChunkConfig` assumption is needed. -/
theorem ConstraintContext.chunkBits_le_72
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    {params : WitnessParams} (context : ConstraintContext joltInstance privateInputs params) :
    params.chunkBits ≤ 72 := by
  have fits := context.oneHotFitsSetup
  unfold JoltInstance.one_hot_fits_setup at fits
  cases layoutIs : joltInstance.memory_layout with
  | none => simp [layoutIs] at fits
  | some layout =>
    cases setupIs : VerifierSizes.dorySetupLogN layout
        joltInstance.max_padded_trace_length.toNat with
    | none => simp [layoutIs, setupIs] at fits
    | some setupLogN =>
      simp only [layoutIs, setupIs, decide_eq_true_eq] at fits
      have setupBound := VerifierSizes.dorySetupLogN_le_72 layout _ setupLogN setupIs
      omega

/-- A one-hot chunk has fewer entries than the characteristic.
This supplies the cardinality bound used by the generic one-hot lemmas. -/
theorem ConstraintContext.chunk_card_lt_char {F : Type} [Field F]
    (charAbove2pow127 : 2 ^ 127 < ringChar F)
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    {params : WitnessParams} (context : ConstraintContext joltInstance privateInputs params) :
    Fintype.card (Fin (2 ^ params.chunkBits)) < ringChar F := by
  rw [Fintype.card_fin]
  have width := context.chunkBits_le_72
  exact lt_of_le_of_lt (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)) charAbove2pow127

end JoltConstraints
