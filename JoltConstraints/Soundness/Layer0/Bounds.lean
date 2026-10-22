import JoltConstraints.constraint_context
import Mathlib.Algebra.CharP.Defs
import Mathlib.Data.Fintype.Card

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
the rounded-up base-two logarithm of the maximum padded trace length; eight for
the honest prover's one-hot chunk width (`committedLogKChunk`); and at most 64
for either advice region.
Rounding the maximum up to an even number preserves the bound of 72.
This uses the setup definition in `verifier_sizes.lean`; precommitted program
tables (`extra_candidates`) are outside that model. Revisit 72 if they are added. -/
theorem VerifierSizes.dorySetupLogN_le_72 (layout : MemoryLayout) (maxLength : Nat)
    (fits : maxLength < 2 ^ 64) : VerifierSizes.dorySetupLogN layout maxLength ≤ 72 := by
  have logBound : Nat.clog 2 maxLength ≤ 64 := Nat.clog_le_of_le_pow (Nat.le_of_lt fits)
  have chunkBound : VerifierSizes.committedLogKChunk (Nat.clog 2 maxLength) ≤ 8 := by
    unfold VerifierSizes.committedLogKChunk
    split <;> omega
  have trusted := VerifierSizes.adviceVars_le_64 _ layout.max_trusted_advice_size.isLt
  have untrusted := VerifierSizes.adviceVars_le_64 _ layout.max_untrusted_advice_size.isLt
  dsimp only [VerifierSizes.dorySetupLogN]
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
    rw [layoutIs] at fits
    have bound := of_decide_eq_true fits
    have setupBound := VerifierSizes.dorySetupLogN_le_72 layout _
      joltInstance.max_padded_trace_length.isLt
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
