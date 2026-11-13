/-
Primality of Jolt's two field moduli, proved by Pratt (Lucas) certificates.
With these instances in scope, `JoltField.zmod_akitaModulus` and
`JoltField.zmod_bn254ScalarModulus` from `Soundness/Assumptions.lean` hold with
no hypotheses: both production fields satisfy the soundness theorem's field premise.
-/
import JoltConstraints.Soundness.Assumptions
import JoltConstraints.Vendor.PrattCertificate

set_option autoImplicit false

/-- Akita's modulus `2^128 - 1780711455` is prime.
Pratt certificate: `7` has order `p - 1` modulo `p`, and
`p - 1 = 2^5 · 3^3 · 5^8 · 6635108027 · 151955935914427270231`; `pratt` builds the
certificates for the two large factors. Jolt checks the same fact with a
Pocklington certificate in HOL Light (a16z/jolt#2403). -/
theorem akitaModulus_prime : akitaModulus.Prime := by
  have literal : akitaModulus = 340282366920938463463374607429987500001 := by
    norm_num [akitaModulus]
  rw [literal]
  refine PrattCertificate'.out (p := 340282366920938463463374607429987500001)
    ⟨7, by reduce_mod_char, ?_⟩
  refine .split [2 ^ 5, 3 ^ 3, 5 ^ 8, 6635108027, 151955935914427270231]
    (fun r hr => ?_) (by norm_num)
  simp only [Nat.reducePow, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with hr | hr | hr | hr | hr <;> rw [hr]
  · exact .prime 2 5 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 3 3 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 5 8 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 6635108027 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 151955935914427270231 1 _ (by pratt) (by reduce_mod_char; decide)
      (by norm_num)

/-- BN254's scalar modulus is prime. The certificate is CompPoly's
`BN254.ScalarField_is_prime` (`CompPoly/Fields/BN254/Basic.lean` at `e28da34`):
`5` has order `r - 1`, and
`r - 1 = 2^28 · 3^2 · 13 · 29 · 983 · 11003 · 237073 · 405928799 · 1670836401704629 ·
13818364434197438864469338081`. -/
theorem bn254ScalarModulus_prime : bn254ScalarModulus.Prime := by
  unfold bn254ScalarModulus
  refine PrattCertificate'.out
    (p := 21888242871839275222246405745257275088548364400416034343698204186575808495617)
    ⟨5, (by reduce_mod_char), ?_⟩
  refine .split [2 ^ 28, 3 ^ 2, 13, 29, 983, 11003, 237073, 405928799, 1670836401704629,
    13818364434197438864469338081] (fun r hr => ?_) (by norm_num)
  simp only [Nat.reducePow, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with hr | hr | hr | hr | hr | hr | hr | hr | hr | hr <;> rw [hr]
  · exact .prime 2 28 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 3 2 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 13 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 29 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 983 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 11003 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 237073 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 405928799 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 1670836401704629 1 _ (by pratt) (by reduce_mod_char; decide)
      (by norm_num)
  · exact .prime 13818364434197438864469338081 1 _ (by pratt) (by reduce_mod_char; decide)
      (by norm_num)

instance akitaModulus_fact_prime : Fact akitaModulus.Prime := ⟨akitaModulus_prime⟩

instance bn254ScalarModulus_fact_prime : Fact bn254ScalarModulus.Prime :=
  ⟨bn254ScalarModulus_prime⟩

/-- Akita's field satisfies the soundness theorem's field premise. -/
theorem JoltField.akita : JoltField (ZMod akitaModulus) :=
  JoltField.zmod_akitaModulus

/-- BN254's scalar field satisfies the soundness theorem's field premise. -/
theorem JoltField.bn254 : JoltField (ZMod bn254ScalarModulus) :=
  JoltField.zmod_bn254ScalarModulus
