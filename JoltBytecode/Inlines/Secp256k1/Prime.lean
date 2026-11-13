import JoltBytecode.Inlines.Secp256k1.Spec
import JoltConstraints.Vendor.PrattCertificate

/-!
# The secp256k1 moduli are prime

`p_prime` and `n_prime` prove that the base-field prime `p` and the group order `n` are prime,
with Pratt (Lucas) certificates checked by the kernel. `coprime_of_mod_ne_zero` then turns a
divisor that is nonzero modulo a prime into one coprime to it, which is the form the `DIV`
completeness proof uses (`FieldDiv.lean`).

Each certificate names a base `a` of order `q - 1` modulo `q` and the factorization of `q - 1`.
The `pratt` tactic (from `JoltConstraints/Vendor/PrattCertificate.lean`, vendored from CompPoly)
builds the certificates of the smaller factors by itself. It factors with Pollard's rho, which
cannot split `P237 - 1` below, so `p237_prime` gives that factorization explicitly.
-/

set_option autoImplicit false

namespace JoltISA.Inlines.Secp256k1

/-- The largest prime factor of `p - 1` (237 bits) is prime.
Certificate: `10` has order `P237 - 1` modulo `P237`, and
`P237 - 1 = 2 · 3 · 5 · 29^2 · 31 · 7723 · 132896956044521568488119 ·
255515944373312847190720520512484175977`. -/
theorem p237_prime :
    Nat.Prime 205115282021455665897114700593932402728804164701536103180137503955397371 := by
  refine PrattCertificate'.out
    (p := 205115282021455665897114700593932402728804164701536103180137503955397371)
    ⟨10, by reduce_mod_char, ?_⟩
  refine .split [2, 3, 5, 29 ^ 2, 31, 7723, 132896956044521568488119,
    255515944373312847190720520512484175977] (fun r hr => ?_) (by norm_num)
  simp only [Nat.reducePow, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with hr | hr | hr | hr | hr | hr | hr | hr <;> rw [hr]
  · exact .prime 2 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 3 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 5 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 29 2 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 31 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 7723 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 132896956044521568488119 1 _ (by pratt) (by reduce_mod_char; decide)
      (by norm_num)
  · exact .prime 255515944373312847190720520512484175977 1 _ (by pratt)
      (by reduce_mod_char; decide) (by norm_num)

/-- The base-field modulus `p = 2^256 - 2^32 - 977` is prime.
Certificate: `3` has order `p - 1` modulo `p`, and
`p - 1 = 2 · 3 · 7 · 13441 · P237`, with `P237` from `p237_prime`. -/
theorem p_prime : p.Prime := by
  have literal : p =
      115792089237316195423570985008687907853269984665640564039457584007908834671663 := by
    norm_num [p]
  rw [literal]
  refine PrattCertificate'.out
    (p := 115792089237316195423570985008687907853269984665640564039457584007908834671663)
    ⟨3, by reduce_mod_char, ?_⟩
  refine .split [2, 3, 7, 13441,
    205115282021455665897114700593932402728804164701536103180137503955397371]
    (fun r hr => ?_) (by norm_num)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with hr | hr | hr | hr | hr <;> rw [hr]
  · exact .prime 2 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 3 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 7 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 13441 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime _ 1 _ p237_prime (by reduce_mod_char; decide) (by norm_num)

/-- The group order `n` is prime.
Certificate: `7` has order `n - 1` modulo `n`, and
`n - 1 = 2^6 · 3 · 149 · 631 · 107361793816595537 · 174723607534414371449 ·
341948486974166000522343609283189`. -/
theorem n_prime : n.Prime := by
  have literal : n =
      115792089237316195423570985008687907852837564279074904382605163141518161494337 := by
    norm_num [n]
  rw [literal]
  refine PrattCertificate'.out
    (p := 115792089237316195423570985008687907852837564279074904382605163141518161494337)
    ⟨7, by reduce_mod_char, ?_⟩
  refine .split [2 ^ 6, 3, 149, 631, 107361793816595537, 174723607534414371449,
    341948486974166000522343609283189] (fun r hr => ?_) (by norm_num)
  simp only [Nat.reducePow, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with hr | hr | hr | hr | hr | hr | hr <;> rw [hr]
  · exact .prime 2 6 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 3 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 149 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 631 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 107361793816595537 1 _ (by pratt) (by reduce_mod_char; decide)
      (by norm_num)
  · exact .prime 174723607534414371449 1 _ (by pratt) (by reduce_mod_char; decide)
      (by norm_num)
  · exact .prime 341948486974166000522343609283189 1 _ (by pratt)
      (by reduce_mod_char; decide) (by norm_num)

/-- A number that is nonzero modulo a prime `q` is coprime to `q`.
Example: `2 % p = 2 ≠ 0`, so `Nat.Coprime 2 p` (with `p_prime`). -/
theorem coprime_of_mod_ne_zero {q b : Nat} (hq : q.Prime) (hb : b % q ≠ 0) :
    Nat.Coprime b q :=
  ((Nat.Prime.coprime_iff_not_dvd hq).mpr fun hd => hb (Nat.mod_eq_zero_of_dvd hd)).symm

end JoltISA.Inlines.Secp256k1
