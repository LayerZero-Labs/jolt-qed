# secp256k1 advice transcriptions and known-answer tests (I0(d))

Date: 2026-11-11.
Jolt: a16z/jolt `a6b6dc7177ec5ea5a3c60bd5cea4409c07ca6dc5`.
jolt-qed: commit `4b24363a6aaf7311061aee58bf05f603a9d7302c` on branch `inline/i0d-advice` (based on `bf22776`, `spec/inline-precompiles`); the driver and checker at that commit produced and checked the results below.
This report covers phase I0(d) of `docs/inline-precompiles.md` and the secp256k1 part of I0(b).

## What was added

- `JoltBytecode/Inlines/Secp256k1/Spec.lean`: the moduli, `p'`, the limb conversions and the integer relations of spec section 3.
- `JoltBytecode/Inlines/Secp256k1/Advice.lean`: computable transcriptions of Jolt's advice functions and `joltAdvice` per inline.
- `scripts/secp256k1-kat/`: a Rust driver that runs Jolt's advice code and Jolt's tracer and writes JSON.
- `JoltTests/Secp256k1Kat/Main.lean`: the `secp256k1-kat` executable in the new `JoltTests` library (not a default target), which checks the Lean code against that JSON.

Both Lean files build under the strict standard.
They contain no `sorry`, `native_decide`, `decide +kernel`, `bv_decide`, or heartbeat or recursion-depth option.
The constant facts (`p_eq`, `pPrime_p`, `pPrime_n`, the `glv.rs` byte strings and `glv_lattice`) are proved by `decide`.
`Spec.lean` imports nothing beyond core; `Advice.lean` imports `Mathlib.Data.ZMod.Basic` for the modular inverse.

## How to run

```
JOLT_DIR=~/claude-work/jolt-inline-pin-a6b6 scripts/secp256k1-kat/build.sh WORK
WORK/secp256k1-kat/target/release/secp256k1-kat WORK/kat.json
lake exe secp256k1-kat WORK/kat.json
```

The checker requires the corpus to come from Jolt `a6b6dc7177ec5ea5a3c60bd5cea4409c07ca6dc5`.
To check a corpus from another Jolt commit, pass `lake exe secp256k1-kat --jolt-commit SHA WORK/kat.json`.

The first `lake exe secp256k1-kat` compiles the C code of the Mathlib modules that `ZMod` imports, which took about 10 minutes on a 10-core Mac; later runs take seconds.

## Transcribed functions

Each Lean definition cites its Rust source in its docstring.

| Lean (`JoltISA.Inlines.Secp256k1`) | Rust at the pin |
|---|---|
| `p`, `n` | `ark_secp256k1::Fq::MODULUS`, `Fr::MODULUS`, via `secp256k1_modulus` (`jolt-inlines/secp256k1/src/sequence_builder.rs`); `n` also as `glv.rs` `r` |
| `pPrime`, `pPrime_p`, `pPrime_n` | the `LUI` constants of `MulqBuilder::inline_sequence` (`sequence_builder.rs:192-198`) |
| `Limbs`, `limbsToNat`, `natToLimbs` | `limbs_to_nbiguint`, `nbiguint_to_limbs` (`jolt-inlines/sdk/src/host.rs`); the `LD` at offset `8·i` into `a[i]` (`sequence_builder.rs:162-191`) |
| `fieldLimbs?` | `nbiguint_to_field_limbs` (`host.rs:71`), `none` where its `assert!` panics |
| `mulqQuotientAdvice` | `mulq_quotient_advice` (`host.rs:98`) with `mulq_operands` (`host.rs:79`) |
| `fieldInvMul` | the `field_inv_mul` closure of `MulqBuilder::division_advice` (`sequence_builder.rs:131-160`) |
| `mulqDivisionAdvice` | `mulq_division_advice` (`host.rs:130`) |
| `quotientWords` | `QuotientAdvice::into_runtime_advice` (`host.rs:211`) |
| `divisionWords` | `ModularDivisionAdvice::into_runtime_advice` (`host.rs:217`) |
| `glvA1`, `glvB1`, `glvA2`, `natOfBytesLE` and the `glv_*_bytes` theorems | `a1`, `b1`, `a2`, `r` (`jolt-inlines/secp256k1/src/glv.rs:9-44`) |
| `glvLambda` | the `lambda` limbs of `decompose_scalar_impl` (`jolt-inlines/secp256k1/src/sdk.rs:767-772`) |
| `roundedDiv` | `rounded_div` (`glv.rs:46`), with `Int.tdiv` and `Int.tmod` for `BigInt::div_rem` |
| `glvSplit` | the body of `decompose_scalar` (`glv.rs:56`) before `to_sign_abs` |
| `toSignAbs` | `to_sign_abs` (`glv.rs:71`) |
| `decomposeScalar` | `decompose_scalar` (`glv.rs:56`) |
| `decomposeScalarToU64s` | `decompose_scalar_to_u64s` (`glv.rs:80`) and `GlvDecompositionAdvice::into_runtime_advice` (`host.rs:234`) |
| `glvrAdvice` | `GlvrAdvBuilder::advice` (`sequence_builder.rs:25-35`) |
| `Secp256k1Inline`, `joltAdvice` | the seven `InlineOp` implementations (`sequence_builder.rs:500-576`), `InlineOp::build_runtime_advice` (`host.rs`) |

The advice word order follows the builder.
MUL and SQUARE consume `w[0..3]` in order: one `VirtualAdvice` into `w[i]` per iteration of the load loop (`sequence_builder.rs:162-191`).
DIV consumes `c[0], w[0], c[1], w[1], …`: in each iteration the `VirtualAdvice` into `a[i]` (the result) comes before the one into `w[i]` (`sequence_builder.rs:178-190`), which matches the interleaving of `ModularDivisionAdvice::into_runtime_advice`.
`GLVR_ADV` consumes six words in order, one `VirtualAdvice` and one `SD` each (`emit_advice_stores`, `host.rs`; `GlvrAdvBuilder::inline_sequence`, `sequence_builder.rs:36-40`).

Rust panics in three places, and the Lean functions return `none` there.
`mulq_quotient_advice` panics in `nbiguint_to_field_limbs` when `⌊a·b/q⌋ ≥ 2^256`, which needs unreduced operands.
`mulq_division_advice` panics in `inverse().expect(…)` when `b ≡ 0 (mod q)`.
`GlvrAdvBuilder::advice` does not panic.

The tests showed that `Fq::new`, `Fr::new` reduce unreduced limbs modulo the modulus, as the transcriptions assume: `fieldInvMul` reduces both operands, and `glvrAdvice` splits `k mod n`.

## The relations

`MulRel q a b w c` is `a·b = w·q + c ∧ w < 2^256 ∧ c < 2^256`.
`DivRel q a b w c` is `c·b = w·q + a ∧ w < 2^256 ∧ c < 2^256`, where `a` is the dividend as read from memory, not reduced.
`Canonical q c` is `c < q`.
`rows_identity_iff` proves that the rows' identity `a·b + w·p' = c + 2^256·w` is equivalent to `a·b = w·q + c` when `q ≤ 2^256`.

## The bound on `w` and the carries (spec section 10, question 4)

The rows check no bound on `w` beyond its being four 64-bit limbs, that is `w < 2^256`.
The carry handling makes the identity `a·b + w·p' = c + 2^256·w` hold over the integers, as follows.

1. The rows compute the left-hand side one 64-bit column at a time, `k = 0..7`, in two registers `r[k mod 2]` (the column value) and `r[(k+1) mod 2]` (the carry count into the next column) (`sequence_builder.rs:213, 224-228`).
2. Every addition into the column is followed by `SLTU`, which yields 1 exactly when the 64-bit addition wrapped, and the carry count adds that bit (`mac_low_w_carry`, `mac_high_w_carry`, `m2ac_*_w_carry`, `sequence_builder.rs:426-497`).
   The first addition of a column uses the variant that sets the carry register instead of adding to it (`mac_low`, `mac_high`, `m2ac_low`, `m2ac_high`), because that register still holds the previous column's value, which was already stored or checked.
   The `first` flag selects the variant (`sequence_builder.rs:225-346`).
3. The column after `k` starts from the carry count of column `k` (the registers swap roles), so the column values are exact as long as the count does not wrap.
   I replicated the loop structure and counted the carry bits per column: at most 12 (scalar-field MUL, SQUARE and DIV, column 3), 9 for the base field.
   A count that small cannot wrap a 64-bit register.
4. Columns 0 to 3 are stored as `c` (MUL, SQUARE, `sequence_builder.rs:221, 354-357`) or compared with the dividend limbs reloaded from `rs1` (DIV, `sequence_builder.rs:216-218, 349-353`).
   Columns 4 to 6 are compared with `w[0..2]` (`VirtualAssertEQ`, `sequence_builder.rs:359-362`).
5. Column 7 holds only the carry from column 6 plus the high half of `a[3]·b[3]` (no `w` term reaches column 7: `w[3]·p` ends in column 4, and for the scalar field `w[3]·p2` and `w[3]·1` end in column 5).
   The rows compute `aux = MULHU(a[3], b[3])`, `r[1] = r[1] + aux`, then `assert_eq r[1], w[3]` and `assert_lte aux, r[1]` (`sequence_builder.rs:364-382`).
   `VirtualAssertLTE` compares unsigned 64-bit values (`tracer/src/instruction/virtual_assert_lte.rs`, `VirtualAssertLTE::exec`).
   Since the carry before the addition is below `2^64`, the sum wrapped exactly when the result is below `aux`, so the `assert_lte` says that column 7 did not overflow.
6. Hence the whole left-hand side is below `2^512` and equals `c + 2^256·w` exactly.
   Without the `assert_lte`, the rows would check the identity only modulo `2^512`.
   A wrap is possible only when `a·b + w·p' ≥ 2^512`, which needs operands near `2^256`.

For DIV, the same argument gives `c·b + w·p' = a + 2^256·w` with `a` the dividend limbs read again from memory after the checks are computed and before any result store (`sequence_builder.rs:383-392`).

## Inputs tested

The driver (`scripts/secp256k1-kat/src/main.rs`) calls each inline's `InlineOp::build_advice` and `build_runtime_advice`, which call `mulq_quotient_advice` and `mulq_division_advice` with Jolt's own moduli and inverse closure, through a guest-memory view.
It runs each inline in Jolt's tracer with `INLINE::trace` on a fresh CPU from `tracer/src/utils/inline_test_harness.rs`, which expands the inline through the registered expansion and patches the advice into the `VirtualAdvice` rows, and records the advice the rows received from the trace cycles.

Field inlines, each of the six:

- every pair (or every single value, for SQUARE) from 16 edge values: 0, 1, 2, `q-1`, `q-2`, `q`, `q+1`, `(q+1)/2`, `2^256-q`, `2^256-1` (all limbs `0xFFFF…`), `2^255`, `2^128`, `2^64-1`, `[0xFFFF…, 0, 0, 0]`, `[0, 0, 0, 0xFFFF…]`, and all limbs `0x8000…`;
- the spec section 5.3 case `a = 2`, `b = (q+1)/2`;
- 100 random canonical pairs and 30 pairs of uniform random 256-bit limbs, which are almost always canonical (a uniform 256-bit value is at least `q` with probability about `3.7·10^-68` for `p` and `3.7·10^-39` for `n`);
- deliberately unreduced operands, drawn uniformly from `[q, 2^256)`: for MUL and DIV, 10 pairs each with `a` unreduced, with `b` unreduced and with both unreduced (the other operand random canonical); for SQUARE, 10 unreduced values;
- for DIV, 10 random dividends each with divisor 1 and with divisor `q-1` (both also among the edge pairs).

GLV:

- 113 edge scalars: 0, 1, 2, `n-1`, `n-2`, `(n±1)/2`, `λ`, `n-λ`, `λ² mod n`, `λ±1`, `2^128-1`, `2^128`, `2^128+1`, `2^127`, `2^255`, `a1`, `b1`, `a2` and their neighbours and negatives modulo `n`, `(a1+a2)/2`, `(b1+a1)/2`, the products of `λ` with the basis entries, the rounding thresholds of `β1 = round(k·a1/n)` and `β2 = round(k·b1/n)` (the smallest `k` past `j·n + n/2` and `k ± 1, ± 2`, for `j` in `0, 1, 2, 1000`, `⌊coeff/2⌋` and `coeff - 2`), and multiples of `⌈n/coeff⌉`;
- 10,000 random scalars below `n`;
- 8 scalars outside `[0, n)` given to `decompose_scalar` directly (`-1`, `-λ`, `-(n-1)`, `-(2^200+12345)`, `n`, `2n+5`, `2^256-1`, `2^300+7`), which the production path never passes but which pin down the truncating division and the 128-bit truncation of `to_sign_abs`;
- `GLVR_ADV` advice and tracer runs on the 113 edge scalars, 4 fixed unreduced limb inputs (`n`, `n+1`, `n+2`, `2^256-1`), 10 random unreduced limb inputs in `[n, 2^256)` and 100 random scalars.

## Results

`lake exe secp256k1-kat` on the driver's output (Jolt `a6b6dc717`) runs 90,132 checks with 0 failures.

Besides the checks below, the checker verifies the Jolt commit, checks every case label against its operands (for example that an `unreduced a` case has `a ≥ q`), and runs 95 coverage checks.
The coverage checks require, among both the advice cases and the tracer runs, at least 16 edge, 100 random canonical and 10 unreduced cases for each field inline, and edge, unreduced and 100 random `GLVR_ADV` inputs.
They also require 16 named GLV edge scalars with their values (for example `(n-1)/2` and `(b1+a1)/2`) among both the GLV scalars and the `GLVR_ADV` inputs, rounding thresholds of both `β1` and `β2`, multiples of `⌈n/coeff⌉`, 10,000 random scalars, and scalars outside `[0, n)` both below 0 and at least `n`.

- Advice transcriptions: 2,247 advice cases, 5,348 checks (including the label checks).
  For every case, `joltAdvice` returns exactly the words of `build_runtime_advice`, and `mulqQuotientAdvice`, `mulqDivisionAdvice` or `decomposeScalar` (on `k mod n`) returns exactly the typed `build_advice` result.
  Lean returns `none` exactly where Rust panics: 32 zero divisors per DIV inline (`b` in `{0, q}`, against the 16 dividends), and the MUL and SQUARE cases whose quotient needs a fifth limb: per field, 3 MUL and 1 SQUARE edge cases (`a, b` in `{q+1, 2^256-1}` with at least one `2^256-1`, and `a = 2^256-1` for SQUARE), and among the unreduced cases 4 MULQ, 5 MULR, 6 SQUAREQ and 7 SQUARER cases, all with both operands unreduced.
- GLV on scalars: 10,121 scalars, 70,823 checks.
  `glvSplit` equals the untruncated split of the driver's replica of `glv.rs` (which the driver checks against `glv::decompose_scalar` on every scalar), and `decomposeScalar` and `decomposeScalarToU64s` equal `decompose_scalar` and `decompose_scalar_to_u64s`, including the 8 scalars outside `[0, n)`, where truncating division and the 128-bit truncation matter.
  For example, `decompose_scalar(-(n-1))` has an untruncated `|k1|` of 129 bits, and both Rust and Lean keep its low 128 bits.
- GLV bounds: the checker computes from `k` whether a scalar is in `[0, n)`, checks the JSON's `in_range` label against it, and for each of the 10,113 scalars in `[0, n)` (113 edge, 10,000 random) fails unless the untruncated split has `|k1| < 2^128` and `|k2| < 2^128`.
  The largest `|k1|` is `0xa2a8918ca85bafe22016d0b917e4dd76` (128 bits, at `k = (n-1)/2`) and the largest `|k2|` is `0x89b6f7af5220ac3bcf568008c3e9d1ea` (128 bits, at the random scalar `0x8607de81387b1b6afff5f2dbb04262ed41e4ca7dd704e7bd63730a0a0fe0f23e`).
  No split reaches `2^128`, and every untruncated split satisfies `k1 + λ·k2 ≡ k (mod n)`.
  I found no Jolt completeness bug.
- Edge scalars: `0 ↦ (0, 0)`, `1 ↦ (1, 0)`, `n-1 ↦ (-1, 0)`, `λ ↦ (0, 1)`, `n-λ ↦ (0, -1)`, `λ² mod n ↦ (-1, -1)`, `2^128 ↦ (-0x14ca…cfd8, -0x3086…eb15)`, `a2 ↦ (0, -a1)`; all rounding-threshold scalars split within the bounds.
- Tracer runs: 2,247 runs, 13,862 checks; 2,029 runs passed and 218 panicked, and Lean predicts each outcome from `joltAdvice` and `MulRel`/`DivRel`.

| Inline | Rows | Passing runs | Panicking runs |
|---|---|---|---|
| `SECP256K1_MULQ` | 186 | 410 | 3 edge + 4 unreduced (advice panic, quotient too large) |
| `SECP256K1_SQUAREQ` | 167 | 149 | 1 edge + 6 unreduced (advice panic) |
| `SECP256K1_DIVQ` | 194 | 343 | 32 (zero divisor) + 42 edge + 20 unreduced (dividend `≥ p`: honest advice fails `VirtualAssertEQ`) |
| `SECP256K1_MULR` | 232 | 409 | 3 edge + 5 unreduced (advice panic) |
| `SECP256K1_SQUARER` | 213 | 148 | 1 edge + 7 unreduced (advice panic) |
| `SECP256K1_DIVR` | 240 | 343 | 32 (zero divisor) + 42 edge + 20 unreduced (dividend `≥ n`) |
| `SECP256K1_GLVR_ADV` | 13 | 227 | 0 |

Among the unreduced cases, every MUL run with one unreduced operand passes, and every DIV run with only the divisor unreduced passes.
Every DIV run with an unreduced dividend panics.

The runs of each field inline include 100 random canonical inputs, and those of `GLVR_ADV` include 100 random scalars.
On every passing run, the words the `VirtualAdvice` rows received equal `joltAdvice`, the inputs at `rs1` and `rs2` are unchanged, and:

- MUL and SQUARE: `MulRel q a b w c` and `c < q` hold for the advice `w` and the stored `c`;
- DIV: the stored `c` equals the advice result, and `DivRel q a b w c` and `c < q` hold;
- `GLVR_ADV`: the six stored words equal `glvrAdvice k`, both sign words are 0 or 1, both magnitudes are below `2^128`, and `k ≡ ±k1 ± λ·k2 (mod n)`; this includes the unreduced inputs `n`, `n+1`, `n+2`, `2^256-1` and the 10 random ones in `[n, 2^256)`, which confirms that `Fr::new` reduces `k` modulo `n`.

The spec section 5.3 case `a = 2`, `b = (q+1)/2` gives `w = 1` and `c = 1` for `MULQ` and `MULR`.

I checked that the checker fails on corrupted data: changing one advice word, one stored DIV word, one stored GLV sign word and one `decompose_scalar_to_u64s` word gave 6 failures and exit status 1.
Each of the following mutations also makes it exit with status 1:

- the full corpus labelled with Jolt commit `wrong-pin` (1 failure);
- a corpus labelled `wrong-pin` with empty arrays (96 failures), and the same corpus checked with `--jolt-commit wrong-pin` (95 coverage failures);
- the corpus without the `DIVR` tracer runs (3 failures) or without the `round(b1)` threshold scalars (1 failure);
- the scalar `-(n-1)` labelled in range (1 failure);
- an `unreduced a` case whose `a` is replaced by 1 (4 failures).

No scalar in `[0, n)` violates the GLV bound, so a corpus cannot exercise that check.
I tested it by lowering the `|k1|` bound in the checker to `2^127`: the check then failed on 931 scalars with exit status 1, and I restored the bound before committing.

## Anything contradicting `docs/inline-precompiles.md`

I found no contradiction in substance.
The row counts in spec section 3 (186, 167, 194, 232, 213, 240, 13) match the traced rows.
The spec section 5.3 table matches Jolt: for `a = 2`, `b = (q+1)/2`, Jolt's advice is `w = 1` and the stored `c` is 1, for both fields.

Points the spec does not state, or states loosely:

- Section 3 cites `secp256k1/src/sdk.rs:751` for the guest's GLV checks.
  At the pin, line 751 is the signature of `decompose_scalar_impl`; the sign-word checks are at `sdk.rs:765-766` and the recombination check at `sdk.rs:781-783`.
- Jolt's honest DIV advice fails Jolt's own rows when the dividend is unreduced (`a ≥ q`): the advice gives `c·b ≡ a (mod q)` with `w = ⌊c·b/q⌋`, so `c·b - w·q = a mod q ≠ a`, and the tracer panics in `VirtualAssertEQ`.
  `Pre c` (inputs below the modulus) excludes this case, so `rows_jolt_advice_complete` is unaffected, but `Pre c` for DIV must require `a < q`; `b` may be unreduced as long as `b ≢ 0 (mod q)`.
- Jolt's MUL and SQUARE advice panics for unreduced operands with `⌊a·b/q⌋ ≥ 2^256` (`nbiguint_to_field_limbs`).
  Spec section 5.4 mentions only the DIV zero-divisor panic.
- The analytic GLV bound is `|k1| ≤ (a1 + a2)/2 = 0xa2a8918ca85bafe22016d0b917e4dd76` and `|k2| ≤ (b1 + a1)/2 = 0x8a65287bd47179fb2be08846cea267ec`, both below `2^128`; `glv_lattice` proves the lattice facts it rests on (the determinant `a1² + b1·a2 = n` and the two congruences).
  The edge scalars `(n-1)/2` and `(n+1)/2` reach the `k1` bound exactly.
  The largest `|k2|` seen, `0x89b6f7af5220ac3bcf568008c3e9d1ea`, is just below the `k2` bound.
  This supports the risk-table entry of section 11: no scalar gives a split of `2^128` or more, so the completeness lemma can keep its unconditional form.
