# Step 5: completeness about Jolt's prover

Ari approved this step on 2026-11-03.
It is written for an agent that has not seen the earlier steps.
Delete this file once the step is reviewed and its content is in the code and in `JoltConstraints/model_review.md`.

## Context

- Work only in the git worktree `/Users/ari.biswas/Lean/jolt-qed-completeness`, branch `migration/completeness-prover`, which starts at commit `e299498`.
  Another agent is changing soundness files in `/Users/ari.biswas/Lean/jolt-qed-public`; do not touch that directory.
  Read `AGENTS.md` first; it overrides your defaults.
- Jolt's code is in `/Users/ari.biswas/Work-with-A16z/jolt`; read it with `git -C /Users/ari.biswas/Work-with-A16z/jolt show c6703570:<path>`.
- Read `reports/2026-11-03-constraints-migration-completeness.md` for the current state of completeness.
  `lake build JoltConstraints.Completeness` succeeds at `e299498`.

## Why the statement changes

Jolt is a proof system: a prover and a verifier.
With the cryptography removed, the prover sends its table of witness columns in the clear, and the verifier checks `AllConstraints` on it.
Completeness of Jolt says: for every instance and every witness that puts it in the language, the verifier accepts the table Jolt's prover builds, at the sizes Jolt's prover picks.

The current `JoltInstance.completeness` (`JoltConstraints/Completeness/completeness.lean:69`) proves something weaker: that some table is accepted.
Its proof uses the honest trace at corrected sizes (`HonestTrace.corrected_prover_config`, RAM size `K = pow2(h + 1)`, where `h` is the index of the highest RAM word the run touched).
Jolt's prover instead picks `K = pow2(h)` (`Trace.prover_config` in `JoltConstraints/prover_config.lean`, modelling `ProverConfig::derive_from_dimensions` in `crates/jolt-prover/src/config.rs`).
An array of `K` words holds indices `0` to `K - 1`, so Jolt's table cannot hold word `h` when `h` is a power of two (a16z/jolt#1951 item 4, `bug-report/ram-k-off-by-one/`).

## Work

1. Add `HonestTrace.witness_params (config : ProverConfig) (proverAccepts : trace.prover_config joltInstance = some config) : WitnessParams`: the witness sizes Jolt's prover picks, built from Jolt's `ProverConfig` the way `HonestTrace.corrected_witness_params` (`JoltConstraints/witness_params.lean:145`) is built from the corrected one.
   Its fields must match what Jolt's prover uses; cite the Jolt code.
2. Restate `JoltInstance.completeness` exactly as Ari approved:

   ```lean
   theorem JoltInstance.completeness {F : Type} [Field F]
       (joltInstance : JoltInstance SourceInstruction)
       (assumptions : joltInstance.CompletenessAssumptions)
       (privateInputs : JoltPrivateInputs)
       (trace : HonestTrace joltInstance privateInputs)
       (claimsRunOutputs : trace.matches_outputs joltInstance)
       (spoilAssertsPass : trace.SpoilAssertsPass)
       (config : ProverConfig)
       (proverAccepts : trace.prover_config joltInstance = some config) :
       JoltConstraints.AllConstraints joltInstance privateInputs
         (HonestTrace.honestWitness (F := F) (trace.witness_params config proverAccepts) trace)
   ```

   Adjust only the Lean details needed to make it elaborate, and keep its meaning: every honest trace that meets the three conditions of `InLanguage`, and the honest witness at Jolt's own sizes.
3. Keep the current statement as `JoltInstance.completeness_someWitness`, with its statement unchanged, and prove it from the new `JoltInstance.completeness` by unpacking `InLanguage`.
   Do this first, with the new theorem's body as `sorry`, and build, so the top-down shape is checked before the long proof.
4. Then prove the new `JoltInstance.completeness`.
   Most of the existing proof carries over: repeat it at Jolt's sizes.
   Keep every existing helper lemma, including the corrected-size ones such as `HonestTrace.allConstraints_corrected_sizes` and `HonestTrace.corrected_witness_params_ram_bounds`; adapt each one to Jolt's sizes rather than deleting it.
   Prefer generalizing a helper over the sizes it uses, so one lemma serves both, over writing a second copy (`AGENTS.md`, "Making proofs general").
5. The one known-false fact.
   At Jolt's sizes the table holds every touched RAM word only when `h < K`, which fails when `h` is a power of two.
   Ari decided on 2026-11-03 to leave this as a known-false gap: put exactly that fact in one lemma, stated for an honest trace and Jolt's config, whose body is `sorry`, and use it only where the proof needs it.
   Its docstring says, in plain words, what fails and why, with an example (`h = 1024` gives `K = pow2(1024) = 1024`, which holds indices `0` to `1023`), and links a16z/jolt#1951 item 4.
   At Jolt's sizes, the verifier's RAM maximum should now hold, because `pow2(h) ≤ pow2(⌊(heap_end - lowest)/8⌋)`; if so, prove that half of the RAM-bounds lemma instead of leaving it `sorry`.
6. The existing completeness gaps stay as they are: (01), (37), (38), the (08) and (11) wrap lemmas, and whatever of the RAM-bounds lemma you cannot prove.
   Add no other `sorry`.

## Approved without asking

Ari has approved, in advance, any proof repair and any new, changed or generalized helper lemma, when both of these hold:

- the two statements in work items 2 and 3, `InLanguage`, the assumptions and the restrictions stay as given;
- every caller can prove a helper's hypotheses from the premises it already has.

Make such changes without stopping, and list each one in the report.

## Stop and report to Ari

Do not stop at the first problem.
Leave a blocked lemma as it is, finish everything else, then stop and report all blockers together.
A blocker is a fact the proof needs, other than the one in work item 5, that you cannot prove from the current premises; state it as its own named lemma with `sorry` and give the exact missing fact or a counterexample.

## Rules

- `AGENTS.md` applies.
- No `native_decide`, `decide +kernel` or `bv_decide`, and never raise `maxHeartbeats`.
- No new premise on any theorem beyond the statements above.
- Do not commit.
- Before every build run `pgrep -fl lake`, and never start a build while another is running in this worktree.
  The other agent builds in `/Users/ari.biswas/Lean/jolt-qed-public`; its Lake processes run there, not in your worktree, so a process whose path is that directory does not block you.
- Give every new or changed declaration a docstring that defines its terms and gives a concrete example.
- List every proof that takes more than about ten seconds.
- In Markdown, one sentence per line; in prose, name the actor (Jolt's tracer, prover or verifier), not "Rust".
- Put scratch files outside the repository and outside `/tmp`.

## Deliverables

1. The diff in this worktree, uncommitted.
2. "Proofs owed" in `JoltConstraints/model_review.md` updated to match the code, and the completeness lines of `JoltConstraints/constraints.md` if they change.
3. A report, `reports/2026-11-03-completeness-jolt-prover.md`, one sentence per line, giving the Lean commit `e299498`, every declaration changed or added with file and line, every statement change, the build commands and results, `#print axioms` for both theorems, any proof slower than about ten seconds, and every blocker.

Then stop for review.
