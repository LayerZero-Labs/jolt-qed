# Remove the soundness `bv_decide`

Read `/Users/ari.biswas/Lean/jolt-qed-public/AGENTS.md` first.
Claude wrote this plan and has made mistakes in this proof before; check each claim against the code before relying on it, and stop and report if one is wrong.
Work in `/Users/ari.biswas/Lean/jolt-qed-public` on `feat/soundness`; do not commit.

## Why

The soundness theorem is closed: `#print axioms JoltInstance.soundness` (full build at `b9efd78`) gives `propext`, `sys_enable_experimental_extensions`, `Classical.choice`, `Quot.sound` and one `bv_decide` axiom, `JoltConstraints.branch_target_toNat._native.bv_decide.ax_1_5`.
`bv_decide` was accepted only to make progress; the soundness theorem must not depend on it.
The other 19 uses in the repository are in completeness and bytecode-equivalence proofs that the soundness theorem does not use; they are out of scope (Ari, 2026-10-23).
Change no statement.

## Part 1: the soundness use

`branch_target_toNat` (`JoltConstraints/Completeness/NextUnexpandedPCEqPCPlusImmIfShouldBranch.lean`, line 104) proves `(offset.signExtend 128).setWidth 64 = offset.signExtend 64` by `bv_decide`.
`encoded_branch_offset` (`JoltBytecode/JoltISA/Values.lean`, line 145) proves the same fact by `bv_decide`, after a `change` to that form.
Prove it once without `bv_decide` in `Values.lean` (for example by `BitVec.eq_of_getLsbD_eq` with `getLsbD_setWidth` and `getLsbD_signExtend`, or a core lemma if one exists), and use it in `branch_target_toNat`; `JoltConstraints` already imports `JoltBytecode`.
Then build `JoltConstraints` and run `#print axioms JoltInstance.soundness`; it should list only `propext`, `sys_enable_experimental_extensions`, `Classical.choice` and `Quot.sound`.
Then stop.

## Rules

No `native_decide`, `decide +kernel` or raised limits; `decide` on a closed small term is fine.
Keep each proof under about 60 lines.
If a use needs a long brute-force proof, stop and report the goal rather than write it.
Do not edit `JoltConstraints/model_review.md` or `methods/soundness.md`; the auditor updates the `bv_decide` list from your report.

## Before you stop

Build `JoltBytecode` and `JoltConstraints`, run `#print axioms JoltInstance.soundness`, and time every changed proof; list any over about ten seconds.
Write `methods/bv-decide-report.md` with each changed declaration (file and line), each new lemma, the build and axiom results, and timings.
Do not commit.
