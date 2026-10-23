# Remove every `bv_decide`

Read `/Users/ari.biswas/Lean/jolt-qed-public/AGENTS.md` first.
Claude wrote this plan and has made mistakes in this proof before; check each claim against the code before relying on it, and stop and report if one is wrong.
Work in `/Users/ari.biswas/Lean/jolt-qed-public` on `feat/soundness`; do not commit.

## Why

The soundness theorem is closed: `#print axioms JoltInstance.soundness` (full build at `b9efd78`) gives `propext`, `sys_enable_experimental_extensions`, `Classical.choice`, `Quot.sound` and one `bv_decide` axiom, `JoltConstraints.branch_target_toNat._native.bv_decide.ax_1_5`.
`bv_decide` was accepted only to make progress; every use must go before the proof is final.
There are 22 uses (`grep -rn bv_decide JoltConstraints JoltBytecode`); change no statement while removing them.

## Part 1: the soundness use

`branch_target_toNat` (`JoltConstraints/Completeness/NextUnexpandedPCEqPCPlusImmIfShouldBranch.lean`, line 104) proves `(offset.signExtend 128).setWidth 64 = offset.signExtend 64` by `bv_decide`.
`encoded_branch_offset` (`JoltBytecode/JoltISA/Values.lean`, line 145) proves the same fact by `bv_decide`, after a `change` to that form.
Prove it once without `bv_decide` in `Values.lean` (for example by `BitVec.eq_of_getLsbD_eq` with `getLsbD_setWidth` and `getLsbD_signExtend`, or a core lemma if one exists), and use it in `branch_target_toNat`; `JoltConstraints` already imports `JoltBytecode`.
Then build `JoltConstraints` and run `#print axioms JoltInstance.soundness`; it should list only `propext`, `sys_enable_experimental_extensions`, `Classical.choice` and `Quot.sound`.
Report this result before starting Part 2.

## Part 2: the other uses

These are on the completeness and bytecode-equivalence paths:

- `JoltConstraints/Completeness/Helpers/LookupEntryProofHelpers.lean`: eight uses, for the three window-mask entries (a low-bit mask agrees at widths 64 and 128), `halfword_aligned` and `word_aligned` (alignment from the low bits), `lookupEntryCorrect_RangeCheckAligned`, and two byte-swap identities near `rev8w_eq`.
- `JoltBytecode/InstructionEquivalence/Instructions/StoreFamily/Splice.lean`: ten uses, low-bit masks and byte extraction such as `lowByte_zeroExtend`.
- `JoltBytecode/InstructionEquivalence/Instructions/Natives/Sd.lean`, line 83: `x &&& 7 = 0 → x &&& -8 = x`.

Group these by the fact they prove, prove each shared fact once, and derive the uses from it; for example, the three window-mask uses differ only in the mask, and the alignment facts in Splice and Sd may share one lemma.
`JoltConstraints/Soundness/Layer4/Interleave.lean` replaced earlier `bv_decide` uses with bit-level proofs (`getLsbD` simp lemmas, `interval_cases` on a small index range); follow that style where it fits.

## Rules

No `native_decide`, `decide +kernel` or raised limits; `decide` on a closed small term is fine.
Keep each proof under about 60 lines.
If a use needs a long brute-force proof, stop and report the goal rather than write it.
Do not edit `JoltConstraints/model_review.md` or `methods/soundness.md`; the auditor updates the `bv_decide` list from your report.

## Before you stop

Build `JoltBytecode` and `JoltConstraints`; `grep -rn bv_decide JoltConstraints JoltBytecode` should find only comments.
Run `#print axioms` on `JoltInstance.soundness` and `JoltInstance.completeness`, and time every changed proof; list any over about ten seconds.
Write `methods/bv-decide-report.md` with each changed declaration (file and line), each new lemma, the build and axiom results, and timings.
Do not commit.
