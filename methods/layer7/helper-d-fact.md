# Layer 7, helper D: the spoil-assert expansion fact

Read `/Users/ari.biswas/Lean/jolt-qed-public/AGENTS.md`, `methods/layer6/reuse.md` and `methods/layer7/helper-d-report.md` first.
Claude wrote this plan and has made mistakes in this proof before; check each claim against the code before relying on it, and stop and report if one is wrong.
Work in `/Users/ari.biswas/Lean/jolt-qed-public` on `feat/soundness`; do not commit.
Edit only `JoltConstraints/expansion_facts.lean` and `Soundness/Layer7/SpoilAsserts.lean`.
`expansion_facts.lean` is imported by almost everything, so editing it rebuilds most of the project for every agent in this checkout: make the edit in one step, and expect one slow build.

## Why

Helper D is proved from one staged fact, `source_spoil_assert_read_not_temporary` (`SpoilAsserts.lean`): a `VirtualAssertEQ` with a nonzero immediate in one source's expansion reads no instruction temporary.
The fact is true at the pin: every `VirtualAssertEQ` the expander emits has immediate 0, and a guest's own spoil assert decodes to architectural registers (helper D report).
The expansion checker does not give it yet: it accepts a sequence in which a spoil assert reads a temporary.
The checker is our own proof tool, so adding one check to it changes no statement; it replaces a case split over all sources.

## The task

1. Add a check to `sequenceOk` (`expansion_facts.lean`): no instruction in the sequence is a `VirtualAssertEQ` with a nonzero immediate.
   Add its extraction lemma beside `sequenceOk_advicePairsOk`.
   The per-source checker proofs (`slli_ok` and the rest) evaluate the whole of `sequenceOk`, so they should need no change; if one fails, the expansion does contain such an assert, so stop and report it.
2. Prove `source_spoil_assert_read_not_temporary` with `expand_instruction_property`.
   For a sequence, the new check rules the row out.
   For a native row, `nativeRowOk` already includes `tempsReadAfterWrite` of the one-row list, so a native row reads no temporary at all.
3. Measure the elaboration time of `expansion_facts.lean` before and after, as the "Proof-performance cleanup" note in `JoltConstraints/model_review.md` does.

## Before you stop

Build `JoltConstraints` (or your own modules if another agent's edits break it).
Run `#print axioms JoltInstance.soundness_spoil_asserts_pass`; it should not reach `sorryAx`.
Add a "Spoil-assert fact" section to `methods/layer7/helper-d-report.md` with the new declarations (file and line), the elaboration time before and after, and the build and axiom results.
Do not commit.
Then stop.
