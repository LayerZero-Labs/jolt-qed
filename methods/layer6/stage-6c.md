# Layer 6, stage 6c: the honest division replay

Read `/Users/ari.biswas/Lean/jolt-qed-public/AGENTS.md`, `methods/layer6/reuse.md` and `methods/layer6/stage-6a-report.md` first.
Claude wrote this plan and has made mistakes in this proof before; check each claim against the code before relying on it, and stop and report if one is wrong.
Work in `/Users/ari.biswas/Lean/jolt-qed-public` on `feat/soundness`; do not commit.
Another agent works in Layer 5 files, `TerminalNextPC.lean`, `StallSuffix.lean` and `LastJump.lean`, and later in a new `DivisionPrograms.lean`; do not edit those.
Edit `DivisionAppend.lean`; you may make a private lemma of `PlainRow.lean` or `DivisionDefs.lean` public in place, and say which in the report.

## Why

`division_append_honest` is proved from the three lemmas staged in `DivisionAppend.lean`.
They build the honest-advice rows of a division block and carry the witness run's invariant over to them.
This is the core of the division block.

## The task

Prove the three staged lemmas without changing their statements.

1. `division_replay_rows`: split `honestRun` into one execution per instruction (`execProgram_instr_run_retire_inv`) and append them one at a time with `appendUntrustedRow` (`PlainRow.lean`), by induction over the instruction list.
   `arithmetic_advice_suffix_run` (`DivisionDefs.lean`) builds the witness run the same way, in the other direction; if the two share a part, extract it rather than copy.
   The first row's linkage comes from `entry`, as `rawEntry_starts` and `rawEntry_linked` (`PlainRow.lean`) do for a raw entry.
   Each later row follows a row whose countdown is not zero, so its index is one more and its pre-state is the previous post-state.
   Division rows run the same under `execWithTapeAnswer` and `execInstr` (`arithmetic_exec_eq`).
2. `division_replay_complete`.
   The candidate's first block row starts at `pre`: the run's linkage rule and `entry` give the same prepared state.
   Before its last row, a division program writes only temporaries (the stage 6a report checked the eight programs; prove it once over the instruction list).
   So at every block row, the candidate's and the replay's pre-states agree with `pre` outside temporaries, and the candidate's row observations (`RepresentsRows`) transfer to the replay for every operand that is not a temporary.
   No division row touches memory, so RAM addresses are zero in both runs, and `same` gives equal final memory and device, hence equal `TraceWitness.finalRamWord`.
   With all rows done, only registers that are not temporaries are live, and `same` gives them equal values.
   Interior rows have a nonzero countdown, so none is a stable stall.
3. `division_replay_honest_new`: unfold `honestTracerAdviceAtStepN` (`JoltConstraints/honest_trace.lean`) at a new row.
   Its expansion starts at the block's first row (`starts`, and later block rows do not start a source), whose pre-state is `pre` (`firstPre`) and whose source is `kind.source rd rs1 rs2 placeholder` (`source`).
   The source's advice list is `[kind.honestAdvice rd rs1 rs2 pre]`, and the single advice row is the first advice row of the block, so it gets the head of the list; every other row gets none on both sides.

Keep each proof under about 60 lines.
If a step needs a fact that is not a short proof and is not named here or in `reuse.md`, stage it as its own lemma with `sorry`, and stop and report.

## Before you stop

Build `JoltConstraints.Soundness.Layer6.DivisionBlock`, and the whole of `JoltConstraints` if the other agent's files build.
Run `#print axioms JoltInstance.division_append_honest`; it should not reach `sorryAx` unless you staged a lemma.
Write `methods/layer6/stage-6c-report.md` with each new or changed declaration (file and line), each lemma made public, any proof slower than about ten seconds, and the build and axiom results.
Do not commit.
Then stop.
