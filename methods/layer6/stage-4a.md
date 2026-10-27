# Layer 6, stage 4a: live-register step lemmas, then the witness-advice run

Read `/Users/ari.biswas/Lean/jolt-qed-public/AGENTS.md`, `methods/layer6/stage-3a-report.md` and `methods/layer6/reuse.md` first.
Claude wrote this plan and has made mistakes in this proof before; check each claim against the code before relying on it, and stop and report if one is wrong.
Work in `/Users/ari.biswas/Lean/jolt-qed-public` on `feat/soundness`; do not commit.
Another agent works in the same checkout, in `Soundness/Layer6/BoundaryStart.lean` only; do not edit that file.

## Why

`arithmetic_advice_sequence_run` (`Soundness/Layer6/DivisionBlock.lean`) runs a division expansion's rows with the witness's own advice.
At the start of an expansion the instruction temporaries are dead, so the row steps must work with `RegisterAgreementOn live` instead of full `RegisterAgreement`.
The Layer 5 step lemmas use full agreement, and no proof outside `Soundness/Layer5/` uses them yet, so their statements can change freely.

## Part A: the port (then stop)

1. Generalize the register helpers to `RegisterAgreementOn`: `read` and the operand helpers need their source registers live; `write` makes the destination live; `noWrite` and `advance_pc` keep the live set.
   They are in `Soundness/Layer5/Registers.lean`, `RegisterInputs.lean` and the finisher `registerWrite_step` in `LookupWrite.lean`.
   Prove each once for `RegisterAgreementOn`; if a full-agreement version is still used, derive it from the general one rather than keeping a second proof, and delete any that no proof uses.
2. Port the eight step lemmas the division expansions use to `RegisterAgreementOn`, each requiring its source registers to be live and returning agreement with the destination added: `addi_step` (`AddImmediate.lean`), `arithmetic_step` (`Arithmetic.lean`), `xor_step` (`Xor.lean`), `virtualBinary_step` (`VirtualBinary.lean`), `unaryWord_step` (`UnaryWord.lean`), `binaryAssertion_step` (`AssertionsBinary.lean`), `mulAssertion_step` (`AssertionMulOverflow.lean`), `assertLTE_step` (`AssertLessThanEqual.lean`).
   The families share the finisher and operand helpers, so most of the change is in step 1; do not copy a proof per family.
3. Write the missing VirtualAdvice step in a new file `Soundness/Layer5/Advice.lean`: at a selected VirtualAdvice row, the witness's written value (its lookup output, written through `RdWriteValue`) is a 64-bit word `v`, and executing the row with runtime advice `v` writes `v` to its destination, which becomes live.
   The advice row's lookup operand is free (the `Advice` flag gives combined operands), so `v` is whatever the witness chose; only the range check makes it a word.
   `virtual_advice_run` (`reuse.md`) gives the execution side.

Leave the other Layer 5 step lemmas on full agreement for now; a later stage ports them for `row_step`.
Build `JoltConstraints`, run the axiom audit (no new `sorryAx`), add a "Part A" section to `methods/layer6/stage-4a-report.md` listing every changed statement (old and new) and any proof slower than about ten seconds, and stop.
Ari will commit Part A and tell you to continue.

## Part B: the witness-advice run

1. Stage, in a new file `Soundness/Layer6/PlainRow.lean`, one row step for rows that use no restriction: from an `ExpansionState` with `done` below the row count, where the next row is none of LD, SD, HostIO, JAL, JALR, extend the run by that row and get `ExpansionState` with `done + 1`.
   The row's runtime advice is the witness's written value at a VirtualAdvice row; its tape answer is the witness's written value at a tape read.
   It needs no honest advice, so the division block can use it on a run that carries the witness's advice, and `row_step` can use it later for the same rows of other expansions.
   If some row kind needs the soundness assumptions (a branch row may need `NextPCNoWrap`), give the row step that hypothesis; `arithmetic_advice_sequence_run` and `division_block` may then take it too, since their caller `boundary_step` has it.
   Report each such added hypothesis.
2. Prove it by cases on the row's instruction, with one short case per kind that applies that kind's step lemma, for the twelve kinds in `DivisionArithmeticRow` (`DivisionBlock.lean`).
   Stage the remaining kinds together as one statement with `sorry`, in `PlainRow.lean`; a later stage proves it when it ports the other step lemmas.
3. Prove `arithmetic_advice_sequence_run` from the row step, by induction over the expansion's rows, composing the rows' executions into the `Program.Run` it returns (`execProgram_instr_run_retire`, `reuse.md`).
   Its statement does not change.

Before you stop, check each new statement against "Before staging a statement" in `AGENTS.md`.
Build, run the axiom audit, add a "Part B" section to the report with each new declaration (file and line, staged or proved) and any proof slower than about ten seconds, and stop.
Do not commit.
