# Layer 6: the branch and tape-load steps, and the division layout

Read `/Users/ari.biswas/Lean/jolt-qed-public/AGENTS.md`, `methods/layer6/reuse.md`, the Part A section of `methods/layer6/stage-4a-report.md`, and `methods/layer6/stage-6b-report.md` first.
Claude wrote this plan and has made mistakes in this proof before; check each claim against the code before relying on it, and stop and report if one is wrong.
Work in `/Users/ari.biswas/Lean/jolt-qed-public` on `feat/soundness`; do not commit.
Other agents work in `PlainRow.lean`, `RowStepKinds.lean`, `RowStepCommon.lean`, `RowStepJalr.lean`, `RamCutAgreement.lean`, `Jal.lean`, `HostCallRegisterFrame.lean`, `LoadDoubleword.lean`, `StoreDoubleword.lean`, `RamStoreAgreement.lean` and `RamInitialization.lean`; do not edit those.
Edit only new files `Soundness/Layer5/Branch.lean` and `Soundness/Layer5/AdviceLoad.lean`, `Soundness/Layer6/TerminalNextPC.lean` (public or generalize in place only), `Soundness/Layer6/DivisionDefs.lean` (only `division_expansion_layout` and helpers for it), new Layer 6 files for those helpers, and `JoltConstraints.lean` to import new files; you may make a private lemma public in place elsewhere and say which in the report.

## Part 1: two missing Layer 5 steps

`plain_row_step_other` (`PlainRow.lean`) will need a step over `RegisterAgreementOn` for every plain row kind; the stage 6b report lists the branches and `VirtualAdviceLoad` as having none.
Write them, shaped like the ported steps (`binaryAssertion_step`, `advice_step`):

- Branches (BEQ, BNE, BLT, BGE, BLTU, BGEU), one lemma for all six: both operands live, no register write, the row executes successfully under `execWithTapeAnswer`, and agreement holds on the same live set.
  The plan first claimed a canonical expanded branch never fails Sail's target-alignment check; that is false (report: `BEQ x0, x0, +1` passes preprocessing, and its taken target `0x80000001` fails `jump_to`'s bit-0 assertion).
  Derive alignment from the witness instead: when the branch is taken (`stall_branch_lookup_decision`, `Layer7/StallSuffix.lean`), the constrained next unexpanded PC is source address plus offset; at the last cycle or before padding it must be zero, which a branch target cannot be (`branch_target_ne_zero`); so the next cycle is real, its row's address is even (`bytecode_address_ok`), and the target equals it.
  `terminal_real_successor_address` and `terminal_branch_real_target` (`Soundness/Layer6/TerminalNextPC.lean`, private) already do this for a terminal branch; make them public in place and reuse them, generalizing in place if the plain step needs a weaker hypothesis.
  An untaken branch executes without the alignment check.
- `VirtualAdviceLoad`: as `advice_step` (`Layer5/Advice.lean`), the witness's written value is a 64-bit word `v`; executing with tape answer `v` (`execWithTapeAnswer`, `Layer5/TapeSemantics.lean`) writes `v`; the destination becomes live.
  Execution fails for a byte count other than 1, 2, 4 or 8; prove from the expansion checker that expanded bytecode never has one.

Check both statements against "Before staging a statement" in `AGENTS.md` and against Jolt's tracer at the pin.

## Part 2: `division_expansion_layout`

Prove `division_expansion_layout` (`DivisionDefs.lean`) without changing its statement: the advice-bearing source at `first` is one of the eight divisions with `rd ≠ x0`, the image's instruction at its address is that source, the block is exactly the generated program's rows, and they form an `ArithmeticAdviceSequence`.

- `expand_program_source_of_row` (`program_facts.lean`) gives the source and its expansion rows; `expand_program_layout` and `first`'s `starts_source` make `expansionInstructions bytecode first` exactly those rows.
- Only the eight division expansions with `rd ≠ x0` contain `VirtualAdvice` (stage 2 report); prove that over `SourceInstruction.expand` once, not per source.
- `Rv64ProgramImage.instructionAt` (`honest_trace.lean`) looks a source up by address; you need that two image sources never share an address, which follows from successful preprocessing (`pc_map_ok_distinct_addresses`).
  If that fact is not a short proof from existing lemmas, stage it and report.
- For `ArithmeticAdviceSequence`: `arithmetic` from `division_program_rows` (`DivisionPrograms.lean`), `temporaries` from the expansion checker (`sequenceOk_tempsReadAfterWrite`), and `program_eq` and `singleAdvice` by evaluating the eight generated programs once, as `division_program_rows` does.

Keep each proof under about 60 lines.
If a step needs a fact that is not a short proof and is not named here or in `reuse.md`, stage it as its own lemma with `sorry`, and stop and report.

## Before you stop

Build `JoltConstraints` (or your own modules if another agent's edits break it).
Run `#print axioms` on the two new steps and on `JoltInstance.division_block`; none should reach `sorryAx` unless you staged a lemma.
Write `methods/layer6/plain-steps-and-layout-report.md` with each new or changed declaration (file and line), each lemma made public, any proof slower than about ten seconds, and the build and axiom results.
Do not commit.
Then stop.

## Correction after the tape-load finding

The expansion checker does not check a `VirtualAdviceLoad` byte count: `nativeRowOk` and `sequenceOk` both accept `VirtualAdviceLoad x1 9`, which `execWithTapeAnswer` rejects.
The tape-load step, with the checker change that fixes this, is reassigned to the agent proving `plain_row_step_other` (see the last section of `methods/layer6/plain-row-other.md`).
This agent now does Part 2 only: `division_expansion_layout`.
Do not edit `expansion_facts.lean`, `TapeRebuild.lean`, `AdviceExpansion.lean`, `PlainRow.lean` or `Layer5/AdviceLoad.lean`; the checker change will rebuild most of `JoltConstraints`, so build only your own modules while it is in progress.

## Correction: module placement of `division_expansion_layout`

`division_program_rows` (`DivisionPrograms.lean`) cannot be used in `DivisionDefs.lean`, because `DivisionPrograms.lean` imports `DivisionDefs.lean`.
Move `division_expansion_layout`, with its name, statement and docstring unchanged, into a new `Soundness/Layer6/DivisionLayout.lean` that imports `DivisionPrograms`; import the new module from `DivisionBlock.lean` and add it to `JoltConstraints.lean`.
Helpers for the layout proof go in `DivisionLayout.lean` or new files; you may make a private lemma in `DivisionPrograms.lean` public in place (for example `division_program_rows_shape`) and extract a general lemma from an existing proof there rather than copy it.
