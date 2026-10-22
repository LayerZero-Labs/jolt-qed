# Layer 6, stage 3a: split the files, then stage the division block

Read `/Users/ari.biswas/Lean/jolt-qed-public/AGENTS.md`, `methods/layer6/stage-2-report.md` and `methods/layer6/reuse.md` first.
Claude wrote this plan and has made mistakes in this proof before; check each claim against the code before relying on it, and stop and report if one is wrong.
Work in `/Users/ari.biswas/Lean/jolt-qed-public` on `feat/soundness`; do not commit.
Another agent will work in the same checkout after Part A; edit only the files this plan names.

## Part A: one file per staged lemma (then stop)

`JoltConstraints/Soundness/Layer6/PrefixAgreement.lean` holds the definitions, the five staged lemmas and their callers.
Two agents cannot work on it at once, so restructure it, changing no statement and no proof:

- `Layer6/PrefixState.lean`: `BoundaryState`, `expansionRowCount`, `ExpansionHasAdvice`, `ExpansionLive`, `RunExtends`, `ExpansionState`.
- `Layer6/BoundaryStart.lean`: `boundaryState_empty` and `expansion_start`, still `sorry`.
- `Layer6/DivisionBlock.lean`: `division_block`, still `sorry`.
- `Layer6/RowStep.lean`: `row_step`, still `sorry`.
- `Layer6/ExpansionFinish.lean`: `expansion_finish`, still `sorry`.
- `Layer6/PrefixAgreement.lean` keeps `boundary_step` and `soundness_execution_prefix_agreement` and imports the four files above.

Also add to `Soundness/Layer5/Registers.lean` two small proved helpers, each with a docstring: `RegisterAgreement` gives `RegisterAgreementOn live` for every `live`, and `RegisterAgreementOn` for one live set gives it for any smaller live set.

Build `JoltConstraints`, check that `#print axioms JoltInstance.soundness` reaches `sorryAx` only through the same five lemmas and helpers C and D, add a short "Part A" section to `methods/layer6/stage-3a-report.md`, and stop.
Ari will commit Part A and tell you to continue.

## Part B: stage the division block

`division_block` (now in `DivisionBlock.lean`) appends a whole division expansion with honest advice.
Do not change its statement or `ExpansionState`.
The argument, for `rem a0, a1, zero` where the witness's quotient is 5 and the honest one is 0:

1. The source at `first` is one of the eight divisions with `rd ≠ x0`, and its rows are its generated program's rows (`ExpandedSource.ofPureProgram`).
2. Run the witness's rows on Sail states with the witness's own advice: each row's Layer 5 step lemma gives its execution and keeps register agreement on the registers its rows read.
   Composed (see "Running a whole expansion" in `reuse.md`), this is a successful run of the generated program with advice 5, ending in agreement with the witness's next register column outside instruction temporaries, with the witness's RAM unchanged.
   Agreement on instruction temporaries is not available at the start (they are dead) and is not needed: the block writes each before reading it.
3. `remProgram_sound` turns that run into its final Sail state: `stateAfterWrite js.sail a0 (honest remainder)`.
   For DIV, DIVU and DIVW, `*Program_sound` instead gives that the witness's advice is the honest value.
4. `remProgram_concrete` gives the honest run from the same start, with the same final Sail state; split it into its rows to extend the run.
   The run's other state parts (device, tape, virtual registers outside temporaries) are unchanged across the block; use the frame lemmas in `reuse.md`.
5. The new run's rows match the witness's on PC, RAM address, and every operand that is not an instruction temporary; registers outside temporaries agree after the block, and RAM is unchanged.

Stage each step that is not a short proof as its own lemma with `sorry`, in `DivisionBlock.lean`, with a docstring and the REM example.
State the step 2 lemma for any row kind that occurs in the eight division expansions, not per division: one statement, over the rows of a sequence that contains no load, store, jump or HostIO.
Then prove `division_block` from the staged lemmas, with no `sorry` in its body.
Step 2 needs the Layer 5 step lemmas to work with `RegisterAgreementOn` instead of full `RegisterAgreement`; do not port them in this stage, but state step 2 so that the port is the only missing piece, and say in the report which step lemmas it needs.
Also say which of these step lemmas do not exist yet (VirtualAdvice has none).

Before you stop, check each staged statement against "Before staging a statement" in `AGENTS.md`.
Build, run the axiom audit, add a "Part B" section to the report with each new declaration (file and line, staged or proved) and any proof slower than about ten seconds, and stop.
Do not commit.
