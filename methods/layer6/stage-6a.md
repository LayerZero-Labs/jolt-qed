# Layer 6, stage 6a: append the honest division rows

Read `/Users/ari.biswas/Lean/jolt-qed-public/AGENTS.md`, `methods/layer6/reuse.md` and `methods/layer6/stage-4a-report.md` first.
Claude wrote this plan and has made mistakes in this proof before; check each claim against the code before relying on it, and stop and report if one is wrong.
Work in `/Users/ari.biswas/Lean/jolt-qed-public` on `feat/soundness`; do not commit.
Your Part B work is reviewed but not yet committed, because `LastJump.lean` also holds the other agent's unfinished edits; build on it as it is.
The other agent works in `TerminalNextPC.lean`, `ExpansionFinish.lean`, and parts of `LastJump.lean` and `StallSuffix.lean`; do not edit those four files.
Edit `DivisionBlock.lean`, and put new lemmas in a new file `Soundness/Layer6/DivisionAppend.lean` that `DivisionBlock.lean` imports, so that `DivisionBlock.lean` stays readable.
`division_append_honest` uses definitions from `DivisionBlock.lean`, so to avoid an import cycle first move the definitions it needs (`DivisionKind` through `DivisionFinalAgreement`, and helpers such as `arithmetic_exec_eq`) unchanged into a new `Soundness/Layer6/DivisionDefs.lean` that both files import.
Do not edit `JoltConstraints/model_review.md` or `methods/soundness.md`.

## Why

`division_append_honest` (`DivisionBlock.lean`) is the hardest of the four division gaps.
It turns the witness-advice run into the honest-advice run that `BoundaryState` needs, so every program with a DIV or REM depends on it.

## The task

Prove `division_append_honest` without changing its statement.
The run `run'` is `run` followed by one row per instruction of the honest program run `honestRun`, with the honest advice word on the VirtualAdvice row.
Each field then follows from `complete` (the witness-advice candidate) and `same` (the two final states agree outside temporaries):

1. Split `honestRun` into one successful execution per instruction (`execProgram_instr_run_retire_inv`, `Program.Run.append_inv`), and build `run'` with `appendUntrustedRow` (`PlainRow.lean`).
   Arithmetic rows run the same under `execWithTapeAnswer` and `execInstr` (`arithmetic_exec_eq`, private in `DivisionBlock.lean`).
   The first row's entry comes from `entry`; each later row's pre-state is the previous row's post-state.
2. Row observations (`RepresentsRows`).
   The PC and RAM address of each row are the same as in the candidate, since both runs use the same bytecode rows and no division row touches memory.
   For the operand values, the candidate gives the witness's value for every operand that is not a temporary.
   It remains to show the honest pre-state has the same value there.
   Before its last row, a division program writes only temporaries, so every other register still holds its value from `pre` in both runs.
   Check this against the eight generated programs before relying on it; prove it once over the instruction list, not once per program.
3. RAM at the cut and the termination word: no division row stores, and `same` gives equal Sail memory and device at the end, so `TraceWitness.finalRamWord` is the same for both runs.
4. `registers`: with all rows done, only registers that are not temporaries are live; `same` gives equal values there.
5. `noEarlierStop`: interior rows have a nonzero countdown, so none is a stable stall (Part B uses the same fact).
6. Honest advice at every row of `run'`: the old rows keep theirs (`honestTracerAdviceAtStepN_extract`, `Layer7/TerminationStore.lean`), and every new row's honest advice is the one computed from the source at `pre`, which is `kind.honestAdvice rd rs1 rs2 pre`.
   This last fact unfolds `honestTracerAdviceAtStepN` (`JoltConstraints/honest_trace.lean`) over the appended block; state it as its own lemma.

If a step is not a short proof and is not named here or in `reuse.md`, stage it as its own lemma with `sorry`, continue with the rest, and list it in the report; do not prove a staged lemma in this task.
Keep each proof under about 60 lines; if one grows past that, a lemma is missing.

## Before you stop

Build `JoltConstraints`.
Run `#print axioms JoltInstance.division_append_honest`; it should reach `sorryAx` only through lemmas you staged.
Write `methods/layer6/stage-6a-report.md` with each new or changed declaration (file and line, staged or proved), any proof slower than about ten seconds, and the build and axiom results.
Do not commit.
Then stop.
