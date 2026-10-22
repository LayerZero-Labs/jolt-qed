# Layer 6, stage 3b: the start of the run and of each source instruction

Read `/Users/ari.biswas/Lean/jolt-qed-public/AGENTS.md`, `methods/layer6/stage-2-report.md` and `methods/layer6/reuse.md` first.
Claude wrote this plan and has made mistakes in this proof before; check each claim against the code before relying on it, and stop and report if one is wrong.
Start only after Ari tells you that Part A of `methods/layer6/stage-3a.md` is committed.
Work in `/Users/ari.biswas/Lean/jolt-qed-public` on `feat/soundness`; do not commit.
Another agent works in the same checkout: edit only `JoltConstraints/Soundness/Layer6/BoundaryStart.lean`, and make a private lemma public in place where you need it (say which in the report).
If you need a change to any other file, stop and report it.

## The task

Prove the two staged lemmas in `BoundaryStart.lean`, without changing their statements:

- `boundaryState_empty`: the run with no rows satisfies `BoundaryState`.
  Build the run from `context.expands` and `context.initialized`; its execution, start and linkage conditions are vacuous.
  The fields, at cycle 0:
  - `represents`: no rows; RAM at column 0 equals `TraceWitness.finalRamWord` of the empty run at every word except termination.
    The witness's column 0 is `context.initialRam` (`ramVal_initial_state`), which is `initialRamWordFromState` of the initial state (`context.initialized`).
    For the empty run, `finalRamWord` reads the initial state; the initial device has no outputs and panic false (`JoltInstance.initial_state`, `JoltConstraints/program.lean`), so its output and panic words are 0, as in the initial RAM.
    Prove this agreement of the two word functions as its own lemma.
  - `registers`: `RegisterAgreement.initial`, then the helper from Part A that gives `RegisterAgreementOn`.
  - `terminationWord`: `context_initial_termination_zero` (`Layer7/TerminationStore.lean`, private).
  - `ready`: if cycle 0 is real, it selects the entry slot (`selected_entry`, `Layer6/BytecodePC.lean`); `context.entryIsRust` and `get_first_pc` (`JoltConstraints/program.lean`) give the slot of the first bytecode row whose address is the entry address, and the slot is that row plus one.
    That this row starts a source instruction is not in `get_first_pc` itself: it follows from the bytecode layout (`expand_program_layout`) and the uniqueness of source addresses (`pc_map_ok` with `pc_map_ok_distinct_addresses`, which preprocessing checked).
    Completeness proves the converse direction in `HonestTrace.first_pc_eq_entry` (`JoltConstraints/Completeness/completeness.lean`).
    Entry address 0 maps to the no-op slot 0, so cycle 0 is then padding.
    `NextStep` of the empty run holds: its honest-advice and no-earlier-stop parts are vacuous.
    If cycle 0 is padding, `ready` is vacuous.
- `expansion_start`: from `BoundaryState`, a real next cycle and no final stable stall, the `ExpansionState` with `done = 0`.
  Every field comes from `BoundaryState`: `ready` gives the next row, its slot and `NextStep`; `atBoundary` gives `priorBoundary`; `registers` gives the live-set agreement through the Part A helper, since with `done = 0` only registers that are not instruction temporaries are live.

If a step turns out to need a fact that is not a short proof and not in `reuse.md`, state it as its own lemma with `sorry` in `BoundaryStart.lean`, and stop and report rather than proving a long argument.

## Before you stop

Build `JoltConstraints`.
Run `#print axioms JoltInstance.soundness`; `boundaryState_empty` and `expansion_start` should no longer reach `sorryAx`, unless you staged a sub-lemma.
Write `methods/layer6/stage-3b-report.md` with each new or changed declaration (file and line), each private lemma you made public, any proof slower than about ten seconds, and the build and axiom results.
Do not commit.
Then stop.
