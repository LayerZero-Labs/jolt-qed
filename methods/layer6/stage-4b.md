# Layer 6, stage 4b: the entry row and the empty run's RAM

Read `/Users/ari.biswas/Lean/jolt-qed-public/AGENTS.md`, `methods/layer6/stage-3b-report.md` and `methods/layer6/reuse.md` first.
Claude wrote this plan and has made mistakes in this proof before; check each claim against the code before relying on it, and stop and report if one is wrong.
Work in `/Users/ari.biswas/Lean/jolt-qed-public` on `feat/soundness`; do not commit.
Another agent works in the same checkout on Layer 5 files, `DivisionBlock.lean` and a new `PlainRow.lean`.
Edit only `JoltConstraints/Soundness/Layer6/BoundaryStart.lean`; you may make a private lemma public in place where you need it, and say which in the report.

## The task

Prove the two lemmas you staged in `BoundaryStart.lean`, without changing their statements.

### `first_row_of_entry_slot`

`get_first_pc` (`JoltConstraints/program.lean`) returns the first slot whose row has the entry address.
`preprocess` builds the slots as the no-op, then one slot per bytecode row, then padding no-ops, so a nonzero slot `k` found this way holds bytecode row `k - 1`, and that row has the entry address.
It remains to show that this row starts its source instruction.
The rows of one source instruction are consecutive and share its address, and its first row is the one marked `starts_source` (`expand_program_layout`, `JoltConstraints/ProgramLayout.lean`).
Distinct source instructions have distinct addresses (`pc_map_ok_distinct_addresses`, `JoltConstraints/program_facts.lean`), which preprocessing checked (`preprocess` requires `pc_map_ok`).
So the first row with the entry address is the first row of the source at that address.
`HonestTrace.first_pc_eq_entry` (`JoltConstraints/Completeness/completeness.lean`) proves a related fact in the other direction and may show the useful lemmas.

### `empty_run_ram_word`

For the empty run, `TraceWitness.finalRamWord` reads the initial state (`finalTraceState` of an empty trace).
Compare it with `TraceWitness.initialRamWordFromState` (both in `JoltConstraints/witness_helpers/ram_state.lean`): the RAM part and the trusted-advice, untrusted-advice and input overlays are the same.
The differences:
- the output overlay, with the initial device's empty outputs (`JoltInstance.initial_state`, `program.lean`); check what `overlayRamBytes` does with no bytes;
- the panic word, which `finalRamWord` sets to 0 since the initial panic flag is false; show the initial image is also 0 there;
- the termination word, excluded by the hypothesis.

`MemoryLayout.new` (`JoltBytecode/JoltISA/JoltDevice.lean`) places the advice, input, output, panic and termination regions back to back with overflow-checked arithmetic, so the panic word lies in no advice or input region.
The same argument for the termination word is already proved in the private `initialRamWord_termination_zero` and `termination_word_absolute` (`JoltConstraints/Soundness/Layer7/TerminationStore.lean`); reuse its pattern or its lemmas.
The I/O-region geometry lemmas `new_io_geometry` and `new_io_word_geometry` (`JoltConstraints/layout_facts.lean`) may also help.

If either proof needs a fact that is not a short proof and not listed here or in `reuse.md`, state it as its own lemma with `sorry` and stop and report.

## Before you stop

Build `JoltConstraints`.
Run `#print axioms JoltInstance.boundaryState_empty`: it should no longer reach `sorryAx`, unless you staged a new lemma.
Add a section "Stage 4b" to `methods/layer6/stage-3b-report.md` with each new or changed declaration (file and line), each private lemma made public, any proof slower than about ten seconds, and the build and axiom results.
Do not commit.
Then stop.
