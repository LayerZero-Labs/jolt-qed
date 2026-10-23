# Layer 7, helper C: the RAM size computes

Read `/Users/ari.biswas/Lean/jolt-qed-public/AGENTS.md`, `methods/layer6/reuse.md`, then `methods/layer7/helper-c-report.md`, section "3. Checked RAM size", which gives the argument and the lemmas.
Claude wrote this plan and has made mistakes in this proof before; check each claim against the code before relying on it, and stop and report if one is wrong.
Work in `/Users/ari.biswas/Lean/jolt-qed-public` on `feat/soundness`; do not commit.
Edit only `Soundness/Layer7/ProverAccepts.lean`; you may make a private lemma public in place elsewhere, and say which in the report.
Another agent may be working in `ProverAccepts.lean` on `represented_trace_ends_in_jump`; edit only your lemma's part of that file.
Other agents work in Layer 5 files and the Layer 6 division files; do not edit those.

## The task

Prove `represented_ram_size_computes` without changing its statement.

1. Every nonzero RAM address in the trace's rows is at least the layout's lowest address: the witness's address equals it (`ramAddress`), and the RAM-address and selector constraints make every nonzero witness address the base plus eight times a selected index (`ramRa_unique_of_address_ne_zero`, `ramAddress_of_selected`, `ramAddress_eq_of_selected`, `ram_address_value_lt_char`).
   Identify the trace's layout with the context's through `initialized`, `initial_state_device` and `context.publicIo`.
2. Connect the fold in `Trace.execution_dimensions` (`ram_bounds`) to that bound by induction over the rows, so `checkedTouched` succeeds; `ExecutionDimensions.observe` ignores address zero.
3. The image start and end and the final rounding fit: `context.ramSizeBounds` gives successful verifier RAM sizes, the maximum is at most `2^61`, and every touched slot is below `2^61`.

Keep each proof under about 60 lines.
If a step needs a fact that is not a short proof and is not named here or in the report, stage it as its own lemma with `sorry`, and stop and report.

## Before you stop

Build `JoltConstraints.Soundness.Layer7.ProverAccepts`.
Run `#print axioms JoltInstance.represented_ram_size_computes`; it should not reach `sorryAx`.
Add a "RAM size" section to `methods/layer7/helper-c-report.md` with each new declaration (file and line), each lemma made public, any proof slower than about ten seconds, and the build and axiom results.
Do not commit.
Then stop.
