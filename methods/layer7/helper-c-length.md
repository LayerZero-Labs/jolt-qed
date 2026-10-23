# Layer 7, helper C: the padded length fits

Read `/Users/ari.biswas/Lean/jolt-qed-public/AGENTS.md` and `methods/layer7/helper-c-report.md` (section "2. Checked trace length") first.
Claude wrote this plan and has made mistakes in this proof before; check each claim against the code before relying on it, and stop and report if one is wrong.
Work in `/Users/ari.biswas/Lean/jolt-qed-public` on `feat/soundness`; do not commit.
Edit only `Soundness/Layer7/ProverAccepts.lean`; other agents work in the division files and `Soundness/Layer5/DeviceMemory.lean`.

## The task

Prove the staged `checked_trace_length_fits` (`ProverAccepts.lean`) without changing its statement.
It is arithmetic only, and the report's section 2 gives the argument:

- Let `M = maximum.toNat` and `P = 2 ^ Nat.log2 M`, the largest power of two at most `M`.
- `2 ^ logT ≤ M` gives `2 ^ logT ≤ P`, so `rows ≤ P`; with `notMax`, `rows + 1 ≤ P`.
- `P ≤ M < 2 ^ 64`, so the checked addition and the checked rounding in `ProverConfig.checkedTraceLength` (`JoltConstraints/prover_config.lean`) succeed, and the rounded value is at most `P`.
- The 256 floor stays at most `M` by `floor`.

Unfold `checkedTraceLength`, `MemoryLayout.checkedAdd` and `VerifierSizes.checkedNextPowerOfTwo` only as far as needed; `checkedTraceLength_rounding` and `checkedRound_some` in `prover_config.lean` show the shape of their results.
The report names the `Nat.log2`, `Nat.clog` and power lemmas to use.
Keep the proof under about 60 lines, split into helper lemmas if needed.

## Before you stop

Build `JoltConstraints.Soundness.Layer7.ProverAccepts`.
Run `#print axioms JoltInstance.checked_trace_length_fits`; it should not reach `sorryAx`.
Add a "Padded length" section to `methods/layer7/helper-c-report.md` with each new declaration (file and line), and the build and axiom results.
Do not commit.
Then stop.
