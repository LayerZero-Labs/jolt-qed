# Layer 6: prove the device-memory LD and SD steps

Read `/Users/ari.biswas/Lean/jolt-qed-public/AGENTS.md`, `methods/layer6/reuse.md`, then `methods/layer6/device-memory-report.md`, which states the two steps, their invariants, the per-region argument and the lemmas to reuse.
Claude wrote this plan and has made mistakes in this proof before; check each claim against the code before relying on it, and stop and report if one is wrong.
Work in `/Users/ari.biswas/Lean/jolt-qed-public` on `feat/soundness`; do not commit.
Other agents work in `DivisionAppend.lean`, `DivisionPrograms.lean`, `expansion_facts.lean` and `Soundness/Layer7/SpoilAsserts.lean`; do not edit those.
Edit `Soundness/Layer5/DeviceMemory.lean`, and new Layer 5 files if a helper belongs elsewhere; you may make a private lemma public in place in another Layer 5 file, and say which in the report.

## The task

Prove `sd_device_step` and `ld_device_step` (`DeviceMemory.lean`) without changing their statements.
Do the store first: it is where the device and the RAM table could still disagree.

1. SD, region by region, hardest first: the output buffer (eight byte stores that grow the buffer with zeros, against one table word), the panic word (`PanicStoresOne` makes the stored word 1, and the normalized image word is 1), then termination (state unchanged, index excluded from the agreement).
   The advice, input and unmapped regions are excluded by `TracerAddressChecks`; show their hypotheses are inconsistent.
2. LD: the buffer regions read the same bytes the image overlays; panic before any panic store reads zero (from the run's history, not a bare device); termination before any store reads zero (`TerminationTableZero`); address zero reads zero on both sides; other unmapped addresses are excluded by the RAM-address constraints and the layout's lowest address, as the report argues.
3. Prove the byte-packing facts once (eight little-endian bytes against one 64-bit word) and use them for every buffer region; do not prove them per region.

If a region's proof shows the staged statement is false, stop and report the exact case; that is a decision for Ari.
Keep each proof under about 60 lines.
If a step needs a fact that is not a short proof and is not named in the report or `reuse.md`, stage it as its own lemma with `sorry`, continue with the other regions, and list it in the report.

## Before you stop

Build `JoltConstraints` (or your own modules if another agent's edits break it).
Run `#print axioms` on both steps; they should not reach `sorryAx` unless you staged a lemma.
Add a "Proofs" section to `methods/layer6/device-memory-report.md` with each new declaration (file and line), each lemma made public, any proof slower than about ten seconds, and the build and axiom results.
Do not commit.
Then stop.

## Next: the five region lemmas

The steps are proved from five staged lemmas in `DeviceMemory.lean` (report, "Staged obligations and their premises").
Prove them in this order, hardest first: `device_output_store_image`, `device_load_image_bytes`, `device_store_cases`, `device_panic_store_image`, `device_termination_store_image`.
Each concerns the device and the run alone, with no witness.
The run gives the history: unchanged layout, advice and input buffers, output bounds, and panic false before any panic store; use the device-relation preservation theorems (`Layer5/TapeSemantics.lean`, `Layer5/TapeDeviceFrame.lean`) over the run's rows rather than a new frame proof.
If one is false as stated, stop and report the exact case.
Add the results to the report's "Proofs" section.
