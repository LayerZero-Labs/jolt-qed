# Layer 6: LD and SD on device memory (staging)

Read `/Users/ari.biswas/Lean/jolt-qed-public/AGENTS.md`, `methods/layer6/reuse.md`, and in `methods/soundness.md` the sections "Order of the remaining work" and "Layer 5b: one execution step" (its device-memory obligations) first.
Claude wrote this plan and has made mistakes in this proof before; check each claim against the code before relying on it, and stop and report if one is wrong.
Work in `/Users/ari.biswas/Lean/jolt-qed-public` on `feat/soundness`; do not commit.
Other agents work in the Layer 6 division files, `PlainRow.lean`, `expansion_facts.lean` and `Soundness/Layer7/SpoilAsserts.lean`; do not edit those.
Edit only one new file, `Soundness/Layer5/DeviceMemory.lean`, and `JoltConstraints.lean` to import it.

## Why

`row_step` (`Soundness/Layer6/RowStep.lean`) must append LD and SD rows.
`ld_ram_step` and `sd_ram_step_agreement` (`Layer5/LoadDoubleword.lean`, `Layer5/RamStoreAgreement.lean`) cover only ordinary RAM, at or above `RAM_START_ADDRESS`, through `OrdinaryRamAgreement`.
Below it lie the device words: trusted and untrusted advice, inputs, outputs, the panic word and the termination word.
There Jolt's device (`common/src/jolt_device.rs`, `JoltDevice::load` and `store`, and the MMU checks) may not behave like a plain RAM word, which is how the witness's RAM table treats every word.
Whether the temporary restrictions are enough here has never been established, so this is the largest unknown left in the soundness proof.
This stage only states the steps and checks them; it proves nothing.

## The task

1. The invariant the steps must keep is the cut RAM agreement in `RepresentsPrefix.cutRam` (`Layer6/ExecutionPrefix.lean`) and the `terminationWord` field of `ExpansionState` (`Layer6/PrefixState.lean`): every table word other than termination equals `TraceWitness.finalRamWord` of the run, which overlays the final device on the RAM image (`witness_helpers/ram_state.lean`).
   State, as a definition in `DeviceMemory.lean`, the part of it for word indices below `RAM_START_ADDRESS`, so that it and `OrdinaryRamAgreement` together give the whole.
2. For each region (trusted advice, untrusted advice, inputs, outputs, panic word, termination word, and addresses in none of them), and for LD and SD, record in the report:
   what Jolt's tracer does (device and MMU code at the pin, cited by file and function);
   what the Lean model does (`execWithTapeAnswer` on LD and SD, and the device functions it calls);
   which restriction applies (`TracerAddressChecks`, `PanicStoresOne`, `TerminationThenStall`, in `Soundness/Assumptions.lean` and `Layer5/`);
   and whether the step keeps the agreement, with the reason.
   The termination word is already known to differ (`Layer5/DeviceMemoryObstruction.lean`); check that `TerminationThenStall` and `terminationWord` cover it.
3. Stage `ld_device_step` and `sd_device_step` in `DeviceMemory.lean`, shaped like `ld_ram_step` and `sd_ram_step_agreement` but for an address below `RAM_START_ADDRESS`, keeping the device-word agreement.
   Give them only hypotheses `row_step` can supply: it has the soundness assumptions, the temporary restrictions and the run.
   Split them by region if the regions behave differently.
   Check each against "Before staging a statement" in `AGENTS.md`.

If a region's step is false under the current restrictions, do not stage it: write down the exact counterexample (the instruction, the address, the device state, the witness value and the table value) and stop.
That is a decision for Ari: a model fix, a new restriction, or a Jolt issue.

## Before you stop

Build your module.
Write `methods/layer6/device-memory-report.md` with the per-region table from step 2, each staged statement (file and line), and the build result.
Do not commit.
Then stop.
