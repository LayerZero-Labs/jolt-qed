# Agent 4: device memory, LD and SD on every address, SC.W and SC.D

Read `README.md` in this directory first, then `AGENTS.md`, then agent 1's Phase 0 report `methods/layer6/phase0_report.md`.
Start only after Ari has approved Phase 0.
Work in a worktree under `/Users/ari.biswas/Lean/` on a branch `layer6-agent-4`, created from the commit named in the Phase 0 report.

## Your task

1. Define the device-word agreement agent 1 staged, and prove its initial case.
2. Prove the `RowStep` lemmas for LD and SD on every address, ordinary RAM and device memory.
3. Show that rows which do not access memory preserve device agreement.
4. Give agent 1 the cut: at the cut, the witness's RAM equals the run's final RAM at every device word except the termination word.
5. Afterwards: the SC.W and SC.D expansions, so the temporary restriction `NoStoreConditional` can be removed.

## Device-word agreement

`RepresentsPrefix.cutRam` (`Layer6/ExecutionPrefix.lean:30-45`, moved to `Layer6/Represents.lean` in Phase 0) compares the witness's RAM with `TraceWitness.finalRamWord` (`JoltConstraints/witness_helpers/ram_state.lean:87-102`) at every word except the termination word.
`finalRamWord` reads the input, advice and output words from the device, and the panic word is the panic flag as 0 or 1.
So the invariant relates `witness.RamVal i t` at each device word `i` to the word the run's device gives there.

What the cases need:

- **Inputs and advice:** they are read-only for the program.
  `TracerAddressChecks` (`Layer5/MemoryAccessRestriction.lean:86`; `ld_address_checks` and `sd_address_checks` at `:103` and `:117`) excludes stores to them.
- **Outputs:** stores update the device's output bytes; show the table word and the device word move together.
- **Panic:** `PanicStoresOne` (`Layer5/PanicRestriction.lean:63`) says every store to the panic word stores 1, and no load reads it after such a store.
  Before any store both read 0; after one, the table holds 1 and the flag is set.
  This is the panic word's `cutRam`, which was left to this proof when Layer 8 was closed.
- **Termination:** it is excluded from `cutRam`.
  Jolt's tracer ignores stores to it and loads it as 0, while the table keeps the stored value.
  `TerminationThenStall` (`Layer5/TerminationRestriction.lean:59`) forbids loading it after a store, and before a store both read 0.
  `Layer5/DeviceMemoryObstruction.lean` shows the mismatch on a concrete layout.
- **Initial agreement:** `RamInitialization.lean:107` covers ordinary RAM only.
  Prove the device words of `context.initialRam` agree with the initial device.

See "Device memory" in `methods/soundness.md` for the open obligations: alignment, peripheral dispatch in `load_raw?`/`store_raw?`, and that successful execution must not be inferred from the address restriction alone.

## LD and SD

The existing `ld_ram_step` (`Layer5/LoadDoubleword.lean:37`), `sd_ram_step` (`Layer5/StoreDoubleword.lean:62`) and `sd_ram_step_agreement` (`Layer5/RamStoreAgreement.lean:18`) cover `RAM_START_ADDRESS ≤ address`.
Extend them to device addresses, and adapt both to the `RowStep` interface and to live-register agreement.
You own these files, so agent 5 does not port them.

## SC.W and SC.D

The SC expansions' rows already have local steps (see "SC.W" in `methods/soundness.md`), but their LD and SD steps were for ordinary RAM.
Once LD and SD cover every address, show the SC expansions compose under the induction.
Then remove `NoStoreConditional` from `TemporaryRestrictions` (`Soundness/Assumptions.lean`).
Ask Ari before removing it, since it changes the main theorem's restrictions bundle.

## Files you own

- `Layer5/LoadDoubleword.lean`, `Layer5/StoreDoubleword.lean`, `Layer5/RamStoreAgreement.lean`, `Layer5/RamAgreement.lean`, `Layer5/RamInitialization.lean`;
- new files under `Layer5/` whose names start with `Device`;
- the SC files under `Layer5/` (agent 1's Phase 0 report lists them).

## Report

Per-declaration timings, any helper hypotheses you added, any new `bv_decide` use, and your branch's head commit.
