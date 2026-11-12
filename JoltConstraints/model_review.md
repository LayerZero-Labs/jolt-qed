---
title: Jolt model in Lean, open issues
updated: 2026-11-05
rust: c97e93004fbf804409f0374fe8457c8f1562ce71
lean_head: e29949809bbf2c54c315c2ca55ae3b90c7fd37a6
---

# Open issues

This file lists what the theorems rest on that is not proved: Jolt issues, assumptions, owed proofs and gaps in the model.
`JoltInstance.soundness` was proved at Lean HEAD `7096dca`, under the temporary restrictions, with no `sorry`; see the [current status](../methods/soundness.md#current-top-level-status-2026-10-23).
With the Step 4 changes on top of `e299498`, `JoltConstraints` builds against the migrated model and `JoltInstance.soundness` is again proved with no `sorry`; see [Current state](../methods/soundness.md#current-state-2026-11-03).
`JoltInstance.completeness` still has the `sorry`s listed under "Proofs owed".
The latest check of the soundness statement against Jolt's code is `reports/2026-10-29-soundness-statement-audit.md`.

**Jolt pin:** `c97e93004fbf804409f0374fe8457c8f1562ce71`, the merge of a16z/jolt#2250, since 2026-11-05.
The constraints were migrated to `c6703570`; of the seven commits from it to the pin, only #2250 changes modeled code.
The previous pin was `5def437f`.
Older findings below keep the revision at which they were established.

The completeness theorem is `JoltInstance.completeness` (`Completeness/completeness.lean`): for every instance that meets `JoltInstance.CompletenessAssumptions`, and every honest trace that meets the three conditions of `JoltInstance.InLanguage` (`language.lean`) with Jolt's prover config `config`, the honest witness at Jolt's own sizes (`HonestTrace.witness_params`) satisfies `AllConstraints`.
The earlier existential form, some private inputs and some witness, is `JoltInstance.completeness_someWitness`, proved from it by unpacking `InLanguage`.
Its workhorse is `HonestTrace.allConstraints_prover_sizes` (`Completeness/All.lean`).
`Trace.prover_config` models Jolt's checked sizing policy, and `HonestTrace.witness_params` takes its trace length and RAM size.
The models of Jolt's prover RAM size (`ProverConfig.checkedRamSize`) and Jolt's verifier maximum (`VerifierSizes.maxRamSize`) follow [a16z/jolt#2250](https://github.com/a16z/jolt/pull/2250), which made the fix that #1951 item 4 proposes, `touched + 1` and `div_ceil(8)`, so `HonestTrace.prover_config_holds_highest_slot` is proved; see `reports/2026-11-03-ram-k-fix-experiment.md`.

**Source-language scope.** Completeness and soundness cover programs represented by `SourceInstruction`: the modeled RISC-V instructions, the listed Jolt custom instructions at opcode `0x5B`, and five registered inlines at opcode `0x0B` (SHA256, SHA256_INIT, KECCAK256, KECCAK256_ABSORB_PERMUTE and BLAKE2; see `docs/inline-precompiles.md`).
Every other `0x0B` encoding, opcode `0x2B` and the field-inline opcode `0x7B` are outside this type.
The Sail whole-run theorems (`JoltConstraints/WholeRun/Top.lean`) cover RISC-V blocks only: `BlockConforms.riscv` excludes custom instructions and inlines.
The SDK's `field_to_limbs!` and `field_from_limbs!` conversions emit `0x7B` instructions.
A guest containing these instructions is outside the theorems' scope by construction.
This restriction is recorded in [`expansion_helpers.lean`](./expansion_helpers.lean); it is not an additional premise or a verifier check.

`AllConstraints joltInstance privateInputs witness` binds the constraint data to the instance through `ConstraintContext` (`constraint_context.lean`).
Bytecode, initial RAM, public I/O and the entry slot cannot be chosen independently of these inputs.
Trusted advice is part of the instance; Jolt's verifier holds a commitment to it, and we model its contents directly.
Untrusted advice is prover-chosen.
Both contribute to initial RAM without being public I/O.
The context also checks the instance's input/output sizes and lowest address, the padded trace length, the bytecode domain, and the verifier's RAM bounds.
`ConstraintEquations` is the underlying equation bundle over those data.

## Upstream issues

Jolt issues that stop a completeness proof.
If one is still open when the main proofs pass, escalate it.

| Issue | What breaks | In our model |
|---|---|---|
| [#1949](https://github.com/a16z/jolt/issues/1949) | Address sums that wrap break (01), floor-row addition in (08), and ShiftData right-input equality in (11) | (01) and the two honest-row address-bound lemmas remain `sorry`, as approved by Ari on 2026-11-03 |
| [#1951](https://github.com/a16z/jolt/issues/1951) item 1 | A run that does not panic and never stores to the termination word: an SDK guest exiting through `platform_exit` or `std::process::exit`, or a bare ELF that reaches `j .` first. The tracer records no write to the word, but `jolt-witness`'s `final_ram_state` sets its `RamValFinal` slot to 1 from the panic flag alone, while initial RAM and the increments give 0 | (38) stays `sorry`. The fix proposed in the issue changes only the SDK's exit paths, so a bare ELF stays unprovable |
| [#1950](https://github.com/a16z/jolt/issues/1950), [#1951](https://github.com/a16z/jolt/issues/1951) item 2 | A store to the termination word is recorded but the device ignores it, so a later load reads 0 (`bug-report/ram-val-termination/`) | (37) stays `sorry`; `Trace.matches_outputs` leaves the termination word out, and `Represents.finalRam` excludes it |
| [#1951](https://github.com/a16z/jolt/issues/1951) item 3 | A load from a nonzero address below the lowest address: the tracer runs it, the checked prover configuration rejects it | such runs have no checked `Trace.prover_config` |
| [#1951](https://github.com/a16z/jolt/issues/1951) item 4 | `ram_K` is one slot too small when the highest touched slot is a power of two (`bug-report/ram-k-off-by-one/`). The verifier's maximum is also one word short: `compute_max_ram_k` rounds `total_bytes / 8` down. When `heap_end` is not a multiple of 8 (`program_size` is not rounded), a program may access the word that straddles `heap_end`, and an honest run that does so gets no proof. The issue proposes `touched + 1` together with `div_ceil(8)` | Fixed in Jolt by [a16z/jolt#2250](https://github.com/a16z/jolt/pull/2250), merged at the pin `c97e9300`: `ProverConfig.checkedRamSize` rounds `touched + 1` and `VerifierSizes.maxRamSize` rounds `(totalBytes + 7) / 8`, as the issue proposes; completeness uses these sizes. `HonestTrace.prover_config_holds_highest_slot` (the highest touched word is below `ram_K`) and the verifier's RAM bounds (`HonestTrace.witness_params_ram_bounds`) are both proved, since every access starts below `heap_end`, so `touched + 1 ≤ ⌈(heap_end - lowest) / 8⌉` (`HonestTrace.highest_ram_slot_lt_heap_end`) |
| [#1951](https://github.com/a16z/jolt/issues/1951) item 5 | Jolt's tracer loads only some ELF section kinds into RAM; preprocessing loads every section | Lean uses preprocessing's `memory_init` for both (`initialRam`, `program.lean`); see finding 3 of the 2026-10-29 report |

## Device memory

Jolt's device ignores stores to the termination word and reads it as 0.
A store to the panic word sets a flag whatever value it stores, and every panic byte reads the flag.
Jolt's tracer rejects stores to the input and advice regions.
Lean's execution model follows these rules; they were rechecked at `5def437f` in the 2026-10-29 report.
The RAM table keeps the stored bytes instead, so the soundness proof uses the temporary restrictions `TerminationThenStall`, `PanicStoresOne` and `TracerAddressChecks` (see Assumptions).

Ari's [#2044](https://github.com/a16z/jolt/issues/2044), following [#2041](https://github.com/a16z/jolt/issues/2041), reports an accepted proof at `00508a09` of stores into the input and both advice regions, which Jolt's tracer rejects.
The report and patch have been read but not rerun here; Michael's comments on #2044 are still to be reviewed with Ari.
`TracerAddressChecks` also covers four unconfirmed candidates: stores at zero, the I/O padding gap, stack-canary stores, and accesses at or above `heap_end`.
Each has its description and next check in `methods/soundness.md`, Layer 5b.

## Assumptions

Premises or fields of the final theorems, with their source or reason.

| Assumption | Where | Why |
|---|---|---|
| The field's characteristic exceeds `2^128` | `JoltField F`, soundness premise `joltField` | Ari, 2026-10-10: the base relation must distinguish full 128-bit lookup addresses. BN254 satisfies this; model Akita's field and extra address guard separately. PCS security is outside this work |
| Every attempted native or floor load/store passes the tracer's address assertions (temporary) | `JoltInstance.TracerAddressChecks` in `Soundness/Layer5/MemoryAccessRestriction.lean`, field `tracerAddressChecks` | Approved for #2044 and the zero-store, I/O-gap, canary and heap-bound candidates; the floor-row extension was applied at `e299498`, checking the containing doubleword without supplying alignment or device-value agreement. |
| Every attempted HostIO call succeeds (temporary) | `JoltInstance.HostCallsSucceed` in `Soundness/Layer5/HostCallRestriction.lean`, field `hostCallsSucceed` | Excludes host-call failures in live mode, which the constraints do not encode; program-execution condition approved by Ari pending the a16z batch |
| Termination is followed by a stall and no later termination load (temporary) | `JoltInstance.TerminationThenStall` in `Soundness/Layer5/TerminationRestriction.lean`, field `terminationThenStall` | Approved by Ari for a witness that stops early at a jump, and the termination word's device/table mismatch. Ari approved on 2026-11-03 extending it and `StoresTerminationAt` to the floor loads and stores at their containing doubleword `ea &&& ~~~7`, only to fit the new ISA |
| Every store to the panic word stores 1, and no load reads the panic word after such a store (temporary) | `JoltInstance.PanicStoresOne` in `Soundness/Layer5/PanicRestriction.lean`, field `panicStoresOne` | Added 2026-10-20 to exclude a store of 0 being proved as "no panic" (`LayerZero-Research/LZ-Notes:content/projects/jolt-qed/blog/completeness-and-soundness/index.md`). A Jolt bug: it must be fixed in Jolt and may not remain a restriction. Ari approved on 2026-11-03 extending it and `StoresPanicAt` to the floor loads and stores at their containing doubleword `ea &&& ~~~7`, only to fit the new ISA |
| The claim says "no panic" (temporary) | `JoltInstance.ClaimsNoPanic` in `Soundness/Layer5/PanicRestriction.lean`, field `claimsNoPanic` | Added 2026-10-20 to exclude a "panicked" claim proved from an execution cut short at a jump (`LayerZero-Research/LZ-Notes:content/projects/jolt-qed/blog/proof-stops-at-any-jump/index.md`). A Jolt bug: it must be fixed in Jolt and may not remain a restriction |
| No relaxed trace has exactly the largest power-of-two number of real rows within the instance maximum (temporary) | `JoltInstance.NoMaxLengthTrace`, field `noMaxLengthTrace` | Ari, 2026-10-22: excludes the full-length prover/verifier mismatch in `LayerZero-Research/LZ-Notes:content/projects/jolt-qed/blog/prover-verifier-trace-length/index.md`, preserves a 256-row run under maximum 1024 that Jolt's prover pads to 512, and must be removed when Jolt resolves the mismatch |
| The maximum padded RAM region satisfies `lowest + 8 * maxRamSize ≤ 2^64` | `JoltInstance.RamRegionFits` in `Soundness/Layer3/Layout.lean`, field `ramRegionFits` of `JoltInstance.SoundnessAssumptions` | Approved by Ari, 2026-10-10. With the verifier's RAM-size check, all eight bytes of each in-domain word fit, so satisfying LD/SD cycles have nonwrapping addresses. NOTE: to confirm with a16z. An instance restriction, not a verifier check |
| A program is never empty: its memory image loads at least one byte | `Rv64ProgramImage.ImageNonempty`, field `imageNonempty` of `JoltInstance.CompletenessAssumptions` | a16z, by phone, 2026-10-08. Jolt's prover does not reject an empty ELF: it traces it and picks `ram_K = 4`, and only Jolt's verifier rejects that size (`InvalidRamK`, minimum 16 with a 64-byte output region; `bug-report/verifier-ram-minimum/`) |
| A program does not change its own code ([#1952](https://github.com/a16z/jolt/issues/1952)) | Modeling assumption, not a theorem premise: traces execute the expanded bytecode, while Jolt's tracer decodes each instruction from memory (`HonestTrace` docstring, `honest_trace.lean`) | a16z, 2026-10-07. The unused premise `codeUnchanged` was removed from soundness on 2026-11-03 with Ari's approval |
| A run uses no RAM 2 GiB or more above `RAM_START` (`bug-report/final-ram-over-2gib/`) | ASSUMPTION in `finalRamWord` | a16z, 2026-10-07 |
| No spoil assert fails | `Trace.SpoilAssertsPass`, part of `JoltInstance.InLanguage` | Part of L, not a premise (Ari, 2026-10-15): a spoiled run is meant to have no proof (`jolt-platform/src/spoil.rs`) |
| Jolt's prover accepts the trace | `(trace.prover_config joltInstance).isSome`, part of `JoltInstance.InLanguage` | Part of L, not a premise (Ari, 2026-10-15): Jolt's prover refuses other traces (`ProverConfig::derive_from_dimensions`). `JoltInstance.completeness` takes the accepted config `config` and uses Jolt's sizes, modeled with the fix of [#1951](https://github.com/a16z/jolt/issues/1951) item 4 from [a16z/jolt#2250](https://github.com/a16z/jolt/pull/2250) |

`TracerAddressChecks` quantifies over every private input and relaxed prefix with honest internal runtime advice and checks the next attempted row without assuming that execution succeeds.
It checks permissions at the starting address in RAM and at every accessed byte below RAM; floor rows use `ea &&& ~~~7`.
It remains a temporary execution restriction to narrow or remove as the cases are resolved, not a verifier check.

The SC.W and SC.D restriction `noStoreConditional`, which no proof used after a16z/jolt#2039, was removed on 2026-11-03 with Ari's approval.

The premise `pcNoWrap`, that no instruction's next PC passes 2^64, was removed from both theorems on 2026-11-05 with Ari's approval.
Since a16z/jolt#2129, Jolt's ELF decoder (`decode_elf` in `crates/jolt-program/src/image/elf.rs`) rejects any program that breaks it, so it is now the image field `Rv64ProgramImage.next_pc_no_wrap` in `program.lean`.

## Proofs owed

**Soundness.** At Lean HEAD `7096dca`, `JoltInstance.soundness` (`Soundness/soundness.lean`) had no `sorry`.
On 2026-10-23, `lake build JoltBytecode JoltConstraints` passed (8,832 jobs) and `#print axioms JoltInstance.soundness` listed only `propext`, `sys_enable_experimental_extensions`, `Classical.choice` and `Quot.sound`.
On 2026-11-03, with the Step 4 changes on top of `e299498`, `lake build JoltConstraints` passed against the migrated model (8,837 jobs), and `#print axioms JoltInstance.soundness` lists the same four axioms and no `sorryAx`.
No soundness proof has a `sorry`, and no blocker lemma was staged.
Since the Sail model was regenerated with the Jolt hart patch, `sys_enable_experimental_extensions` is a definition, not an axiom, and `#print axioms JoltInstance.soundness` lists only `propext`, `Classical.choice` and `Quot.sound`.
The proof's structure is in `methods/soundness.md`, "The argument in brief".
See the [Step 4 report](../reports/2026-11-03-constraints-migration-soundness.md).

**Completeness.** On 2026-11-03 (Step 5), `JoltInstance.completeness` states that the honest witness at the sizes Jolt's prover picks satisfies `AllConstraints`; the earlier existential statement is `JoltInstance.completeness_someWitness`.
`#print axioms` for both lists `propext`, `sorryAx`, `sys_enable_experimental_extensions`, `Classical.choice` and `Quot.sound`.
`lake build JoltConstraints.Completeness` and `lake build JoltConstraints.Completeness.completeness` pass.
The working tree has these five completeness gaps, including Ari's two approved #1949 wrap lemmas; see the [Step 2 report](../reports/2026-11-03-constraints-migration-completeness.md) and the [Step 5 report](../reports/2026-11-03-completeness-jolt-prover.md).
The #1951 item 4 lemma `HonestTrace.prover_config_holds_highest_slot` is proved under the fix of [a16z/jolt#2250](https://github.com/a16z/jolt/pull/2250) ([experiment report](../reports/2026-11-03-ram-k-fix-experiment.md)).
The verifier's RAM bounds at Jolt's sizes, `HonestTrace.witness_params_ram_bounds` (`Completeness/Helpers/VerifierSizes.lean`), are proved, including that both bounds compute.

| Theorem | What it needs |
|---|---|
| (01) `honestWitness_ramAddrEqRs1PlusImmMinusLookupIfLoadStore` (`Completeness/RamAddrEqRs1PlusImmMinusLookupIfLoadStore.lean:33`) | false until #1949 is fixed |
| (08) `HonestTrace.floorAccess_address_nonneg` (`Completeness/RightLookupAdd.lean:50`) | false until #1949 is fixed: the signed base-plus-immediate sum must be nonnegative on an actual floor row of an honest trace |
| (11) `HonestTrace.shiftData_address_noWrap` (`Completeness/RightLookupEqRightInputOtherwise.lean:49`) | false until #1949 is fixed: the signed address-plus-immediate sum must lie in `[0, 2^64)` on an actual ShiftData row of an honest trace |
| (37) `honestWitness_ramValEqInitialPlusPrefixRamInc` | false until #1950 is fixed |
| (38) `honestWitness_ramValFinalEqInitialPlusRamInc` | false until #1951 item 1 is fixed |

No `bv_decide` remains in `JoltBytecode` or `JoltConstraints`; all 21 uses were replaced on 2026-10-23.

### Bytecode

`JoltBytecode/` has no `sorry`.
At Lean HEAD `7096dca` it had seven: ECALL, EBREAK, LR.W, SC.W, LR.D and SC.D in the dispatcher `equivalenceStatement_holds`, and MRET's exception-handler postlude in `InstructionEquivalence/Instructions/System/Mret.lean`.
The MRET theorem is now proved.
`joltRun_eq_execute` (`JoltBytecode/Step/Instructions.lean`) replaces the dispatcher, and the step theorems in `JoltBytecode/Step/` cover ECALL's trap entry and LR/SC against `try_step`.
EBREAK is not executed: the whole-run theorem stops in front of it (`docs/riscv-alignment.md` section 4).

Do not weaken a main statement to close a gap.

### Existing tactic debt

These are source debt, not permission to add such tactics or raise limits during repair.
- `decide +kernel` at `JoltConstraints/Soundness/Layer5/DeviceMemoryObstruction.lean:52` and `:59`; `AGENTS.md` bans it.
- `decide +kernel` is outside the closure of `JoltInstance.sail_soundness`: `DeviceMemoryObstruction` formalizes the termination-device obstruction (#1950/#1951), and only the root module imports it.
- No raised limits remain in `JoltBytecode/` or `JoltConstraints/` (2026-11-09); the generated model's remaining declaration-local limits are listed in `docs/riscv-alignment.md` section 8.
- No executable `bv_decide` use remains in `JoltBytecode/` or `JoltConstraints/`; the only textual match is a comment in `Soundness/Layer4/Interleave.lean:17`.

### Constraints migration (2026-11-03)

Steps 1–3 targeting `c6703570` are committed through `e299498`.
Completeness builds with its six listed gaps, including the two approved honest-row address-wrap obligations.
Step 3 extends `TracerAddressChecks` to floor loads and stores at their containing doubleword.
Step 4 repairs input routing, ShiftData, retired alignment helpers, plain-row classifiers, stall flags and replay-address preservation.
It classifies LD/SD and the floor rows once by width (`Soundness/Layer5/MemoryRows.lean`) and proves every memory step over that classification.
Ari approved on 2026-11-03 extending `PanicStoresOne`, `TerminationThenStall`, `StoresPanicAt` and `StoresTerminationAt` to the floor rows; no other restriction changed.
The main theorem, `InLanguage`, assumptions and completeness files are unchanged by Step 4.
The eleven migration items are in [constraints.md](constraints.md#migration-outline).
See the [Step 4 report](../reports/2026-11-03-constraints-migration-soundness.md).
Step 5 restates `JoltInstance.completeness` at Jolt's own sizes and adapts every corrected-size helper to them; see the [Step 5 report](../reports/2026-11-03-completeness-jolt-prover.md).

### Cleanup

- Speed up `expansion_facts.lean`: its declarations rose from about 11 s to 44 s after the step (c) checker extension (CSRRS 7.7 s, CSRRW 4.5 s, SLLI 1.7 s). Keep the shared expansion checker and avoid another per-instruction proof table.
- Split the Layer 6 proofs longer than about 60 lines: `division_replay_complete_transfer` (`DivisionAppend.lean`, about 315 lines), `division_candidate_first_pre`, `append_expansion_row`, `arithmetic_execution` and `arithmetic_plain_row_step` (`PlainRow.lean`), `arithmetic_advice_suffix_run` (`DivisionDefs.lean`), and `terminal_branch` and `terminal_branch_taken` (`TerminalNextPC.lean`).
- Unpack `JoltInstance.initial_state` once: `initial_state_device`, `initial_state_inputs` (`layout_facts.lean`), `initial_state_empty_outputs_and_input_bound` (`Layer6/BoundaryStart.lean`) and `initial_state_misa` (`Layer5/MisaFrame.lean`) each repeat it.
- `RawRowEntry` (`Layer6/PlainRow.lean`) repeats the entry and linkage clause of `UntrustedAnswerRun.NextStep` and `ExpansionState.next`; defining both from it changes approved definitions and waits for Ari.
- `source_expansion_split` and `expansion_block_eq` (`Layer6/DivisionLayout.lean`) repeat part of the private `expand_program_block` (`Layer6/PlainRow.lean`); generalize it and derive both.
- `source_advice_kind` (`Layer6/DivisionLayout.lean`) classifies every source instruction with a long `simp` list; a checker fact would be shorter.
- Delete the unused `fence_step` (`Layer5/Fence.lean`) and `HonestTrace.code_unchanged` (`honest_trace.lean`).
- `Soundness/Layer5/DeviceMemoryObstruction.lean` uses `decide +kernel`, which `AGENTS.md` bans; only `JoltConstraints.lean` imports it and no proof uses it, so delete it or move its finding to the docs.
- `append_load_row` and `append_store_row` (`Layer6/RowStepMemory.lean`) share their operand and append steps, as their LD/SD predecessors did; extract the shared part once both are reviewed.

## Gaps in our model

- **Untrusted-advice words.** Lean builds untrusted advice from bytes, so every advice word in initial RAM is a 64-bit value; Jolt's verifier takes those words from a committed polynomial and does not range-check them.
  The soundness hypothesis is therefore stronger than Jolt's check, and the gap appears to allow a false claim (2026-10-29 report, finding 1; not reproduced).
  Modeling the words as field elements changes a core definition and waits for Ari.
- **HostIO END marker.** Lean's `execHostIOWith` does not read the label for a cycle-marker END, while Jolt's tracer does and can abort on it (2026-10-29 report, finding 2).
- **ELF sections and `tohost`.** Lean's initial RAM uses preprocessing's `memory_init` for the run; Jolt's tracer loads fewer section kinds, and sizes RAM differently when the ELF defines `tohost` (2026-10-29 report, findings 3 and 4).
- **Termination word.** `InLanguage` compares only the outputs and the panic flag; Jolt's verifier also checks the termination word, so the theorem says less than Jolt enforces (2026-10-29 report, finding 5).
- **Images Jolt never produces.** `Rv64ProgramImage` carries decoded instructions without a decoder certificate.
  It admits ANDN as a source instruction, odd branch and jump offsets, a quotient field on divisions, and instruction lists not tied to the text bytes.
  These only add instances to the theorems.
  A taken odd branch fails Sail's alignment assertion in `jump_to`, so a satisfying witness can never take one: its next unexpanded PC would be odd, but a real next row has an even address and padding or the last cycle forces zero.
- **Trusted base.** The semantics of each Jolt instruction are translated from Jolt's code by hand.
  Native RV64 instructions are proved against Sail (`JoltBytecode/InstructionEquivalence`); virtual instructions have nothing to prove against.
- **Trace representation.** Jolt's `JoltTraceRow` stores encoded operands, optional captures and a resolved bytecode PC.
  Lean's `TraceRow` derives observations from full pre- and post-states; this is a source-audited correspondence, not a formal equivalence with Jolt's packed representation.
  Lean does not represent missing captures or noncanonical NoOp rows; Jolt's row-constructor checks are producer checks, not verifier constraints or premises.
- **Not modeled.** The Akita build's 4096-cycle padding floor, program commitments (ProgramBytecode, ProgramImageInit), and the advice witness columns and commitment protocols.
  Trusted advice contents are modeled directly as part of the instance; Lean has no flag for a trusted-advice commitment being absent.
- **Akita.** The base relation omits Akita's instruction-address canonicality guard, which Jolt enables with the `akita` feature; Akita is to be modeled separately (`methods/soundness.md`, Layer 4).
- **Expansions.** `SourceInstruction.expand` uses the bytecode project's programs.
  On 2026-10-29 every source kind's rows were compared with Jolt's expander at `5def437f` and match (2026-10-29 report).
  The header of `JoltBytecode/JoltISA/ExpansionsAutomated.lean` says it is generated by `jolt-lean-gen`, but the generator at the pin cannot produce it; the local generator patches are in `methods/model_update/`.
  LR/SC are not proved against Sail.
- **LR/SC reservation correspondence.** Jolt's native `SCW::exec` and `SCD::exec` consult `cpu.reservation_covers`; the expanded sequences and this model compute success from virtual registers 32 and 33.
  Their agreement remains to be proved at source-instruction boundaries: initialization, LR.W setting only the word reservation, LR.D setting both, either SC clearing both, and other instructions preserving them.
  It is an obligation relating the model to Jolt's execution paths, not a soundness premise.
- **To do.** Fix comments that cite `/Users/ari.biswas/...` paths, an unpinned fork, or the crate `jolt-trace`; answer the `metadata.lean` TODOs the 2026-10-29 report settled.
  Drop the unused `ramFits`, `traceFits` and `bytecodeDomain` arguments.

## Classifier call sites

Step 1 replaced `opcodeFlag_load_requiresLD` and `opcodeFlag_store_requiresSD` by `opcodeFlag_load_cases` and `opcodeFlag_store_cases`, covering LD/SD and the floor rows with unchanged hypotheses.
Step 2 migrated both completeness load callers through `Completeness/Helpers/MemoryValueFacts.lean` and the store caller in `Completeness/Rs2EqRamWriteIfStore.lean`.
These proofs use the shared classification and retain their original premises.
Step 4 migrates `plain_no_memory` (`Soundness/Layer6/PlainRow.lean`) and `stable_stall_source_no_store` (`Soundness/Layer7/StallSuffix.lean`) to the widened classifiers.
`loadRow_of_flag` and `storeRow_of_flag` (`Soundness/Layer5/MemoryRows.lean`) wrap them as the `LoadRow`/`StoreRow` classification used by `row_kind` (`Soundness/Layer6/RowStepKinds.lean`), `row_panic_of_no_store` (`Soundness/Layer5/DeviceMemory.lean`) and `termination_effect_is_store` (`Soundness/Layer7/TerminationStore.lean`).
No call to the old SD-only or LD-only classifiers remains.

## Correspondence migration (2026-11-03)

- Step 1 migrated the seven instruction flags, AddressOffset tables, metadata, register selectors and floor-row observations; Ari reviewed those definitions.
- Step 2 migrates the completeness proofs with no new premises and only the approved (08) and (11) wrap gaps.
  Its AddressOffset dispatch and constraint (39) now build after the approved `Soundness.Layer4.WordEntry` repair.
- `TracerAddressChecks` (`Soundness/Layer5/MemoryAccessRestriction.lean:87`) now covers native and floor loads/stores, as approved in Step 3.
  `PanicStoresOne`, `TerminationThenStall` and their completed-store predicates cover them too, as approved by Ari on 2026-11-03 (Step 4, work item 5).
