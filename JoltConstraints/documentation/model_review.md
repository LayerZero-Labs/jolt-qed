---
title: Jolt model in Lean, open issues
updated: 2026-11-25
rust: ff6fc656813d950565c9f6e1258b78bdaf0e60e8
lean_head: db02bb9
---

# Open issues

The `ff6fc6568` re-pin is complete at `3ff14b2` on `split/c-constraints`.
At that commit `lake build JoltConstraints` succeeds, and `JoltInstance.soundness` depends only on `propext`, `Classical.choice` and `Quot.sound`.
The soundness theorem takes no temporary program restriction: the three flag-word restrictions, `tracerAddressChecks` and `hostCallsSucceed` are all removed, and so is the `TemporaryRestrictions` structure.
`hostCallsSucceed` became unnecessary because the merged bytecode HostIO model is total, as Jolt's tracer is at this pin: an invalid event or a rejected guest read is ignored, and every call retires (`JoltISA.execHostIO_succeeds`).
The selected RAM word's address and protected-value checks follow from the pinned constraints.
Both requested RAM-history completeness theorems are proved with unchanged statements.
The three #1949 obligations are proved since 2026-11-25: honest memory rows never wrap their effective address (`HonestTrace.access_noWrap`, `theorems/Completeness/Helpers/AddressWindow.lean`), and `JoltInstance.completeness` has no `sorry`.
The whole-run relation and initialization use the shared byte map, and the shared-memory simulations replace the old device-memory and I/O modules.
`docs/whole-run-theorem.md` and `docs/riscv-alignment.md` describe the current whole-run statements since 2026-11-25.
See [the re-pin report](../../reports/2026-11-24-constraints-repin.md) for the changed statements.
Neither `JoltBytecode/` nor `JoltConstraints/` has a `sorry`.

This file lists what the theorems rest on that is not proved: Jolt issues, assumptions, owed proofs and gaps in the model.
Two earlier milestones keep their revisions: `JoltInstance.soundness` was first proved at Lean HEAD `7096dca`, under temporary restrictions that the re-pin removed ([2026-10-23 status](../../methods/soundness.md#top-level-status-on-2026-10-23)), and again after the Step 4 migration on top of `e299498` ([2026-11-03 state](../../methods/soundness.md#current-state-2026-11-03)).
The latest check of the soundness statement against Jolt's code is `reports/2026-10-29-soundness-statement-audit.md`.

**Jolt pin:** `ff6fc656813d950565c9f6e1258b78bdaf0e60e8`, since 2026-11-24.
The previous pin was `c97e93004fbf804409f0374fe8457c8f1562ce71`, the merge of a16z/jolt#2250.
The earlier constraint migration targeted `c6703570`, then `c97e9300`.
The current migration also models the shared-memory and halt-end changes at `ff6fc6568`.
The previous pin was `5def437f`.
Older findings below keep the revision at which they were established.

The completeness theorem is `JoltInstance.completeness` (`theorems/Completeness/completeness.lean`): for every instance and every honest trace that meets the three conditions of `JoltInstance.InLanguage` (`language.lean`) with Jolt's prover config `config`, the honest witness at Jolt's own sizes (`HonestTrace.witness_params`) satisfies `AllConstraints`.
The earlier existential form, some private inputs and some witness, is `JoltInstance.completeness_someWitness`, proved from it by unpacking `InLanguage`.
Its workhorse is `HonestTrace.allConstraints_prover_sizes` (`theorems/Completeness/All.lean`).
`Trace.prover_config` models Jolt's checked sizing policy, and `HonestTrace.witness_params` takes its trace length and RAM size.
The models of Jolt's prover RAM size (`ProverConfig.checkedRamSize`) and Jolt's verifier maximum (`VerifierSizes.maxRamSize`) follow [a16z/jolt#2250](https://github.com/a16z/jolt/pull/2250), which made the fix that #1951 item 4 proposes, `touched + 1` and `div_ceil(8)`, so `HonestTrace.prover_config_holds_highest_slot` is proved; see `reports/2026-11-03-ram-k-fix-experiment.md`.

**Source-language scope.** Completeness and soundness cover programs represented by `SourceInstruction`: the modeled RISC-V instructions and the listed Jolt custom instructions at opcode `0x5B`.
Jolt's inline/precompile opcodes `0x0B` and `0x2B`, including the SHA-256 and Keccak inlines, and its field-inline opcode `0x7B` are outside this type.
The SDK's `field_to_limbs!` and `field_from_limbs!` conversions emit `0x7B` instructions.
A guest containing these instructions is outside the theorems' scope by construction.
This restriction is recorded in [`expansion_helpers.lean`](../translation/expansion_helpers.lean); it is not an additional premise or a verifier check.

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
| [#1949](https://github.com/a16z/jolt/issues/1949) | Address sums that wrap break (01), floor-row addition in (08), and ShiftData right-input equality in (11) | Not an issue for honest traces: the tracer accepts an address only in `[0x40000000, 2^63 + 2^31)` and every offset is a sign-extended 12-bit value, so no retired row wraps. (01) and the two honest-row address-bound lemmas are proved since 2026-11-25 (`HonestTrace.access_noWrap`, `HonestTrace.shiftData_store`) |
| [#1951](https://github.com/a16z/jolt/issues/1951) item 1 | The old device model synthesized a termination word in final RAM | The shared-memory pin removes that word; (38) is proved at `ce5f298` |
| [#1950](https://github.com/a16z/jolt/issues/1950), [#1951](https://github.com/a16z/jolt/issues/1951) item 2 | The old device ignored termination stores | Shared memory retains every accepted store; (37) is proved at `ce5f298`, and `Represents.finalRam` compares every word |
| [#1951](https://github.com/a16z/jolt/issues/1951) item 3 | A load from a nonzero address below the lowest address: at the earlier pin the tracer ran it and only the checked prover configuration rejected it | Resolved at `ff6fc6568`: the tracer's MMU panics on a load below the lowest address (`IoUnderflow`), on any other access below RAM outside the I/O region (`UnmappedDevice`), and on any access at or above the end of the padded RAM backing (`BeyondRamDomain`) (`tracer/src/emulator/mmu.rs:133-143, 269-283`). The checked prover configuration also rejects such runs |
| [#1951](https://github.com/a16z/jolt/issues/1951) item 4 | `ram_K` is one slot too small when the highest touched slot is a power of two (`bug-report/ram-k-off-by-one/`). The verifier's maximum is also one word short: `compute_max_ram_k` rounds `total_bytes / 8` down. When `heap_end` is not a multiple of 8 (`program_size` is not rounded), a program may access the word that straddles `heap_end`, and an honest run that does so gets no proof. The issue proposes `touched + 1` together with `div_ceil(8)` | Fixed in Jolt by [a16z/jolt#2250](https://github.com/a16z/jolt/pull/2250), merged at the pin `c97e9300`: `ProverConfig.checkedRamSize` rounds `touched + 1` and `VerifierSizes.maxRamSize` rounds `(totalBytes + 7) / 8`, as the issue proposes; completeness uses these sizes. `HonestTrace.prover_config_holds_highest_slot` (the highest touched word is below `ram_K`) and the verifier's RAM bounds (`HonestTrace.witness_params_ram_bounds`) are both proved, since every access starts below `heap_end`, so `touched + 1 ≤ ⌈(heap_end - lowest) / 8⌉` (`HonestTrace.highest_ram_slot_lt_heap_end`) |
| [#1951](https://github.com/a16z/jolt/issues/1951) item 5 | Jolt's tracer loads fewer ELF sections into RAM than preprocessing does | Open. Lean uses preprocessing's `memory_init` for both (`initialRam`, `program.lean`); see "ELF sections and `tohost`" under "Gaps in our model" and finding 3 of the 2026-10-29 report |

## Shared memory and halt claims

At `ff6fc6568`, input, advice, output and ordinary RAM bytes all belong to `sail.mem`.
`JoltDevice` retains the layout and the CPU's panic claim.
Protected stores succeed when the affected bytes preserve their old values, including stores into code, input, advice and canary words.
`Layer5/SharedMemoryChecks` derives the selected row's address and protected-value checks from the RAM constraints.
The soundness theorem therefore takes no `tracerAddressChecks` restriction, and the `TracerAddressChecks` predicate no longer exists.

A valid proof ends at an explicit success or panic halt row.
Row 21 binds the public panic claim to that kind.
`Layer7/Stopping` now checks this argument for either claim, without termination or panic memory words.
The three flag-word restriction fields and their definition modules have been removed.
The full `lake build JoltConstraints` at `3ff14b2`, recorded at the top of this file, includes the whole-run simulation and the soundness assembly for both claims.

## Assumptions

Premises or fields of the final theorems, with their source or reason.

| Assumption | Where | Why |
|---|---|---|
| The field's characteristic exceeds `2^128 - 2^64` | `JoltField F`, soundness premise `joltField` | Ari, 2026-10-10: the relation must distinguish full 128-bit lookup addresses. On 2026-11-10 the premise was weakened from `2^128` so Akita's `p = 2^128 - 1780711455` (Jolt's production field since a16z/jolt#2403) satisfies it; below characteristic `2^128` constraint (63), Akita's address guard, keeps identity-RAF addresses below `2^128 - 2^64`. BN254 also satisfies it. PCS security is outside this work |
| The maximum padded RAM region satisfies `lowest + 8 * maxRamSize ≤ 2^64` | No longer an assumption: `JoltInstance.ramRegionFits` (`theorems/Soundness/Layer3/Layout.lean`) proves it for every instance, because the verifier's maximum `MemoryLayout::max_ram_k` at `ff6fc6568` rejects any layout that breaks it. `JoltInstance.SoundnessAssumptions`, which held only this field, was removed on 2026-11-25 | Approved by Ari, 2026-10-10, as a premise |
| A program is never empty: its memory image loads at least one byte | No longer an assumption: `HonestTrace.prover_config_image_nonempty` derives `Rv64ProgramImage.ImageNonempty`. Jolt's prover at `ff6fc6568` rejects an empty trace (`TraceDoesNotEndInHalt` in `derive_from_dimensions`), and a program with an instruction loads that instruction's bytes (the image field `Rv64ProgramImage.instruction_loaded`) | a16z, by phone, 2026-10-08. At the earlier revision Jolt's prover traced an empty ELF, picked `ram_K = 4`, and only Jolt's verifier rejected that size (`bug-report/verifier-ram-minimum/`). `JoltInstance.CompletenessAssumptions`, which held only this field, was removed on 2026-11-25 |
| A program does not change its own code ([#1952](https://github.com/a16z/jolt/issues/1952)) | No longer an assumption: Jolt's tracer at `ff6fc6568` rejects every store that changes a code byte (`protected_store_ok`), and the whole-run proof derives that the code stays intact (`JoltCodeIntact.of_block`) | a16z, 2026-10-07. The unused premise `codeUnchanged` was removed from soundness on 2026-11-03 with Ari's approval |
| A run uses no RAM 2 GiB or more above `RAM_START` (`bug-report/final-ram-over-2gib/`) | No longer an assumption: a16z/jolt#2509 (in `ff6fc6568`) removed the branch of `final_ram_state` that filed bytes 2 GiB or more above `RAM_START` at the wrong address, and `TraceWitness.finalRamWord` models the fixed code, which puts every byte at its own address | a16z, 2026-10-07 |
| No spoil assert fails | `Trace.SpoilAssertsPass`, part of `JoltInstance.InLanguage` | Part of L, not a premise (Ari, 2026-10-15): a spoiled run is meant to have no proof (`jolt-platform/src/spoil.rs`) |
| Jolt's prover accepts the trace | `(trace.prover_config joltInstance).isSome`, part of `JoltInstance.InLanguage` | Part of L, not a premise (Ari, 2026-10-15): Jolt's prover refuses other traces (`ProverConfig::derive_from_dimensions`). `JoltInstance.completeness` takes the accepted config `config` and uses Jolt's sizes, modeled with the fix of [#1951](https://github.com/a16z/jolt/issues/1951) item 4 from [a16z/jolt#2250](https://github.com/a16z/jolt/pull/2250) |

The SC.W and SC.D restriction `noStoreConditional`, which no proof used after a16z/jolt#2039, was removed on 2026-11-03 with Ari's approval.

The premise `pcNoWrap`, that no instruction's next PC passes 2^64, was removed from both theorems on 2026-11-05 with Ari's approval.
Since a16z/jolt#2129, Jolt's ELF decoder (`decode_elf` in `crates/jolt-program/src/image/elf.rs`) rejects any program that breaks it, so it is now the image field `Rv64ProgramImage.next_pc_no_wrap` in `program.lean`.

The premise `imageNonempty`, that the program's memory image loads at least one byte, was removed from completeness on 2026-11-25.
Jolt's prover rejects an empty trace, every trace row runs a row of the expanded bytecode, and `decode_elf` emits an instruction only from a nonzero halfword of a loaded section. `HonestTrace.prover_config_image_nonempty` combines the three, with the last as the image field `Rv64ProgramImage.instruction_loaded`.

## Proofs owed

**Soundness.** At Lean HEAD `7096dca`, `JoltInstance.soundness` (`theorems/Soundness/soundness.lean`) had no `sorry`.
On 2026-10-23, `lake build JoltBytecode JoltConstraints` passed (8,832 jobs) and `#print axioms JoltInstance.soundness` listed only `propext`, `sys_enable_experimental_extensions`, `Classical.choice` and `Quot.sound`.
On 2026-11-03, with the Step 4 changes on top of `e299498`, `lake build JoltConstraints` passed against the migrated model (8,837 jobs), and `#print axioms JoltInstance.soundness` lists the same four axioms and no `sorryAx`.
No soundness proof has a `sorry`, and no blocker lemma was staged.
Since the Sail model was regenerated with the Jolt hart patch, `sys_enable_experimental_extensions` is a definition, not an axiom, and `#print axioms JoltInstance.soundness` lists only `propext`, `Classical.choice` and `Quot.sound`.
The proof's structure is in `methods/soundness.md`, "The argument in brief".
See the [Step 4 report](../../reports/2026-11-03-constraints-migration-soundness.md).

**Completeness.** On 2026-11-03 (Step 5), `JoltInstance.completeness` states that the honest witness at the sizes Jolt's prover picks satisfies `AllConstraints`; the earlier existential statement is `JoltInstance.completeness_someWitness`.
On that date `#print axioms` for both listed `propext`, `sorryAx`, `Classical.choice` and `Quot.sound`. Since 2026-11-25 neither theorem has a `sorry`. `sys_enable_experimental_extensions` has been a definition, not an axiom, since the Sail model was regenerated with the Jolt hart patch.
`lake build JoltConstraints.theorems.Completeness` and `lake build JoltConstraints.theorems.Completeness.completeness` pass.
The three #1949 completeness gaps recorded in the [Step 2 report](../../reports/2026-11-03-constraints-migration-completeness.md) and the [Step 5 report](../../reports/2026-11-03-completeness-jolt-prover.md) are proved since 2026-11-25, as the table below records.
The #1951 item 4 lemma `HonestTrace.prover_config_holds_highest_slot` is proved under the fix of [a16z/jolt#2250](https://github.com/a16z/jolt/pull/2250) ([experiment report](../../reports/2026-11-03-ram-k-fix-experiment.md)).
The verifier's RAM bounds at Jolt's sizes, `HonestTrace.witness_params_ram_bounds` (`theorems/Completeness/Helpers/VerifierSizes.lean`), are proved, including that both bounds compute.

| Theorem | What it needs |
|---|---|
| (01) `honestWitness_ramAddrEqRs1PlusImmMinusLookupIfLoadStore` (`theorems/Completeness/RamAddrEqRs1PlusImmMinusLookupIfLoadStore.lean`) | proved on 2026-11-25 from `HonestTrace.access_noWrap` |
| (08) `HonestTrace.floorAccess_address_nonneg` (`theorems/Completeness/RightLookupAdd.lean`) | proved on 2026-11-25 from `HonestTrace.access_noWrap` |
| (11) `HonestTrace.shiftData_address_noWrap` (`theorems/Completeness/RightLookupEqRightInputOtherwise.lean`) | proved on 2026-11-25: the floor store two rows later has the same base and offset (`HonestTrace.shiftData_store`) and does not wrap |

Both RAM-history completeness theorems, (37) and (38), are proved at the shared-memory pin; the flag-word bugs no longer apply.

No `bv_decide` remains in `JoltBytecode` or `JoltConstraints`; all 21 uses were replaced on 2026-10-23.

### Bytecode

`JoltBytecode/` has no `sorry`.
At Lean HEAD `7096dca` it had seven: ECALL, EBREAK, LR.W, SC.W, LR.D and SC.D in the dispatcher `equivalenceStatement_holds`, and MRET's exception-handler postlude in `InstructionEquivalence/Instructions/System/Mret.lean`.
The MRET theorem is now proved.
`joltRun_eq_execute` (`JoltBytecode/Step/Instructions.lean`) replaces the dispatcher, and the step theorems in `JoltBytecode/Step/` cover ECALL's trap entry and LR/SC against `try_step`.
Explicit halts (EBREAK and `jolt.success`) are not executed: the whole-run theorem stops in front of the first one (`docs/riscv-alignment.md` section 4).

Do not weaken a main statement to close a gap.

### Existing tactic debt

These are source debt, not permission to add such tactics or raise limits during repair.
- The obsolete `DeviceMemoryObstruction.lean` and its root import are deleted during the re-pin.
  This removes its two pre-existing executable kernel-decision commands; the harness regex also matches those deleted diff lines, as recorded in the re-pin report.
- No raised limits remain in `JoltBytecode/` or `JoltConstraints/` (2026-11-09); the generated model's remaining declaration-local limits are listed in `docs/riscv-alignment.md` section 8.
- No executable `bv_decide` use remains in `JoltBytecode/` or `JoltConstraints/`; the only textual match is a comment in `theorems/Soundness/Layer4/Interleave.lean:19`.

### Constraints migration (2026-11-03)

Steps 1–3 targeting `c6703570` are committed through `e299498`.
Completeness builds with its six listed gaps, including the two approved honest-row address-wrap obligations.
Step 3 extends `TracerAddressChecks` to floor loads and stores at their containing doubleword.
Step 4 repairs input routing, ShiftData, retired alignment helpers, plain-row classifiers, stall flags and replay-address preservation.
It classifies LD/SD and the floor rows once by width (`theorems/Soundness/Layer5/MemoryRows.lean`) and proves every memory step over that classification.
Ari approved on 2026-11-03 extending `PanicStoresOne`, `TerminationThenStall`, `StoresPanicAt` and `StoresTerminationAt` to the floor rows; no other restriction changed.
The main theorem, `InLanguage`, assumptions and completeness files are unchanged by Step 4.
The eleven migration items are in [constraints.md](constraints.md#migration-outline).
See the [Step 4 report](../../reports/2026-11-03-constraints-migration-soundness.md).
Step 5 restates `JoltInstance.completeness` at Jolt's own sizes and adapts every corrected-size helper to them; see the [Step 5 report](../../reports/2026-11-03-completeness-jolt-prover.md).

### Cleanup

- Speed up `expansion_facts.lean`: its declarations rose from about 11 s to 44 s after the step (c) checker extension (CSRRS 7.7 s, CSRRW 4.5 s, SLLI 1.7 s). Keep the shared expansion checker and avoid another per-instruction proof table.
- Split the Layer 6 proofs longer than about 60 lines: `division_replay_complete_transfer` (`DivisionAppend.lean`, about 315 lines), `division_candidate_first_pre`, `append_expansion_row`, `arithmetic_execution` and `arithmetic_plain_row_step` (`PlainRow.lean`), `arithmetic_advice_suffix_run` (`DivisionDefs.lean`), and `terminal_branch` and `terminal_branch_taken` (`TerminalNextPC.lean`).
- Unpack `JoltInstance.initial_state` once: `initial_state_device`, `initial_state_inputs` (`layout_facts.lean`), `initial_state_empty_outputs_and_input_bound` (`Layer6/BoundaryStart.lean`) and `initial_state_misa` (`Layer5/MisaFrame.lean`) each repeat it.
- `RawRowEntry` (`Layer6/PlainRow.lean`) repeats the entry and linkage clause of `UntrustedAnswerRun.NextStep` and `ExpansionState.next`; defining both from it changes approved definitions and waits for Ari.
- `source_expansion_split` and `expansion_block_eq` (`Layer6/DivisionLayout.lean`) repeat part of the private `expand_program_block` (`Layer6/PlainRow.lean`); generalize it and derive both.
- `source_advice_kind` (`Layer6/DivisionLayout.lean`) classifies every source instruction with a long `simp` list; a checker fact would be shorter.
- Delete the unused `fence_step` (`Layer5/Fence.lean`). The re-pin already deleted `HonestTrace.code_unchanged`.
- `append_load_row` and `append_store_row` (`Layer6/RowStepMemory.lean`) share their operand and append steps, as their LD/SD predecessors did; extract the shared part once both are reviewed.

## Gaps in our model

- **Advice words in initial RAM.** Lean builds untrusted advice from bytes, and every advice word in initial RAM is therefore a 64-bit value. Jolt's verifier takes those words from a committed polynomial and does not range-check them.
  The soundness hypothesis is therefore stronger than Jolt's check: the theorems say nothing about a proof whose committed advice holds a word of `2^64` or more.
  Trusted advice has the same gap, because Lean also models its contents as bytes.
  The 2026-10-29 report (finding 1) suggested that LD followed by MULHU could turn such a word into a false claim. The constraints block that attack at `ff6fc6568`: LD carries `RightOperandIsRdWriteValue` (`crates/jolt-riscv/src/instructions/i/ld.rs:1-8`). Constraint (11) therefore makes the loaded value the right lookup operand, and constraint (41) bounds that operand below `2^64` through the instruction read-RAF.
  Closing the gap still needs either a proof that no satisfying witness reads an out-of-range advice word, or a model of advice words as field elements, which changes a core definition and waits for Ari.
- **HostIO END marker (resolved by the re-pin).** At `ff6fc6568` Jolt's tracer reads the label for both cycle-marker events and ignores a rejected read; the total host-call model (`JoltISA.execHostIOWith`) does the same, so finding 2 of the 2026-10-29 report no longer applies.
- **Host allocation.** The model assumes every host allocation succeeds. In Jolt's tracer at `ff6fc6568`, `read_host_bytes` returns `HostReadError::Allocation` when `try_reserve` fails (`tracer/src/emulator/host_io.rs:72-75`), and `handle_advice_write` then logs the error and appends nothing (`tracer/src/emulator/cpu.rs:1185-1196`). The model appends the bytes to the advice tape. Host out-of-memory aborts, for example in memory-access bookkeeping or the tracing subscriber, are not modelled as guest outcomes ([host-call report](../../reports/2026-11-24-hostio-repin.md), "Explicit modelling choices and limits").
- **ELF sections and `tohost`.** Lean's initial RAM (`initialRam`, `program.lean`) zero-fills the RAM region and writes preprocessing's `memory_init`, which `decode_elf` fills from every section at or above `RAM_START_ADDRESS` (`crates/jolt-program/src/image/elf.rs:84-133`). Jolt's tracer differs in two ways (`setup_program`, `tracer/src/emulator/mod.rs:270-340`). The model cannot state either difference, because `ElfSection` (`WholeRun/Elf.lean`) records no section type, file offset or symbol (2026-10-29 report, findings 3 and 4).
  - **Section types and offsets.** The tracer loads only sections of type `SHT_PROGBITS`, `SHT_INIT_ARRAY`, `SHT_FINI_ARRAY` and `SHT_PREINIT_ARRAY` (1, 14, 15 and 16), and only when the section starts at or above `RAM_START_ADDRESS` and has a nonzero file offset and size. Any other section that `decode_elf` loads stays zero in the tracer.
  - **`tohost` cap.** When the ELF has a nonzero `tohost` symbol (`tohost_address`, `mod.rs:51-56`), the tracer treats it as a riscv-tests ELF and caps its RAM backing at the smaller of the layout's RAM size and `TEST_MEMORY_CAPACITY` (`DEFAULT_HEAP_SIZE`, `mod.rs:1`). Accesses past that cap fault in the tracer, while the model keeps the full layout.
- **Termination word (resolved by the re-pin).** The old verifier/model gap described in finding 5 of the 2026-10-29 report disappears with the removed memory word.
  The new halt lane checks the public claim instead, and the soundness proof uses it for both claims (`Layer7/Stopping`).
- **Images Jolt never produces.** `Rv64ProgramImage` carries decoded instructions without a decoder certificate.
  It admits ANDN as a source instruction, odd branch and jump offsets, a quotient field on divisions, and instruction lists not tied to the text bytes.
  These only add instances to the theorems.
  A taken odd branch fails Sail's alignment assertion in `jump_to`, so a satisfying witness can never take one: its next unexpanded PC would be odd, but a real next row has an even address and padding or the last cycle forces zero.
- **Trusted base.** The semantics of each Jolt instruction are translated from Jolt's code by hand.
  Native RV64 instructions are proved against Sail (`JoltBytecode/InstructionEquivalence`); virtual instructions have nothing to prove against.
- **Trace representation.** Jolt's `JoltTraceRow` stores encoded operands, optional captures and a resolved bytecode PC.
  Lean's `TraceRow` derives observations from full pre- and post-states; this is a source-audited correspondence, not a formal equivalence with Jolt's packed representation.
  Lean does not represent missing captures or noncanonical NoOp rows; Jolt's row-constructor checks are producer checks, not verifier constraints or premises.
- **Not modeled.** The Akita build's prover configuration (see the Akita item below), program commitments (ProgramBytecode, ProgramImageInit), and the advice witness columns and commitment protocols.
  Trusted advice contents are modeled directly as part of the instance; Lean has no flag for a trusted-advice commitment being absent.
- **Akita.** The field premise and the constraint algebra cover Akita's field. The relation includes Akita's instruction-address canonicality guard as constraint (63), on exactly when the characteristic is below `2^128`, as Jolt's `akita` feature turns it on together with the fp128 field (`methods/soundness.md`, Layer 4).
  The prover configuration and sizing model is for the base Dory build only. `translation/prover_config.lean` pads to at least 256 rows, `WitnessParams.ProverChunkConfig` follows the base one-hot chunk policy, `ConstraintContext.traceLengthFloor` requires only 256 rows, and `oneHotFitsSetup` checks Dory's setup bound (`dorySetupLogN`).
  With the `akita` feature, pinned Jolt pads every trace to at least 4096 rows (`crates/jolt-verifier/src/config.rs:93-103`) and keeps 4/16-bit one-hot chunks at every trace length (`one_hot_config`, `crates/jolt-prover/src/config.rs:207-208`), where the base build switches to 8/32-bit chunks from `log_T = 25`.
  Completeness at Akita's own sizes is therefore not proved.
- **Expansions.** `SourceInstruction.expand` uses the bytecode project's programs.
  On 2026-10-29 every source kind's rows were compared with Jolt's expander at `5def437f` and match (2026-10-29 report).
  The header of `JoltBytecode/JoltISA/ExpansionsAutomated.lean` says it is generated by `jolt-lean-gen`, but the generator at the pin cannot produce it; the local generator patches are in `methods/model_update/`.
  The LR/SC expansions are proved against Sail by `joltRun_eq_execute` (`JoltBytecode/Step/Instructions.lean`).
- **LR/SC reservations.** Jolt's native `SCW::exec` and `SCD::exec` consult `cpu.reservation_covers`, but the tracer does not use them at `ff6fc6568`: `SCW::trace` and `SCD::trace` run the expanded sequence, and untraced execution (`Instruction::execute`, `tracer/src/instruction/mod.rs:714-741`) dispatches to `trace(cpu, None)`.
  The expansions and this model both compute success from virtual registers 32 and 33. No correspondence with the native reservation remains to be proved.
- **Floating-point axioms.** `LeanRV64D/RiscvExtras.lean`, the Sail model's handwritten platform file, declares 67 floating-point primitives (for example `riscv_f16Add`) as Lean `axiom`s.
  They lie outside the headline closures: F and D are off in Jolt's hart, their instruction modules are not generated (`docs/riscv-alignment.md` section 8), and `#print axioms` for the soundness and whole-run theorems lists none of them.
- **To do.** Fix comments that cite an unpinned fork or the crate `jolt-trace`; answer the `metadata.lean` TODOs the 2026-10-29 report settled.
  Drop the unused `ramFits`, `traceFits` and `bytecodeDomain` arguments.

## Classifier call sites

Step 1 replaced `opcodeFlag_load_requiresLD` and `opcodeFlag_store_requiresSD` by `opcodeFlag_load_cases` and `opcodeFlag_store_cases`, covering LD/SD and the floor rows with unchanged hypotheses.
Step 2 migrated both completeness load callers through `theorems/Completeness/Helpers/MemoryValueFacts.lean` and the store caller in `theorems/Completeness/Rs2EqRamWriteIfStore.lean`.
These proofs use the shared classification and retain their original premises.
Step 4 migrates `plain_no_memory` (`theorems/Soundness/Layer6/PlainRow.lean`) and `stable_stall_source_no_store` (`theorems/Soundness/Layer7/StallSuffix.lean`) to the widened classifiers; the `ff6fc6568` re-pin later deleted `stable_stall_source_no_store` with the stall-based ending.
`loadRow_of_flag` and `storeRow_of_flag` (`theorems/Soundness/Layer5/MemoryRows.lean`) wrap them as the `LoadRow`/`StoreRow` classification used by `row_kind` (`theorems/Soundness/Layer6/RowStepKinds.lean`).
Before the `ff6fc6568` re-pin, `row_panic_of_no_store` (`Layer5/DeviceMemory.lean`) and `termination_effect_is_store` (`Layer7/TerminationStore.lean`) used it too; the re-pin deleted both files.
No call to the old SD-only or LD-only classifiers remains.

## Correspondence migration (2026-11-03)

- Step 1 migrated the seven instruction flags, AddressOffset tables, metadata, register selectors and floor-row observations; Ari reviewed those definitions.
- Step 2 migrates the completeness proofs with no new premises and only the approved (08) and (11) wrap gaps.
  Its AddressOffset dispatch and constraint (39) now build after the approved `Soundness.Layer4.WordEntry` repair.
- `TracerAddressChecks` (then at `theorems/Soundness/Layer5/MemoryAccessRestriction.lean:89`) covered native and floor loads/stores, as approved in Step 3.
  `PanicStoresOne`, `TerminationThenStall` and their completed-store predicates covered them too, as approved by Ari on 2026-11-03 (Step 4, work item 5).
  The `ff6fc6568` re-pin removed all three restrictions.
