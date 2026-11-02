---
title: Jolt model in Lean, open issues
updated: 2026-11-02
rust: 5def437f21a0006e13c063a03f0b5a7c9b93cd6f
alignment_target: c6703570588e88033b8722bd4dec47c7f46f3b16
lean_head: 7096dcaeb62e4a49d259b511dce76c3bc77bae5f
---

# Open issues

This file lists what the theorems rest on that is not proved: Jolt issues, assumptions, owed proofs and gaps in the model.
`JoltInstance.soundness` was proved at Lean HEAD `7096dca`, under the temporary restrictions, with no `sorry`; see the [current status](../methods/soundness.md#current-top-level-status-2026-10-23).
It has not been re-verified since the bytecode migration, and `JoltConstraints` does not build against the migrated bytecode; see [Current state](../methods/soundness.md#current-state-2026-11-02).
`JoltInstance.completeness` still has the `sorry`s listed under "Proofs owed".
The latest check of the soundness statement against Jolt's code is `reports/2026-10-29-soundness-statement-audit.md`.

**Jolt pin:** `5def437f21a0006e13c063a03f0b5a7c9b93cd6f` since 2026-10-22.
**Migration target:** `c6703570588e88033b8722bd4dec47c7f46f3b16`, the local `origin/main` of the fork `abiswas3/jolt`; this is not a pin update.
Older findings below keep the revision at which they were established.

The completeness theorem is `JoltInstance.completeness` (`Completeness/completeness.lean`): every instance in `JoltInstance.InLanguage` (`language.lean`) has private inputs and a witness that satisfy `AllConstraints`, given `JoltInstance.CompletenessAssumptions`.
Its workhorse is `HonestTrace.allConstraints_corrected_sizes` (`Completeness/All.lean`), which builds the witness at corrected sizes, because Jolt's own RAM size can be one slot too small (#1951 item 4).
`Trace.prover_config` models Jolt's checked sizing policy; when it accepts, so does the corrected policy (`HonestTrace.corrected_prover_config_isSome`).

**Source-language scope.** Completeness and soundness cover programs represented by `SourceInstruction`: the modeled RISC-V instructions and the listed Jolt custom instructions at opcode `0x5B`.
Jolt's inline/precompile opcodes `0x0B` and `0x2B`, including the SHA-256 and Keccak inlines, and its field-inline opcode `0x7B` are outside this type.
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
| [#1949](https://github.com/a16z/jolt/issues/1949) | A load/store address that wraps past 2^64 breaks the RAM-address constraint | (01) stays `sorry`; a fix PR is announced in the issue |
| [#1951](https://github.com/a16z/jolt/issues/1951) item 1 | A run that does not panic and never stores to the termination word: an SDK guest exiting through `platform_exit` or `std::process::exit`, or a bare ELF that reaches `j .` first. The tracer records no write to the word, but `jolt-witness`'s `final_ram_state` sets its `RamValFinal` slot to 1 from the panic flag alone, while initial RAM and the increments give 0 | (38) stays `sorry`. The fix proposed in the issue changes only the SDK's exit paths, so a bare ELF stays unprovable |
| [#1950](https://github.com/a16z/jolt/issues/1950), [#1951](https://github.com/a16z/jolt/issues/1951) item 2 | A store to the termination word is recorded but the device ignores it, so a later load reads 0 (`bug-report/ram-val-termination/`) | (37) stays `sorry`; `Trace.matches_outputs` leaves the termination word out, and `Represents.finalRam` excludes it |
| [#1951](https://github.com/a16z/jolt/issues/1951) item 3 | A load from a nonzero address below the lowest address: the tracer runs it, the checked prover configuration rejects it | such runs have no checked `Trace.prover_config` |
| [#1951](https://github.com/a16z/jolt/issues/1951) item 4 | `ram_K` is one slot too small when the highest touched slot is a power of two (`bug-report/ram-k-off-by-one/`). The verifier's maximum is also one word short: `compute_max_ram_k` rounds `total_bytes / 8` down. When `heap_end` is not a multiple of 8 (`program_size` is not rounded), a program may access the word that straddles `heap_end`, and an honest run that does so gets no proof. The issue proposes `touched + 1` together with `div_ceil(8)` | `Trace.prover_config` preserves Jolt's formula. The separate `HonestTrace.corrected_prover_config` uses `touched + 1` for completeness. The discrepancy blocks the upper half of the verifier's RAM-size check (`ramSizeBounds`, via `HonestTrace.corrected_witness_params_ram_bounds`) |
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
| No source row is SC.W or SC.D (temporary) | `Rv64ProgramImage.NoStoreConditional`, field `noStoreConditional` of `JoltInstance.TemporaryRestrictions` | Ari, 2026-10-10, for the SC advice mismatch (#2037), fixed upstream by #2039. No proof uses it |
| Every attempted LD/SD passes the tracer's address assertions (temporary) | `JoltInstance.TracerAddressChecks` in `Soundness/Layer5/MemoryAccessRestriction.lean`, field `tracerAddressChecks` | Approved by Ari for #2044 and four separate candidates: zero stores, the I/O gap, canary stores and accesses at or above `heap_end`. Quantifies over every private input and relaxed prefix with honest internal runtime advice; checks the next attempted row without assuming it succeeds. Uses `Mmu.effective_address_ok` at the start for RAM, every byte for devices. FIXME to narrow or remove as each case is resolved and proved; not a verifier check. Covers LD and SD only.
Ari approved on 2026-11-02 extending it to floor-row accesses (`VirtualLoad/StoreB/H/W`) as a temporary premise; the extension is part of the constraints migration (constraints.md, item 10) |
| Every attempted HostIO call succeeds (temporary) | `JoltInstance.HostCallsSucceed` in `Soundness/Layer5/HostCallRestriction.lean`, field `hostCallsSucceed` | Excludes host-call failures in live mode, which the constraints do not encode; program-execution condition approved by Ari pending the a16z batch |
| Termination is followed by a stall and no later termination load (temporary) | `JoltInstance.TerminationThenStall` in `Soundness/Layer5/TerminationRestriction.lean`, field `terminationThenStall` | Approved by Ari for a witness that stops early at a jump, and the termination word's device/table mismatch |
| Every store to the panic word stores 1, and no load reads the panic word after such a store (temporary) | `JoltInstance.PanicStoresOne` in `Soundness/Layer5/PanicRestriction.lean`, field `panicStoresOne` | Added 2026-10-20 to exclude a store of 0 being proved as "no panic" (`LayerZero-Research/LZ-Notes:content/projects/jolt-qed/blog/completeness-and-soundness/index.md`). A Jolt bug: it must be fixed in Jolt and may not remain a restriction |
| The claim says "no panic" (temporary) | `JoltInstance.ClaimsNoPanic` in `Soundness/Layer5/PanicRestriction.lean`, field `claimsNoPanic` | Added 2026-10-20 to exclude a "panicked" claim proved from an execution cut short at a jump (`LayerZero-Research/LZ-Notes:content/projects/jolt-qed/blog/proof-stops-at-any-jump/index.md`). A Jolt bug: it must be fixed in Jolt and may not remain a restriction |
| No relaxed trace has exactly the largest power-of-two number of real rows within the instance maximum (temporary) | `JoltInstance.NoMaxLengthTrace`, field `noMaxLengthTrace` | Ari, 2026-10-22: excludes the full-length prover/verifier mismatch in `LayerZero-Research/LZ-Notes:content/projects/jolt-qed/blog/prover-verifier-trace-length/index.md`, preserves a 256-row run under maximum 1024 that Jolt's prover pads to 512, and must be removed when Jolt resolves the mismatch |
| The PC does not wrap past 2^64 | `Rv64ProgramImage.NextPCNoWrap`, field `pcNoWrap` of `JoltInstance.SoundnessAssumptions` and `JoltInstance.CompletenessAssumptions` | a16z, 2026-10-07: such an ELF is illegal |
| The maximum padded RAM region satisfies `lowest + 8 * maxRamSize ≤ 2^64` | `JoltInstance.RamRegionFits` in `Soundness/Layer3/Layout.lean`, field `ramRegionFits` of `JoltInstance.SoundnessAssumptions` | Approved by Ari, 2026-10-10. With the verifier's RAM-size check, all eight bytes of each in-domain word fit, so satisfying LD/SD cycles have nonwrapping addresses. NOTE: to confirm with a16z. An instance restriction, not a verifier check |
| A program is never empty: its memory image loads at least one byte | `Rv64ProgramImage.ImageNonempty`, field `imageNonempty` of `JoltInstance.CompletenessAssumptions` | a16z, by phone, 2026-10-08. Jolt's prover does not reject an empty ELF: it traces it and picks `ram_K = 4`, and only Jolt's verifier rejects that size (`InvalidRamK`, minimum 16 with a 64-byte output region; `bug-report/verifier-ram-minimum/`) |
| A program does not change its own code ([#1952](https://github.com/a16z/jolt/issues/1952)) | `JoltInstance.CodeUnchanged`, field `codeUnchanged` of `JoltInstance.SoundnessAssumptions`; completeness does not use it | a16z, 2026-10-07. No proof uses it |
| A run uses no RAM 2 GiB or more above `RAM_START` (`bug-report/final-ram-over-2gib/`) | ASSUMPTION in `finalRamWord` | a16z, 2026-10-07 |
| No spoil assert fails | `Trace.SpoilAssertsPass`, part of `JoltInstance.InLanguage` | Part of L, not a premise (Ari, 2026-10-15): a spoiled run is meant to have no proof (`jolt-platform/src/spoil.rs`) |
| Jolt's prover accepts the trace | `(trace.prover_config joltInstance).isSome`, part of `JoltInstance.InLanguage` | Part of L, not a premise (Ari, 2026-10-15): Jolt's prover refuses other traces (`ProverConfig::derive_from_dimensions`). Completeness uses the corrected sizes, so Jolt's undersized RAM ([#1951](https://github.com/a16z/jolt/issues/1951) item 4) needs no premise |

No proof uses `noStoreConditional` or `codeUnchanged` (code search, 2026-10-29), so both can be dropped from the soundness statement with Ari's approval.

## Proofs owed

**Soundness.** At Lean HEAD `7096dca`, `JoltInstance.soundness` (`Soundness/soundness.lean`) had no `sorry`.
On 2026-10-23, `lake build JoltBytecode JoltConstraints` passed (8,832 jobs) and `#print axioms JoltInstance.soundness` listed only `propext`, `sys_enable_experimental_extensions`, `Classical.choice` and `Quot.sound`.
That check used the old definitions; the working tree's `JoltConstraints` does not build now (see the constraints migration below), so this proof is not verified against the migrated bytecode.
The proof's structure is in `methods/soundness.md`, "The argument in brief".

**Completeness.** `#print axioms JoltInstance.completeness` lists `propext`, `sorryAx`, `sys_enable_experimental_extensions`, `Classical.choice` and `Quot.sound`; its `sorryAx` comes from these gaps:

| Theorem | What it needs |
|---|---|
| (01) `honestWitness_ramAddrEqRs1PlusImmIfLoadStore` | false until #1949 is fixed |
| (37) `honestWitness_ramValEqInitialPlusPrefixRamInc` | false until #1950 is fixed |
| (38) `honestWitness_ramValFinalEqInitialPlusRamInc` | false until #1951 item 1 is fixed |
| `HonestTrace.corrected_witness_params_ram_bounds` (`Completeness/Helpers/VerifierSizes.lean`) | The empty program is excluded by the `ImageNonempty` assumption. Lower half: proved once the minimum computes successfully; still to prove that both bounds compute successfully. Upper half: false until #1951 item 4 is fixed, because the verifier's maximum rounds the word count down |

No `bv_decide` remains in `JoltBytecode` or `JoltConstraints`; all 21 uses were replaced on 2026-10-23.

### Bytecode

The seven source `sorry` occurrences are all present at Lean HEAD `7096dca` and in the working tree.
`lake build JoltBytecode` passed on 2026-11-02 with exit 0 and 8459 jobs.

| Instruction | Source occurrence | Existing obligation |
|---|---|---|
| ECALL | `JoltBytecode/RiscvInstruction.lean:805` | Dispatcher equivalence case remains admitted. |
| EBREAK | `JoltBytecode/RiscvInstruction.lean:807` | Dispatcher equivalence case remains admitted. |
| LR.W | `JoltBytecode/RiscvInstruction.lean:813` | Load-reserved equivalence remains admitted. |
| SC.W | `JoltBytecode/RiscvInstruction.lean:815` | Store-conditional equivalence remains admitted. |
| LR.D | `JoltBytecode/RiscvInstruction.lean:817` | Load-reserved equivalence remains admitted. |
| SC.D | `JoltBytecode/RiscvInstruction.lean:819` | Store-conditional equivalence remains admitted. |
| MRET | `JoltBytecode/InstructionEquivalence/Instructions/System/Mret.lean:162` | The generated Sail exception-handler postlude remains unproved. |

Do not weaken a main statement to close one of these gaps.

### Existing tactic debt

These are source debt, not permission to add such tactics or raise limits during repair.
- `decide +kernel` at `JoltConstraints/Soundness/Layer5/DeviceMemoryObstruction.lean:52` and `:59`; `AGENTS.md` bans it.
- Raised heartbeat limits: `set_option maxHeartbeats 1000000` at `JoltConstraints/Completeness/Helpers/LookupWriteProofHelpers.lean:4`, and `400000` at `JoltConstraints/Completeness/Helpers/TracePCProofHelpers.lean:7`.
- No executable `bv_decide` use remains in `JoltBytecode/` or `JoltConstraints/`; the only textual match is a comment in `Soundness/Layer4/Interleave.lean:17`.

### Constraints migration (not started)

The `c6703570` migration of the constraints has not started.
Its eleven items, with the verified target facts, are in [constraints.md](constraints.md#migration-outline).
Ari approved retiring the three alignment lookup-entry theorems (item 6); that retirement is not executed yet.
Until the migration is done, `JoltConstraints` does not build, and no completeness or soundness claim is re-verified against the target.

### Cleanup

- Speed up `expansion_facts.lean`: its declarations rose from about 11 s to 44 s after the step (c) checker extension (CSRRS 7.7 s, CSRRW 4.5 s, SLLI 1.7 s). Keep the shared expansion checker and avoid another per-instruction proof table.
- Split the Layer 6 proofs longer than about 60 lines: `division_replay_complete_transfer` (`DivisionAppend.lean`, about 315 lines), `division_candidate_first_pre`, `append_expansion_row`, `arithmetic_execution` and `arithmetic_plain_row_step` (`PlainRow.lean`), `arithmetic_advice_suffix_run` (`DivisionDefs.lean`), and `terminal_branch` and `terminal_branch_taken` (`TerminalNextPC.lean`).
- Unpack `JoltInstance.initial_state` once: `initial_state_device`, `initial_state_inputs` (`layout_facts.lean`), `initial_state_empty_outputs_and_input_bound` (`Layer6/BoundaryStart.lean`) and `initial_state_misa` (`Layer5/MisaFrame.lean`) each repeat it.
- `RawRowEntry` (`Layer6/PlainRow.lean`) repeats the entry and linkage clause of `UntrustedAnswerRun.NextStep` and `ExpansionState.next`; defining both from it changes approved definitions and waits for Ari.
- `source_expansion_split` and `expansion_block_eq` (`Layer6/DivisionLayout.lean`) repeat part of the private `expand_program_block` (`Layer6/PlainRow.lean`); generalize it and derive both.
- `source_advice_kind` (`Layer6/DivisionLayout.lean`) classifies every source instruction with a long `simp` list; a checker fact would be shorter.
- Delete the unused `fence_step` (`Layer5/Fence.lean`) and `HonestTrace.code_unchanged` (`honest_trace.lean`).
- `Soundness/Layer5/DeviceMemoryObstruction.lean` uses `decide +kernel`, which `AGENTS.md` bans; only `JoltConstraints.lean` imports it and no proof uses it, so delete it or move its finding to the docs.

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

`JoltMetadata.opcodeFlag_load_requiresLD` (`metadata.lean:215`) and `opcodeFlag_store_requiresSD` (`metadata.lean:220`) conclude that a flagged instruction is LD or SD, respectively.
Once the six floor rows receive their target flags, these conclusions must also cover the floor constructors.
They are helper statements, so generalizing them needs no approval and adds no premise.
Each caller should use one shared classification, not a new whole-instruction case split.

| Classifier | Call site |
|---|---|
| Load | `Completeness/RamReadEqRamWriteIfLoad.lean:27` |
| Load | `Completeness/RamReadEqRdWriteIfLoad.lean:27` |
| Load | `Soundness/Layer6/PlainRow.lean:949` |
| Store | `Completeness/Rs2EqRamWriteIfStore.lean:27` |
| Store | `Soundness/Layer6/PlainRow.lean:954` |
| Store | `Soundness/Layer7/TerminationStore.lean:703` |
| Store | `Soundness/Layer7/StallSuffix.lean:3305` |

## Correspondence still to audit (2026-11-02)

- `witness.lean:21` declares six instruction flags; the target has seven, with `RightOperandIsRdWriteValue` appended after `IsNoop`.
  Its `LookupTableKind` still has `AlignAddr`, `HalfwordAlignment` and `WordAlignment`, which the target replaces with `AddressOffsetB/H/W`.
- `metadata.lean`, `register_encoding.lean`, and several witness helpers still refer to the retired instructions.
- `TraceRow.ram_address` (`trace.lean:50`) recognizes only `LD` and `SD`.
  Floor-row observations, operand selectors, and lookup inputs and outputs must agree with the target tracer and witness, not merely make pattern matches exhaustive.
- `TracerAddressChecks` (`Soundness/Layer5/MemoryAccessRestriction.lean:97`) returns `True` for every row other than LD and SD.
  Its comment at line 82, that LD and SD are the only memory accesses after expansion, is stale.
