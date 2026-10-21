---
title: Jolt model in Lean, open issues
updated: 2026-10-21
rust: 8bbb2357890928d8f83b00ca542879077c4d3d28
migration: implemented and validated
---

# Open issues

For the next soundness session, start with
[the change of course](../methods/soundness.md#change-of-course-top-down-2026-10-20):
since 2026-10-20 the soundness proof is built top-down from
`JoltInstance.soundness`, with helper lemmas stated as `sorry` first. The same
section summarizes the argument and says where to start. The
[Layer 5b handoff](../methods/soundness.md#layer-5b-handoff-updated-2026-10-20)
records the existing step lemmas: 77 of 88 native row kinds have local steps,
two are unreachable, and nine remain, plus device agreement and the
dispatcher.
`ExpansionFacts.expand_temps_ok` proves per-expansion temporary write-before-read; the global induction will use [live-register agreement](../methods/soundness.md#register-agreement-must-be-over-live-registers) instead of keeping the HostIO temporary unavailable.

**Current Rust semantics pin, selected with Ari on 2026-10-15:** upstream
[`8bbb2357890928d8f83b00ca542879077c4d3d28`](https://github.com/a16z/jolt/commit/8bbb2357890928d8f83b00ca542879077c4d3d28).
The inspected local merge is `1c8aaff2`; its unpublished generator changes
are recorded separately, with a reproducible patch, in the migration checklist.
Chunks 1–6 were reviewed by reading and adopted. The corrected-sizing
completeness caller remains; the unused Rust-sizes corollary and supporting
lemmas were later removed, as the migration follow-up records. The previous
baseline was `43cc043` plus the reviewed SC and advice-length changes. The
[migration checklist](../methods/model_update.md) records the concrete changes,
source audits and remaining proof obligations. Historical revision citations
below retain the revision at which each finding was established.

The completeness theorem is `JoltInstance.completeness`
(`Completeness/completeness.lean`): every instance in `JoltInstance.InLanguage`
(`language.lean`) has private inputs and a witness that satisfy
`AllConstraints`, given `JoltInstance.CompletenessAssumptions`. Its workhorse is
`HonestTrace.allConstraints_corrected_sizes` (`Completeness/All.lean`), which
claims the modeled verifier checks and constraints hold at the explicitly
corrected mathematical sizes, against the verifier’s public I/O.
`Trace.prover_config` models Rust’s checked policy at `8bbb2357`; when it
accepts, so does the corrected policy (`HonestTrace.corrected_prover_config_isSome`).
Rust's accepted RAM domain need not contain the highest touched slot (#1951
item 4), so the witness uses the corrected sizes. The former Rust-sizes
corollary and its bridge lemmas were deleted on 2026-10-15 as unused.
The theorem retains the existing `sorry`s under "Proofs owed" and eight native
bit-vector axioms listed in the migration record; it is not a completed
completeness proof.
The native-proof repair remains deferred until after migration review.
Everything it rests on that is not proved is listed here.

**Source-language scope.** Completeness and soundness cover programs represented
by `SourceInstruction`: the modeled RISC-V instructions and the listed Jolt custom
instructions at opcode `0x5B`. Jolt's inline/precompile opcodes `0x0B` and `0x2B`,
including the SHA-256 and Keccak inlines, and its field-inline opcode `0x7B`
are outside this type. The SDK's `field_to_limbs!` and `field_from_limbs!`
conversions emit `0x7B` instructions, as checked in the migration record.
A guest containing these instructions is outside the theorems' scope by
construction. This existing type
restriction is recorded in [`expansion_helpers.lean`](./expansion_helpers.lean);
it is not an additional premise or a verifier check.

**Advice ISA update.** The model includes the removal from
[PR #2049](https://github.com/a16z/jolt/pull/2049), at
`7b311c939eb63bdd6cbb243b432e55023d2b68e9`. `VirtualAdviceLen` is removed from
the source and final instruction types, both interpreters, metadata and witness
helpers. The 1/2/4/8-byte loads and generated expansions are unchanged.
The finite-tape interpreter still fails on exhaustion; the relaxed interpreter
still accepts independent answers. This removal was adopted before the full
migration recorded above. Lean has no ELF decoder or
serialized instruction format, so upstream rejection of the old encoding and
retirement of tag `0x0062` are outside this translation.

`AllConstraints joltInstance privateInputs witness` binds the constraint data to
the instance through `ConstraintContext` (`constraint_context.lean`). Bytecode,
initial RAM, public I/O and the entry slot cannot be chosen independently of
these inputs. Trusted advice is part of the instance; Jolt's verifier holds a
commitment to it, and we model its contents directly. Untrusted advice is
prover-chosen. Both contribute to initial RAM without being public I/O.
The context also checks the instance's input/output sizes and lowest address,
the padded trace limit, the bytecode domain, and the verifier's RAM bounds.
`ConstraintEquations` is the underlying equation bundle over those data.

## Upstream issues

Jolt issues that stop a completeness proof. If one is still open when the main proofs
pass, escalate it.

| Issue | What breaks | In our model |
|---|---|---|
| [#1949](https://github.com/a16z/jolt/issues/1949) | A load/store address that wraps past 2^64 breaks the RAM-address constraint | (01) stays `sorry`; a fix PR is announced in the issue |
| [#1951](https://github.com/a16z/jolt/issues/1951) item 1 | A run that does not panic and never stores to the termination word: an SDK guest exiting through `platform_exit` or `std::process::exit`, or a bare ELF that reaches `j .` first. The tracer records no write to the word, but `jolt-witness`'s `final_ram_state` sets its `RamValFinal` slot to 1 from the panic flag alone, while initial RAM and the increments give 0 | (38) stays `sorry`. The fix proposed in the issue changes only the SDK's exit paths, so a bare ELF stays unprovable |
| [#1950](https://github.com/a16z/jolt/issues/1950), [#1951](https://github.com/a16z/jolt/issues/1951) item 2 | A store to the termination word is recorded but the device ignores it, so a later load reads 0 (`bug-report/ram-val-termination/`) | (37) stays `sorry`; `Trace.matches_outputs` leaves the termination word out, and `Represents.finalRam` excludes it |
| [#1951](https://github.com/a16z/jolt/issues/1951) item 3 | A load from a nonzero address below the lowest address: the tracer runs it, the checked prover configuration rejects it | such runs have no checked `Trace.prover_config` |
| [#1951](https://github.com/a16z/jolt/issues/1951) item 4 | `ram_K` is one slot too small when the highest touched slot is a power of two (`bug-report/ram-k-off-by-one/`). The verifier's maximum is also one word short: `compute_max_ram_k` rounds `total_bytes / 8` down. When `heap_end` is not a multiple of 8 (`program_size` is not rounded), a program may access the word that straddles `heap_end`, and an honest run that does so gets no proof. The issue proposes `touched + 1` together with `div_ceil(8)` | `Trace.prover_config` preserves Rust’s formula. The explicitly separate `HonestTrace.corrected_prover_config` retains `touched + 1` for completeness. The discrepancy remains open and blocks the upper half of the verifier's RAM-size check (`ramSizeBounds`, via `HonestTrace.corrected_witness_params_ram_bounds`) |
| [#1951](https://github.com/a16z/jolt/issues/1951) item 5 | The emulator loads only some ELF section kinds into RAM, preprocessing loads every section | assumed to agree: `initialRam` TODO in `program.lean` |

## Device-memory soundness findings

The [Layer 5b audit](../methods/soundness.md#layer-5b-one-execution-step), at
Jolt revision `43cc043332762034b5f65379441576e06e7a3890`, distinguishes three
cases. Termination ignores writes (#1950/#1951 item 2); panic sets a flag
regardless of the first byte stored and ignores writes to the other bytes
(B6); input/advice stores are rejected by the MMU. The Lean execution model
matches those behaviours. The source behavior was rechecked at `8bbb2357`
in [migration chunk 6](../methods/model_update.md#chunk-6-source-recheck-and-historical-citations);
the report above remains historical evidence. RAM-table history alone does not establish them.

**Input/advice stores:** the candidate in
[#2041](https://github.com/a16z/jolt/issues/2041) now has a reproduction reported
by Ari in [#2044](https://github.com/a16z/jolt/issues/2044). At `00508a09`, the
tracer aborts at the input store, while a modified tracer records stores into
all three read-only regions and the unchanged verifier accepts outputs 7, 9
and 11 in clear/Dory mode. The report and patch have been read, but this session
has not independently rerun them. This contradicts soundness relative to the
tracer's execution semantics if the reported verification is reproduced.

Ari approved the broader temporary `TracerAddressChecks` premise. It supplies
`Mmu.effective_address_ok` for the next attempted LD or SD after an initialized
relaxed prefix with honest internal runtime advice, even if the attempt would
abort. It matches the tracer's starting-address check for RAM and eight byte
checks for device memory. No witness columns appear in the predicate.

The plan separately records four further candidates: stores at zero, the I/O
padding gap, stores to the stack canary, and loads/stores at or above `heap_end`.
No complete satisfying witness or verifier reproduction exists for those cases
in this work; #2044 does not establish them. Each has its own next check in the
plan. The FIXME links #2044 and these candidates and requires narrowing or
removal as each is resolved and proved. This replaces the input/advice-only
restriction.
Alignment, unsupported peripheral dispatch and panic/termination value agreement remain separate obligations, and stopping is proved in Layer 7; address assertions alone do not establish successful execution.

The [migration source recheck](../methods/model_update.md#source-audits-refreshed-at-the-public-pin)
records the unchanged device/MMU behavior at the public pin and refreshes the
relevant source references. A GitHub API check on 2026-10-15 reports #2044 open.
Michael's comments remain to be reviewed with Ari before revisiting the finding
or its temporary premise; issue state alone does not settle the semantics.

## Assumptions

Premises or fields of the final theorem, with their source or reason below.

| Assumption | Where | Why |
|---|---|---|
| The field's characteristic exceeds `2^128` | `JoltField F`, soundness premise `joltField` | Ari, 2026-10-10: the base relation must distinguish full 128-bit lookup addresses. BN254 satisfies this; model Akita's field and extra address guard separately. PCS security is outside this work |
| No source row is SC.W or SC.D (temporary) | `Rv64ProgramImage.NoStoreConditional`, field `noStoreConditional` of `JoltInstance.TemporaryRestrictions` | Ari, 2026-10-10: exclude the SC advice mismatch (#2037) while proving the remaining cases; remove this restriction after the constraints and model are fixed |
| Every attempted LD/SD passes the tracer's address assertions (temporary) | `JoltInstance.TracerAddressChecks` in `Soundness/Layer5/MemoryAccessRestriction.lean`, field `tracerAddressChecks` of `JoltInstance.TemporaryRestrictions` | Approved by Ari for #2044 and four separate candidates: zero stores, the I/O gap, canary stores and accesses at or above `heap_end`. Quantifies over every private input and relaxed prefix with honest internal runtime advice; checks the next attempted row without assuming it succeeds. Uses `Mmu.effective_address_ok` at the start for RAM, every byte for devices. FIXME to narrow or remove as each case is resolved and proved; not a verifier check |
| Every attempted HostIO call succeeds (temporary) | `JoltInstance.HostCallsSucceed` in `Soundness/Layer5/HostCallRestriction.lean`, field `hostCallsSucceed` | Excludes unencoded host-call failures in live mode; program-execution condition approved by Ari pending the a16z batch |
| Source HostIO calls name x0 (temporary) | `Rv64ProgramImage.HostCallRdZero`, field `hostCallRdZero` | Approved by Ari to exclude an unconstrained architectural destination. The expanded row writes a temporary; its value must be shown dead across the source boundary using `ExpansionFacts.expand_temps_ok` |
| Termination is followed by a stall and no later termination load (temporary) | `JoltInstance.TerminationThenStall` in `Soundness/Layer5/TerminationRestriction.lean`, field `terminationThenStall` | Approved by Ari for the B6 stopping discrepancy; remains until the unrestricted argument is established |
| Every store to the panic word stores 1, and no load reads the panic word after such a store (temporary) | `JoltInstance.PanicStoresOne` in `Soundness/Layer5/PanicRestriction.lean`, field `panicStoresOne` of `JoltInstance.TemporaryRestrictions` | Added 2026-10-20 to exclude a store of 0 being proved as "no panic" (`blog/content/blog/completeness-and-soundness/index.md`). A Jolt bug: it must be fixed in Jolt and may not remain a restriction |
| The claim says "no panic" (temporary) | `JoltInstance.ClaimsNoPanic` in `Soundness/Layer5/PanicRestriction.lean`, field `claimsNoPanic` of `JoltInstance.TemporaryRestrictions` | Added 2026-10-20 to exclude a "panicked" claim proved from an execution cut short at a jump (`blog/content/blog/proof-stops-at-any-jump/index.md`). A Jolt bug: it must be fixed in Jolt and may not remain a restriction |
| The PC does not wrap past 2^64 | `Rv64ProgramImage.NextPCNoWrap`, field `pcNoWrap` of `JoltInstance.SoundnessAssumptions` and `JoltInstance.CompletenessAssumptions` | a16z, 2026-10-07: such an ELF is illegal |
| The maximum padded RAM region satisfies `lowest + 8 * maxRamSize ≤ 2^64` | `JoltInstance.RamRegionFits` in `Soundness/Layer3/Layout.lean`, field `ramRegionFits` of `JoltInstance.SoundnessAssumptions` | Approved by Ari, 2026-10-10, replacing the run-based address restriction. With the verifier's RAM-size check, all eight bytes of each in-domain word fit. The signed sum is then recovered from satisfying constraints, including address zero. NOTE: to confirm with a16z. This is an instance restriction, not a verifier check |
| A program is never empty: its memory image loads at least one byte | `Rv64ProgramImage.ImageNonempty`, field `imageNonempty` of `JoltInstance.CompletenessAssumptions` | a16z, by phone, 2026-10-08. Rust's prover does not reject an empty ELF: it traces it and picks `ram_K = 4`, and only Rust's verifier rejects that size (`InvalidRamK`, minimum 16 with a 64-byte output region; `bug-report/verifier-ram-minimum/`) |
| A program does not change its own code ([#1952](https://github.com/a16z/jolt/issues/1952)) | `JoltInstance.CodeUnchanged`, over every `ValidRun`; honest traces get it from `HonestTrace.code_unchanged`. Field `codeUnchanged` of `JoltInstance.SoundnessAssumptions`; completeness does not use it | a16z, 2026-10-07 |
| A run uses no RAM 2 GiB or more above `RAM_START` (`bug-report/final-ram-over-2gib/`) | ASSUMPTION in `finalRamWord` | a16z, 2026-10-07 |
| No spoil assert fails | `Trace.SpoilAssertsPass`, part of `JoltInstance.InLanguage` | Part of L, not a premise (Ari, 2026-10-15): a spoiled run is meant to have no proof (`jolt-platform/src/spoil.rs:1-3`) |
| The corrected sizing policy accepts the run | `HonestTrace.corrected_prover_config = some config` | Retains the previous theorem’s exact hypothesis; includes last-jump, length and address guards, with the intentional `touched + 1` correction. It is not Rust acceptance. `JoltInstance.completeness` derives it from Jolt's prover accepting (`HonestTrace.corrected_prover_config_isSome`) |
| Jolt's prover accepts the trace | `(trace.prover_config joltInstance).isSome`, part of `JoltInstance.InLanguage` | Part of L, not a premise (Ari, 2026-10-15): Jolt's prover refuses other traces (`config.rs:63-110`). Completeness uses the corrected sizes, so Jolt's undersized RAM ([#1951](https://github.com/a16z/jolt/issues/1951) item 4, `bug-report/ram-k-off-by-one/`) needs no premise |

## Proofs owed

Sorried theorems behind the final theorems; `#print axioms` shows `sorryAx` through them.

**Soundness.** `JoltInstance.soundness` (`Soundness/soundness.lean`) is a short proof from the obligations in `Soundness/TopLevel.lean` and the reverse language inclusion in `Soundness/Layer7/TapeRebuild.lean`.
Its statement has no new premises.
`RepresentsRows` in `Soundness/Layer6/ExecutionPrefix.lean` records the row count, PC, source values and RAM addresses for the relaxed trace cut at its first stable stall, padding, or final witness cycle.
`RepresentsPrefix` adds RAM agreement at that cut for the stopping proof.
`Represents` adds final RAM agreement for every witness RAM index except the termination word, which the device ignores as a store; B, C and D use this form without cut RAM.
The following declarations still use `sorry`:

| Declaration | What it needs |
|---|---|
| `JoltInstance.soundness_execution_prefix_agreement` (`Soundness/Layer6/ExecutionPrefix.lean`) | Build the relaxed run through the first stable stall or padding or the last witness cycle, with real retained rows, no earlier stable stall, represented row observations and honest runtime advice. It must also give `cutRam`: RAM agreement at the cut, or `RamValFinal` agreement when the run fills every cycle, for every RAM word except the termination word, including input, advice, output and panic words. |
| `JoltInstance.soundness_prover_accepts` (C) | ⚠️ **DANGER: known false in two cases, assumed on purpose** until a16z answers the trace-length issue. |
| `JoltInstance.soundness_spoil_asserts_pass` (D) | Connect each spoil assert's pre-state operands to the represented witness source values, then use the lookup/assert equations to rule out a failed assertion. |

Steps 1–6 of the tape-rebuild closing plan are complete; `feat/layer7-tape-rebuild`, rebased onto step (c) commit `de5aff70de66d290ceaeb6e7357ba352b855c5d0`, is merged into `feat/soundness`.
`rebuild_rows` maps the relaxed rows directly with `Array.ofFn`, proving execution, initialization, linkage, row agreement and source-start agreement.
The rebuilt-tape read theorem, the narrow-load shape, and all transfer theorems are proved.
Both advice and register-shift pairs use the checker-independent lift in `Soundness/Layer7/AdjacentRows.lean`.
`TapeRebuild.lean` has no `sorry`, and the axiom audit for `untrustedAnswerLanguage_implies_inLanguage` reports no `sorryAx`.
The tape-growth and device frame proofs instantiate the shared `InstructionFrame.execInstr_rule`; their statements and callers are unchanged.
No protected statement or existing helper hypothesis changed, and no new `bv_decide`, native decision proof or raised limit was used.
See the [step 6 declaration timings and validation report](../methods/soundness.md#tape-rebuild-step-6-2026-10-21) and the [shared-frame report](../methods/soundness.md#tape-rebuild-shared-instruction-frame-2026-10-21).

With Ari's permission (2026-10-20), C remains assumed while a16z considers `blog/content/blog/prover-verifier-trace-length/index.md`.
C fails when the instance maximum is below 256, and when execution fills every cycle of a witness whose length is the largest power of two within the maximum.
In both cases the claim is true, but Jolt's prover rejects the trace.
No other helper uses C.
Apart from those cases, C needs the last-jump, RAM-address and padded-length guards from the constraints and represented rows.

Helper B checks public words outside the termination word through constraint 26, `Represents.finalRam`, field-to-word injectivity and the final RAM overlay.
Its proof is now about `UntrustedAnswerTrace` and has no direct `sorry` or panic restriction.
`Trace.finalTraceState_device_relation`, `UntrustedAnswerTrace.final_device_same`, `UntrustedAnswerTrace.final_outputs_fit_layout` and `public_words_determine_matches_outputs` are proved.
The fixed and relaxed `Same` callers use the trace-kind relation lemmas, and the output decoder uses the proved word-index geometry.
B's axiom audit shows no `sorryAx`.
The previous fixed-tape support proofs were removed from `TopLevel.lean` during the redesign.

The trace-independent statements Ari approved on 2026-10-20 are proved: `execInstr_rule_of_device_relation`, `new_io_geometry`, `ramImageWord_getLsbD`, `ramImageWord_injective_byte`, `trimTrailingZeros_append_zeros`, `trimTrailingZeros_of_padded_eq`, `trimTrailingZeros_idempotent`, `public_io_words_fit_ram`, `ramPublicIoWord_output`, and `ramPublicIoWord_panic`.
`trimTrailingZeros_append_zeros` is private, and `execInstr_rule` for `Same` uses the generic instruction rule directly.
The plain-`Trace` pre-state frame and final RAM overlay were restated for both fixed-tape and relaxed callers and are proved.
The byte-store output bound has only the layout and panic/output span as its geometry premise.
The approved plain-`Trace` final RAM overlay and byte-store output bound are proved.
The generic pre-state relation retains `refl` with Ari's approval because its row-zero case requires it after the start hypothesis became an equality.
The five shared device and geometry statements are proved.
Helper A is proved from the staged execution-prefix statement and the assembled stopping theorem.
The five original step (c) gaps in `StallSuffix.lean` are proved, using the strengthened expansion checker and its proved materialization lift.
`Emission.lean` has been deleted, and the architectural JALR singleton fact now uses the checker.
The approved `expand_program_source_of_row` is proved by extracting the shared traversal from `expand_program_rowOk`; both row validity and JALR operand forms use it.
The final 2026-10-21 axiom audit finds no `sorryAx` in `soundness_stopping`.
A reaches `sorryAx` only through `soundness_execution_prefix_agreement`.
`lake build JoltBytecode JoltConstraints` passed with 8800 jobs.
See the [integration report](../methods/step_c_closing_report.md) for the completed helper, build, axiom audit and declaration timings.
The prefix owns RAM agreement at the cut, and stopping owns final RAM agreement after the constraint-level zero-update proof for repeated stall rows and padding.
The modeled stopping rule follows a16z/jolt PR #2109 at head d2995380, with no new restriction.
Soundness obtains the positive row count from the termination store.

Step (a) defines output matching, checked prover configuration and spoil-assert success once on the plain `Trace`, and both languages use those definitions.
The fixed-tape inclusion is proved with all three conditions.
The reverse inclusion is proved without `sorryAx` in Layer 7 and is the final step of `JoltInstance.soundness`.
The axiom audit found no `sorryAx` in B, the plain-`Trace` final RAM overlay, the byte-store output bound, or the five newly proved statements.
After restating A's obligations, `lake build JoltConstraints.Soundness.TopLevel` passed (8703 jobs) and `git diff --check` passed.
The full `lake build` also passed (8797 jobs).
After replacing source-level replay with the constraint-level suffix statement, `lake build JoltBytecode JoltConstraints` passed (8797 jobs).
With synchronous elaboration, the five new proofs took 12 ms (`writeDst_rule_of_device_relation`), 74 ms (`execWithTapeAnswer_rule_of_device_relation`), 537 ms (`HonestTrace.device_relation`), 494 ms (`UntrustedAnswerTrace.device_relation`), and 213 ms (`new_io_word_geometry`).
The output decoder took 381 ms after using `new_io_word_geometry`, down from 1996 ms before this refactor.

### Proof-performance cleanup

Speed up `expansion_facts.lean` after the step (c) checker extension.
Synchronous declaration elaboration rose from about 11 s to 44 s (11.375 s to 44.287 s measured), with CSRRS at 7.728 s, CSRRW at 4.481 s and SLLI at 1.739 s.
Retain the shared expansion checker and avoid another per-instruction proof table.
This is deferred cleanup authorized by Ari; it is not a remaining logical gap in stopping.

### bv_decide

`bv_decide` is temporarily accepted under the updated `AGENTS.md` rules.
The uses on the step (c) proof path are tracked here for later removal.

| Declaration | Use |
|---|---|
| `JoltConstraints.branch_target_toNat` (`Completeness/NextUnexpandedPCEqPCPlusImmIfShouldBranch.lean:104`) | Existing use proving `(offset.signExtend 128).setWidth 64 = offset.signExtend 64`; `soundness_stopping` depends on this lemma. |

The step (c) checker integration and bytecode proofs have introduced no new uses.

**Completeness:**

| Theorem | What it needs |
|---|---|
| (01) `honestWitness_ramAddrEqRs1PlusImmIfLoadStore` | false until #1949 is fixed |
| (37) `honestWitness_ramValEqInitialPlusPrefixRamInc` | false until #1950 is fixed |
| (38) `honestWitness_ramValFinalEqInitialPlusRamInc` | false until #1951 item 1 is fixed |
| `HonestTrace.corrected_witness_params_ram_bounds` (`Completeness/Helpers/VerifierSizes.lean`) | The empty program is excluded by the `ImageNonempty` assumption. Lower half: proved once the minimum computes successfully; still to prove that both bounds compute successfully. Upper half: false until #1951 item 4 is fixed, because the verifier's maximum rounds the word count down |

## Gaps in our model

- **Trusted base.** The semantics of each Jolt instruction are translated from Rust by
  hand. Native RV64 instructions are proved against Sail
  (`JoltBytecode/InstructionEquivalence`); virtual instructions have nothing to prove
  against.
- **Trace representation.** At `8bbb2357`, Rust's unified `JoltTraceRow` stores
  encoded operands, optional captures and a resolved bytecode PC. The completed
  tracer path and `TraceData::proof_rows()` were rechecked against Lean's state-based
  extractors in [migration chunk 3](../methods/model_update.md#chunk-3-correspondence-audit).
  Their logical values agree in the modeled scope. This remains a source audit,
  not a formal equivalence proof for Rust's packed representation. Lean does not
  represent every accepted missing-capture or noncanonical NoOp record. Rust's
  row-constructor checks are producer checks; no new verifier constraint or
  theorem premise was introduced. Soundness still starts from an arbitrary witness.
- **Not modeled.** The Akita build's 4096-cycle padding floor (`prover_config` uses the
  default build's 256), program commitments (ProgramBytecode, ProgramImageInit), and
  TrustedAdvice/UntrustedAdvice witness columns and commitment protocols. Trusted
  advice contents are modeled directly as part of the instance.
- **Akita soundness scope.** The base constraint relation also omits Akita's
  instruction-address canonicality guard, as recorded in `constraints.md`.
  Rechecked at `8bbb2357`, the `akita` feature enables
  `CANONICAL_INSTRUCTION_ADDRESS` in `jolt-claims`; the stage-5 verifier excludes
  identity-RAF addresses whose upper 64 bits are all ones. The source audit and
  separate-model plan are in [Layer 4](../methods/soundness.md#layer-4-lookups).
  The current soundness theorem uses `2^128 < ringChar F`; its earlier `2^127`
  bound did not justify full-address injectivity for the unguarded base relation.
- **Not modeled.** Rust can trace nonempty trusted-advice bytes without a commitment,
  then fail proving because the verifier expects zeros; Lean has no separate
  commitment-presence flag to express that mismatch.
- **Expansions.** `SourceInstruction.expand` (`expansions.lean`) uses the bytecode
  project's programs. At public pin `8bbb2357`, all 57 programs in
  `ExpansionsAutomated.lean` match fresh `jolt-lean-gen` output byte for byte,
  including both destination branches. LR.W, LR.D, SC.W and SC.D were handwritten
  in that file; chunk 2 adds generator coverage and reproduces their bodies
  unchanged. The generator fixes and reproduction commands are recorded in
  [the migration checklist](../methods/model_update.md). LR/SC are not proved
  against Sail. The unused older `JoltISA.lrwProgram`/`lrdProgram` helpers and
  their import have been removed at Ari's request.
  The rows they emit are checked in `expansion_facts.lean`. Still relied on and not
  stated there: operand order is Rust's rs1/rs2, and `VirtualRev8W` has immediate 0.
- **SC success flag, PR #2039 model.** The new expansion computes success
  with XOR and SLTIU from virtual register 32 (SC.W) or 33 (SC.D) and the target
  address. The RAM guard remains. The patched tracer no longer supplies SC advice,
  so neither does `honestTracerAdvice`. `Layer5/RuntimeAdvice.lean` proves that
  no SC row is a `VirtualAdvice` and that a row without advice has runtime-advice
  agreement `none = none`. Constraint-to-execution
  soundness only needs the ordinary instruction proofs for SC's rows. Register
  agreement supplies the same values of registers 32 and 33 to the witness and
  run, without an invariant interpreting them as an emulator reservation.
  `NoStoreConditional` currently remains pending that instruction coverage.
  The main theorem depends on `sorry` only through `soundness_execution_prefix_agreement`, `soundness_prover_accepts` and `soundness_spoil_asserts_pass`.
  The follow-up steps are in the plan's PR #2039 section.
- **XOR and SLTIU soundness steps.** `Layer5/Xor.lean` and
  `Layer5/SetLessThanImmediate.lean` prove successful execution, the constrained
  write value and preservation of register agreement for selected rows.
  Operand canonicality, RAF, table selection and inputs come from the row and
  constraints; source/destination aliases need no extra condition. This covers
  SC's two comparison instructions individually. Composing the whole expansion,
  the remaining instruction families and RAM agreement are still open.
- **Shared register steps, 2026-10-15.** `Layer5/LookupWrite.lean` shares source
  recovery, interleaved lookup-write reasoning and the final successful
  destination write/register update. XOR and SLTIU supply their proved metadata
  and Layer 4 rules; ADDI also uses the final step lemma. Each caller proves the
  interpreter's read/write equation from successful reads given by register
  agreement. The shared proof derives write success from bytecode canonicality.
  No soundness premise is added. `withRuntimeAdvice_eq_of_noAdvice` is now public,
  and the three step lemmas accept the row's runtime advice and execute the
  patched instruction exactly as the trace definition does. Their results still
  cover aliases, the full post-state and execution at the final cycle. This
  closes the earlier application mismatch; it does not complete Layer 5b.
- **Shared operands and further Layer 5b steps, 2026-10-15.**
  `Layer5/RegisterInputs.lean` now holds the source-value helpers and shares
  register/register and register/immediate input recovery across instruction
  families. The existing ADDI, XOR and SLTIU statements are unchanged. New
  results cover LUI, XORI and VirtualAssertLTE, with one `arithmetic_step`
  covering ADD, SUB and MUL. They derive successful execution from selected
  bytecode, constraints and current register agreement; runtime advice, aliases
  and final-cycle execution are included. VirtualAssertLTE derives that its
  check passes and preserves the entire state, using `RegisterAgreement.noWrite`
  for the next table column. All other new steps reuse `registerWrite_step`.
  The source audit and validation are in `methods/soundness.md`.
  SC.W's remaining rows `VirtualAssertWordAlignment`, `VirtualAlignAddr`, `ANDI`, `LD`, `VirtualWindowMaskW`, `VirtualPextSigned`, `ANDN`, `VirtualShiftDataW` and `SD`, and SC.D's `LD` and `SD`, now have local steps, with LD and SD for ordinary RAM only.
  RAM/PC agreement and whole-trace composition remain open; no main-theorem or instance premise was added.
- **Alignment and ordinary-RAM SD, 2026-10-15.** `Layer5/RamAlignment.lean`
  derives eight-byte alignment from the encoded address and RAM selection,
  including the zero-address case. `Layer5/RamStore.lean` reuses the existing
  byte hit/frame lemmas to show that an eight-byte write updates exactly one
  word on the RAM table's grid. `Layer5/StoreDoubleword.lean` combines these
  with source-register agreement and constraints in `sd_ram_step`: execution
  succeeds, the interpreter and witness perform matching word updates, and
  registers retain agreement. The last-cycle result updates `RamValFinal`.
  This covers the ordinary-RAM branch using the existing address-check fact;
  it adds no instance or main-theorem premise.
  LD and initial ordinary-RAM agreement are now proved (`ld_ram_step` in `Layer5/LoadDoubleword.lean`, `initialRamWord_eq_ram_doubleword` in `Layer5/RamInitialization.lean`); device stores and execution-prefix composition remain open.
  The source check and validation are recorded in `methods/soundness.md`; no new Jolt issue is claimed.
- **LR/SC reservation correspondence (model obligation).** Jolt's native
  execution methods `SCW::exec` and `SCD::exec` consult `cpu.reservation_covers`;
  the patched inline trace path and this model compute success from virtual
  registers 32 and 33. Their agreement remains to be proved at source-instruction
  boundaries: initialization, LR.W setting only the word reservation, LR.D
  setting both, either SC clearing both, and other instructions preserving them.
  Include reservation validity and width, source-register aliases, `rd = x0`,
  and the RAM guard excluding the cleared value zero. Do not assert this
  correspondence inside SC.W, which temporarily uses these registers for the
  success bit and store data. The previous `honestTracerAdvice` translation
  already relied on this unproved correspondence. It is an obligation relating
  the model to Jolt's execution paths, not a soundness premise or a prerequisite
  for removing `NoStoreConditional` from the constraint-to-execution theorem.
- **Soundness execution data.** The relation is proved independent of `advice_tape`
  (`AllConstraints.advice_tape_irrelevant`). Layer 5a now defines
  [`execWithTapeAnswer`](./Soundness/Layer5/TapeSemantics.lean) and
  [`UntrustedAnswerLanguage`](./Soundness/Layer5/TapeTrace.lean) separately from
  the fixed-tape specification. Each tape load gets any 64-bit
  answer; load widths remain restricted to 1, 2, 4 or 8 bytes and advance the
  cursor, but the relaxed rule does not enforce tape contents or exhaustion.
  The answer sequence is private existential data in the relaxed trace.
  Fixed-tape inclusion is proved with identical states, outputs and stopping
  facts. `NarrowAdvice.lean` proves the narrow-load post-processing keeps only
  the signed low-width portion of an answer. `AdviceExpansion.lean` now proves
  the generated AdviceLB/LH/LW sequences and their full execution under the
  relaxed per-row rule, including cursor increments and x0's temporary-register
  branch. Connecting these states to a satisfying witness remains open.
  This implements Ari's decision of 2026-10-10. PR #2049's
  [revised documentation](https://github.com/a16z/jolt/blob/7b311c939eb63bdd6cbb243b432e55023d2b68e9/book/src/usage/runtime_advice.md#security-model)
  explicitly distinguishes the tracer's finite tape from the proof's untrusted
  answers. The removed length-query example is retained as historical evidence
  in the plan; no complete satisfying witness was constructed for it.
  The ISA removal does not change the main theorem's fixed-tape target.
  On 2026-10-15 Ari decided the theorem keeps that target: Jolt's tracer reads
  one tape whose contents the prover chooses, so the relaxed semantics is a
  proof device. Rebuilding one tape from the answers' low bytes gives the same
  registers and memory at the end of every source instruction; that step is
  proved in Layer 7 (`untrustedAnswerLanguage_implies_inLanguage`).
  Internal runtime-advice agreement remains open as part of the execution prefix; see B6 in `methods/review_completeness_and_soundness.md`.
- **RAM region restriction.** `RamRegionFits` now bounds the instance's maximum
  padded RAM region by `2^64`; Ari approved this replacement on 2026-10-10.
  NOTE: to confirm with a16z. The old run-based predicate and next-step helper
  are deleted. `Layer3/Layout.lean` transfers the bound to the witness domain
  using `ConstraintContext.ramSizeBounds`. `Layer5/MemoryAddress.lean` recovers
  the signed integer sum as the selected word address, or exactly zero when
  no word is selected, before deriving the machine address. No premise over
  fixed-tape or relaxed runs is needed. The remaining execution proof must
  establish source-register agreement and actual memory-access behavior.
- **Code-memory assumption.** `CodeUnchanged` also quantifies over fixed-tape runs,
  but the soundness proof executes bytecode rather than fetching it from memory.
  No proved soundness lemma uses this premise, and no relaxed counterpart is
  needed for that execution proof. It is retained as justification for relating
  the model to Jolt's tracer; its role in the final theorem can be reviewed
  separately. It is not a Layer 5b proof blocker.
- **Register agreement.** `Layer5/Registers.lean` now proves initialization,
  successful operand reads, and preservation through PC preparation and
  destination writes for the register part of the soundness invariant.
  It includes `AllRegistersPresent` because `sourceValue` defaults missing
  architectural registers to zero, while execution rejects missing reads.
  Presence follows from initialization and is preserved by writes; it is not
  a new premise. Instruction families still have to establish successful
  writes and their value's encoding in `RdWriteValue` before applying the
  shared update lemma. The new proofs use only Lean's three standard axioms.
- **Routine Layer 5b rows, 2026-10-15.**
  The grouped local steps then covered 68 of 88 row kinds and now cover 77 of 88, with LD and SD established for ordinary RAM.
  The latest batch closes Ari's 29-kind routine list: 27 have local execution steps and VirtualROTRI/VirtualROTRIW are excluded by checked expansion facts.
  Immediate right shifts obtain their mask shape from `immShiftOk`; register-fed
  shifts use a paired producer/shift lemma that derives the shape from the
  preceding mask write. The dispatcher still must connect predecessor and
  successor rows in the execution-prefix induction. Constraint (19) by itself
  only forces `DoNotUpdateUnexpandedPC` before an interior virtual row, and a
  padding no-op also sets that flag. Layer 6 must use entry selection, the
  nonpadding prefix, shifted flags and expanded PC, and the
  expansion's `ShiftPairs` fact to establish the actual predecessor. Rev8W's
  table/interpreter equality is kernel-checked without `bv_decide`. `lake build JoltBytecode
  JoltConstraints` passed (8778 jobs); the new axiom audits contain no native
  decision axiom or `sorryAx`. The source comparison and detailed row list are
  recorded in `methods/soundness.md`. Register-write steps retain register
  agreement; the dispatcher will carry ordinary-RAM agreement with
  `OrdinaryRamAgreement.noAccess` and `afterWriteDst`. No main-theorem premise
  changed.
- **Six assertion rows and HostIO mode, 2026-10-15.** Local steps for
  AssertEQ, both alignment assertions, AssertMulUNoOverflow, AssertValidDiv0
  and AssertValidUnsignedRemainder are imported and built. Their lookup and
  `assertLookupOne` proofs establish successful execution without new premises;
  AssertEQ also handles the nonzero spoil immediate.
  The count was then 74 of 88 row kinds with steps, plus two proved unreachable; it is now 77 of 88.
  The new axiom audits contain no native decision axiom or `sorryAx`.
  VirtualHostIO was then open and now has a local step (`Layer5/HostCallRegisterFrame.lean`).
  The modeled initial state and pass 1 of Jolt's tracer use live mode, whereas only the tracer's chunk workers replay.
  Live advice-write calls can extend the tape, and marker/print calls can fail on invalid events.
  The replay no-op branch is therefore insufficient for the soundness execution step.
  Ari has since added
  `HostCallsSucceed` to the temporary restrictions; it compiles in the root
  build and requires successful execution of attempted host calls.
  `host_call_exec_sail_frame` derives that success and preserves Sail registers
  and RAM while allowing advice-tape changes. The
  separate register-increment obligation for a HostIO row with nonzero `rd`
  and the model's disabled pointer-overflow check remain under review. Details
  and pinned Rust ranges are in `methods/soundness.md`.
- **Termination restriction and HostIO destination, 2026-10-16.** Ari added
  `TerminationThenStall` to the temporary restrictions. It is imported by
  `Assumptions.lean` and the root build passes. Its application lemmas rule out
  a later termination load and JALR; a later JAL must have offset zero, and
  `termination_next_jal_stalls` proves that executing it sets `nextPC` to its
  own address.
  The Layer 7 last-row argument is proved (`Layer7/LastJump.lean`, `Layer7/TerminationStore.lean`); device agreement remains open.
  At pin `8bbb2357`, Rust accepts a HostIO source instruction with nonzero
  `rd` (`image/decode.rs:196-208`, `format_i.rs:7-24`). Even when the source
  uses `rd = x0`, `expand/materialize.rs:79-90` rewrites its side-effecting
  destination to a temporary virtual register. Thus a source-level `rd = x0`
  clause alone does not force the expanded HostIO row's `RdInc` to zero. Ari
  approved a temporary source `HostCallRdZero` restriction to exclude the
  architectural-destination case. The pinned allocator gives ordinary
  expansion temps 40–47, disjoint from LR/SC reservations 32 and 33.
  `ExpansionFacts.expand_temps_ok` checks every source expansion: a temporary
  is written before its first read in that expansion, counting a row's read
  before its write. The global register-agreement induction must still use
  this fact to drop the rewritten HostIO temporary at the source boundary.
- **Layer 6 bytecode PC bridge, 2026-10-15.** `Layer6/BytecodePC.lean` is
  imported and built. It identifies the entry slot, proves an interior row's
  selected predecessor from the sequence and expanded-PC constraints when
  that predecessor is a real row, and connects a selected register shift to
  its expansion's mask producer. Its five public lemmas use only Lean's three
  standard axioms.
  Padding persistence (`padding_persists`, `padding_from`) is now proved in this file, and the padding suffix is proved in Layer 7.
  The execution-prefix state link, entry-start fact, source-boundary transition and full dispatcher remain open; no main-theorem premise changed.
  The validation and scope are recorded in `methods/soundness.md`.
- **ADDI soundness step.** `Layer5/AddImmediate.lean` now proves a selected
  ADDI row executes to the concrete destination-write state, writes the
  wrapped sum constrained by the lookup, and preserves register agreement
  whenever a next table column exists. Operands, metadata and write success
  are derived from bytecode validity, the constraints and current register
  agreement. `Layer5/RegisterWrite.lean` proves canonical destination writes
  succeed. Neither lemma adds a soundness premise. The ADDI result's axiom
  list contains the standard three plus the allowed uninterpreted Sail
  constant `sys_enable_experimental_extensions`; the write helper uses only
  the standard three. Other families, RAM agreement and control flow remain
  open.
- **To do.** The [migration to the new pin](../methods/model_update.md) is complete.
  Existing proof gaps and native-proof repairs remain open. Fix comments that cite
  `/Users/ari.biswas/...` paths. Drop the unused `ramFits`, `traceFits` and
  `bytecodeDomain` arguments. `constraints.md` still calls (16) a statement.
