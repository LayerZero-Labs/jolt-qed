# Doc refresh check, 2026-11-02

Date: 2026-11-02.
Jolt: migration target `c6703570` (local `origin/main` of the fork `abiswas3/jolt`); recorded pin `5def437f`.
Upstream [a16z/jolt#2132](https://github.com/a16z/jolt/pull/2132) is merge commit `629b7d95` (2026-10-27).
Lean: HEAD `7096dca`, plus the uncommitted working tree.

Scope: check the four documents rewritten by Agent B against the restored originals and against the code, then restore the originals and make targeted updates.
No Lean file, statement, assumption, restriction or proof was changed.

## Restoration

- `methods/soundness.md` (1144 lines), `JoltConstraints/model_review.md` (142), `JoltConstraints/constraints.md` (487), `methods/constraint_proving.md` (187).
  Source: transcript-recovered copies `scratchpad/recovered_{soundness,model_review,constraints,constraint_proving}_pre_B.md`, with one trailing blank line removed.
- Git has no copy of these pre-refresh versions; the HEAD versions are older (soundness 2648 lines).
- B's versions are kept in `scratchpad/doc_snapshot_173426/`, identical to the working tree at snapshot time.

## What B's rewrite removed

- `soundness.md`: headings 30 to 5; dated decision lines 29 to 1.
  Removed Layers 0 to 8, Key ideas, the workflow, the approval history, Questions for a16z, and the history of remaining work.
- `model_review.md`: removed Upstream issues, Device memory, the Assumptions table with approval rationale, Gaps in our model, the Cleanup list, and To do.
- `constraints.md`: headings 19 to 6.
  Removed the 62 checklist items with their links and statuses, the equation text for (01) to (62), Notation, and the Rust links.
- `constraint_proving.md`: removed the four-step workflow, the row and trace fact tables, the premise rules, counterexample guidance, and the worked example for (01).

## Checks of B's new claims

| Claim | Evidence | Result |
|---|---|---|
| `lake build JoltBytecode` exit 0, 8459 jobs | `scratchpad/audit_root.log`, 16:50:33: "Build completed successfully (8459 jobs)" | Verified from the log; exit code not captured separately |
| Seven bytecode `sorry`s | grep over `JoltBytecode` | Verified: `RiscvInstruction.lean:805, 807, 813, 815, 817, 819` and `Mret.lean:162`; at `7096dca`, 6 and 1 |
| `Basic.lean` builds after the `store_rule _ _` fix | `scratchpad/basic_build2.log`, 14:36:00, after the edit at 14:35:49 | Verified |
| Plain `lake build` fails, 8835 jobs | `lakefile.toml` lists `JoltConstraints` in `defaultTargets`; `register_encoding.lean:54` uses `.VirtualAlignAddr` | Partly verified: the default target and the removed reference are confirmed; the exit code and job count were not re-run |
| `c6703570` is `origin/main`; `629b7d95` is #2132, 2026-10-27 | `git rev-parse`, `git log` | Verified |
| Remote is the fork `abiswas3/jolt` | `git remote -v` | Verified |
| Target has seven instruction flags, `RightOperandIsRdWriteValue` after `IsNoop` | `crates/jolt-riscv/src/flags.rs`, `InstructionFlags` | Verified; the commit that added the flag was not identified |
| Lean has six flags and three retired table constructors | `JoltConstraints/witness.lean:21-24`; `LookupTableKind` | Verified |
| Target has 55 tables; `AddressOffsetB/H/W` at indices 52, 53, 54 | `crates/jolt-lookup-tables/src/tables/mod.rs`, `LookupTableKind` | Verified |
| `AddressOffset` output is `index & (8 - WIDTH)` | `crates/jolt-lookup-tables/src/tables/address_offset.rs:25` | Verified |
| R1CS row 0 right side is `Rs1Value + Imm - LookupOutput` | `crates/jolt-claims/src/protocols/composed/r1cs/rv64.rs`, row 0 comment | Verified |
| Jolt R1CS row 10 is `RightLookupEqRightInputOtherwise`, Lean (11) | Zero-based position in the row-name array | Verified |
| (33) gains `RightOperandIsRdWriteValue * RdWriteValue` | `input_virtualization.rs` | Verified |
| Stage-3 gamma powers: flag 7, then `VirtualInstruction` 8 and `IsFirstInSequence` 9 | `bytecode.rs`, flag combination list | Verified |
| Floor-row and LD flag assignments | `instructions/virt/{load,store}_b.rs`, `instructions/i/ld.rs`, `instructions/virt/shift_data_b.rs` | Verified |
| Lookup-entry lines 317, 780, 795 and dispatch 891, 892, 924 | grep, `LookupEntryProofHelpers.lean` | Verified |
| Four constraint-side uses of `jolt_virtual_align_addr_value64` | grep | Verified: `Values.lean:286` (definition), `LookupEntryProofHelpers.lean:321`, `AddressMasks.lean:32, 124`, `lookup_output.lean:81` |
| Seven classifier call sites in six files | grep | Verified |
| `decide +kernel` at `DeviceMemoryObstruction.lean:52, 59` | grep | Verified |
| Raised `maxHeartbeats` at `LookupWriteProofHelpers.lean:4` and `TracePCProofHelpers.lean:7` | grep | Verified: 1000000 and 400000 |
| No executable `bv_decide`; one comment at `Soundness/Layer4/Interleave.lean:17` | grep | Verified |
| No `sorry` in `JoltConstraints/Soundness/` | grep | Verified |
| `TracerAddressChecks` covers LD and SD, `True` otherwise; comment at line 82 is stale | `Soundness/Layer5/MemoryAccessRestriction.lean:82, 93-97` | Verified |
| `TraceRow.ram_address` handles only LD and SD | `trace.lean:50-55` | Verified |
| Floor-row Rust sources exist at `c6703570` | `git cat-file`: `tracer/src/instruction/floor_access.rs`, `crates/jolt-program/src/expand/memory/shared.rs` | Verified |
| SB program has six rows | `ExpansionsAutomated.lean`, `sbProgramAuto` | Verified |
| Floor-row address rule: recorded address `ea - (ea & offset_mask)` asserted a multiple of 8; accessed doubleword `ea & !7` | `tracer/src/instruction/floor_access.rs`, `addresses`, lines 59–75 at `c6703570` | Verified |
| Named soundness declarations and files exist | grep | Verified: `soundness_reconstruct_trace`, `soundness_matches_outputs`, `soundness_prover_accepts`, `soundness_spoil_asserts_pass`, `untrustedAnswerLanguage_implies_inLanguage`, `advice_tape_irrelevant`, `soundness_stopping`, `soundness_termination_store_exists`; `TopLevel.lean`, `Layer6/ExecutionPrefix.lean`, `Layer7/TapeRebuild.lean`, `advice_inputs.lean` |
| Row 11 formula subtracts `RightInstructionInput` with no second `RdWriteValue` term | Not checked | Left out of the docs |
| `SourceInstruction` composition list in B's soundness plan | Not checked | Dropped; the original wording stays |
| "Non-interleaved index" wording for `materialize_entry` | Not checked | Not used |
| Per-item "Body present" statuses for the 62 items | Not checked one by one | Dropped; each checklist item links to its proof |

## Corrections to B's wording

- Removed the unverified `SourceInstruction` sentence.
- Pointed links at headings that exist in the restored files.
  B's `model_review.md#assumptions-in-the-source` does not exist in the restored file, whose heading is `## Assumptions`.
- Repaired the `NextPCFrame` link in `constraint_proving.md`.
  The file is now `JoltConstraints/nextpc_frame.lean`; the old path appears in git history only.

## Historical claims kept as dated history

- The 2026-10-23 soundness axiom check at `7096dca` (8,832 jobs) is kept, labelled with its commit and date.
- The 62-equation and 55-table check at `5def437f` (2026-10-29) is kept, not re-run.

## Outside the four documents

- Tracked files under `methods/` are deleted in the working tree: `advice_fix_report.md`, `bv-decide-report.md`, `layer6/` (17 files), `layer7/` (2 files), `model_update.md`, `review_completeness_and_soundness.md`, `pin_update_report.md`, and `step_c_closing_report.md`.
  These deletions were already in `git status` at the start of this session, before B's work, so B did not cause them.
  Not restored here.
  Ari to decide whether they stay deleted under the `AGENTS.md` rule for removing plans and reports.
- `AGENTS.md` and `README.md` show as modified; this check did not touch either.

## Statement and proof impact

- Lean files changed in this check: none.
- Statements changed: none.
- Hypotheses added: none.
- `bv_decide` uses added: none.
- Proofs timed: none; no proof was run.

## Decisions for Ari

1. Extend `TracerAddressChecks` to floor-row accesses (`constraints.md`, item 10).
   Approved by Ari on 2026-11-02 as a temporary premise; it is added in the migration, not in this check.
   The rule applied: ask only when a main theorem statement changes or an assumption is added.
   The classifier theorems are helper statements, so the migration may generalize them without asking (`model_review.md`, "Classifier call sites").
3. Retire the three alignment lookup-entry theorems (`constraints.md`, item 6). Approved, not executed.
4. Keep or restore the deleted `methods/` files.
5. Keep the pin at `5def437f`; the migration target stays `c6703570`.
