# Provenance and trust checks: T7

Date: 2026-11-11, updated 2026-11-12 after the Codex review (section "Review fixes") and with the decisions in section "Decisions".
This report describes four checks that Track T phase T7 adds (`docs/inline-precompiles.md`, section 7).

1. `provenance.toml` names the one Jolt revision the project is checked against and, for every Lean file under `JoltBytecode/` and `JoltConstraints/`, the Jolt files it models.
   `scripts/check-provenance.py` checks the manifest and fails on any new local path, Jolt fork citation or unrecorded Jolt revision.
2. `scripts/check_hygiene.py` scans the Lean sources for `sorry`, trusted tactics, raised limits and axioms against `scripts/hygiene-baseline.toml`.
3. `JoltAudit/Axioms.lean` checks during the build that nine headline theorems use only `propext`, `Classical.choice` and `Quot.sound`.
4. `ci/comparator/` re-checks six of those theorems with Lean's built-in `lake comparator`.
   Its CI job does not block until it has passed once.

The first three pass locally, and `scripts/tests/` holds 32 regression tests for the two Python checkers.
The built-in `lake comparator` accepts the six theorems on macOS without its sandbox; the sandboxed run is the CI job.

## Revisions

jolt-qed: branch `inline/t7-provenance` on top of `b648846`.
Toolchain: `leanprover/lean4:v4.35.0`.

Jolt pin: a16z/jolt#2384 at `580084fcfad4788ebf48413a92dd640ca090c45f` (`580084fcf`), the revision the T1 expansion-parity, T2 decoder-sweep and T4 lookup-tables jobs check (section "Decisions").
`README.md` and `methods/soundness.md` still record `c97e93004fbf804409f0374fe8457c8f1562ce71` (`c97e9300`), the merge of a16z/jolt#2250, as the project pin; `provenance.toml` says so in its pin note.

The provenance job also compares against the earlier Track T pin, a16z/jolt `main` at `a6b6dc7177ec5ea5a3c60bd5cea4409c07ca6dc5` (`a6b6dc717`), and reports without failing the `models` paths missing there.
`a6b6dc717` is an ancestor of `580084fcf`.

## The provenance manifest

`provenance.toml` has one `[jolt]` table with the pin and one `[[file]]` entry for each of the 633 Lean files under `JoltBytecode/` and `JoltConstraints/`.
Each entry has `lean`, `models` (the Jolt paths the file transcribes or relies on), an optional `checked` revision and an optional `note`.

I derived `models` and `checked` from each file's own citations.
`checked` is the published a16z/jolt revision the file names most often, with the later commit on a tie.
`models` are the Jolt files the file cites that exist at `checked`.
A citation counts with brace lists expanded (`virt/{load,store}_{b,h,w}.rs` is six files) and with a bare file name read in the directory of the `.rs` path cited just before it (`tracer/src/instruction/div.rs, divu.rs, rem.rs`).
A GitHub URL prefix or a local checkout prefix up to `/jolt/` is dropped.
A path the file cites that is missing at `checked` goes into the note instead.
The review found 13 cited files missing from `models` this way (the div/rem family and `scd.rs`, `jalr.rs` in `honest_trace.lean`, three witness files in `RamAddrEqRs1PlusImmMinusLookupIfLoadStore.lean`, `shift_data_h.rs` in `RegistersReadProofHelpers.lean`); they are now in `models`, and the check enforces the rule.

| Entries | Count |
|---------|-------|
| All entries | 633 |
| With `models` | 262 |
| With `models` and a `checked` revision | 174 |
| With `models` and no `checked` revision | 88 |
| Without `models` (no Jolt counterpart) | 371 |

The 88 entries without a `checked` revision cite Jolt paths but name no published a16z/jolt revision.
Most are `JoltConstraints/Constraints/` files that cite `abiswas3/jolt/tree/main`.
`JoltBytecode/Decode/Agreement.lean` names only `b65455e6d`, which is not on GitHub.

| `checked` revision | Files |
|--------------------|-------|
| `5def437f21a0006e13c063a03f0b5a7c9b93cd6f` | 60 |
| `c6703570588e88033b8722bd4dec47c7f46f3b16` | 56 |
| `8bbb2357890928d8f83b00ca542879077c4d3d28` | 49 |
| `c336a6da706d0a0d11c3489c7aef71ee80c2e370` | 3 |
| `0249591a293aa40dc4ebba92818e1367c66ea633` | 2 |
| `c97e93004fbf804409f0374fe8457c8f1562ce71` | 2 |
| `e012da54c3bb26a6436b5ca74e86c19bb39695ad` | 1 |
| `8e536f199735ac8187156aa589ed1387722a079a` | 1 |

Every `checked` revision is reachable from an a16z/jolt branch.
`c336a6da7` is reachable only from `feat/zicsr-remaining-forms` (a16z/jolt#2384).
`JoltBytecode/JoltISA/Expansions/System.lean` gets `c336a6da7`, because the revision it names most, `a86ec3716`, is not published.

`[[other_revision]]` lists commits of other repositories that the scanned files cite: three jolt-qed commits, the Sail RISC-V fork and compiler commits of `sail-import/PROVENANCE.toml`, a riscv-isa-manual commit and an EthLib commit.

### What the check enforces

`scripts/check-provenance.py` needs only Python 3.11.
Without `--jolt-dir`, it checks the following.

- The manifest has one 40-digit pin.
- Every Lean file under `JoltBytecode/` and `JoltConstraints/` has exactly one entry, every entry names an existing Lean file under those roots, and no entry has a key other than `lean`, `models`, `checked` and `note`.
- Every `checked` revision has 40 hex digits and comes with `models`.
- The scanned files have no local path, Jolt fork citation or Jolt revision beyond the `[[known]]` baseline.
  The scan covers `*.lean` and `*.md` under `JoltBytecode/`, `JoltConstraints/` and `docs/`, plus `README.md` and `provenance.toml` (without the `text` lines of its own `[[known]]` entries).
  A local path is `/Users/…`, `/home/…`, `~/…` or `/private/tmp/…`, and its baseline entry quotes the whole path.
  A fork citation is a `github.com/<owner>/jolt` link with an owner other than `a16z`, and its baseline entry quotes the whole URL.
  A revision is a token of 7 to 40 hex digits with at least one digit and one letter.
  An all-digit or all-letter token counts as a revision when a citation word precedes it (`commit`, `revision`, `rev`, `pin`, `sha`, `hash`, `checked`, or `@`) or when it is the revision of a repository-qualified citation.
  A repository-qualified citation (`github.com/<owner>/<repo>/blob|tree|commit|commits|compare/<rev>` or `<owner>/<repo>@<rev>`) must name the pin or the file's `checked` revision when the repository is a Jolt repository, and an `[[other_revision]]` of that same repository otherwise.
  An unqualified token may match the pin, the file's own `checked` revision or any `[[other_revision]]`, by prefix.
- Every `models` path of an entry without a `checked` revision is recorded as an `unchecked-model` entry in `[[known]]`, so a new unchecked path fails.
- Every `[[known]]` count matches the tree exactly.
  A fixed violation therefore fails the check until its entry is lowered or deleted, and replacing one baselined citation with another fails twice: the old entry goes stale and the new citation is unrecorded.

With `--jolt-dir <a16z/jolt clone>`, it also checks the following.

- The pin and every `checked` revision resolve.
- Every `models` path exists at its `checked` revision.
- Every Jolt file a Lean file cites (as section "The provenance manifest" defines) that exists at its `checked` revision is in its `models`.
- Every `models` path of an entry without a `checked` revision exists at the pin.

It reads only trees, and a shallow blobless fetch of each revision is enough.
It then reports, without failing, the `models` paths missing at the pin and at `--compare`.

### Baseline

The baseline records 412 existing violations in 137 files, in 316 `[[known]]` entries.

| Kind | Occurrences | Files | Where |
|------|-------------|-------|-------|
| Local path (`/Users/…`) | 47 | 32 | 6 in `JoltBytecode/`, 26 in `JoltConstraints/` |
| Fork citation (`abiswas3/jolt`) | 60 | 50 | 2 in `JoltBytecode/`, 48 in `JoltConstraints/` |
| Other Jolt revision | 164 | 43 | 3 in `JoltBytecode/`, 36 in `JoltConstraints/`, 3 in `docs/`, `README.md` |
| `models` path with no `checked` revision | 141 | 88 | the 88 entries above |

Moving the pin to `580084fcf` added the two citations of the old pin `a6b6dc717` in `docs/inline-precompiles.md`, which that document uses for its code references.
The table below lists the first three kinds; `provenance.toml` lists every entry, including the exact citation text.

No file contains a `~/` path; every local path starts with `/Users/`.
The most frequent other revisions are `8bbb2357` (42), `5def437f` (41), `0249591a` (30), `c6703570` (13) and `c97e9300` (11).
They occur in files whose `checked` revision is a different one.

<details>
<summary>Baseline by file</summary>

| File | Local paths | Fork citations | Other revisions |
|------|-------------|----------------|-----------------|
| `JoltBytecode/Assumptions.lean` | 1 |  |  |
| `JoltBytecode/Decode/Agreement.lean` |  |  | `b65455e6d` ×2 |
| `JoltBytecode/JoltISA/AdviceTape.lean` | 2 |  |  |
| `JoltBytecode/JoltISA/Expansions/System.lean` |  |  | `a86ec3716` ×6 |
| `JoltBytecode/JoltISA/Instruction.lean` | 2 | 5 | `5def437f` ×2 |
| `JoltBytecode/JoltISA/Values.lean` | 3 | 1 |  |
| `JoltBytecode/JoltISA/semantic_helpers.lean` | 3 |  |  |
| `JoltBytecode/RiscvInstruction.lean` | 2 |  |  |
| `JoltConstraints/Completeness/BytecodeRaAtEntryEqOne.lean` |  |  | `3cb4e2436` |
| `JoltConstraints/Completeness/Helpers/VerifierSizes.lean` |  |  | `c97e9300` ×3 |
| `JoltConstraints/Constraints/AssertLookupOne.lean` |  | 1 |  |
| `JoltConstraints/Constraints/BytecodeRaChunkBooleanity.lean` |  | 1 |  |
| `JoltConstraints/Constraints/BytecodeRaChunkHammingWeight.lean` |  | 1 |  |
| `JoltConstraints/Constraints/BytecodeReadData.lean` |  | 4 |  |
| `JoltConstraints/Constraints/BytecodeReadSelectors.lean` |  |  | `5def437f2` ×2 |
| `JoltConstraints/Constraints/InstructionRaChunkBooleanity.lean` |  | 1 |  |
| `JoltConstraints/Constraints/InstructionRaChunkHammingWeight.lean` |  | 1 |  |
| `JoltConstraints/Constraints/InstructionRaEqChunkProduct.lean` |  | 1 |  |
| `JoltConstraints/Constraints/LeftInstructionInputEqSelection.lean` |  | 1 |  |
| `JoltConstraints/Constraints/LeftLookupEqLeftInputOtherwise.lean` |  | 1 |  |
| `JoltConstraints/Constraints/LeftLookupOperandEqInstructionRaf.lean` |  | 1 |  |
| `JoltConstraints/Constraints/LeftLookupZeroIfAddSubMul.lean` |  | 1 |  |
| `JoltConstraints/Constraints/LookupOperandData.lean` |  | 1 |  |
| `JoltConstraints/Constraints/MemoryLayout.lean` |  |  | `754fc8821` |
| `JoltConstraints/Constraints/MustStartSequenceFromBeginning.lean` |  | 1 |  |
| `JoltConstraints/Constraints/NextPCEqPCPlusOneIfInline.lean` |  | 1 |  |
| `JoltConstraints/Constraints/NextUnexpandedPCEqLookupIfShouldJump.lean` |  | 1 |  |
| `JoltConstraints/Constraints/NextUnexpandedPCEqPCPlusImmIfShouldBranch.lean` |  | 1 |  |
| `JoltConstraints/Constraints/NextUnexpandedPCUpdateOtherwise.lean` |  | 1 |  |
| `JoltConstraints/Constraints/RamAddrEqZeroIfNotLoadStore.lean` |  | 1 |  |
| `JoltConstraints/Constraints/RamAddressEqRamRaf.lean` |  | 1 |  |
| `JoltConstraints/Constraints/RamHammingWeightBooleanity.lean` |  | 1 |  |
| `JoltConstraints/Constraints/RamOutputEqPublicIo.lean` |  | 1 |  |
| `JoltConstraints/Constraints/RamRaChunkBooleanity.lean` |  | 1 |  |
| `JoltConstraints/Constraints/RamRaChunkHammingWeight.lean` |  | 1 |  |
| `JoltConstraints/Constraints/RamRaEqChunkProduct.lean` |  | 1 |  |
| `JoltConstraints/Constraints/RamReadData.lean` |  | 4 |  |
| `JoltConstraints/Constraints/RamReadEqRamWriteIfLoad.lean` |  | 1 |  |
| `JoltConstraints/Constraints/RamReadEqRdWriteIfLoad.lean` |  | 1 |  |
| `JoltConstraints/Constraints/RamReadValueEqRamRead.lean` |  | 1 |  |
| `JoltConstraints/Constraints/RamValEqInitialPlusPrefixRamInc.lean` |  | 1 |  |
| `JoltConstraints/Constraints/RamValFinalEqInitialPlusRamInc.lean` |  | 1 |  |
| `JoltConstraints/Constraints/RamWriteValueEqRamReadWrite.lean` |  | 1 |  |
| `JoltConstraints/Constraints/RdWriteEqLookupIfWriteLookupToRd.lean` |  | 1 |  |
| `JoltConstraints/Constraints/RdWriteEqPCPlusConstIfJump.lean` |  | 1 |  |
| `JoltConstraints/Constraints/RdWriteValueEqRegistersReadWrite.lean` |  | 1 |  |
| `JoltConstraints/Constraints/RegistersValEqPrefixRdInc.lean` |  | 1 |  |
| `JoltConstraints/Constraints/RightLookupAdd.lean` |  | 1 |  |
| `JoltConstraints/Constraints/RightLookupEqProductIfMul.lean` |  | 1 |  |
| `JoltConstraints/Constraints/RightLookupEqRightInputOtherwise.lean` |  | 1 |  |
| `JoltConstraints/Constraints/RightLookupOperandEqInstructionRaf.lean` |  | 1 |  |
| `JoltConstraints/Constraints/RightLookupSub.lean` |  | 1 |  |
| `JoltConstraints/Constraints/Rs1ValueEqRegistersRead.lean` |  | 1 |  |
| `JoltConstraints/Constraints/Rs2EqRamWriteIfStore.lean` |  | 1 |  |
| `JoltConstraints/Constraints/Rs2ValueEqRegistersRead.lean` |  | 1 |  |
| `JoltConstraints/Constraints/ShouldBranchEqLookupOutputMulBranch.lean` |  | 1 |  |
| `JoltConstraints/Constraints/ShouldJumpEqJumpMulNotNextIsNoop.lean` |  | 1 |  |
| `JoltConstraints/Soundness/Layer4/Interleave.lean` |  |  | `8bbb23578` |
| `JoltConstraints/Soundness/Layer5/AssertionsBinary.lean` |  |  | `8bbb2357` |
| `JoltConstraints/Soundness/Layer5/DeviceMemory.lean` |  |  | `c6703570` ×3 |
| `JoltConstraints/Soundness/Layer5/MemoryAccessRestriction.lean` |  |  | `0249591a`, `8bbb2357` |
| `JoltConstraints/Soundness/Layer5/RamStore.lean` |  |  | `8bbb2357` |
| `JoltConstraints/Soundness/Layer5/StoreDoubleword.lean` |  |  | `5def437f` |
| `JoltConstraints/Soundness/Layer5/TapeTrace.lean` |  |  | `5def437f` |
| `JoltConstraints/Soundness/Layer5/VirtualBinary.lean` |  |  | `8bbb2357` |
| `JoltConstraints/Soundness/Layer6/RowStepMemory.lean` |  |  | `5def437f` ×2 |
| `JoltConstraints/Soundness/Layer7/LastJump.lean` |  |  | `5def437f` ×2 |
| `JoltConstraints/Soundness/Layer7/StallSuffix.lean` |  |  | `0249591a` ×19, `5def437f` ×15 |
| `JoltConstraints/Soundness/Layer7/Stopping.lean` |  |  | `0249591a` |
| `JoltConstraints/Soundness/Layer7/TapeRebuild.lean` |  |  | `0249591a`, `8bbb2357` |
| `JoltConstraints/Soundness/Layer7/TerminationStore.lean` |  |  | `0249591a` ×2 |
| `JoltConstraints/WholeRun/Blocks.lean` |  |  | `0249591a` |
| `JoltConstraints/constraints.md` |  |  | `5def437f` ×2, `5def437f2` ×2, `8bbb2357` ×3, `8bbb23578` ×26, `c6703570` ×4, `c97e9300` |
| `JoltConstraints/execution_conditions.lean` |  |  | `0249591a` |
| `JoltConstraints/expansion_facts.lean` |  |  | `5def437f` ×3 |
| `JoltConstraints/expansion_temp_liveness.lean` |  |  | `8bbb2357` |
| `JoltConstraints/honest_trace.lean` |  |  | `0249591a` ×3, `0dad0d9e`, `8bbb2357`, `8bbb23578` |
| `JoltConstraints/layout_facts.lean` |  |  | `5def437f` |
| `JoltConstraints/lookup_table.lean` |  | 1 |  |
| `JoltConstraints/metadata.lean` | 1 |  | `8bbb2357` |
| `JoltConstraints/model_review.md` | 1 |  | `00508a09`, `5def437f` ×3, `c6703570` ×2, `c97e9300`, `c97e93004` ×2 |
| `JoltConstraints/program.lean` |  |  | `0249591a`, `5def437f` ×2 |
| `JoltConstraints/prover_config.lean` |  |  | `c97e9300` |
| `JoltConstraints/prover_config_facts.lean` |  |  | `5def437f`, `c6703570` ×3 |
| `JoltConstraints/register_encoding.lean` |  | 1 |  |
| `JoltConstraints/trace.lean` |  |  | `5def437f2`, `8bbb2357` |
| `JoltConstraints/verifier_sizes.lean` |  |  | `c97e9300` |
| `JoltConstraints/witness.lean` | 1 |  | `8bbb2357` |
| `JoltConstraints/witness_domain.lean` | 1 |  |  |
| `JoltConstraints/witness_helpers/address_chunk.lean` | 2 |  |  |
| `JoltConstraints/witness_helpers/branch.lean` | 1 |  |  |
| `JoltConstraints/witness_helpers/bytecode_ra_chunk.lean` | 1 |  |  |
| `JoltConstraints/witness_helpers/imm.lean` | 1 |  |  |
| `JoltConstraints/witness_helpers/instruction_flags.lean` | 1 |  |  |
| `JoltConstraints/witness_helpers/instruction_ra.lean` | 1 |  |  |
| `JoltConstraints/witness_helpers/instruction_ra_chunk.lean` | 1 |  |  |
| `JoltConstraints/witness_helpers/instruction_raf_flag.lean` | 1 |  |  |
| `JoltConstraints/witness_helpers/left_instruction_input.lean` | 1 |  |  |
| `JoltConstraints/witness_helpers/left_lookup_operand.lean` | 1 |  |  |
| `JoltConstraints/witness_helpers/lookup_index.lean` | 4 |  | `5def437f` |
| `JoltConstraints/witness_helpers/lookup_output.lean` | 1 |  |  |
| `JoltConstraints/witness_helpers/lookup_table_flag.lean` | 1 |  |  |
| `JoltConstraints/witness_helpers/op_flags.lean` | 1 | 1 |  |
| `JoltConstraints/witness_helpers/product.lean` | 1 |  |  |
| `JoltConstraints/witness_helpers/ram_address.lean` |  |  | `8bbb23578` |
| `JoltConstraints/witness_helpers/ram_hamming_weight.lean` | 1 |  |  |
| `JoltConstraints/witness_helpers/ram_ra.lean` | 1 |  |  |
| `JoltConstraints/witness_helpers/ram_ra_chunk.lean` | 2 |  |  |
| `JoltConstraints/witness_helpers/ram_state.lean` | 4 |  |  |
| `JoltConstraints/witness_helpers/ram_val_final.lean` | 1 |  |  |
| `JoltConstraints/witness_helpers/register_address.lean` | 1 |  |  |
| `JoltConstraints/witness_helpers/unexpanded_pc.lean` | 1 |  |  |
| `JoltConstraints/witness_params.lean` |  |  | `c97e9300` |
| `README.md` |  |  | `c336a6da7`, `c97e9300` |
| `docs/inline-precompiles.md` |  |  | `4e55c9a5f` ×2, `629b7d959`, `70e00da09` ×2, `a6b6dc717` ×2, `db9679295` ×2 |
| `docs/riscv-alignment.md` |  |  | `9407f93f` ×2, `c336a6da7` ×2, `c6703570` |
| `docs/whole-run-theorem.md` |  |  | `c336a6da7` |

</details>

### Result

`python3 scripts/check-provenance.py` passes: 633 entries, 412 baseline violations, no new ones.
With `--jolt-dir` on a full a16z/jolt clone and `--compare a6b6dc717`, it passes and reports these notes.

- No `models` path is missing at the pin `580084fcf`.
- Three `models` paths of `JoltBytecode/JoltISA/Expansions/System.lean` are missing at `a6b6dc717`: `crates/jolt-program/src/expand/control_flow/csr.rs`, `csr_immediate.rs` and `csrrc.rs`.
  #2384 adds them.
- Three revisions in the files are not a16z/jolt commits.
  `b65455e6d` (`JoltBytecode/Decode/Agreement.lean`) and `a86ec3716` (`System.lean`) exist only in local Jolt clones, and GitHub's API returns 422 for both.
  `3cb4e24361ae2006e9713ae65d58a3fa51fd0518` (`JoltConstraints/Completeness/BytecodeRaAtEntryEqOne.lean`) is in no a16z/jolt clone I have.
- 88 entries name `models` but no `checked` revision.

The same run on a shallow blobless fetch of the pin, the eight `checked` revisions and `a6b6dc717` passes with the same notes, except the one on revisions that are not commits, which the check skips in a shallow clone.
That fetch, the one CI does, took 7 seconds and 1.4 MB.

Some files cite Jolt paths that no a16z/jolt commit contains: `crates/jolt-trace/src/preprocess/bytecode.rs`, `crates/jolt-trace/src/preprocess/public_io.rs` and `crates/jolt-riscv/src/instructions/b/beq.rs`.
The notes of their entries say so.
Other notes record citation drift, for example `floor_access.rs`, which is missing at `5def437f` and `e012da54` and present at `c6703570` and at the pin.

I checked that the check fails on each of these: a new Markdown file under `docs/` with a local path, a fork citation and an unknown revision; a baseline count one above the tree; a Lean file with no entry; and a `models` path that does not exist at its `checked` revision.
`scripts/tests/test_check_provenance.py` covers each review finding (section "Review fixes"), and the `provenance` CI job runs it.

## The hygiene scan

`scripts/check_hygiene.py` blanks comments, docstrings and the text of string, raw-string and character literals, then counts these tokens: `sorry`, `admit`, `native_decide`, `decide +kernel` (also `kernel := true`), `bv_decide`, `set_option maxHeartbeats`, `maxRecDepth`, `synthInstance.*` options and the `axiom` keyword anywhere in code.
A quoted identifier (`«…»`) is one opaque name, so `def «--»` does not start a comment.
A text scan cannot tell whether Lean parses a string literal as interpolated: `s!"…"` is, and so is `throwError "…"` or any syntax that takes `interpolatedStr`.
The scan therefore reads each file twice, once with the `{…}` parts of every literal blanked and once with them kept as code, and counts an occurrence that either reading finds.
Each reading alone can be misled (a plain `"{"` misleads the second, a nested string inside `{…}` misleads the first), but a token has to hide from both to escape.
The scan is a guard against accidents and not the trust boundary: the axiom gate and the comparator decide whether a headline theorem uses `sorryAx` or another axiom.
Each root has its own policy, and each root module (for example `JoltBytecode.lean`) is scanned with its root.

| Root | Policy | Occurrences |
|------|--------|-------------|
| `JoltBytecode/` | Zero tolerance | 0 |
| `JoltConstraints/` | `[[known]]` baseline | 7 |
| `JoltTests/` | Zero tolerance | 0 |
| `LeanRV64D/` | `[[generated]]` baseline | 77 |

The `[[known]]` baseline of `JoltConstraints/` has 5 `sorry` and 2 `decide +kernel`.

- One `sorry` in each of these files under `JoltConstraints/Completeness/`: `RamAddrEqRs1PlusImmMinusLookupIfLoadStore.lean`, `RamValEqInitialPlusPrefixRamInc.lean`, `RamValFinalEqInitialPlusRamInc.lean`, `RightLookupAdd.lean` and `RightLookupEqRightInputOtherwise.lean`.
- Two `decide +kernel` in `JoltConstraints/Soundness/Layer5/DeviceMemoryObstruction.lean` (lines 54 and 61).

The `[[generated]]` baseline of `LeanRV64D/` has 67 `axiom` (the `riscv_f*` floating-point axioms in `RiscvExtras.lean`), 3 `set_option maxHeartbeats` and 7 `maxRecDepth`.

| File | Token | Count |
|------|-------|-------|
| `LeanRV64D/RiscvExtras.lean` | `axiom` | 67 |
| `LeanRV64D/InstsEnd.lean` | `maxHeartbeats` | 2 |
| `LeanRV64D/InstsEnd.lean` | `maxRecDepth` | 4 |
| `LeanRV64D/RvfiDii.lean` | `maxHeartbeats` | 1 |
| `LeanRV64D/SysControl.lean` | `maxRecDepth` | 1 |
| `LeanRV64D/ZicsrInsts.lean` | `maxRecDepth` | 2 |

`python3 scripts/check_hygiene.py` passes on 778 files.
A test file with a `sorry`, a `set_option maxHeartbeats` and an `axiom` makes it fail, and the same tokens inside a comment, a docstring or a string do not.
`scripts/tests/test_check_hygiene.py` covers the review's bypasses (an interpolated `sorry`, `def «--» : Nat := by sorry`, `set_option … in axiom`) and the cases that must keep passing.
Like `scripts/check-provenance.py`, it fails when a baseline count no longer matches.

## The axiom gate

`JoltAudit/Axioms.lean` runs `Lean.collectAxioms`, the routine behind `#print axioms`, on each gated theorem during `lake build JoltAudit`.
It fails the build if a theorem depends on an axiom other than `propext`, `Classical.choice` and `Quot.sound`, and it logs each theorem's axioms otherwise.
The `build` job of `lean.yml` runs `lake build JoltAudit` after the default build.
`JoltAudit` is not a default target, and the default build does not change.

| Theorem | File |
|---------|------|
| `WholeRun.HonestTrace.sail_reproduces` | `JoltConstraints/WholeRun/Top.lean` |
| `JoltInstance.sail_soundness` | `JoltConstraints/WholeRun/Top.lean` |
| `JoltInstance.soundness` | `JoltConstraints/Soundness/soundness.lean` |
| `Decode.joltDecode_agrees` | `JoltBytecode/Decode/Agreement.lean` |
| `Decode.joltDecode_compressed_agrees` | `JoltBytecode/Decode/Compressed.lean` |
| `RiscvInstruction.joltRun_eq_execute` | `JoltBytecode/Step/Instructions.lean` |
| `RiscvInstruction.joltStep_eq_try_step_base` | `JoltBytecode/Step/Instructions.lean` |
| `RiscvInstruction.joltStep_eq_try_step_compressed` | `JoltBytecode/Step/Instructions.lean` |
| `RiscvInstruction.joltStep_eq_try_step_ecall` | `JoltBytecode/Step/Ecall.lean` |

`JoltInstance.completeness` and `JoltInstance.completeness_someWitness` are not gated, because they depend on `sorryAx` through the five open gaps above.

`lake build JoltAudit.Axioms` passes locally, and each of the nine theorems depends on exactly `propext`, `Classical.choice` and `Quot.sound`.
The build ran from a cold `JoltConstraints` build and took one hour on a loaded machine; the audit module itself takes 3.5 seconds.
`#print axioms JoltInstance.completeness` lists `sorryAx` besides the three, and `#audit_axioms` on it, or on a theorem proved by `sorry`, fails with an error that names `sorryAx`.

## The comparator gate

`ci/comparator/` is a separate Lake package that requires jolt-qed by path and shares its dependency directory.
`Challenge.lean` copies six statements verbatim and proves each with `sorry`.
`Solution.lean` repeats each statement and proves it by applying the jolt-qed theorem.
`config.json` names the six theorems (`sail_reproduces`, `sail_soundness`, `soundness`, `joltDecode_agrees`, `joltDecode_compressed_agrees` and `joltRun_eq_execute`, each under `ComparatorGate`) and permits `propext`, `Quot.sound` and `Classical.choice`.

`scripts/run_comparator.sh` runs Lean's built-in `lake comparator` by default (`COMPARATOR_ENGINE=lake`).
It first builds the three jolt-qed modules that `Challenge.lean` imports, which is trusted code and the same build as `lean.yml`, and checks that `Solution.lean` has exactly the same imports.
It never builds `Challenge` or `Solution` itself, and it deletes any of their build output left in `ci/comparator/.lake`.
`lake comparator` then builds, exports and checks both modules inside its `bwrap` sandbox, so no elaborator in `Solution.lean` runs outside the sandbox.
The deprecated external engine (`COMPARATOR_ENGINE=external`, built by `scripts/setup_comparator_toolchain.sh` at comparator `e3dcf3083fc53d44b27a4431fabf7d43181583f5`, lean4export `5a9a355dc6c5fd82b69058d433e2ae2e8dfbf8fe` and landrun `5ed4a3db3a4ad930d577215c6b9abaa19df7f99f`) is still available and also builds both modules inside its own `landrun` sandbox.

The `comparator` job in `provenance.yml` installs `bubblewrap`, allows unprivileged user namespaces (Ubuntu 24.04 restricts them through AppArmor), and runs `scripts/run_comparator.sh`.
Its steps use `continue-on-error: true`, and a last step reports a failure as a warning, until the job has passed once.

`COMPARATOR_NO_SANDBOX=1 scripts/run_comparator.sh` on macOS accepts all six theorems: the statements match, Lean's kernel accepts the exported proofs, and they use only the three permitted axioms.
That run has no `bwrap` sandbox and does not test the isolation.
With one proof in `Solution.lean` replaced by `sorry`, the same run rejects the solution with `Illegal axiom detected: 'sorryAx'`.

## How to run

From the repository root:

```bash
python3 scripts/check-provenance.py
python3 scripts/check-provenance.py --jolt-dir <a16z/jolt checkout> --compare a6b6dc7177ec5ea5a3c60bd5cea4409c07ca6dc5
python3 scripts/check_hygiene.py
python3 -m unittest discover -s scripts/tests
lake build JoltAudit
```

The Jolt checkout needs the pin and every `checked` revision; `python3 scripts/check-provenance.py --list-revisions` prints them.
`--print-baseline` on either script prints the baseline that matches the tree today.
To fix a recorded violation, remove it from the file and lower or delete its baseline entry in the same commit.

The comparator gate needs `bwrap`, so its sandboxed run is Linux only (`ci/comparator/README.md`):

```bash
scripts/run_comparator.sh
```

## Contradictions with the brief

- `get_16_random_bits` is an `opaque` in `LeanRV64D/RiscvExtras.lean`, not an axiom.
  The axioms of `LeanRV64D/` are the 67 `riscv_f*` floating-point axioms, which `docs/riscv-alignment.md` (section 8) records as unreached.
- No `bv_decide` remains in the sources, and there is no `bv_decide` list to record.
  `JoltConstraints/model_review.md` agrees, and it records no raised limits in `JoltConstraints/`.
  The only trusted-tactic debt is the two `decide +kernel` in `DeviceMemoryObstruction.lean`.
- No file contains a `~/` path; all 47 local paths start with `/Users/`.
- The leanprover/comparator README marks the project as deprecated and says it moved into Lean core as of v4.35.0.
  Lean v4.35.0, this repository's toolchain, ships `lake comparator`, which runs the same check in a `bwrap` sandbox and needs neither lean4export nor landrun.
  I first built the external gate the brief asks for; section "Decisions" moves CI to `lake comparator`.

## Decisions

Quang decided on 2026-11-12 that the project settles these points itself instead of waiting for Ari's review.
Each was open in the first version of this report.

1. **Pin: `580084fcf`.**
   It is the revision the T1, T2 and T4 CI jobs check, so the manifest and those jobs now agree.
   No `models` path is missing there (three were missing at `a6b6dc717`), and moving the pin added only two baselined citations of `a6b6dc717` in `docs/inline-precompiles.md`.
   When a16z/jolt#2384 gets a new head, the pin, the T1/T2/T4 `JOLT_REV` and this report move together in one jolt-qed pull request.
2. **Fork and `/Users/` citations stay as baseline debt.**
   They are in 117 existing Lean and Markdown files that T7 does not edit, and most cite `abiswas3/jolt/tree/main`, which names no revision to translate.
   The baseline now quotes each citation exactly, so it can only shrink, and any new local path or fork citation fails.
3. **The two `decide +kernel` in `JoltConstraints/Soundness/Layer5/DeviceMemoryObstruction.lean` stay as baseline debt.**
   `decide +kernel` adds no axiom, only the root module imports the file, and the axiom gate shows that no headline theorem depends on anything beyond the three standard axioms.
   AGENTS.md forbids the tactic in new code, which the zero-tolerance roots and the exact baseline enforce.
4. **The comparator job uses `lake comparator`.**
   The change was small: the job drops the Go setup and the three external builds and installs `bubblewrap` instead.
   It also fixes review finding 7, because the comparator now does the only build of `Challenge` and `Solution`.
   The local test is the unsandboxed run above; the sandboxed run is the CI job, which stays non-blocking until it passes once.

## Review fixes

A Codex review (`gpt-6.1-sol`, high effort) of `b648846..1ff8284` found seven problems.

| # | Finding | Fix | Test |
|---|---------|-----|------|
| 1 | The hygiene scan blanked interpolated strings and misread `«--»` as a comment | Interpolation read both ways; quoted identifiers kept opaque; raw strings handled | `test_check_hygiene.py`: interpolated, `throwError`, nested-string, quoted-identifier and raw-string cases |
| 2 | `axiom` matched only at the start of a line | Keyword matched anywhere in code | `test_axiom_after_set_option_in` and `test_axiom_after_attribute_and_modifiers` |
| 3 | `models` paths of the 88 entries without `checked` were not checked, and an entry for `README.md` passed | `unchecked-model` baseline, existence at the pin with `--jolt-dir`, entries limited to Lean files under the two roots, unknown keys rejected | `test_new_unchecked_models_path_fails`, `test_entry_outside_the_lean_roots_fails`, `test_unknown_entry_key_fails` |
| 4 | Abbreviated citation lists were not expanded into `models` | Brace lists and bare names expanded; with `--jolt-dir`, a cited file at `checked` must be in `models`; 13 paths added | `CitedPathsTest` |
| 5 | All-digit and all-letter revisions were skipped, and other repositories' revisions were exempt in Jolt URLs | Citation-context detection; repository-qualified citations checked against their repository | `RevisionTest` |
| 6 | The baseline recorded markers and owners, so one citation could replace another | Baseline quotes the whole citation | `BaselineTextTest` |
| 7 | `run_comparator.sh` built `Solution` outside the sandbox | The script builds only the trusted imports and leaves both gate modules to the sandboxed comparator | Smoke run on macOS; sandboxed run in CI |

## Follow-ups

- Publish or replace `a86ec3716` and `b65455e6d`, and identify `3cb4e243`.
- Give the 88 entries without a `checked` revision one, starting with the `JoltConstraints/Constraints/` files that cite `abiswas3/jolt/tree/main`, and delete their `unchecked-model` entries.
- Replace the 47 local paths and the 60 fork citations with a16z/jolt links at a recorded revision, and lower the baseline.
- Once the `comparator` job passes on GitHub, drop its `continue-on-error` steps and the warning step.
- Decide whether the project pin in `README.md` and `methods/soundness.md` (`c97e9300`) moves to `580084fcf`. That needs the review `methods/soundness.md` did for `c6703570` to `c97e9300`: which commits change modeled code, and whether the model follows them.
