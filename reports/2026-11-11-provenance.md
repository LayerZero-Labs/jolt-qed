# Provenance and trust checks: T7

Date: 2026-11-11.
This report describes four checks that Track T phase T7 adds (`docs/inline-precompiles.md`, section 7).

1. `provenance.toml` names the one Jolt revision the project is checked against and, for every Lean file under `JoltBytecode/` and `JoltConstraints/`, the Jolt files it models.
   `scripts/check-provenance.py` checks the manifest and fails on any new local path, Jolt fork citation or unrecorded Jolt revision.
2. `scripts/check_hygiene.py` scans the Lean sources for `sorry`, trusted tactics, raised limits and axioms against `scripts/hygiene-baseline.toml`.
3. `JoltAudit/Axioms.lean` checks during the build that nine headline theorems use only `propext`, `Classical.choice` and `Quot.sound`.
4. `ci/comparator/` re-checks six of those theorems with leanprover/comparator.
   Its CI job is untested and does not block.

The first three pass locally.
The external comparator has not run, and the built-in `lake comparator` accepts the six theorems on macOS without its sandbox.
No CI job has run yet, because the branch is not pushed.

## Revisions

jolt-qed: branch `inline/t7-provenance` on top of `b648846`.
Toolchain: `leanprover/lean4:v4.35.0`.

Jolt pin: a16z/jolt `main` at `a6b6dc7177ec5ea5a3c60bd5cea4409c07ca6dc5` (`a6b6dc717`), the pin of Track T.
`README.md` and `methods/soundness.md` still record `c97e93004fbf804409f0374fe8457c8f1562ce71` (`c97e9300`) as the project pin.
`provenance.toml` records that disagreement in a note and leaves the project pin to Ari.

The provenance job also compares against a16z/jolt#2384 at `580084fcfad4788ebf48413a92dd640ca090c45f` (`580084fcf`), the revision the T1 expansion-parity job checks.
The pin is an ancestor of `580084fcf`.

## The provenance manifest

`provenance.toml` has one `[jolt]` table with the pin and one `[[file]]` entry for each of the 633 Lean files under `JoltBytecode/` and `JoltConstraints/`.
Each entry has `lean`, `models` (the Jolt paths the file transcribes or relies on), an optional `checked` revision and an optional `note`.

I derived `models` and `checked` from each file's own citations.
`checked` is the published a16z/jolt revision the file names most often, with the later commit on a tie.
`models` are the full Jolt paths the file cites that exist at `checked`.
A path the file cites that is missing at `checked` goes into the note instead.

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
- Every Lean file under `JoltBytecode/` and `JoltConstraints/` has exactly one entry, and every entry names an existing file.
- Every `checked` revision has 40 hex digits and comes with `models`.
- The scanned files have no local path, Jolt fork citation or Jolt revision beyond the `[[known]]` baseline.
  The scan covers `*.lean` and `*.md` under `JoltBytecode/`, `JoltConstraints/` and `docs/`, plus `README.md` and `provenance.toml`.
  A local path is `/Users/…`, `/home/…`, `~/…` or `/private/tmp/…`.
  A fork citation is a `github.com/<owner>/jolt` link with an owner other than `a16z`.
  A revision is a token of 7 to 40 hex digits with at least one digit and one letter.
  The check allows the pin, the file's own `checked` revision and any `[[other_revision]]`, matched by prefix.
- Every `[[known]]` count matches the tree exactly.
  A fixed violation therefore fails the check until its entry is lowered or deleted.

With `--jolt-dir <a16z/jolt clone>`, it also checks that the pin and every `checked` revision resolve and that every `models` path exists at its `checked` revision.
It reads only trees, and a shallow blobless fetch of each revision is enough.
It then reports, without failing, the `models` paths missing at the pin and at `--compare`.

### Baseline

The baseline records 269 existing violations in 117 files.

| Kind | Occurrences | Files | Where |
|------|-------------|-------|-------|
| Local path (`/Users/…`) | 47 | 32 | 6 in `JoltBytecode/`, 26 in `JoltConstraints/` |
| Fork citation (`abiswas3/jolt`) | 60 | 50 | 2 in `JoltBytecode/`, 48 in `JoltConstraints/` |
| Other Jolt revision | 162 | 43 | 3 in `JoltBytecode/`, 36 in `JoltConstraints/`, 3 in `docs/`, `README.md` |

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
| `docs/inline-precompiles.md` |  |  | `4e55c9a5f` ×2, `629b7d959`, `70e00da09` ×2, `db9679295` ×2 |
| `docs/riscv-alignment.md` |  |  | `9407f93f` ×2, `c336a6da7` ×2, `c6703570` |
| `docs/whole-run-theorem.md` |  |  | `c336a6da7` |

</details>

### Result

`python3 scripts/check-provenance.py` passes: 633 entries, 269 baseline violations, no new ones.
With `--jolt-dir` on a full a16z/jolt clone and `--compare 580084fcf`, it passes and reports these notes.

- Three `models` paths of `JoltBytecode/JoltISA/Expansions/System.lean` are missing at the pin: `crates/jolt-program/src/expand/control_flow/csr.rs`, `csr_immediate.rs` and `csrrc.rs`.
  #2384 adds them, and none is missing at `580084fcf`.
- Three revisions in the files are not a16z/jolt commits.
  `b65455e6d` (`JoltBytecode/Decode/Agreement.lean`) and `a86ec3716` (`System.lean`) exist only in local Jolt clones, and GitHub's API returns 422 for both.
  `3cb4e24361ae2006e9713ae65d58a3fa51fd0518` (`JoltConstraints/Completeness/BytecodeRaAtEntryEqOne.lean`) is in no a16z/jolt clone I have.
- 88 entries name `models` but no `checked` revision.

The same run on a shallow blobless fetch of the pin, the eight `checked` revisions and `580084fcf` passes with the same notes, except the one on revisions that are not commits, which the check skips in a shallow clone.
That fetch, the one CI does, took 7 seconds and 1.4 MB.

Some files cite Jolt paths that no a16z/jolt commit contains: `crates/jolt-trace/src/preprocess/bytecode.rs`, `crates/jolt-trace/src/preprocess/public_io.rs` and `crates/jolt-riscv/src/instructions/b/beq.rs`.
The notes of their entries say so.
Other notes record citation drift, for example `floor_access.rs`, which is missing at `5def437f` and `e012da54` and present at `c6703570` and at the pin.

I checked that the check fails on each of these: a new Markdown file under `docs/` with a local path, a fork citation and an unknown revision; a baseline count one above the tree; a Lean file with no entry; and a `models` path that does not exist at its `checked` revision.

## The hygiene scan

`scripts/check_hygiene.py` blanks comments, docstrings, strings and character literals, then counts these tokens: `sorry`, `admit`, `native_decide`, `decide +kernel` (also `kernel := true`), `bv_decide`, `set_option maxHeartbeats`, `maxRecDepth`, `synthInstance.*` options and `axiom` declarations.
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

`scripts/setup_comparator_toolchain.sh` builds comparator at `e3dcf3083fc53d44b27a4431fabf7d43181583f5`, lean4export at `5a9a355dc6c5fd82b69058d433e2ae2e8dfbf8fe` (both "bump toolchain to v4.35.0") and landrun at the `main` commit `5ed4a3db3a4ad930d577215c6b9abaa19df7f99f` that openvm-fv uses.
`scripts/run_comparator.sh` builds `Challenge` and `Solution` and runs the comparator.
The `comparator` job in `provenance.yml` runs both scripts.
Its steps use `continue-on-error: true`, and a last step reports a failure as a warning.

Nobody has run the external comparator, because `landrun` uses Linux Landlock and does not build on macOS, and the CI job has not run.
`Challenge.lean` and `Solution.lean` elaborate with `lake env lean`; `Challenge.lean` warns about its six `sorry`s and `Solution.lean` has none.

The built-in `lake comparator` of Lean v4.35.0 does run on macOS.
`COMPARATOR_ENGINE=lake COMPARATOR_NO_SANDBOX=1 scripts/run_comparator.sh` accepts all six theorems: the statements match, Lean's kernel accepts the exported proofs, and they use only the three permitted axioms.
That run has no `bwrap` sandbox and does not test the isolation.
With one proof in `Solution.lean` replaced by `sorry`, the same run rejects the solution with `Illegal axiom detected: 'sorryAx'`.

## How to run

From the repository root:

```bash
python3 scripts/check-provenance.py
python3 scripts/check-provenance.py --jolt-dir <a16z/jolt checkout> --compare 580084fcfad4788ebf48413a92dd640ca090c45f
python3 scripts/check_hygiene.py
lake build JoltAudit
```

The Jolt checkout needs the pin and every `checked` revision; `python3 scripts/check-provenance.py --list-revisions` prints them.
`--print-baseline` on either script prints the baseline that matches the tree today.
To fix a recorded violation, remove it from the file and lower or delete its baseline entry in the same commit.

The comparator gate runs on Linux only (`ci/comparator/README.md`):

```bash
scripts/setup_comparator_toolchain.sh
COMPARATOR_NO_SANDBOX=1 scripts/run_comparator.sh
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
  I built the external gate the brief asks for, and `scripts/run_comparator.sh` also runs `lake comparator` with `COMPARATOR_ENGINE=lake`.
  Moving the CI job to `lake comparator` would remove the three external builds.

## Follow-ups

- Decide the project pin: `README.md` and `methods/soundness.md` record `c97e9300`, and Track T uses `a6b6dc717`.
- Publish or replace `a86ec3716` and `b65455e6d`, and identify `3cb4e243`.
- Give the 88 entries without a `checked` revision one, starting with the `JoltConstraints/Constraints/` files that cite `abiswas3/jolt/tree/main`.
- Replace the 47 local paths and the 60 fork citations with a16z/jolt links at a recorded revision, and lower the baseline.
- Run the `comparator` job once on GitHub, then make it blocking, or move it to `lake comparator`.
