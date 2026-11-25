# Stale assumptions at the `ff6fc6568` pin, and how to catch them automatically

## Finding

On 2026-11-25 an audit of every premise of the headline theorems against Jolt `ff6fc6568`
found four assumptions that the pinned Jolt no longer needs. The Lean model already
transcribed the Jolt checks that make each one true:

| Assumption | Jolt change that made it unnecessary | Lean transcription that already had it | Now |
|---|---|---|---|
| `JoltInstance.HeapNoWrap` (whole-run premise) | `MemoryLayout::validate_heap_end`, a16z/jolt#2415 | the first guard of `MemoryLayout.max_ram_k?` | `new_heap_end_le` |
| `Rv64ProgramImage.ImageNonempty` (completeness premise) | `derive_from_dimensions` rejects an empty trace (`TraceDoesNotEndInHalt`) | the first guard of `ProverConfig.deriveFromDimensions` | `HonestTrace.prover_config_image_nonempty`, with the new image field `instruction_loaded` |
| `JoltInstance.RamRegionFits` (soundness premise) | `MemoryLayout::max_ram_k` rejects a padded region past `2^64` | the last guard of `MemoryLayout.max_ram_k?` | `JoltInstance.ramRegionFits` |
| No RAM 2 GiB above `RAM_START` (documented only) | a16z/jolt#2509 removed the misfiling branch of `final_ram_state` | `TraceWitness.finalRamWord` | removed from `model_review.md` |

The comments on the three #1949 `sorry`s ("until a16z/jolt#1949 is fixed") are stale in
the same way. The issue is still open, but `assert_effective_address` in Jolt's tracer and
the layout bounds already exclude a wrapping access.

After these removals `JoltInstance.soundness` takes only `JoltField F`, and
`JoltInstance.completeness` takes nothing about the instance.

## Cause

Each re-pin transcribed new Jolt checks into the model, and review read the diff of the
transcription. No step asked which premise the new check makes provable. A premise is a
claim that the model does *not* guarantee something. Nothing tested that claim, so it
stayed after it became false.

## Design

Two directions of drift need separate checks.

### 1. The model starts guaranteeing a premise: necessity witnesses

Every premise of a headline theorem, every `sorry`, and every trusted field of
`Rv64ProgramImage` gets a *necessity witness*: a Lean `example` that builds a concrete model
object violating the premise at the boundary where the premise is stated. Some examples:

- `HeapNoWrap`: `∃ config layout, MemoryLayout.new config = some layout ∧ 2^64 - 8 < layout.heap_end.toNat`.
- `ImageNonempty`: an execution summary with `trace_length = 0` that
  `deriveFromDimensions` accepts.
- `RamRegionFits`: a layout whose `max_ram_k?` succeeds with `lowest + 8 * k > 2^64`.

Each witness is a small `decide` or `rfl` proof on concrete data. When a re-pin transcribes
a check that makes the premise hold, the witness stops building, CI fails, and the premise
has to be removed. All three premises above would have failed this way at the re-pin.

A witness guards only the boundary it names. It is stated at the premise's own boundary,
not at a helper, so that a guarantee arriving through a different function still breaks it.
A witness shows that a headline theorem needs its premise only when the object it builds
meets every other premise of that theorem. The `JoltField` and `BlockConforms.riscv`
witnesses do not yet (see the order of work), and `witness_shows` in `assumptions.toml`
says what each witness proves.

### 2. Jolt changes code the model transcribes: anchored citations, checked against Jolt main

Two checks on this branch compare the model with Jolt, both at a fixed `JOLT_REV`:
constraint generation (`scripts/expansion-parity/`, which despite the folder name holds
only `constraint-gen`) and difftest (`scripts/difftest/`, Sail against Jolt's tracer). This
branch has no expansion-parity, decoder-sweep or lookup-table executable, and the
provenance manifest is proposed in #56 (T7), not on this branch. Nothing compared the model
with Jolt *main*, and the #56 manifest records whole files, which is too coarse for
`config.rs`.

- **Function anchors.** Every `See : jolt/<path> (<fn>) at <rev>` citation names a Rust
  function. A checker extracts each cited function's body at the pin, hashes it, and
  records the hash in the provenance manifest. `--compare <rev>` then lists the Lean
  definitions whose cited functions changed, not whole files.
- **Nightly job against Jolt main.** A scheduled workflow runs the generated checks and
  the anchor comparison against Jolt main's head, and updates one tracking issue with the
  regenerated-data diffs and the list of Lean definitions whose cited functions changed.
  Drift then shows up within a day, before anyone plans a re-pin.

### 3. One registry that ties the two together

`assumptions.toml` lists each premise, `sorry`, trusted image field and scope premise with:

- its Lean name and kind;
- the Jolt functions it depends on, as anchors;
- its necessity witness;
- its upstream issue and its bug-report folder.

CI checks that every binder of the gated headline theorems, every `sorry` and every
`Rv64ProgramImage` field appears in the registry. It also checks that every entry has a
witness that builds or an explicit reason for having none (a field premise such as
`JoltField`, or a trust boundary such as `DecodedFrom`). The nightly job flags an entry
when one of its anchors changes or its upstream issue closes. A re-pin script prints the
flagged entries as the re-pin's follow-up list.

Each bug-report folder gets a header with its status, the revision it reproduced at, and
the registry entries it backs. A re-pin reruns the reproducers. A reproducer that no
longer reproduces, or no longer builds, flags its entries.

## Order of work

1. Done on 2026-11-25 (branch `drift-guards`): the registry and the necessity witnesses.
   `assumptions.toml` has an entry for every binder of the headline theorems, every `sorry` (the three #1949 `sorry`s were proved the same day, in `db02bb9`), every field of `Rv64ProgramImage` and the scope premises.
   `JoltConstraints/Audit/Premises.lean` makes the build fail when a binder or field changes, and `scripts/check-assumptions.py` (a step of `lean.yml`) checks that the registry and those lists agree.
   `JoltConstraints/Audit/Necessity.lean` has witnesses for `JoltField`, `BlockConforms.riscv` and `memory_init_in_program`.
   `JoltConstraints/Audit/ImageFields.lean` proves that `DecodedFrom` implies `next_pc_no_wrap`, `instruction_loaded` and `program_end_ge_ram_start` without using the image fields.
   `memory_init_in_program` does not follow yet: `ElfSection` records nothing about the data length of a non-text section, and the witness shows the gap.
   Recording that every loaded section has at most `size` bytes of data closes it, but changes a definition.
   The bug-report folders have headers with their status.
2. Done on 2026-11-25: the nightly job against Jolt main (`.github/workflows/jolt-main-drift.yml`) with the tracking issue "Drift against Jolt main".
   It compares anchors file by file, and also every Jolt file the Lean sources cite (`scripts/jolt_citations.py`), so a newly cited file is watched without a registry edit.
   The job writes the report and updates the issue even when an earlier step fails; the report opens with whether the run could monitor Jolt main, and only a monitoring failure fails the job.
   The generator writes into an empty directory, and the report labels the equivalence result by whether new data was produced.
3. Done on 2026-11-25, after a review of this branch:
   - `scripts/check-lean-policy.py` (a step of `lean.yml`) rejects `sorry`, `admit`, axioms outside `scripts/lean-policy-allowlist.toml`, `native_decide`, `bv_decide`, `decide +kernel`, `maxHeartbeats`, `synthInstance` options, `respectTransparency false`, and `maxRecDepth` outside the five generated Sail options.
   - `JoltConstraints/Audit/Statements.lean` checks the axioms of the headline theorems, the necessity witnesses and the derived facts (`#audit_statements`), and compares their full statements and a fingerprint of every definition the statements depend on with a checked-in table. A definition that changes the meaning of a headline statement fails the build even when every proof still compiles. `scripts/update-audit-tables.py` rewrites the table after a reviewed change.
   - The audit commands resolve names exactly, and `scripts/check-assumptions.py` compares the registry's `witness` and `derived_by` names with the audited lists.
   - `assumptions.toml` gained entries for the Dory-only configuration, the tracer's initialization and host allocation, and `derived` entries for `HeapNoWrap`, `ImageNonempty` and `RamRegionFits`, whose Jolt functions stay watched.
   - `scripts/check-sail-model.sh --inputs-only` (every build) requires the Lean Sail runtime in `lakefile.toml` and `lake-manifest.json` to be `[runtime]` in `sail-import/PROVENANCE.toml`; a change to the Lake files or `lean-toolchain` triggers the full regeneration check.
4. Still open: function anchors in the provenance manifest. This builds on #56's T7 scripts, so it
   waits until the #71–#73 re-pin and #56 meet.
   The nightly job then switches from file-level to function-level anchors.
5. Follow-ups: remove the three image fields that `DecodedFrom` now implies from `Rv64ProgramImage`, which changes a definition; a `JoltField` witness at the constraint boundary (an instance outside the language with a satisfying assignment over a small field) rather than any small field; a `BlockConforms.riscv` witness at the block level (a `HonestTrace` whose `HaltPrefix` has a block with a `.jolt` row); both need a concrete program run. Also the per-instruction `JoltBytecode` theorems, which the registry does not gate yet. Every Lean citation of a Jolt file now resolves at the pin (`scripts/jolt_citations.py --unresolved` lists none), and the constraint-generation job fails when a new one does not.
