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

### 2. Jolt changes code the model transcribes: anchored citations, checked against Jolt main

Some checks already compare the model with Jolt, all at a fixed `JOLT_REV`:
constraint generation, expansion parity, the decoder sweep, lookup tables, difftest, and
the provenance manifest from #56 (T7). Nothing compares the model with Jolt *main*, and
the provenance manifest records whole files, which is too coarse for `config.rs`.

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
   It compares anchors file by file.
3. Still open: function anchors in the provenance manifest. This builds on #56's T7 scripts, so it
   waits until the #71–#73 re-pin and #56 meet.
   The nightly job then switches from file-level to function-level anchors.
4. Follow-ups: remove the three image fields that `DecodedFrom` now implies from `Rv64ProgramImage`, which changes a definition; a `JoltField` witness at the constraint boundary rather than any small field; a `BlockConforms.riscv` witness at the block level; the per-instruction `JoltBytecode` theorems, which the registry does not gate yet.
