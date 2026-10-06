---
title: Reviewing Jolt model in Lean
started: 2026-10-06
lean_commit: 9b962da (feat/soundness)
rust_commit: 8e536f199735ac8187156aa589ed1387722a079a (main, $HOME/Work-With-A16z/jolt)
---

# Reviewing Jolt model in Lean

Earlier reviews are kept for reference:
[model_review_archive_2026-10-06.md](model_review_archive_2026-10-06.md) and
[model_review_archive_2026-09-25.md](model_review_archive_2026-09-25.md).

## Flagged for later

Notes collected on 2026-10-06 while reading the archives against the current
sources. They are leads to recheck, not settled findings.

### Rust checkout

- The checkout is at `$HOME/Work-With-A16z/jolt`; older documents spell it
  `Work-with-A16z`.
- Revision `3cb4e24`, cited by the archives for (37), (42) and the fork replay,
  is not in this checkout. Its two Jolt fixes, `f012bfb1` (CSRRS `x0` lowering)
  and `66f35559` (VirtualSRLIW zero mask), are present at HEAD.
- None of the known open issues is fixed at `8e536f19`: the (01) load/store
  address wrap, the (16) self-branch with a padding successor, the (37)
  termination-word store, source-PC wraparound
  ([#1949](https://github.com/a16z/jolt/issues/1949)), `ram_k = 1` giving zero
  RAM chunks, zero-mask shifts, and heap-end/stack-canary checks.
- Changes since `922af71c` that touch modeled behavior:
  - #1902 and #1958: the decoder now rejects MISC-MEM words with funct3 ≠ 000
    and LR.W/LR.D with rs2 ≠ 0.
  - #1973: a HostIO cycle-marker END now reads its label bytes through the
    checked MMU path and can panic on a bad pointer. Check whether the Lean
    HostIO model assumes END performs no memory access.
  - #1808 (field-inline) and #1975 (External inlines) sit behind a feature that
    is off by default; the base RV64 relations, witnesses and lookups are
    unchanged.
  - #1997 and #1998 change only comments and tests.

### Lean source versus current documents

- Inventory: 57 targets proved with no `sorry` in their own files; (39) is
  proved modulo six `lookupEntryCorrect_*` shift/rotate lemmas; (01), (16),
  (37) and (38) are `theorem … := by sorry`.
- `JoltProgram.rowValid` and `NoEarlyNextPCChange` in `program.lean` are
  `sorry`. They are only default values for trace fields, but no
  `#print axioms` run has confirmed that no theorem reaches them.
- [constraints.md](constraints.md) still calls (16) a statement rather than a
  theorem, and the `Completeness/All.lean` docstring says only the branch result
  uses `sorry`.
- (13) keeps an unused `…Statement : Prop` definition beside its proof.
- The register targets (34)–(36) and (42) take an `initialRegistersZero`
  premise that `JoltTrace.initialized` now implies.
- `Completeness/All.lean` uses the slot-equality form of (53), not the
  `_of_address` corollary.
- `trace_new.lean`, the fresh model the 2026-09-25 archive describes, was never
  committed.
- Program and trace definitions moved from `trace.lean` to `program.lean`, and
  completeness theorems moved from `Constraints/` to `Completeness/`. Archive
  links still use the old locations.
- Some Lean comments still cite `/Users/ari.biswas/...` paths.
- `JoltConstraints/Tests` is listed in `.gitignore`, but its 16 modules are
  tracked.
- Rust's `trace_load` rounds the address down to a multiple of 4 before reading
  (`tracer/src/emulator/mmu.rs:480-481`); Lean's `trace_doubleword?` reads at
  the address as given. For LD this cannot differ, since `load_doubleword`
  panics unless the address is a multiple of 8 (`mmu.rs:331`). HostIO byte
  reads go through Rust's `load`, which calls `trace_load`; `JoltISA.Mmu.load`
  models both, including `trace_load`'s panics.
- `MemoryLayout::new` rounds every size up to a multiple of 8 except
  `program_size`, and `program_size = program_end − RAM_START_ADDRESS` can be
  any value. So `stack_end` and `heap_end` need not be multiples of 8. Rust's
  64-bit RAM checks look only at the start address (`mmu.rs:160-183`), so an
  aligned access may reach up to 7 bytes into the stack canary or past
  `heap_end` without a panic; RAM is backed in whole 64-bit units
  (`memory.rs:49-51`), so such reads return 0. `JoltISA.Mmu` copies this
  start-only check as Rust has it.
- Misaligned LD/SD: Lean traps (the alignment check in `Semantics.lean`), Rust
  panics (`mmu.rs:331`, `mmu.rs:437-443`). Decided 2026-10-06: assume it never
  happens.
- HostIO pointers: the constraints never check HostIO byte reads, but Rust
  panics on a bad pointer. So the verifier can accept runs that Rust rejects; a
  soundness theorem stated against Rust's semantics must exclude them. Harmless
  in practice: HostIO changes no register, RAM or output.
- Cycle-marker END reads its label bytes in Rust (#1973, `cpu.rs:1205-1206`);
  Lean's `execHostIOWith` reads nothing on END. With a bad pointer, Rust panics
  and Lean retires.
- Two initial RAMs in Rust: the verifier's from `decode_elf`'s `memory_init`
  (every section in RAM, `elf.rs:45-66`), the prover's from the tracer (only
  PROGBITS, INIT_ARRAY, FINI_ARRAY and PREINIT_ARRAY sections,
  `tracer/src/emulator/mod.rs:204-213`). They differ if an ELF puts another
  kind of section in RAM. `program_fresh.lean` assumes they agree and uses
  `memory_init` for both; Jolt's linker script (`src/linker.ld.template`) only
  places those kinds and NOBITS in RAM. Revisit once the main proofs pass.
- Termination word (archive item (37)): the verifier expects the final I/O region
  to hold termination word 1 when the run did not panic and 0 when it did
  (`jolt-program/src/preprocess/public_io.rs:47-52`; on panic the segment is
  omitted, so the word must be 0). But `JoltDevice::store` ignores every write to
  the termination word (`common/src/jolt_device.rs:150-156`), and Lean's
  `JoltDevice.store?` copies that. So nothing in the run itself records
  termination. `HonestTrace.matches_outputs` in `honest_trace.lean` checks only
  the outputs and the panic flag; settle where the 1 comes from before the
  witness's final RAM is wired in.
- An entry address of 0 passes Rust's entry check: `get_first_pc(0)` returns slot
  0, the leading NoOp (`preprocess/bytecode.rs:218-226`). `JoltInstance.bytecode`
  in `program_fresh.lean` copies this.

### Open items recorded only in the archives

Audit IDs are those of the 2026-09-25 archive.

- **#3** Program provenance: no bytecode address range or alignment condition
  and no run-length limit. The approved `addressSequenceUnique` and its Rust
  justification (`BytecodePCMapper::try_new`, `validate_run`) are documented
  only there.
- **#5** HostIO byte loads and full MMU/capture correspondence.
- **#6** Loader correspondence: the entry, RAM image, IO layout, advice tape
  and HostIO configuration passed to `init_state` are existential.
- **#9** `honestWitness` accepts prefix and empty traces, while the final RAM
  always writes termination word 1.
- **#13** Rust accepts `ram_k = 1`; its padding `RamRa` witness is zero while
  the empty chunk product is one. (58) carries a positive-chunk premise.
- **#14** IO layout and buffer validity beyond `AdviceBelowInput`.
- **#15** Heap-end and stack-canary checks, with the approved scope:
  `stack_end`, `stack_start` and `heap_end` formulas, `STACK_CANARY_SIZE = 128`,
  and `assert_effective_address` checking only the start address on the
  doubleword fast path.
- **#16** RAM image validation: an unremappable overlay start is ignored, and
  there is no image or final-marker fit check.
- **#17** Zero-mask shifts. Lean's VirtualSRLI, SRAI, SRAIW, ROTRI and ROTRIW
  (and the register-mask SRL, SRA, SRLW, SRAW) use `ctz 0 = 0`. In Rust release
  builds, mask 0 leaves SRLI, SRAI and ROTRI unchanged, SRAIW gives
  `sext32(rs1)` (a debug build panics), and ROTRIW gives `zext32(rs1)`. Lean's
  results for SRAIW and ROTRIW are unchecked.
- **#20** No TrustedAdvice or UntrustedAdvice witness families.
- **#21** Backend/profile correspondence (the 8-versus-12 padding floor) and
  program commitments (BytecodeChunk, ProgramImageInit).
- **Process** Every modeling-code change needs explicit approval, presented
  with Rust evidence, the proposed Lean code and a justification.
