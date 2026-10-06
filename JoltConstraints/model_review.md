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
  address wrap ([#1949](https://github.com/a16z/jolt/issues/1949)), the (16)
  self-branch with a padding successor, the (37) termination-word store,
  source-PC wraparound, `ram_k = 1` giving zero RAM chunks, zero-mask shifts,
  and heap-end/stack-canary checks. Correction (2026-10-06): #1949 is the
  wrapping LD address only; no upstream issue tracks source-PC wraparound, so
  the old `program.lean` WARNING on `addressAdvanceNoWrap` cites the wrong issue.
  See "Upstream issues" below for the current status of each.
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
  happens. No longer assumed: every row of an honest trace retires, so its LD/SD
  address is a multiple of 8 (`HonestTraceRow.load_aligned` and `store_aligned`
  in `execution_facts.lean`).
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
  Reported upstream as a16z/jolt#1951 item 5 (open).
- Termination word (archive item (37)): the verifier expects the final I/O region
  to hold termination word 1 when the run did not panic and 0 when it did
  (`jolt-program/src/preprocess/public_io.rs:47-52`; on panic the segment is
  omitted, so the word must be 0). But `JoltDevice::store` ignores every write to
  the termination word (`common/src/jolt_device.rs:150-156`), and Lean's
  `JoltDevice.store?` copies that. So nothing in the run itself records
  termination. `HonestTrace.matches_outputs` in `honest_trace.lean` checks only
  the outputs and the panic flag; settle where the 1 comes from before the
  witness's final RAM is wired in. Related upstream: a16z/jolt#1951 items 1-2
  and #1950 (open).
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

## Completeness conditions

Decided 2026-10-06. The final completeness theorem covers every honest trace
that fits, except the runs below, which Rust's own prover does not prove. Every
other assumption of the old theorem is proved or derived from the trace.

Assumed (Rust does not prove these runs):

- **Loads below the lowest address.** WARNING: Rust's tracer and prover disagree.
  The tracer lets a program read any nonzero address at most
  `RAM_START_ADDRESS - 8`, so also below the lowest address, and returns 0
  (`mmu.rs:139, 154`, `jolt_device.rs:144-147`). This was added with ZeroOS
  (#1229); before it the tracer rejected such reads as "I/O underflow". The
  prover panics on them (`jolt-prover/src/config.rs:183-195`: "a malformed
  trace, failed loudly here"), and the verifier can only rebuild addresses of
  the form `8k + lowest` (`ram_raf_evaluation.rs:136-149`). We follow the
  prover. Already reported upstream: a16z/jolt#1951 item 3 (open), whose
  proposed fix makes the tracer reject these reads.
- **Spoil asserts.** `VirtualAssertEQ` with imm ≠ 0 and unequal sides: Rust warns
  "proof will be unsatisfiable" and continues (`virtual_assert_eq.rs:24-31`);
  the failing proof is intended. Asserts with imm = 0 are proved to hold
  (`assert_eq_holds`).

To prove, not assume:

- **Address-0 loads.** Rust treats address 0 as "no RAM access"
  (`jolt_device.rs:491-492`, `verifier.rs:986-990`). An LD at 0 reads 0 (no
  device region starts below 8, by `validate_inputs`), and an SD at 0 never
  retires (`mmu.rs:142-145`). Fix the one step in
  `Constraints/RamReadSelection.lean` that uses "address ≠ 0" during the
  rewiring. An address that wraps to 0 stays bug (01).
- **Entry address 0.** The trace is empty (a first row would sit at address 0,
  below every bytecode address). Constraint (53) still holds: Rust's padding row
  is a NoOp in slot 0 (`preprocess/bytecode.rs:65-68`), the entry slot is 0
  (`bytecode.rs:121-123, 218-226`), and Lean's `bytecodePc` gives padding 0.

FIXME (modeled as it should be, not as Rust is):

- **`ram_K` one slot too small.** Rust rounds up the highest touched slot instead
  of that slot plus one (`jolt-prover/src/config.rs:143`). When the highest slot
  is a power of two, the RAM table is one slot too small and Rust's witness
  rejects the run ("RAM access address remapped to 1024, beyond ram_k 1024").
  Reported as a16z/jolt#1951 item 4 (open), with the fix `(touched + 1)`.
  Reproduced at `8e536f19` with `bug-report/ram-k-off-by-one/run.sh`.
  `HonestTrace.prover_config` uses the fixed formula; rerun the repro to check
  when Rust changes.

Derived from the trace with Rust's `ProverConfig::derive_from_rows`
(`jolt-prover/src/config.rs:110-152`): `traceFits`, the bound in `ramFits`,
`bytecodeDomain` and `ramChunksPos`. The derived `ram_K` is at least 2, since the
program image ends at slot 2 or later, so archive item #13 (`ram_k = 1`) cannot
arise from a derived configuration.

## Upstream issues

Every Jolt issue that stops a completeness proof, where we mark it, and what we
do about it. Checked against a16z/jolt on 2026-10-06; our Rust checkout is
`8e536f19` (2026-10-05). If an open item is still open when the main proofs
pass, escalate it.

| Issue | What breaks | Status | In our model |
|---|---|---|---|
| [#1951](https://github.com/a16z/jolt/issues/1951) item 3 | A load from a nonzero address below the lowest address: the tracer runs it, the prover panics | open | condition: `HonestTrace.prover_config` (WARNING) |
| [#1951](https://github.com/a16z/jolt/issues/1951) item 4 | `ram_K` one slot too small when the highest touched slot is a power of two | open; reproduced at `8e536f19` (`bug-report/ram-k-off-by-one/`) | modeled as fixed: `HonestTrace.prover_config` (FIXME) |
| [#1951](https://github.com/a16z/jolt/issues/1951) item 5 | The emulator and preprocessing load different ELF sections | open | assumed equal: `initialRam` TODO in `program_fresh.lean`; note above |
| [#1951](https://github.com/a16z/jolt/issues/1951) items 1-2, [#1950](https://github.com/a16z/jolt/issues/1950) | Termination and panic words: the device treats them as flags, the proof as memory | open | `HonestTrace.matches_outputs` leaves the termination word out; (37) stays `sorry` |
| [#1949](https://github.com/a16z/jolt/issues/1949) | A load/store address that wraps past 2^64 breaks the RAM-address constraint | open; a fix PR is announced in its comments | (01) stays `sorry` |
| [#1916](https://github.com/a16z/jolt/issues/1916) | A trace that ends on a taken self-branch breaks the next-PC constraint | fixed by PR [#1968](https://github.com/a16z/jolt/pull/1968) (merged 2026-10-06, upstream `00508a09`): the prover refuses traces whose last row is not a jump | modeled: `HonestTrace.prover_config` has the jump check; (16) can be proved during the rewiring |
| [#1952](https://github.com/a16z/jolt/issues/1952) | The emulator fetches instructions from memory, the proof uses the decoded bytecode | open | assumed: field `HonestTrace.code_unchanged` (FIXME) |
| none | The source PC wraps past 2^64 | asked a16z on 2026-10-07, no answer yet: can an ELF Jolt accepts contain an instruction whose next PC passes 2^64? | assumed: `Rv64ProgramImage.NextPCNoWrap` (WARNING) |
| [#1914](https://github.com/a16z/jolt/issues/1914) | CSRRS writeback | closed, fixed (`f012bfb1`) | (13) proved |

Not issues, by design: spoil asserts (`HonestTrace.SpoilAssertsPass`) and runs
longer than the instance's limit (`HonestTrace.prover_config`).

## Proofs owed

Sorried theorems in the new pipeline. `#print axioms` shows `sorryAx` on every
theorem that uses one of them; nothing else in the new files is sorried
(`SourceInstruction.expand` is `opaque`, which adds no axiom).

| Theorem | File | What it needs |
|---|---|---|
| `pc_map_ok_iff` | `program_fresh.lean` | the shape of `expand_instruction`'s output; unused so far |
| `HonestTrace.prover_config_log_ram_K_lt` | `witness_params.lean` | every touched address is below `heap_end` (MMU), so `ram_K ≤ 2^61` |
| `HonestTraceRow.store_word_present` | `execution_facts.lean` | an SD stores over bytes that are present: RAM below `heap_end` (all put in memory by `initialRam`, stores only add) or the device's output/panic/termination words; used by `RamReadValue` |

