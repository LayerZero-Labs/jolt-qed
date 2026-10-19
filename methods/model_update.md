---
title: Migration to the current Jolt pin
updated: 2026-10-19
rust: 8bbb2357890928d8f83b00ca542879077c4d3d28
status: migration implemented and validated
---

# Reference revision

Ari selected the latest pulled version on 2026-10-15. The publicly available
**Rust semantics pin** is upstream
[`8bbb2357890928d8f83b00ca542879077c4d3d28`](https://github.com/a16z/jolt/commit/8bbb2357890928d8f83b00ca542879077c4d3d28).
Use this revision for Rust semantic citations.

The inspected local checkout is `/Users/ari.biswas/Work-with-A16z/jolt`, branch
`rust-to-lean-second-round`, at merge
`1c8aaff2db4306db1c2c6d9a4f755e83949a7416`. That merge is unpublished. Its
committed differences from the upstream pin are only the Lean generator and
agent instructions, not the tracer or constraint semantics. No Jolt fetch or push
was performed; this records the latest pulled upstream revision, not live main.

**Generator provenance is separate:** the local change originates in
`7dfe8a0f829a4ab3e9126eb5ac5b5b15208cf5fc` (`fix(lean-gen): emit normalized
final operands`) and is retained in the local merge. That commit is also absent
from local remote-tracking branches. The exact generator delta from the public
pin to the inspected merge is saved as
[`lean-gen-local.patch`](./model_update/lean-gen-local.patch), so reproducing it
does not require fetching either unpublished commit. Its SHA-256 is
`9e1a43276eac154be22903d7f13d2d16ed073db44ca5acaaa3dd5c64b7047bcf`.
Apply it to the public pin in a scratch checkout, then apply
[`lean-gen-chunk2.patch`](./model_update/lean-gen-chunk2.patch). The second patch
adds LR/SC generation and fixes advice rendering and immediate-width annotations;
its SHA-256 is
`b8f4a7d83665c4c849d8682a73cc5f97826c44fb3dd712692f716761109d0a26`.
LR/SC were handwritten in Lean before this work; the generator had never covered
them. The second patch reproduces those existing bodies unchanged. Both patches
are tooling changes, separate from the public semantics pin. The pre-existing
uncommitted Rust-checkout changes (agent instructions and `nvim.log`) are preserved.

The previous model baseline was `43cc043` plus PR #2039 at `2a924239` and
PR #2049’s advice-length removal at `7b311c9`. The initial 36-commit inventory
was a source-only audit. The implementation, proof builds and source rechecks
for the six migration chunks are recorded below; review and existing proof
gaps are separate from adopting this source pin.

Ari reviewed chunks 1–3 against the public pin by reading the Rust source and
accepted them. Deferred notes 1 (the saved generator patch and hash) and 2
(the placement of the layout facts) are resolved. Deferred note 3, the
`43cc043` citation search, is completed and classified in chunk 6. Ari also
reviewed chunks 4–6 by reading. The corrected-sizing completeness caller is
implemented, built and retained; the unused Rust-sizes corollary and its
supporting bridge lemmas were later deleted, as recorded in the follow-up
below. Migration adoption is closed. Existing
native-proof repairs remain deferred at Ari’s request.
The present theorem scope remains
decoded RV64 and the modeled custom instructions, with the base field bound.
Akita remains separate, and PCS security, committed-program protocols and
inline/precompile instructions remain outside that theorem. New premises
require Ari's approval. Migration findings remain local until discussed.

# Migration checklist

1. **Checked memory-layout construction — implemented and reviewed.**
   `MemoryLayout::try_new` now rejects an I/O region whose padded start is zero,
   and reports checked-arithmetic failures as errors. Lean's `MemoryLayout.new`
   already represented arithmetic failures with `none`, but its `adviceRegions`
   previously permitted start zero. The acceptance condition is now updated,
   and the layout, initialization and verifier-size proofs build. The source is
   `common/src/jolt_device.rs`; the principal Lean files are
   `JoltBytecode/JoltISA/JoltDevice.lean`, `layout_facts.lean` and `program.lean`.
   Implementation and validation are recorded below.

2. **Expansion generator and merged ISA changes — implemented and reviewed.**
   Added LR.W, LR.D, SC.W and SC.D generator coverage. All 57 regenerated programs
   match `ExpansionsAutomated.lean` byte for byte, including both destination
   branches. The merged SC fix (`0dad0d9e`, #2039) and advice-length removal
   (`3a290ae1`, #2049) agree with our existing translations. Immediate widths,
   row metadata and runtime-advice patching were rechecked; details below.

3. **Unified execution/proof trace — audited, built and reviewed.** PR #1996
   (`a104dc63`) replaces the separate proof-row representation with
   `jolt_riscv::JoltTraceRow` and changes the witness backend to consume
   `TraceData::proof_rows()`. Check captured register identities and values,
   load/store observations, resolved bytecode PCs, no-op validation, missing
   captures and padded successor values against Lean's `TraceRow` and witness
   helpers. Rust's checked row constructor is a producer-side check; do not
   silently turn it into a verifier constraint or a soundness premise.

4. **Prover and verifier sizing — implemented, reviewed; bridge follow-up validated.**
   `ProverConfig::derive_from_dimensions` replaces the old row scan and adds
   explicit checked-overflow/error paths. Reconcile trace padding, RAM bounds
   and setup sizing with `HonestTrace.prover_config`, `WitnessParams`,
   `verifier_sizes.lean` and their completeness proofs. At this pin Rust still
   rounds `max(touched, image_end)`, whereas Lean deliberately uses
   `max(touched + 1, image_end)` (#1951 item 4). That is an existing documented
   mismatch, not a fixed upstream issue.

   **Direction:** the reference model must describe the Rust policy as it is,
   including its bug. Preserve the intentional `touched + 1` correction as an
   explicitly identified corrected variant, linked to
   [`bug-report/ram-k-off-by-one`](../bug-report/ram-k-off-by-one/). Before changing
   existing definitions or theorem dependencies, show the actual and corrected
   policies side by side and identify which completeness results use each.
   Keep the current deviation documented until that separation is reviewed;
   neither silently remove `+ 1` nor silently claim Rust now uses it. This plan
   changes no formula and authorizes no extra premise.

   The verifier's maximum still divides by eight before rounding. Akita's new
   chunk profiles belong to its separate model; the base prover policy is
   still 4-bit chunks below log trace length 25 and 8-bit chunks above it.

5. **Constraint and bytecode correspondence — audited and reviewed.**
   The RV64 R1CS definitions moved from `jolt-r1cs/src/constraints/rv64.rs` to
   `jolt-claims/src/protocols/composed/r1cs/rv64.rs`; the diff shows imports and
   type-path changes, not changed RV64 equations. Refresh the constraint source
   mapping and check the full modeled relation and verifier checks.

   Correction to the earlier Layer 1 warning: `8bbb2357` removes chunking of
   the **precommitted program table**, replacing `BytecodeChunk` commitments
   with one `ProgramBytecode` commitment. It does not remove the selector
   chunks: `BytecodeRa(usize)`, `BytecodeRaChunk` and
   `bytecode_d = ceil(logBytecodeK / committed_chunk_bits)` remain. Those are
   the chunks used by `Layer1/Chunks.lean`, `Addresses.lean` and `Bytecode.lean`.
   No wholesale rewrite of Layer 1 is justified by this commit alone. Program
   commitments are already outside the model; still check any effect on the
   setup-size argument used in Layer 0.

6. **Validation and source record — complete; results below.**
   Build each changed chunk and both libraries, audit the affected top lemmas'
   axioms, and update source references and model-gap notes. Use default
   heartbeats and smaller lemmas. Check every changed source area that feeds
   the current theorem, recording unchanged or out-of-scope areas explicitly.
   Decoder changes in this range remove the advice-length encoding and move
   tests; Lean still starts from decoded instructions. Lookup-table bodies
   show no semantic change in the inspected diff. New binary-field, Akita,
   field-inline, accelerated-tracer and PCS work does not automatically expand
   our theorem's scope. Redo the earlier source audits at the public pin:
   verifier sizes and Dory setup (including the source of the Layer 0 bound),
   device/MMU rules underlying `TracerAddressChecks`. Discussion of #2044 stays
   deferred until Ari supplies Michael’s comments. Use commit permalinks and current function/line references; old
   citations remain historical evidence, not a fresh audit. Initial rechecks
   are recorded below. Remove the migration-pending status only after the
   in-scope correspondence and validation work is finished.

   Open review follow-ups:

   - **Historical citation search — completed in chunk 6:** remaining old-pin
     citations are classified below; current correspondence claims were re-audited
     at `8bbb2357`. This resolves the last deferred review note.
   - **Compiler-trust repair — deferred until after migration review:**
     Ari requested this separately from chunks 4–6. Do not repair these proofs
     during the migration. The later task is to audit the main theorem's full dependency set:
     build `JoltConstraints.Completeness.All`, then run
     `#print axioms HonestTrace.allConstraints_corrected_sizes` (renamed in chunk 4).
     Replace **every**
     native `bv_decide`/compiler-trust dependency in that output with a
     kernel-checked proof, following the Interleave repair. The 24-lemma
     chunk 3 audit was only a sample; its one finding, `branch_target_toNat`,
     is not the repair scope. Use the main theorem's axiom list as the
     authoritative checklist, including dependencies through
     `Completeness/Helpers/LookupEntryProofHelpers.lean` and core ISA lemmas
     in `JoltBytecode/JoltISA/Values.lean` when reachable. Check native proofs
     in instruction equivalence (`Natives/Sd.lean`, `StoreFamily/Splice.lean`)
     if either main theorem depends on them; a source match alone does not
     establish a dependency, and Interleave's comment is not a native proof.
     The [axiom policy](./soundness.md) rules out these dependencies even when
     they predate the migration. Preserve theorem statements and premises,
     split proofs into smaller lemmas if needed, and do not increase
     `maxHeartbeats`. Rebuild affected proofs and repeat the main completeness
     audit until no native-evaluation or compiler-trust axiom remains. Record
     the expected existing `sorryAx` separately; it does not hide other axioms
     or make the proof complete. Repeat the audit for the main soundness
     theorem as its dependencies are finalized. The baseline inventory is
     recorded below; the proof repairs remain open.

# Chunk 1 implementation and validation

Implemented locally on 2026-10-15; stopped for review before chunk 2.
The local checkout's `common/src/jolt_device.rs` was compared with the public
pin `8bbb2357` and has no differences. The Rust checkout was not modified.

- `MemoryLayout.adviceRegions` now computes the checked padded start once and
  rejects zero before either advice ordering, matching
  [`MemoryLayout::try_new`](https://github.com/a16z/jolt/blob/8bbb2357890928d8f83b00ca542879077c4d3d28/common/src/jolt_device.rs#L435-L477).
  `MemoryLayout.new` retains its `Option` interface: Rust error variants are
  erased to `none`. Existing checked additions, subtraction and multiplication
  already cover the arithmetic failures. The checked I/O sum is below `2^64`,
  so its quotient by eight rounds to at most `2^61`; Rust's checked
  next-power-of-two cannot fail there. Multiplication by eight can fail and
  remains checked.
- Repaired `adviceRegions_some`. Added `adviceRegions_starts_pos`,
  `new_lowest_address_pos` and `initial_state_lowest_address_pos`. All 18 existing
  layout theorem statements are unchanged. The initialization, memory-presence
  and verifier-size proofs build without further repairs or added premises.
  No heartbeat setting was added or increased. Constructor and host layout
  source references now cite the public pin.
- Six one-off kernel-checked regression lemmas cover large valid layouts in both
  advice orderings, the newly rejected
  zero-start cases, the exact padding boundary and an oversized region, all five
  upstream arithmetic-overflow examples, missing program size and invalid advice
  capacities. These use `decide +kernel`, without native-evaluation axioms.
  The temporary source-tree regression module was removed after review to
  respect the "do not pollute" convention; reproduce the checks with the
  scratch command below. They are not a library import or a Lake target.

Validation passed:

```text
lake build JoltBytecode JoltConstraints
```

The build includes the affected layout, initialization, memory-presence and
verifier-size modules, and retains the existing `sorry` and linter warnings.
`#print axioms` checked all 21 lemmas in `layout_facts.lean`, the six regression
lemmas, `initial_state_ram_present`, `new_panic_lt_termination`,
`HonestTrace.ram_present`, `HonestTrace.panic_lt_termination`,
`HonestTrace.witness_params_ram_minimum_of_nonempty`,
`VerifierSizes.chunks_fit_dorySetupLogN` and
`HonestTrace.witness_params_one_hot_fits_setup`: 34 lemmas in total.
Their dependencies are subsets of `propext`, `Classical.choice` and `Quot.sound`,
with the already allowed Sail `sys_enable_experimental_extensions` in the four
`HonestTrace` lemmas. No audited lemma depends on `sorryAx` or compiler-trust
axioms. The existing unfinished verifier RAM-bounds theorem remains unchanged.

All pre-existing changed/untracked files were checked against their initial
content hashes and preserved; this migration record is the only such file
edited for chunk 1. At that checkpoint no later chunk had been implemented.
The historical builds for chunks 1–3 also included the now-removed regression
module as a separate target. Its six lemma bodies are preserved unchanged in
this one-off command, run from the Lean repository root. Only a temporary
file is created, and it is removed when the command exits:

```sh
(
  layout_check_dir=$(mktemp -d /tmp/jolt-memory-layout.XXXXXX) || exit 1
  trap 'rm -f "$layout_check_dir/MemoryLayoutChecks.lean"; rmdir "$layout_check_dir"' EXIT
  cat > "$layout_check_dir/MemoryLayoutChecks.lean" <<'LEAN'
import JoltBytecode.JoltISA.JoltDevice

set_option autoImplicit false

namespace MemoryLayout.Tests

-- Rust's constructor regressions and defaults at the public pin:
-- https://github.com/a16z/jolt/blob/8bbb2357890928d8f83b00ca542879077c4d3d28/common/src/jolt_device.rs#L571-L633
-- https://github.com/a16z/jolt/blob/8bbb2357890928d8f83b00ca542879077c4d3d28/common/src/constants.rs#L23-L30
private def config : MemoryConfig :=
  { program_size := some 1024
    max_input_size := 4096
    max_output_size := 4096
    max_trusted_advice_size := 4096
    max_untrusted_advice_size := 4096
    stack_size := 4096
    heap_size := 32 * 1024 * 1024 }

-- Large advice remains admissible in both orderings, with the larger region first.
theorem large_trusted_first :
    (MemoryLayout.new { config with
      max_trusted_advice_size := 2 ^ 29, max_untrusted_advice_size := 2 ^ 28 }).map
      (fun layout => (layout.get_lowest_address.toNat, layout.trusted_advice_end.toNat,
        layout.untrusted_advice_start.toNat, layout.max_untrusted_advice_size.toNat,
        decide (layout.io_end.toNat ≤ JoltISA.RAM_START_ADDRESS))) =
      some (2 ^ 30, 2 ^ 30 + 2 ^ 29, 2 ^ 30 + 2 ^ 29, 2 ^ 28, true) := by decide +kernel

theorem large_untrusted_first :
    (MemoryLayout.new { config with
      max_trusted_advice_size := 2 ^ 28, max_untrusted_advice_size := 2 ^ 29 }).map
      (fun layout => (layout.get_lowest_address.toNat, layout.untrusted_advice_end.toNat,
        layout.trusted_advice_start.toNat, layout.max_trusted_advice_size.toNat)) =
      some (2 ^ 30, 2 ^ 30 + 2 ^ 29, 2 ^ 30 + 2 ^ 29, 2 ^ 28) := by decide +kernel

-- Each configuration pads I/O to exactly RAM_START_ADDRESS; both branch orders reject it.
theorem zero_start_rejected :
    (MemoryLayout.new { config with
      max_trusted_advice_size := 2 ^ 29, max_untrusted_advice_size := 2 ^ 29 }).isNone ∧
    (MemoryLayout.new { config with
      max_trusted_advice_size := 2 ^ 28, max_untrusted_advice_size := 2 ^ 30 }).isNone := by
  decide +kernel

-- Exact upper edge of the admissible padded size, then one extra eight-byte word.
private def boundaryConfig : MemoryConfig :=
  { config with
    max_trusted_advice_size := 0, max_untrusted_advice_size := 0,
    max_output_size := 0, max_input_size := 2 ^ 30 - 16 }

theorem io_padding_boundary :
    (MemoryLayout.new boundaryConfig).map
      (fun layout => (layout.get_lowest_address.toNat, layout.io_end.toNat)) =
        some (2 ^ 30, JoltISA.RAM_START_ADDRESS) ∧
    (MemoryLayout.new { boundaryConfig with max_input_size := 2 ^ 30 - 8 }).isNone ∧
    (MemoryLayout.new { boundaryConfig with max_input_size := 2 ^ 31 }).isNone := by
  decide +kernel

-- Alignment, I/O addition, padded multiplication, program addition and heap addition
-- overflow examples from Rust. No guest memory is allocated by these checks.
theorem arithmetic_overflow_rejected :
    (MemoryLayout.new { config with max_input_size := 2 ^ 64 - 1 }).isNone ∧
    (MemoryLayout.new { config with
      max_input_size := 2 ^ 64 - 8, max_output_size := 0, max_trusted_advice_size := 0,
      max_untrusted_advice_size := 0 }).isNone ∧
    (MemoryLayout.new { config with max_trusted_advice_size := 2 ^ 63 }).isNone ∧
    (MemoryLayout.new { config with program_size := some (2 ^ 64 - 1) }).isNone ∧
    (MemoryLayout.new { config with heap_size := 2 ^ 64 - 8 }).isNone := by
  decide +kernel

theorem invalid_configuration_rejected :
    (MemoryLayout.new { config with program_size := none }).isNone ∧
    (MemoryLayout.new { config with max_trusted_advice_size := 24 }).isNone ∧
    (MemoryLayout.new { config with max_untrusted_advice_size := 40 }).isNone := by
  decide +kernel

end MemoryLayout.Tests
LEAN
  lake env lean "$layout_check_dir/MemoryLayoutChecks.lean"
)
```

# Chunk 2 implementation and validation

Implemented locally on 2026-10-15 after Ari authorized continuing. LR.W, LR.D,
SC.W and SC.D were previously handwritten in `ExpansionsAutomated.lean`;
the Rust generator had never covered them. The added generator coverage now
reproduces those definitions, including their `rd = x0` branches.

The local generator needed three changes in addition to the previously saved
normalized-operand patch: permit the four LR/SC kinds; distinguish a
`VirtualAdvice` runtime value from the fixed `VirtualAdviceLoad` byte count;
and emit 64-bit immediate annotations for the remaining unary virtual rows.
The exact changes, including the generator README, are saved in
[`lean-gen-chunk2.patch`](./model_update/lean-gen-chunk2.patch). Applying both
saved patches in order to the two public-pin generator files reproduces the
local files byte for byte. No Rust tracer, expander or constraint source changed.

Reproduction, from a local Rust checkout at the public pin with both patches applied:

```sh
cargo +1.95 build --locked -p jolt-lean-gen
target/debug/jolt-lean-gen --lean --out /tmp/ExpansionsAutomated.lean
target/debug/jolt-lean-gen --all > /tmp/jolt-expansions.txt
```

Then, from this Lean checkout:

```sh
cmp /tmp/ExpansionsAutomated.lean JoltBytecode/JoltISA/ExpansionsAutomated.lean
lake env lean /tmp/ExpansionsAutomated.lean
lake build JoltBytecode JoltConstraints
```

All passed. The regenerated file has SHA-256
`84c17e2481ba4afab4bdfe564cb192ded316cf616dcf91c20424b603dc43991d`.
It contains 57 programs: 54 with two destination branches and three stores
without an `rd` split, totaling 111 arms and 819 emitted rows. LR.W, LR.D,
SC.W and SC.D emit respectively 9, 5, 26 and 12 rows per branch. None uses
runtime advice. The eight division/remainder programs each take one runtime
advice parameter; the four advice loads retain fixed byte counts 1, 2, 4 and 8.
The generated Lean file itself needed no changes.

Source correspondence was rechecked at `8bbb2357`:

- [Sequence metadata](https://github.com/a16z/jolt/blob/8bbb2357890928d8f83b00ca542879077c4d3d28/crates/jolt-program/src/expand/metadata.rs)
  uses descending remaining-row counts, marks the first row, and puts the source
  compressed flag on the last row. Native rows retain their source metadata.
  [Destination-zero dispatch](https://github.com/a16z/jolt/blob/8bbb2357890928d8f83b00ca542879077c4d3d28/crates/jolt-program/src/expand/materialize.rs)
  preserves side effects through temporary destinations and replaces pure
  destination-zero instructions with `ADDI x0, x0, 0`. This is a real bytecode
  instruction, distinct from the padding `NoOp`.
- The merged SC fix `0dad0d9e` computes success from the reservation register
  and target, through the RAM guard, XOR and SLTIU in
  [the shared expansion](https://github.com/a16z/jolt/blob/8bbb2357890928d8f83b00ca542879077c4d3d28/crates/jolt-program/src/expand/memory/shared.rs#L14-L26).
  The [SC.W tracer](https://github.com/a16z/jolt/blob/8bbb2357890928d8f83b00ca542879077c4d3d28/tracer/src/instruction/scw.rs#L46-L51)
  and corresponding SC.D path use that sequence and clear the reservation;
  they supply no advice. Existing Lean expansions and no-advice facts agree.
- The merged advice-length removal `3a290ae1` agrees with the existing Lean
  instruction set. No `VirtualAdviceLen` remains in either Lean library.
  [Runtime patching](https://github.com/a16z/jolt/blob/8bbb2357890928d8f83b00ca542879077c4d3d28/tracer/src/instruction/mod.rs#L215-L241)
  changes only `VirtualAdvice`'s execution payload, retaining its immediate and
  cached template. `VirtualAdviceLoad` instead reads the finite tape using its
  fixed byte-count immediate. Immediate normalization and widths were checked
  against the final operand formats, including signed branch/assert operands.

At Ari's request, removed the unused older `JoltISA.lrwProgram` and
`JoltISA.lrdProgram` module and its sole import. A repository reference search
found no callers. The four `*ProgramAuto` definitions used by
`SourceInstruction.expand` remain. LR/SC's separate Sail equivalence proofs
remain outside the proved scope; generator parity does not supply those proofs.
Updated their SC boundary comments and the merged-fix citation in `honest_trace`.

Validation also passed `rustfmt +1.95 --check --edition 2021` on the generator
and `cargo +1.95 clippy --locked --offline -p jolt-lean-gen --all-targets -- -D warnings`.
The first Rust build downloaded pinned Akita dependencies missing from the local
cache; subsequent build and clippy checks ran offline. The Lean build completed
8747 jobs with existing warnings. An axiom audit of the four LR/SC expansion
facts, `ExpansionFacts.expand_ok`, all six `expand_instruction_*` metadata facts
and the four relevant runtime-advice lemmas checked 15 lemmas. Dependencies are
subsets of `propext`, `Classical.choice` and `Quot.sound`; none has `sorryAx` or
compiler-trust axioms. No theorem premise or heartbeat setting changed.

# Chunk 3 correspondence audit

Audited locally on 2026-10-15 against the public pin. The unified representation
in PR #1996 (`a104dc63`) preserves the logical observations used by the existing
Lean extractors for completed modeled cycles. No Lean definition or proof body
needed changing. Source comments now cite the pinned row, capture and witness
implementations; stale capture references to `instruction/format/` were moved
to `instruction/registers/`.

| Source area | Correspondence and boundary |
|---|---|
| [Register captures](https://github.com/a16z/jolt/blob/8bbb2357890928d8f83b00ca542879077c4d3d28/tracer/src/instruction/mod.rs#L429-L450) | `capture_pre` precedes execution and `capture_post` records the destination afterwards. The R/I/load/store/branch/U/J, unary, alignment and virtual-shift capture implementations retain source values when registers alias. Lean's `Rs1Value`/`Rs2Value` read the pre-state and `rdValue` selects the requested pre/post state. Explicit x0 reads normalize to zero. HOST_IO still captures its encoded rd even though execution leaves it unchanged. |
| [Packed row accessors](https://github.com/a16z/jolt/blob/8bbb2357890928d8f83b00ca542879077c4d3d28/crates/jolt-riscv/src/trace_row.rs#L388-L464) | Loads share RAM read/write with destination post-value; stores share RAM write with rs2 and retain the old RAM word separately. The Lean RAM extractors already use these observations. Non-memory rows and padding supply zero RAM values. Signed increments subtract widened values rather than wrapping words. |
| [Operand presence](https://github.com/a16z/jolt/blob/8bbb2357890928d8f83b00ca542879077c4d3d28/crates/jolt-riscv/src/trace_row.rs#L500-L540) | Integer operand bits are independent of capture-presence bits. Register selectors and accumulated destination updates use encoded operands, including explicit x0; absent operands select no register. Lean's selectors agree. Missing Rust captures yield zero values but do not remove their encoded selectors. The checked constructor permits this; it does not establish that an execution happened. |
| [Register and RAM accumulation](https://github.com/a16z/jolt/blob/8bbb2357890928d8f83b00ca542879077c4d3d28/crates/jolt-witness/src/backend/trace/registers.rs#L26-L68) | Registers start at zero and record each column before its destination update. [RAM](https://github.com/a16z/jolt/blob/8bbb2357890928d8f83b00ca542879077c4d3d28/crates/jolt-witness/src/backend/trace/ram.rs#L22-L70) retains prior stores and overrides the current accessed cell with the captured pre-access value, including device observations. Padding preserves both accumulated arrays. Existing Lean folds implement these rules. Existing device/RAM completeness gaps are unchanged. |
| [Resolved bytecode PC](https://github.com/a16z/jolt/blob/8bbb2357890928d8f83b00ca542879077c4d3d28/tracer/src/trace_row.rs#L11-L47) | Conversion rejects source-only cycles and unresolved or oversized PCs before constructing a row. The [mapper](https://github.com/a16z/jolt/blob/8bbb2357890928d8f83b00ca542879077c4d3d28/crates/jolt-program/src/preprocess/bytecode.rs#L122-L211) resolves `(source address, remaining rows)` and reserves slot zero for NoOp. Lean's `rowIndex + 1` names the same expanded slot; its witness PC is not an execution-step count. Mapping alone does not compare every instruction operand against public bytecode. |
| [Proof prefix](https://github.com/a16z/jolt/blob/8bbb2357890928d8f83b00ca542879077c4d3d28/crates/jolt-program/src/execution/trace/data.rs#L27-L39) | `TraceData::new` trims only a suffix equal to the complete canonical default row. It preserves interior padding and noncanonical NoOp records. Lean represents actual modeled cycles with implicit trailing padding; it is not a model of every arbitrary `TraceData`. Field events and field-inline rows remain outside scope. |
| [Successor window](https://github.com/a16z/jolt/blob/8bbb2357890928d8f83b00ca542879077c4d3d28/crates/jolt-witness/src/backend/trace/cycle.rs#L99-L118) | The backend now reads `proof_rows()`, supplies a default row beyond the prefix and supplies no successor at `T - 1`. Both cases give next PC/source PC 0, next virtual/first flags 0 and next no-op 1. The existing Lean `Next*` helpers agree. `ShouldJump` deliberately treats a missing successor differently from an explicit NoOp; Lean already matches this, and its existing strict-padding proof handles the final cycle. Sizing-policy changes remain chunk 4. |

The [checked row constructor](https://github.com/a16z/jolt/blob/8bbb2357890928d8f83b00ca542879077c4d3d28/crates/jolt-riscv/src/trace_row.rs#L261-L385)
checks captured identities when present, load/store observation consistency,
reserved-zero PC use, no-op flags/effects, register encoding and immediate
magnitude. These are producer checks. In particular, it neither checks the
effective-address sum nor certifies instruction execution, and its reserved-zero
PC check does not establish full bytecode membership. None of these checks was
added to the Lean verifier relation or made a soundness premise.

Lean's `TraceRow` retains full pre/post states and derives observations from them.
It does not encode arbitrary absent or inconsistent Rust captures, arbitrary
interior NoOp rows, or Rust's private packed storage. Correspondence of the
completed tracer path remains a source-audited translation boundary, not a
formal Rust-to-Lean equivalence theorem. Soundness still quantifies over the
existing arbitrary `Witness`, rather than relying on Rust's constructor.

Validation passed:

```text
lake build JoltBytecode JoltConstraints
```

The build completed 8747 jobs, retaining existing warnings. The final source
versions of the three capture-value helpers also passed individual Lean checks
after their citation line ranges were corrected. All 22 Lean files edited in
this chunk were compared with their pre-edit copies after removing comments:
every declaration, proof and option is unchanged.

An axiom audit checked 24 existing completeness lemmas: the three register
selectors, the two source reads, destination read/write and register history;
the two load equalities, store-source equality and two RAM read/write selection
results; PC/source-PC bytecode reads; all five successor shifts; ShouldJump;
and the four inline/jump/branch/ordinary successor-PC results. None depends on
`sorryAx`. All use the already allowed Sail
`sys_enable_experimental_extensions` in addition to the standard Lean axioms.
One also retains an existing compiler-trust dependency:
`honestWitness_nextUnexpandedPCEqPCPlusImmIfShouldBranch` depends on
`branch_target_toNat._native.bv_decide.ax_1_5`, from the unchanged bit-vector
sign-extension step in `Completeness/NextUnexpandedPCEqPCPlusImmIfShouldBranch.lean`.
This dependency violates the axiom policy despite predating the migration.
The main-theorem audit below widens this finding to eight compiler-trust
axioms. Their kernel-checked replacements are deferred review follow-ups above;
chunk 3 adds no axiom or premise, and accepting its source audit does not close
these repairs.

Preservation check at the review checkpoint: all seven pre-existing Rust files
are byte-identical to their starting hashes. Of the 37 pre-existing Lean-tree
files recorded at chunk 2's start, 29 are byte-identical; six have only the
source-comment updates described above, and two are the migration/review records.
Their pre-existing code and proof bodies are preserved. No commit, push or work
on chunks 4–6 was performed.

## Review follow-up: main completeness axiom baseline

After Ari widened the repair scope, `lake build JoltConstraints.Completeness.All`
passed (8682 jobs). The following scratch audit was run against that build:

```lean
import JoltConstraints.Completeness.All

#print axioms HonestTrace.allConstraints_rust_sizes
```

The complete output was:

```text
'HonestTrace.allConstraints_rust_sizes' depends on axioms: [propext,
 sorryAx,
 sys_enable_experimental_extensions,
 Classical.choice,
 Quot.sound,
 JoltConstraints.branch_target_toNat._native.bv_decide.ax_1_5,
 JoltConstraints.halfword_aligned._native.bv_decide.ax_1_5,
 JoltConstraints.lookupEntryCorrect_RangeCheckAligned._native.bv_decide.ax_1_241,
 JoltConstraints.rev8_32._native.bv_decide.ax_1_10,
 JoltConstraints.windowMaskB_entry._native.bv_decide.ax_1_5,
 JoltConstraints.windowMaskH_entry._native.bv_decide.ax_1_5,
 JoltConstraints.windowMaskW_entry._native.bv_decide.ax_1_5,
 JoltConstraints.word_aligned._native.bv_decide.ax_1_5]
```

All eight `_native.bv_decide` dependencies are required repairs, not just the
branch-offset lemma. Seven come through
[`LookupEntryProofHelpers.lean`](../JoltConstraints/Completeness/Helpers/LookupEntryProofHelpers.lean):
`halfword_aligned`, `word_aligned`, `lookupEntryCorrect_RangeCheckAligned`,
`rev8_32`, and the three `windowMask*_entry` lemmas. The other is
[`branch_target_toNat`](../JoltConstraints/Completeness/NextUnexpandedPCEqPCPlusImmIfShouldBranch.lean).
The expected existing `sorryAx`, three standard axioms and allowed Sail
`sys_enable_experimental_extensions` are shown separately in the same output.
This list is the baseline; rerun the main-theorem audit after each repair batch
and after theorem cleanup rather than assuming the dependency set is fixed.

The native calls in `Values.lean`, `Natives/Sd.lean` and `StoreFamily/Splice.lean`
do not occur in this main completeness theorem's current axiom list. Neither
does `rev8w_eq`, despite its native call in `LookupEntryProofHelpers.lean`.
Recheck their reachability from both final main theorems before closing the
axiom-policy item. No proof was changed in this review follow-up.

The constants source comment in `JoltDevice.lean` now names `8bbb2357` and links
to the pinned `common/src/constants.rs`. The local constants file matches that
public revision; the Lean constants themselves are unchanged.

# All upstream commits in the migration interval

`git rev-list 00508a09..8bbb2357` contains exactly 36 commits. The table lists
all of them, oldest first. **Relevant** means a definition, proof correspondence,
source citation or scope record needs attention in the current migration.
**Not relevant** means no change is required to the current decoded-RV64,
base-field mathematical model: it does not assert formal verification of the
changed implementation. File diffs and the in-scope source paths were inspected;
this is an impact inventory, not a completed correctness audit of every commit.

| Commit | Relevant to this migration? | Reason / checklist item |
|---|---|---|
| [`acc152e0`](https://github.com/a16z/jolt/commit/acc152e0) | Relevant | Checked layout construction adds the nonzero I/O-start condition; item 1. |
| [`65b599c8`](https://github.com/a16z/jolt/commit/65b599c8) | Not relevant | Optimizes Spartan outer arithmetic kernels; does not change the modeled row equations. |
| [`b83b37bb`](https://github.com/a16z/jolt/commit/b83b37bb) | Not relevant | Adds Metal Fp64/Ext2 arithmetic, outside the base relation. |
| [`8e19897a`](https://github.com/a16z/jolt/commit/8e19897a) | Not relevant | Akita chunk profiles are separate from the base prover policy; record for the later Akita model. |
| [`b48a06f1`](https://github.com/a16z/jolt/commit/b48a06f1) | Not relevant | Adds stack-canary faults to the x86 tracer; the modeled interpreter already checks canary stores. |
| [`74679691`](https://github.com/a16z/jolt/commit/74679691) | Not relevant | Agent/comment/test policy documentation only. |
| [`0e63605b`](https://github.com/a16z/jolt/commit/0e63605b) | Not relevant | Adds a PCS-generic standalone Spartan/HyperKZG path; PCS protocols are outside this theorem. |
| [`03330745`](https://github.com/a16z/jolt/commit/03330745) | Relevant | Moves RV64 R1CS definitions into jolt-claims; refresh equation correspondence and citations, item 5. |
| [`36c7b67a`](https://github.com/a16z/jolt/commit/36c7b67a) | Not relevant | Remaps host build paths for reproducible ELF files; the model begins with a decoded image. |
| [`629ed77b`](https://github.com/a16z/jolt/commit/629ed77b) | Not relevant | Akita dependency/adapter update; no base-ISA or modeled constraint change. |
| [`09a93bb5`](https://github.com/a16z/jolt/commit/09a93bb5) | Not relevant | Removes unused verifier/opening dependencies, error variant and generator README; no modeled check changes. |
| [`cdb97faf`](https://github.com/a16z/jolt/commit/cdb97faf) | Relevant | Recheck tracer source references after dead-code removal; removed PC normalization was the identity, item 6. |
| [`efc96205`](https://github.com/a16z/jolt/commit/efc96205) | Not relevant | Deletes unused kernel/poly utilities and lookup-module imports; table meanings remain unchanged. |
| [`ceef2e59`](https://github.com/a16z/jolt/commit/ceef2e59) | Not relevant | Metal Ext2 arithmetic implementation only. |
| [`9ecf8718`](https://github.com/a16z/jolt/commit/9ecf8718) | Not relevant | Changes Akita native trace-column batching and lattice packing; separate from base constraints. |
| [`3d282f2f`](https://github.com/a16z/jolt/commit/3d282f2f) | Relevant | Removes proof/witness helper APIs and moves decoder tests; refresh extraction/source correspondence, items 3 and 6. |
| [`66039c2e`](https://github.com/a16z/jolt/commit/66039c2e) | Not relevant | Changes when obsolete kernel state is dropped, not its mathematical relation. |
| [`eea40ca8`](https://github.com/a16z/jolt/commit/eea40ca8) | Not relevant | Cargo.lock clap version only. |
| [`510d4672`](https://github.com/a16z/jolt/commit/510d4672) | Not relevant | Cargo.lock libc version only. |
| [`43ab84a5`](https://github.com/a16z/jolt/commit/43ab84a5) | Not relevant | Cargo.lock cc version only. |
| [`74f40fd8`](https://github.com/a16z/jolt/commit/74f40fd8) | Not relevant | Cargo.lock alloy-eips version only. |
| [`7f779b2a`](https://github.com/a16z/jolt/commit/7f779b2a) | Not relevant | Cargo.lock alloy-consensus version only. |
| [`322c3df6`](https://github.com/a16z/jolt/commit/322c3df6) | Not relevant | CI installation action update only. |
| [`bfcece09`](https://github.com/a16z/jolt/commit/bfcece09) | Not relevant | P256 inline advice canonicality fix; inline/precompile guests are outside SourceInstruction. |
| [`03f689ab`](https://github.com/a16z/jolt/commit/03f689ab) | Not relevant | Akita dependency and adapter maintenance, outside the base model. |
| [`4c7e46f2`](https://github.com/a16z/jolt/commit/4c7e46f2) | Not relevant | Lazy InstructionReadRaf kernel evaluation; no change to the modeled lookup relation. |
| [`9a1841bd`](https://github.com/a16z/jolt/commit/9a1841bd) | Not relevant | Fuses lookup address scans in optimized kernels; no changed lookup equation. |
| [`0dad0d9e`](https://github.com/a16z/jolt/commit/0dad0d9e) | Relevant | Merged SC success fix; compare generated expansions and tracer advice with Lean, item 2. |
| [`a104dc63`](https://github.com/a16z/jolt/commit/a104dc63) | Relevant | Unifies execution/proof rows and their checks/accessors; item 3. |
| [`8b6099f7`](https://github.com/a16z/jolt/commit/8b6099f7) | Relevant (scope record) | SDK limb conversions emit opcode 0x7B field-inline instructions, outside SourceInstruction; detailed check below. |
| [`d84dafea`](https://github.com/a16z/jolt/commit/d84dafea) | Relevant | Besides kernel context plumbing, introduces ExecutionDimensions and checked sizing; items 3 and 4. |
| [`b9795769`](https://github.com/a16z/jolt/commit/b9795769) | Not relevant | Fixes x86 compiled-jump dispatch; the current semantics use the interpreter. |
| [`355c7c61`](https://github.com/a16z/jolt/commit/355c7c61) | Not relevant | Adds characteristic-two field implementations; the base theorem requires characteristic above 2^128. |
| [`ba9743d3`](https://github.com/a16z/jolt/commit/ba9743d3) | Not relevant | Adds binary-field sumcheck support, outside the deterministic base constraint relation. |
| [`3a290ae1`](https://github.com/a16z/jolt/commit/3a290ae1) | Relevant | Removes advice-length instructions and changes runtime-advice documentation; item 2. |
| [`8bbb2357`](https://github.com/a16z/jolt/commit/8bbb2357) | Relevant (scope/setup audit) | Whole precommitted bytecode replaces table chunks, including lattice packing; selector chunks remain, items 5 and 6. |

## SDK limb conversions: scope checked

At the public pin, [`field_to_limbs!`](https://github.com/a16z/jolt/blob/8bbb2357890928d8f83b00ca542879077c4d3d28/jolt-sdk/src/lib.rs#L270)
calls `field_inline::to_limbs`, and `field_from_limbs!` calls `from_limbs`.
The [implementations](https://github.com/a16z/jolt/blob/8bbb2357890928d8f83b00ca542879077c4d3d28/jolt-sdk/src/field_inline.rs#L60)
emit `FIELD_ADVICE_LIMB`, `FIELD_ASSERT_ZERO`, `FIELD_LOAD_IMM` and
`FIELD_LOAD_ACCUMULATE_FROM_REGISTER/MEMORY`, as appropriate. The encoders
[`field_inline_r_word` and `field_inline_i_word`](https://github.com/a16z/jolt/blob/8bbb2357890928d8f83b00ca542879077c4d3d28/jolt-sdk/src/lib.rs#L76)
use `FIELD_INLINE_OPCODE = 0x7B`. Lean's `SourceInstruction` contains RISC-V
and the listed `0x5B` custom instructions, with no field-inline constructors.
Thus guests containing these field-inline conversions are outside the current
theorem. This is an existing type-level limit, not a new premise. It is distinct
from the `0x0B`/`0x2B` precompile exclusion. No guest build was needed or run for
this source-level emission check.

## Source audits refreshed at the public pin

These are source checks dated 2026-10-15; they do not mark any migration proof
complete. The affected Lean comments must be updated as their chunks land.

- **Verifier sizes:** [`compute_min_ram_k` and `compute_max_ram_k`](https://github.com/a16z/jolt/blob/8bbb2357890928d8f83b00ca542879077c4d3d28/crates/jolt-program/src/preprocess/ram.rs#L96)
  retain their formulas and checked failures. In particular, the maximum still
  divides the byte count by eight before rounding. The verifier still checks
  power-of-two trace/RAM domains, the maximum trace length, and these RAM bounds
  in [`validate_inputs`](https://github.com/a16z/jolt/blob/8bbb2357890928d8f83b00ca542879077c4d3d28/crates/jolt-verifier/src/verifier.rs#L378).
  Item 4 still needs the Lean correspondence and overflow cases.
- **Dory setup and Layer 0:** the ordinary full-program path passes no extra
  program candidates in [`from_shared`](https://github.com/a16z/jolt/blob/8bbb2357890928d8f83b00ca542879077c4d3d28/crates/jolt-prover/src/dory/preprocessing.rs#L54).
  [`setup_total_vars`](https://github.com/a16z/jolt/blob/8bbb2357890928d8f83b00ca542879077c4d3d28/crates/jolt-prover/src/dory/preprocessing.rs#L196)
  retains the trace-plus-chunk/advice maximum, and
  [`canonical_setup_log_n`](https://github.com/a16z/jolt/blob/8bbb2357890928d8f83b00ca542879077c4d3d28/crates/jolt-dory/src/scheme.rs#L120)
  rounds it to an even count. The pinned Cargo.lock still selects
  `dory-pcs 0.4.2`. Re-read its `evaluation_proof.rs:341–352,394–399` locally:
  `point.len() = nu + sigma`, `nu ≤ sigma`, and
  `sigma ≤ setup.max_log_n / 2` give the setup-capacity bound. The current
  Layer 0 argument remains about this full-program path; precommitted program
  candidates and Akita remain outside its setup definition. This does not
  assert PCS security or eliminate the setup-construction checks in item 4.
- **Device and MMU:** [`JoltDevice::load/store`](https://github.com/a16z/jolt/blob/8bbb2357890928d8f83b00ca542879077c4d3d28/common/src/jolt_device.rs#L146)
  still read the panic flag, set it on any store to the panic byte, ignore other
  panic/termination stores, and return zero for termination reads.
  [`Mmu::assert_effective_address`](https://github.com/a16z/jolt/blob/8bbb2357890928d8f83b00ca542879077c4d3d28/tracer/src/emulator/mmu.rs#L112)
  still restricts device stores to output/panic/termination, rejects the I/O
  gap, protects the canary on stores and checks heap bounds. The doubleword
  paths at [load](https://github.com/a16z/jolt/blob/8bbb2357890928d8f83b00ca542879077c4d3d28/tracer/src/emulator/mmu.rs#L611)
  and [store](https://github.com/a16z/jolt/blob/8bbb2357890928d8f83b00ca542879077c4d3d28/tracer/src/emulator/mmu.rs#L721)
  retain the start-address RAM check and per-byte device dispatch. These match
  the address-check part of `TracerAddressChecks`; alignment, peripheral
  dispatch and device-value agreement remain distinct.
- **#2044 status:** a read-only GitHub API check on 2026-10-15 reports
  [#2044](https://github.com/a16z/jolt/issues/2044) **open**, with `closed_at = null`
  and `updated_at = 2026-10-10T14:51:57Z`. Michael's comments have not been
  assessed here; Ari will supply them later. Do not infer his intended semantics
  or a resolution from the issue state. They are not needed for the first
  migration chunks, but must be reviewed before revisiting this finding or
  changing its temporary premise.

# Proof obligations that the pin update does not resolve

- **Device-memory agreement:** panic stores set the flag independently of the
  stored value; termination stores are ignored and loads return zero. Their
  load/store behavior is unchanged in the diff from `43cc043` to the new pin.
  Input/advice store rejection and the separately listed address candidates
  remain in the soundness plan. `TracerAddressChecks` supplies address checks
  only, not device values or successful execution by itself.
- **Stopping:** B6's witness ending at a jump before the tracer's PC stall
  remains a separate obligation. The new configuration path still checks
  `ends_in_jump`, not the tracer's stopping condition.
- **Fixed-tape reconstruction:** after removing length queries, concatenating
  the low bytes of answers is a possible route, not yet a proof. Narrow reads
  can differ in intermediate high bits. In the nonzero-destination branch the
  destination itself holds those bits; the x0 branch uses v40. Compare runs at
  completed expansion boundaries, or prove a relation preserving the live low
  bits within the expansion. Also account for HostIO, whose live mode can
  append tape bytes. Do not describe the complete modeled language as read-only.
- **SC coverage and reservation correspondence:** the merged fix removes the
  old success-advice gap. Removing `NoStoreConditional` still requires the
  ordinary instruction/expansion proof coverage already planned. Correspondence
  between virtual reservation registers and Jolt's emulator reservation remains
  a separate model obligation.

These are proof/specification obligations, not evidence that adopting this pin
alone repairs soundness. Known reproductions and unconfirmed candidates retain
their separate status in [model_review.md](../JoltConstraints/model_review.md)
and [soundness.md](./soundness.md).

# Chunk 4 policy separation

The existing theorem and its supporting proofs used the corrected formula.
Before changing their names, the dependency comparison is:

| Policy | Trace padding | RAM size | Completeness dependencies |
|---|---|---|---|
| Rust at `8bbb2357` | checked `rows + 1`, checked next power of two, floor 256, reject above preprocessing maximum | checked image extent; checked next power of two of `max(touched, image_end)` | Acceptance alone does not imply `RamFits`: a touched slot equal to `ram_K` is possible. The review bridge transfers the existing completeness result when this boundary is excluded. |
| Existing corrected Lean policy | mathematical padding with the same floor and maximum guard | `2 ^ clog 2 (max (touched + 1) image_end)` | `prover_config_ram_fits` → `witness_params_ram_fits` → the main completeness theorem; the other configuration and witness-parameter lemmas also use this policy. |

The existing policy is retained under `HonestTrace.corrected_prover_config`;
its witness parameters and lemmas receive the `corrected_` prefix. The main
theorem is renamed `HonestTrace.allConstraints_corrected_sizes`. Its statement
and proof are otherwise unchanged, including all existing premises and gaps.
`HonestTrace.prover_config` now denotes the checked Rust policy. Initially this separation did not transfer completeness to the Rust policy.
The requested bridge below now does so away from the exact boundary; it does not resolve
[#1951 item 4](../bug-report/ram-k-off-by-one/). The corrected variant remains
a mathematical policy; it is not a replacement implementation of Rust's
checked constructor. Ari accepted this separation and the bridge by reading; final build and axiom
results are recorded below.

The new `prover_config.lean` summarizes the physical rows as
`ExecutionDimensions` (row count, last jump flag, nonzero address bounds), then
models `derive_from_dimensions` for the base/Dory build on a 64-bit host.
It rejects trace addition/rounding overflow, a nonempty non-jump ending,
addresses or image starts below the layout, image extent addition overflow,
RAM rounding overflow, and a padded length above the preprocessing maximum.
It preserves zero as the no-access sentinel. Error variants map to `none`.
`checkedTraceLength_power`, `checkedTraceLength_bounds` and
`checkedRamSize_power` justify omitting Rust’s redundant final geometry checks
after successful checked rounding. `deriveFromDimensions_sizes` exposes the
successful subcomputations, last-jump condition and public length bound.
The record’s Nat addresses represent the ordered nonzero 64-bit bounds produced
by the trace summary; this is not a model of arbitrary malformed external
summaries or a new verifier check.

`verifier_sizes.lean` already matches the checked minimum/maximum formulas in
[`preprocess/ram.rs:96–132`](https://github.com/a16z/jolt/blob/8bbb2357890928d8f83b00ca542879077c4d3d28/crates/jolt-program/src/preprocess/ram.rs#L96-L132).
In particular, the maximum still divides by eight **before** rounding. The
base committed chunks remain 4/8 bits and virtual lookup chunks 16/32 bits,
with threshold `logT = 25`, in
[`one_hot_config`](https://github.com/a16z/jolt/blob/8bbb2357890928d8f83b00ca542879077c4d3d28/crates/jolt-prover/src/config.rs#L204-L234).
Those formulas, the verifier-bound proofs and Layer 0’s bound of 72 are unchanged.
The existing `corrected_witness_params_ram_bounds` gap remains explicit.

## One-off sizing checks

Six temporary lemmas check padding thresholds, the two trace overflow paths,
the empty/nonempty jump rule and public maximum, address rejection and summary
bounds, the two image overflow paths, and the known Rust RAM boundary. All use
`decide +kernel`; their axiom lists contain only `propext` and, where needed,
`Quot.sound`. No regression module or Lake target is added to the source tree.
After `lake build JoltConstraints.prover_config`, reproduce with:

```sh
scratch=$(mktemp /tmp/jolt-sizing.XXXXXX.lean)
trap 'rm -f "$scratch"' EXIT
cat > "$scratch" <<'LEAN'
import JoltConstraints.prover_config

private def config : MemoryConfig := {
  max_input_size := 0, max_trusted_advice_size := 0, max_untrusted_advice_size := 0,
  max_output_size := 0, stack_size := 0, heap_size := 64, program_size := some 8 }
private def layout : MemoryLayout :=
  (MemoryLayout.new config).get (by decide +kernel)
private def dimensions (rows : Nat) (jump : Bool) (bounds : Option (Nat × Nat)) :
    ExecutionDimensions := ⟨rows, jump, bounds⟩
private def sizes (rows : Nat) (jump : Bool) (bounds : Option (Nat × Nat))
    (imageStart imageWords maximum : Nat) : Option (Nat × Nat) :=
  (ProverConfig.deriveFromDimensions (dimensions rows jump bounds) layout
    imageStart imageWords maximum).map fun c => (c.trace_length, c.ram_K)

-- Padding thresholds, including the largest successful host-domain rounding.
theorem padding_boundaries :
    [0, 255, 256, 2^63-1].map ProverConfig.checkedTraceLength =
      [some 256, some 256, some 512, some (2^63)] := by decide +kernel
-- Addition overflow and next-power-of-two overflow are separate failure paths.
theorem padding_overflows :
    ProverConfig.checkedTraceLength (2^64-1) = none ∧
    ProverConfig.checkedTraceLength (2^63) = none := by decide +kernel
-- Empty runs pass the jump check; nonempty runs must end in a jump.
theorem jump_and_limit :
    sizes 0 false none 0 1 256 = some (256, 2) ∧
    sizes 1 false none 0 1 256 = none ∧
    sizes 1 true none 0 1 256 = some (256, 2) ∧
    sizes 0 false none 0 1 255 = none := by decide +kernel
-- Minimum access and image start below the layout are rejected.
theorem checked_addresses :
    sizes 1 true (some (1, 0x80000030)) 0 1 256 = none ∧
    sizes 1 true none 1 1 256 = none ∧
    ExecutionDimensions.observe (ExecutionDimensions.observe none 0) 16 = some (16,16) ∧
    [24,0,16,32,24].foldl ExecutionDimensions.observe none = some (16,32) := by decide +kernel
-- Image extent overflows before rounding, or rounds beyond the host domain.
theorem image_overflows :
    sizes 1 true none 0 (2^64-1) 256 = none ∧
    sizes 1 true none 0 (2^63) 256 = none := by decide +kernel
-- Lowest = RAM_START - 16; address RAM_START + 48 maps to slot 8.
-- Rust picks ram_K = 8, whereas the corrected max(touched+1,image_end) rounds to 16.
theorem rust_ram_boundary :
    sizes 1 true (some (0x80000030, 0x80000030)) 0 1 256 = some (256,8) ∧
    2 ^ Nat.clog 2 (max (8+1) 2) = 16 := by decide +kernel

#print axioms padding_boundaries
#print axioms padding_overflows
#print axioms jump_and_limit
#print axioms checked_addresses
#print axioms image_overflows
#print axioms rust_ram_boundary
LEAN
lake env lean "$scratch"
```

# Chunk 5 constraint and bytecode correspondence

The local source comparison covers all 25 Rust files cited by
[`constraints.md`](../JoltConstraints/constraints.md). Comparing each file at
the previous `43cc043` baseline and the public pin gives **23 byte-identical
files** and two explained changes:

- [`composed/r1cs/rv64.rs`](https://github.com/a16z/jolt/blob/8bbb2357890928d8f83b00ca542879077c4d3d28/crates/jolt-claims/src/protocols/composed/r1cs/rv64.rs)
  moved from `jolt-r1cs/src/constraints/rv64.rs`. Its imports and
  `ConstraintMatrices` type paths changed; its coefficients and equations did not.
- [`geometry/bytecode.rs:533–559`](https://github.com/a16z/jolt/blob/8bbb2357890928d8f83b00ca542879077c4d3d28/crates/jolt-claims/src/protocols/jolt/geometry/bytecode.rs#L533-L559)
  now uses `JoltInstruction::from` instead of fallible conversion with a NoOp
  fallback. Chunk 3 audited that unified instruction representation. The
  row columns, flags and selector formulas for the modeled instructions are unchanged.

| Modeled equations | Checked source families | Result at the pin |
|---|---|---|
| 01–22 | RV64 equality/product rows; Spartan product remainder | Equations unchanged; R1CS source path refreshed. |
| 23–26 | RAM read/write, address RAF, public output and public arrays | Byte-identical cited sources. |
| 27–31 | Spartan shift and non-wrapping successor polynomial | Byte-identical; final-cycle successor is still zero. |
| 32–36 | Instruction input virtualization and register read/write | Byte-identical. |
| 37–42 | RAM/register histories, instruction read/RAF and lookup kinds | Byte-identical; existing completeness gaps remain. |
| 43–53 | Bytecode row values, selectors and entry slot | Same formulas; unified conversion as above. |
| 54–62 | Booleanity, RAM weight, address virtualization and chunk weights | Byte-identical cited sources. |

All constraint declarations are unchanged. Their source mapping now uses
public-pin permalinks and the relocated RV64 path. The checklist count is
corrected to match its existing boxes: 57 checked, four FIXME and one TODO;
this does not claim new proofs or resolve the deferred compiler-trust audit.

The base verifier’s checks were reread at
[`validate_inputs:331–442`](https://github.com/a16z/jolt/blob/8bbb2357890928d8f83b00ca542879077c4d3d28/crates/jolt-verifier/src/verifier.rs#L331-L442)
and [`validate_ram_remap_base:980–999`](https://github.com/a16z/jolt/blob/8bbb2357890928d8f83b00ca542879077c4d3d28/crates/jolt-verifier/src/verifier.rs#L980-L999):
layout equality, lowest address greater than eight, public input/output bounds,
power-of-two trace/RAM domains, the public trace maximum, checked RAM bounds,
instruction-profile support and trimmed outputs. They agree with the existing
`ConstraintContext`, `WitnessParams`, `public_io` and `validate_inputs`
representation in the modeled base instruction scope. Protocol consistency,
commitments, transcript seeding and field-inline profile checks stay outside
this constraint-level theorem. No verifier condition was converted into a new
theorem premise.

The selector dimensions still compute
[`bytecode_d = ceil(bytecode_log_k / committed_chunk_bits)`](https://github.com/a16z/jolt/blob/8bbb2357890928d8f83b00ca542879077c4d3d28/crates/jolt-claims/src/protocols/jolt/geometry/dimensions.rs#L415-L445),
and [`BytecodeRa(usize)` remains](https://github.com/a16z/jolt/blob/8bbb2357890928d8f83b00ca542879077c4d3d28/crates/jolt-claims/src/protocols/jolt/ids.rs#L330-L353).
The changed `ProgramBytecode` commitment is the precommitted program table,
which is outside the model. Layer 1’s selectors and proofs therefore keep their
existing mathematical definitions.

# Chunk 6 source recheck and historical citations

The completed 36-commit inventory above was not restarted. The remaining
checks follow the source areas used by the current theorem:

- **Layer 0 / Dory setup:** full-program
  [`preprocess:57–62`](https://github.com/a16z/jolt/blob/8bbb2357890928d8f83b00ca542879077c4d3d28/crates/jolt-prover/src/dory/preprocessing.rs#L57-L62)
  supplies no extra program candidates;
  [`setup_total_vars:187–210`](https://github.com/a16z/jolt/blob/8bbb2357890928d8f83b00ca542879077c4d3d28/crates/jolt-prover/src/dory/preprocessing.rs#L187-L210)
  takes the trace/chunk and advice maxima, and
  [`canonical_setup_log_n:120–126`](https://github.com/a16z/jolt/blob/8bbb2357890928d8f83b00ca542879077c4d3d28/crates/jolt-dory/src/scheme.rs#L120-L126)
  rounds to even. The changed committed-program candidate is excluded by that
  mode choice; it does not change the modeled bound of 72.
- **Source of `one_hot_fits_setup`:**
  [`stage8/verify.rs:132–145`](https://github.com/a16z/jolt/blob/8bbb2357890928d8f83b00ca542879077c4d3d28/crates/jolt-verifier/src/stages/stage8/verify.rs#L132-L145)
  uses [`final_opening_point`](https://github.com/a16z/jolt/blob/8bbb2357890928d8f83b00ca542879077c4d3d28/crates/jolt-claims/src/protocols/jolt/geometry/committed_openings.rs#L164-L203),
  whose native main point has `logT + chunkBits` variables. The locally installed
  `dory-pcs` **0.4.2**, locked by `Cargo.lock`, checks `point.len() = nu + sigma`
  and `nu ≤ sigma` at `src/evaluation_proof.rs:341–354`, then
  `sigma ≤ setup.max_log_n / 2` at lines 394–401. These imply the modeled point
  size bound. This is the acceptance-bound source audit, not a PCS security proof.
- **Device/MMU:** `JoltDevice::load/store` bodies are unchanged;
  [`tracer/src/emulator/mmu.rs`](https://github.com/a16z/jolt/blob/8bbb2357890928d8f83b00ca542879077c4d3d28/tracer/src/emulator/mmu.rs#L112-L164)
  changes RAM observation type names/imports and removes an unused helper.
  Its address checks, alignment, device dispatch and RAM read/write behavior
  are unchanged. The current load/store line references are in the earlier
  source recheck. `TracerAddressChecks` and the existing soundness theorem
  remain unchanged. Discussion of #2044 remains deferred pending Michael’s comments.
- **Entry, padding and history:** `get_first_pc` still maps zero to slot zero;
  [`step_emulator:328–338`](https://github.com/a16z/jolt/blob/8bbb2357890928d8f83b00ca542879077c4d3d28/tracer/src/lib.rs#L328-L338)
  still stops on the previous PC, initially zero. The shift verifier and
  `eq_plus_one`, RAM/register history verifiers, `derivations.rs` and `lt.rs`
  are byte-identical to the previous audit. The strict earlier-write order,
  all-cycle final RAM sum and final-cycle zero shift are unchanged.
- **Decoded instructions / lookups:** decoder production changes remove the
  advice-length case; the remaining large diff moves tests. No decoder branch
  returns the pseudo NoOp; `noop_for` still emits ADDI x0,x0,0. Ordinary
  instruction bodies, `interleave.rs` and lookup-table bodies are unchanged;
  table prefix/suffix modules only remove unused count constants. The old
  advice-length instruction is already removed in the reviewed chunks.
  Binary decoding, serialization, accelerated backends, Akita, binary fields,
  field-inline instructions and program/PCS commitments do not expand the
  decoded base theorem’s scope.

The required old-pin search used:

```sh
rg -n --hidden '43cc043' -g '!.git/**' -g '!.lake/**'
```

Every original occurrence was classified as follows. Current claims were
rechecked before updating; historical evidence was retained.

| File / occurrence | Classification and action |
|---|---|
| `metadata.lean`, `Layer4/Interleave.lean`, `Layer1/Bytecode.lean`, `Layer5/DeviceMemoryObstruction.lean` | Current decoder, interleave, final-cycle and termination-device claims; rechecked and pinned to `8bbb2357`. |
| `model_review.md`: previous baseline and dated device finding | Historical; retained, with a link to the current source recheck. |
| `model_review.md`: Akita canonical-address guard | Current scope claim; rechecked unchanged and updated. |
| `methods/soundness.md`: NoOp, wrapping/layout arithmetic, Akita guard, entry zero, Layer 0 setup, Layer 1 shift, register/RAM history, arithmetic/interleave/table entries | Current correspondence claims; rechecked at the public pin and updated. |
| `methods/soundness.md`: PR #2049 and #2039 provenance, previous SC behavior, removed advice-length candidate, dated device/MMU candidates, historical Akita scope decision | Historical records; retained. Device source behavior was rechecked above; no issue discussion or premise change. |
| `bug-report/sc-forced-failure/README.md`, `bug-report/device-readonly-stores/issue.md` | Historical reproduction/report provenance; retained without rewriting the reports. |
| `methods/model_update.md` | Previous baseline, comparison endpoints and this citation audit; historical/meta references retained. |

The search found no additional occurrences in `blog/`, hidden workspace files,
or the saved generator patches. No active Lean source citation remains at the
old pin. Deferred review note 3 is resolved.

## Chunk 4 review follow-up: used Rust sizing and the exact boundary

Ari requested a bridge from Rust acceptance to the corrected policy, instead of
leaving the new Rust model unused. `prover_config_facts.lean` now proves:

- `ExecutionDimensions.checkedTouched_fold`: the streaming address bounds and
  the corrected policy’s list scan produce the same largest remapped slot;
  successful checked bounds also imply every nonzero access is above the base.
- `ProverConfig.checkedTraceLength_eq_padded`: successful checked Rust padding
  equals `padded_trace_length`.
- `HonestTrace.prover_config_eq_corrected_iff`: **given Rust acceptance**, the
  corrected constructor returns that same config **if and only if**
  `highest_touched_slot < config.ram_K`.
- `HonestTrace.prover_config_highest_le`: Rust acceptance always gives
  `highest_touched_slot ≤ config.ram_K`. The excluded case is therefore
  precisely equality with `ram_K`.

`HonestTrace.witness_params` now constructs parameters from the actual checked
Rust config. Its logarithm bounds use `checkedTraceLength_bounds`,
`checkedTraceLength_power` and `checkedRamSize_power`; the padding bridge uses
`checkedTraceLength_eq`, and both paths use `deriveFromDimensions_sizes`.
All new sizing definitions and public lemmas have callers.

`HonestTrace.allConstraints_rust_sizes` is now a new corollary in
`Completeness/All.lean`. It calls `allConstraints_corrected_sizes` through the
bridge, using the actual Rust config and parameters. Its explicit
`ramFits : highest_touched_slot < config.ram_K` is the strict-inside condition
Ari requested. `prover_config_highest_le` proves that the only excluded case
is equality with the RAM domain size. The
corrected theorem’s existing statement, premises and proof are preserved under
its renamed definitions. The new corollary inherits the existing completeness
`sorryAx` and eight native bit-vector dependencies; it does not repair them or
claim completed completeness. No soundness premise was added or changed.

# Final validation for chunks 4–6 and the review follow-ups

Passed on 2026-10-15:

```text
lake build JoltConstraints.Completeness.All  # bridge and caller: 8684 jobs
lake build JoltBytecode JoltConstraints     # final version: 8748 jobs
```

`Completeness/All.lean` imports `prover_config_facts.lean`, which imports
`prover_config.lean`. The root library imports `Completeness/All.lean`, so both
new modules are checked by the default library build. The six temporary sizing
checks above passed. `git diff --check` passed.

A temporary Lean file importing `JoltConstraints` audited **33 declarations**:
the five original checked-sizing lemmas, sixteen renamed sizing/witness lemmas,
the corrected completeness theorem, the main soundness theorem, four Layer 0
bounds, the streaming-summary and padding bridges, the config-equivalence and
highest-slot lemmas, the actual-config logarithm bounds, and the new Rust
completeness corollary. The import and declarations were:

```lean
import JoltConstraints

#print axioms ProverConfig.checkedTraceLength_eq
#print axioms ProverConfig.checkedTraceLength_bounds
#print axioms ProverConfig.checkedTraceLength_power
#print axioms ProverConfig.checkedRamSize_power
#print axioms ProverConfig.deriveFromDimensions_sizes
#print axioms HonestTrace.corrected_prover_config_trace_length
#print axioms HonestTrace.corrected_prover_config_last_jump
#print axioms HonestTrace.corrected_prover_config_ram_fits
#print axioms HonestTrace.corrected_prover_config_ram_K_ge_two
#print axioms HonestTrace.corrected_prover_config_log_trace_length_lt
#print axioms HonestTrace.corrected_prover_config_log_ram_K_lt
#print axioms HonestTrace.corrected_witness_params_chunk_config
#print axioms HonestTrace.corrected_witness_params_trace_length
#print axioms HonestTrace.corrected_witness_params_padded
#print axioms HonestTrace.corrected_witness_params_bytecode_domain
#print axioms HonestTrace.corrected_witness_params_ram_chunks_pos
#print axioms HonestTrace.corrected_prover_config_ram_K_pow
#print axioms HonestTrace.corrected_witness_params_ram_fits
#print axioms HonestTrace.corrected_witness_params_ram_minimum_of_nonempty
#print axioms HonestTrace.corrected_witness_params_ram_bounds
#print axioms HonestTrace.corrected_witness_params_one_hot_fits_setup
#print axioms HonestTrace.allConstraints_corrected_sizes
#print axioms JoltInstance.soundness
#print axioms JoltConstraints.VerifierSizes.adviceVars_le_64
#print axioms JoltConstraints.VerifierSizes.dorySetupLogN_le_72
#print axioms JoltConstraints.ConstraintContext.chunkBits_le_72
#print axioms JoltConstraints.ConstraintContext.chunk_card_lt_char
#print axioms ExecutionDimensions.checkedTouched_fold
#print axioms ProverConfig.checkedTraceLength_eq_padded
#print axioms HonestTrace.prover_config_eq_corrected_iff
#print axioms HonestTrace.prover_config_highest_le
#print axioms HonestTrace.prover_config_log_bounds
#print axioms HonestTrace.allConstraints_rust_sizes
```

Results:

- Every new sizing/bridge proof has only a subset of `propext`,
  `Classical.choice`, `Quot.sound` and the allowed Sail constant
  `sys_enable_experimental_extensions`. None introduces `sorryAx`, a native
  evaluator axiom or compiler trust.
- `allConstraints_rust_sizes` and `allConstraints_corrected_sizes` have
  **identical** axiom sets: the standard/Sail axioms, the existing `sorryAx`,
  and exactly the eight native bit-vector axioms in the earlier baseline.
  The earlier baseline used the old theorem name before the policy separation;
  it now describes the inherited dependencies of both results. Their repair
  remains deferred, as requested.
- The main soundness theorem retains its existing `sorryAx` and standard/Sail
  dependencies; the sizing migration did not change its statement or premises.
- Comparing the 35 affected existing Lean files against the pre-task content
  snapshots, with comments and the intended identifier renames normalized,
  confirms that the existing mathematical declarations and proofs are unchanged.
  The only additional existing-file code is the import and new Rust corollary.
  Both new modules contain no `sorry`, axiom declaration, `bv_decide`,
  `native_decide` or heartbeat override.
- All 2,371 snapshotted files in the Rust checkout are byte-identical to their
  pre-task contents. Existing Lean edits outside this migration were preserved.
  No commit, push, Rust edit or persistent regression target was added.

The migration-pending status is lifted. This closes adoption of the public pin
within the stated model scope, not the existing completeness/soundness gaps.
Work stops here for review; native-proof repair and discussion of #2044 remain
separate and deferred.

## Follow-up, 2026-10-15: unused sizing results deleted

`JoltInstance.completeness` now takes `JoltInstance.InLanguage`, which includes
Jolt's prover accepting the trace, and uses the corrected sizes through
`HonestTrace.corrected_prover_config_isSome`. Nothing used the Rust-sizes
corollary any more, so Ari's rule (keep only theorems the main theorems use)
removed it and the results only it used: `HonestTrace.allConstraints_rust_sizes`,
`prover_config_eq_corrected_iff`, `prover_config_highest_le`,
`prover_config_log_bounds`, `HonestTrace.witness_params`,
`HonestTrace.highest_touched_slot`, and `ProverConfig.checkedTraceLength_bounds`,
`checkedTraceLength_power` and `checkedRamSize_power`. The `#print axioms`
lines above that name them no longer apply. The off-by-one they characterized
remains reproduced in `bug-report/ram-k-off-by-one/`.
