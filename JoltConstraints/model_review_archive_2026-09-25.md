# Archived model review — 25 September 2026

This preserves the branch's earlier local review during the fork replay. It is
historical context; see [model_review.md](model_review.md) for the current
status and deferred-work inventory. Paths, commit IDs, and validation claims
below describe the older checkout and should be rechecked before use.

> [!IMPORTANT]
> The FIRST GOAL is always to check that the Lean translation matches the Rust source code.
> Only then do we try to close proofs.
> Writing correct definitions and theorem statements is more important than completing proofs in this project.
> NEVER compromise the fidelity of the translation to force an equivalence or completeness proof to pass.

> [!NOTE]
> **Project goal: correctness of Jolt's honest witness construction.**
> Faithfully translate Rust's execution, trace conversion, NP witness construction, and constraint equations into Lean, then prove that the witness generated for an admissible execution satisfies those constraints.
> The execution model is also checked against Sail, the ISA reference.
> The admissibility conditions must reflect Rust's actual requirements and must not exclude a Rust-produced counterexample just to make a theorem true.
> If a constraint fails, identify whether the fault is in the Lean translation or in Rust and preserve the counterexample until the underlying issue is resolved.
> We exposed bugs in Jolt by refusing to compromise on the translation or force equivalence proofs to pass first.
> Keeping the translations faithful and investigating the failing claims led to concrete counterexamples for `CSRRS x0,mstatus,x0` and a taken self-branch.
> We reproduced those cases in Rust and checked that its generated witness violated the corresponding constraint; an unfinished Lean proof alone was not the evidence.
> The historical reproductions are documented below, and the user reports upstream fixes that still need to be checked and reflected in Lean.

## Start here

The current Lean branch is `feat/witness-on-updated-isa` at `94231e2` in `/Users/ari.biswas/Lean/jolt-qed-public`.
Commit `c751079` merged `feat/npWitness` into the reviewed ISA branch, and `94231e2` added a native-dispatch witness regression.
The whole `JoltBytecode` tree matches `fix/isa-rust-correspondence` at `8bd5438`, the head of [ISA PR #13](https://github.com/LayerZero-Labs/jolt-qed/pull/13).
The witness and constraint sources from `feat/npWitness` were preserved; the only additional constraint-tree file is [Tests/NativeDispatch.lean](Tests/NativeDispatch.lean).
Both libraries built successfully, and all 12 regression modules passed.
Existing proof placeholders remain, and the integration introduced no new `sorry`s.

This document is deliberately Git-ignored and is available in this working folder only unless copied separately.
The numbered items such as **audit #13** below are local review IDs, not GitHub issue numbers.
Numbered constraints such as **constraint (13)** refer to the equations in [constraints.md](constraints.md).
That checklist still contains an outdated summary saying most completeness targets use `sorry`; use the current inventory in this document and inspect the actual theorem premises.

### Rust update pending verification

The user reports that the previously deferred problems have been fixed in Jolt and is pulling the Rust changes while this handoff is updated.
The pull produced Rust revision `3cb4e24361ae2006e9713ae65d58a3fa51fd0518`.
Only the definitions relevant to the later constraint (15) audit, and the two fixes below, have been checked against that revision.
Of the 25 commits in `e012da54..3cb4e24`, two address historical findings and are now ported to the Lean ISA: `f012bfb1` lowers `CSRRS x0, csr, x0` to the canonical no-op (constraint (13)), and `66f35559` makes a zero-mask VirtualSRLIW return 0 (audit #17).
No commit in that range addresses the taken self-branch (constraint (16)) or zero RAM chunks (audit #13).
The detailed Rust findings below describe the historical reference [e012da54c3bb26a6436b5ca74e86c19bb39695ad][rust-commit], reviewed on 23 September.
Later ISA work used the local Rust checkout at `7dfe8a0f829a4ab3e9126eb5ac5b5b15208cf5fc`.
The Rust checkout is `/Users/ari.biswas/Work-with-A16z/jolt`.
After the pull, record its exact HEAD and local modifications, inspect the relevant fixes, and rerun the affected examples before updating Lean.
Keep the old revision-pinned evidence as historical evidence; do not describe its counterexamples as confirmed failures of the newly pulled revision.
A Rust fix does not by itself update this Lean model or close its outstanding proof obligations.

### Correspondence that must survive the update

Rust execution, trace conversion, witness extraction, and constraint equations are the reference for their Lean translations.
Sail is the ISA reference used by the execution-equivalence theorems.
A translation repair must preserve the behavior of its stated reference, including Rust-produced cases whose witnesses fail a constraint.
Do not change a witness, weaken an equation, or exclude a Rust-produced case solely to make a completeness proof pass.
Preserve the existing proofs and their explicit assumptions while checking the effect of upstream changes.
The earlier blanket instruction to defer all completeness work or restore proved targets to placeholders is superseded by the proof work already present on this branch.

- During an instruction body, embedded Sail `PC` represents the decoded instruction's address (`self.address`), and embedded Sail `nextPC` represents Rust's already advanced `cpu.pc`.
- [prepareSource](trace.lean) establishes those values once per source instruction; rows inside its expansion pass the state through without another PC increment.
- JAL and JALR update the represented Rust PC directly; the Sail-equivalence bundles state the readability and target-alignment conditions needed for comparison with Sail's checked jump.
- Native source dispatch rewrites destination `x0` to a temporary for LD, JAL, and JALR, and to `ADDI x0,x0,0` for the 22 pure arithmetic/logical kinds covered by `pureWritebackNativeInstr`.
- The temporary is `v40` for the top-level allocation modeled by these native helpers.
- `execInstr` executes an already-expanded final row with its supplied operands; witness extraction reads that final row and the full Jolt state, including temporary writes.
- The native equivalence statements include source dispatch, while [JoltProgramRow](trace.lean) still lacks a general certificate that its rows came from Rust's source expander; that remaining gap is audit #3.

For example, source `JALR x0,x0,6` at address `0x1000`, with advanced `cpu.pc = 0x1004`, executes a final row targeting `v40`.
It writes `v40 = 0x1004`, sets the represented Rust PC to `6`, and leaves the instruction-address field at `0x1000`.
Witness extraction therefore captures destination value `0x1004` and lookup output `6`.
Target `6` is not four-byte aligned, but Rust's instruction body still executes; Sail equivalence requires the separate alignment condition.
[NativeDispatch checks](Tests/NativeDispatch.lean) cover the execution and capture behavior without projecting away the temporary write.

## Historical constraint (13) counterexample; upstream fix to recheck

**Unrestricted completeness of `RdWriteEqLookupIfWriteLookupToRd` has a counterexample in the current Lean model and the historical Rust reference.**
This is not a claim about the newly pulled Rust revision.

The report is in the existing **[bug-report/ directory](../bug-report/)**: **[CSRRS honest-witness counterexample](../bug-report/issue.md)**. Its commit is `2e276cb`, `docs(bug-report): document CSRRS completeness issue (tentative)`. This report records the earlier local reproduction; this update does not establish its current upstream issue status.

Rust explicitly [exempts CSRRS from the generic rd=x0 rewrite][rust-csr-exemption], because its expansion is expected to handle that case. The [CSRRS expansion][rust-csrrs] checks rs1=x0 first and directly emits `ADDI rd, vCSR, 0`, then returns; it does not special-case rd=x0 in that branch. The emitted final row does not pass through the generic source rewrite again.

Thus `CSRRS x0, mstatus, x0` emits `ADDI x0, v39, 0`. With `v39 = 9`, Rust accepts the execution and proof-trace conversion, and its witness gives:

| Column | Value |
| --- | --- |
| `WriteLookupOutputToRD` | `1` |
| `LookupOutput` | `9` |
| `RdWriteValue` | `0` |

The actual constraint requires `1 × (0 − 9) = 0`, but the residual is `−9`. The report includes the source program, tested revision, and stage-1 `SpartanOuter` sumcheck citations. The check used the Rust tracer, `build_trace_rows`, witness extractors, and R1CS matrix row; an end-to-end prover/verifier run was not performed.

[The Lean constraint file](Constraints/RdWriteEqLookupIfWriteLookupToRd.lean) preserves the equation. Its `honestWitness_rdWriteEqLookupIfWriteLookupToRdStatement` is currently a `def … : Prop`, not a proved theorem and not an admitted theorem. The previous `DestinationsNormalized` workaround is absent and must not be described as a completed repair.

The [CSRRS execution-equivalence theorem](../JoltBytecode/InstructionEquivalence/Instructions/System/Csrrs.lean) compares execution with Sail. Both executions discard the write to x0, so that theorem can hold while the witness constraint fails. Its checked dependencies contain no `sorryAx`.

**Status after the pull:** Rust `f012bfb1` emits `ADDI x0, x0, 0` when both `rs1` and `rd` are x0, and [`csrrsProgram`](../JoltBytecode/JoltISA/Expansions/System.lean) now does the same.
The CSRRS equivalence proof was updated for the new branch and still has no `sorryAx`.
The completeness target remains a proposition definition: fixed `JoltProgramRow`s are not yet tied to the expander (audit #3), so a raw `ADDI x0, v39, 0` row is still admissible.
[DestinationNormalization.lean](Tests/DestinationNormalization.lean) keeps that row as the historical example and checks the new lowering.
The Rust example was not rerun on `3cb4e24`; the fix and its added expansion test were inspected.
Retain this example with its old revision as the explanation of the original defect.

## Earlier repairs retained in the current branch

The Rust checks and build counts in this table are historical records from the earlier review.
The latest Lean integration validation is recorded separately below.

| Earlier issue | Current repair | Evidence and remaining boundary |
| --- | --- | --- |
| **#1 — rows unrelated to control flow** | [`JoltTrace.successor`](trace.lean) requires consecutive bytecode indices inside an expansion. At a source boundary it fetches the address produced by `nextPC` and enters an ordinary row or a sequence beginning. | [TraceBoundary checks](Tests/TraceBoundary.lean) pass. Full bytecode validity remains **#3**. |
| **#2 — missing PC preparation** | [`prepareSource` and `sourceLength`](trace.lean) seed PC/nextPC once per source instruction. Source length comes from the expansion's final row; state passes through unchanged inside the expansion. Instructions still execute through `JoltISA.execInstr`. | Lean checks pass. Rust checks cover cached/uncached fetch, compressed fetch, JAL, compressed JALR, taken/untaken BEQ, and a five-row compressed LW expansion. This does not discharge all PC completeness statements. |
| **#4 — static VirtualAdvice payload** | [`runtimeAdvice`, `withRuntimeAdvice`, and `IsBytecodeTemplate`](trace.lean) separate the static zero template from each execution's payload. Only `VirtualAdvice` takes a `BitVec 64` payload; other instructions take `Unit`. Destination and immediate remain fixed. | [RuntimeAdvice checks](Tests/RuntimeAdvice.lean) pass. A Rust DIVU loop produces payloads 3 and 5 at the same static slot. Full source-expansion/provenance correspondence remains part of **#3**, and HostIO is separately **#5**. |
| **#7 — architectural/virtual register aliasing** | [Canonical register encoding](register_encoding.lean) is required by `JoltProgramRow`. Addresses 0–31 use architectural storage; 32–127 use virtual storage. Raw low-numbered virtual tags cannot bypass that map. | [RegisterEncoding checks](Tests/RegisterEncoding.lean) pass, including all 128 addresses and x0. Initial register/history conditions remain **#6**. |
| **#10 — oversized physical trace** | [`honestWitness`](honest_witness.lean) requires the trace to fit the witness cycle domain, as [Rust does][rust-witness-config], so cycle columns cannot drop an execution suffix while final RAM uses that suffix. The requirement is now subsumed by the stricter **#11** padded-length condition. | [TraceLength checks](Tests/TraceLength.lean) and `lake build JoltConstraints` pass. Committed as `82a090e`. Completion and final-state policy remain **#9**. |
| **#11 — prover padding** | [`ProverPaddedFor`](witness.lean) requires the cycle count [Rust derives][rust-prover-config] from the physical row count: the smallest power of two with a trailing padding row, with a 256-cycle floor in the ordinary build or 4096 in Akita. `honestWitness` and its constraint targets require it. `ShouldJump` and `NextIsNoop` retain Rust's distinct missing-successor behavior. | [ProverPadding checks](Tests/ProverPadding.lean) cover both floors, exact-boundary growth, and rejection of an arbitrary larger domain. Full `lake build` passes (8,571 jobs). Committed as `86831ab`. Linking a particular compiled backend/profile to its floor remains **#21**. |
| **#12 — bytecode witness domain** | [`BytecodeDomainFor`](witness.lean) requires `2^logBytecodeK` to equal Rust's preprocessed bytecode size: insert the leading no-op, round up to a power of two, and use at least two rows. [`honestWitness`](honest_witness.lean) requires this condition, so its bytecode selectors cannot truncate an expanded row or use an arbitrary larger domain. The former separate `bytecodeFits` theorem premises are removed. | [BytecodeDomain checks](Tests/BytecodeDomain.lean) cover empty, exact-boundary, and padded sizes plus rejection of smaller and larger domains. Focused build passes (3,522 jobs); full `lake build` passes (8,571 jobs). Committed as `dc31af5`. Other preprocessing validity remains **#3**. |
| **#13 — dimension bounds (partial)** | [`WitnessParams`](witness.lean) now requires the prover's actual one-hot policy: `(chunkBits, virtualChunkBits) = (4, 16)` for `logT < 25`, or `(8, 32)` for `logT ≥ 25`. It also bounds power-of-two domain exponents to fit a 64-bit `usize`. [`TraceBackendGridFits`](witness.lean) states the trace backend's separate 32 GiB allocation check for a given field size. | [WitnessDimensions checks](Tests/WitnessDimensions.lean) cover both policy branches, rejection of 128-bit chunks, a field-size-dependent allocation failure, and the permitted zero-RAM-chunk formula case. Committed as `83d0f93`. The zero-chunk case remains open below; the allocation predicate must be supplied when modeling that backend's materialization. |
| **#18 — final operand domains** | [Final `Instr` rows](../JoltBytecode/JoltISA/Instruction.lean) carry decoded 64-bit immediates, signed 128-bit branch/assertion immediates, and architectural or virtual alignment bases. `Encoded` constructors decode source immediates once; [execution](../JoltBytecode/JoltISA/Semantics.lean), [metadata](metadata.lean), and witness helpers consume the final operands. Row and trace conditions bound Nat helper immediates and compact signed immediates to Rust's accepted sizes. | [FinalOperands checks](Tests/FinalOperands.lean) pass. The Rust `jolt-lean-gen` translator now emits the same `ExpansionsAutomated.lean` byte for byte and defaults to this checkout. The full `lake build` passes (8,571 jobs). This repairs the stated representation mismatch; it does not establish full execution-to-witness completeness. |
| **#19 — missing VirtualXORROTL1** | The ISA, shared value helper, witness selectors, metadata, lookup index/output, and fixed table implement `rs1 XOR rotate_left(rs2, 1)`. | [VirtualXORROTL1 checks](Tests/VirtualXORROTL1.lean) pass. The Rust check passed 32 executions, covering eight operand pairs and ordinary, aliased, and x0 destinations. ISA changes are in commit `f42ae4f`; related constraint/test changes were included in `dfd9e93`. |
| **#24 — destination regression imports** | [DestinationNormalization.lean](Tests/DestinationNormalization.lean) now imports `JoltConstraints.metadata` instead of the deleted normalization module, and removes the obsolete `open JoltConstraints`. | Both libraries and this regression build successfully together (8,572 jobs). Existing execution/witness checks are unchanged; no normalization restriction was restored. |
| **#23 — constraint checklist documentation** | [constraints.md](constraints.md) records the earlier reviewed Rust revision, predicates, counterexamples, and final-row load capture; its proof-status introduction needs refreshing after subsequent proof work. Its machine-specific Rust links were replaced with revision-pinned GitHub links. | All 62 checklist entries point to existing Lean files. The 25 cited Rust files exist and are unchanged at local Rust HEAD `7dfe8a0f` relative to the reviewed `e012da54` revision. |

### #8 — destination handling and load capture repaired for the identified cases

The hidden LD destination rewrite has been removed from [ISA execution](../JoltBytecode/JoltISA/Semantics.lean), [captured destination values](witness_helpers/rd_value.lean), [destination selectors](witness_helpers/rd_wa.lean), and [fixed bytecode selectors](Constraints/BytecodeReadSelectors.lean). These now use the destination actually present in the final row. Source-level expansion and execution of an already-expanded row are separate stages.

Normal native source dispatch for guest `LD x0` first rewrites its destination to an allocated temporary, modeled here by `ldNativeInstr` using `v40`.
A nonzero load through that normal dispatch therefore writes the temporary; it does not execute the raw final `LD x0` case below.
This distinction also applies to JAL and JALR and must not be removed from the native equivalence statements.

The current Lean model still represents the historical CSRRS counterexample above.
The identified load-capture gap in audit #8 is repaired:

- Rust's [compact trace conversion][rust-trace-conversion] checks that a load's captured RAM value equals its captured destination value.
- Directly executing a supplied final `LD x0` row loading 9 discards the write, and the historical Rust conversion check rejects it; the same final row targeting `v40` converts successfully.
- [`JoltTraceRow.loadCaptureMatches`](trace.lean) now requires the captured pre-execution RAM word to equal the captured post-execution destination for an `LD`. This rejects the raw `LD x0` of 9 without changing the destination or excluding an `LD x0` of 0.
- [LoadCapture checks](Tests/LoadCapture.lean) cover both x0 cases, a virtual destination, and preservation of the CSRRS-generated `ADDI x0` row. Broader preprocessing and trace-conversion correspondence remains **#3**, not an unresolved load-capture condition.

## Current completeness inventory

The 62 numbered constraint files were inspected at Lean commit `94231e2` and updated below for the constraint (40) and (41) proofs.

| Source status | Count | Constraint numbers |
| --- | --- | --- |
| `honestWitness` theorem present and no textual `sorry` in its file | 48 | (02)–(12), (18)–(25), (27)–(33), (40)–(41), (43)–(62) |
| File still contains `sorry` | 12 | (01), (14)–(15), (17), (26), (34)–(39), (42) |
| Unrestricted target retained as a proposition definition | 2 | (13), (16) |

These are source counts, not an audit of transitive axioms or a claim that all theorem premises follow from Rust execution.
Use `#print axioms` when checking whether an individual theorem depends on `sorryAx` through a helper or unfinished table.
For example, constraint (12) requires passing assertion operands, constraint (58) requires a positive RAM-chunk count, and other targets have explicit domain, padding, or initialization premises.
There is no theorem establishing that every Rust execution produces a witness satisfying all 62 constraints.

The earlier five-proof batch is included in this inventory, followed by the later Spartan, bytecode, RAM, and expansion proof work.
Preserve those proofs; the old placeholder-first instruction is no longer the current workflow.
The 12 unfinished targets and the two retained counterexamples require individual review against the pulled Rust revision and the model's remaining gaps.

### Instruction-lookup operand proofs — constraints (40) and (41)

- [Constraint (40)](Constraints/LeftLookupOperandEqInstructionRaf.lean) and [constraint (41)](Constraints/RightLookupOperandEqInstructionRaf.lean) are proved with their existing statements and premises. No witness, metadata, or constraint definition changed. These proofs are uncommitted.
- Both proofs split on the final row's instruction. `instructionRafFlag` is the same expression as `hasCombinedLookupOperands`, so RAF rows give zero on both sides of (40) and the full 128-bit index on both sides of (41).
- For interleaved rows, the odd bits of `interleaveLookupOperands` recover rs1, and the even bits recover `Imm` or `Rs2Value`, including the shift-mask immediates. FENCE, LD, SD, and VirtualHostIO have index 0 and zero instruction inputs.
- The shared bit lemmas are in [LookupOperandData.lean](Constraints/LookupOperandData.lean): `interleaveLookupOperands_testBit`, `sum_testBit_eq_mod`, `bitVec_toNat_cast_eq_sum`, `sum_interleave_odd_bits`, and `sum_interleave_even_bits`.
- `#print axioms` for both theorems lists only the Sail model axioms (`load_reservation`, `match_reservation`, `plat_term_write`, `sys_enable_experimental_extensions`) plus `propext`, `Classical.choice`, and `Quot.sound`. This is the same set as `instructionRead_honest`; there is no `sorryAx`.
- `lake build JoltBytecode JoltConstraints` passed (8,575 jobs). The 12 regression modules were not rerun, and no Rust checks were involved.

## Constraint (15): restart from the Rust program model

The experimental program-validity framework and synthetic two-JAL fixture were removed at the user's request.
Constraint (15) is restored to its earlier statement with its proof pending (`sorry`); this restoration does not establish that the statement is correct.
Study Rust's program construction, execution, and preprocessing before proposing any new premises.
Every modeling decision must follow Rust or Sail, with source evidence; conditions chosen merely to close a proof are unacceptable.

## Approved address uniqueness and constraint (53)

**Current direction:** the user requires an interactive revision of the trace
model, preserving the working model and known failing cases. Further modeling
changes are being developed from scratch in [trace_new.lean](trace_new.lean).
The initial copy of the old model was removed following the user's correction.
The fresh candidate contains only `JoltProgram.entryAddress : BitVec 64`,
matching Rust's `entry_address`; it is an incomplete starting point, not a
complete program model. Each subsequent modeling definition needs approval.
No live module imports the candidate. Its `JoltProgram` name overlaps the old
model, so the two modules must be checked independently. Initialization and
entry-index construction are not yet represented in the fresh candidate.

**Correction to the reported status of (53):** the corollary below is a
conditional proof. It does not complete the intended Rust program-to-witness
correspondence: its entry-row/initial-PC premises do not establish program
loading or preprocessing correspondence. Do not report (53) as closed for that
intended model merely because this corollary compiles or has no `sorryAx`.

The user approved `SequenceLayout.addressSequenceUnique` in [trace.lean](trace.lean):
two program rows with the same address and the same remaining count (using zero
for `None`) must be the same row. This applies to unpadded expanded bytecode.
Rust revision `3cb4e24361ae2006e9713ae65d58a3fa51fd0518` supports this property:
`BytecodePCMapper::try_new` rejects repeated address runs, and `validate_run`
checks a descending count ending at zero. These functions are in
`crates/jolt-program/src/preprocess/bytecode.rs`.

The first constraint proof using this hypothesis is an additional corollary for
**(53), selecting the public entry slot**. The existing theorem assumed that
the first trace row's index equals the supplied entry slot. The approved
`honestWitness_bytecodeRaAtEntryEqOne_of_address` corollary in
[BytecodeRaAtEntryEqOne.lean](Constraints/BytecodeRaAtEntryEqOne.lean) instead
takes an entry program row whose address matches the initial PC, and derives
the first trace row's index. It retains the existing domain, RAM-fit, padding,
and nonempty-trace conditions. Its conclusion uses the entry program index plus
one for the leading no-op slot. Rust's `entry_bytecode_index` calls
`BytecodePCMapper::get_first_pc(entry_address)` at this boundary.

[ProgramLayout.lean](ProgramLayout.lean) contains only proved helper theorems:
`row_at_offset` follows the existing countdown and rules out interior entry
rows; `entry_address_unique` uses it and the approved uniqueness hypothesis to
show that two entry rows at the same address coincide. This covers ordinary
rows and virtual expansions. No additional modeling definitions or conditions
were introduced, and no existing constraint or theorem statement was changed.

Validation: `lake build JoltConstraints` passed (3,524 jobs). `#print axioms`
shows only `propext` and `Quot.sound` for both layout helpers; the new constraint
corollary additionally has the existing Sail model axioms and `Classical.choice`.
None depends on `sorryAx`. No Rust execution tests or regression modules were
run for this proof-only change. The numbered proof inventory is unchanged,
because (53) already had a proof under its explicit slot-equality premise.
Constraint (15) remains pending; address uniqueness alone does not establish
source-expansion provenance or the positions of jumps within expansions.

The user requires explicit approval of every modeling-code change. Present
the Rust evidence, proposed Lean code, and justification before applying one.
Tests are allowed without prior approval; proved corollaries are allowed.

## Outstanding work

These items record remaining Lean gaps and historical Rust questions.
Upstream status must be checked against the pulled revision before deciding which repairs remain necessary.
They are not all Rust bugs, and unfinished proofs are not evidence of a translation error.

| ID | Current issue and consequence | Next work |
| --- | --- | --- |
| **#3 — partial repair** | [`SequenceLayout`](trace.lean) now includes the approved address/count uniqueness condition, excluding duplicate ordinary addresses; entry-address uniqueness is proved in [ProgramLayout.lean](ProgramLayout.lean). Address range/alignment, run-length limits, and complete expansion metadata/source provenance remain uncovered. | Continue from actual Rust preprocessing/expansion requirements, obtaining approval for further modeling changes. Preserve the PC repair above. |
| **#5 — committed as `0c91622`** | [`VirtualHostIO`](../JoltBytecode/JoltISA/HostIO.lean) now models live advice appends, replay suppression, fixed-register arguments, returned-trap handling, invalid print/cycle events, and checked/unchecked pointer arithmetic. Host execution configuration is carried by the state and `init_state`. | See commit `0c91622` and the [local issue](../issues/virtual-host-io.md). Full libraries and 20 focused Lean checks pass; Rust's advice-write test passes. Byte loads use the existing memory abstraction: heap bounds and full MMU/capture correspondence remain separate open work. |
| **#6** | [`init_state`](trace.lean) exists, but `JoltProgram.initialState` remains arbitrary. [RegistersVal](witness_helpers/registers_val.lean) begins at zero regardless of that state. RAM/image, device initialization, and advice cursor conditions are also not tied to the Rust loader. Some theorem statements separately assume zero registers. | Establish initialization/loader correspondence and use it consistently at the construction boundary. Do not treat scattered theorem assumptions as a completed model repair. |
| **#9** | [`JoltTrace`](trace.lean) intentionally permits prefixes and the empty trace. [Final RAM reconstruction](witness_helpers/ram_state.lean) nevertheless supplies the completion/termination word, and `honestWitness` accepts these traces. [`Terminated`](execution_conditions.lean) exists but is only required by selected statements. | Separate prefix traces from completed executions at the witness/final-state boundary. Keep Rust's actual stopping rule, including self-branches. |
| **#13 — remaining** | Rust's [`JoltFormulaDimensions::try_from`][rust-dimensions] explicitly accepts `ram_k = 1`, which gives zero RAM chunks. Rust's [virtual `RamRa` witness][rust-ram-ra] is zero on padding, while its [zero-chunk committed-product expression][rust-ram-product] is one. The [Lean RAM product target](Constraints/RamRaEqChunkProduct.lean) therefore retains a separate positive-chunk premise. This is a possible Rust constraint/witness disagreement, not a reason to reject `ram_k = 1` in the dimension model. | Check whether a full Rust proof can reach `ram_k = 1`; resolve that behavior before changing the constraint or completeness target. Keep field-size-dependent trace-backend allocation checks at the materialization boundary. |
| **#14** | [JoltIOLayout/JoltIOState](../JoltBytecode/JoltISA/Core.lean) can contain overlapping, reversed, unaligned, or misplaced regions and oversized buffers. [RamFits](witness_domain.lean) checks accesses, not layout or buffer validity. | Model the layout and input/advice-buffer checks performed by [Rust][rust-device]. |
| **#15 — included in fresh-model scope; pending** | Rust heap-end and stack-canary access checks are not represented by the current memory model. A Sail-successful access plus `RamFits` does not establish them. | The user has approved including these checks in the fresh `trace_new.lean` model scope, superseding the earlier deferral. Present Rust-backed Lean definitions for approval before implementing them; preserve the live model. See the scope decision below. |
| **#16** | [Initial/final RAM image helpers](witness_helpers/ram_state.lean) sample only the selected RAM domain and can ignore an unremappable overlay start. `RamFits` supplies no image/buffer/final-marker fit check, even for an empty trace. [Rust validates these images][rust-ram]. | Validate all initial/final words and device overlays, not only accessed addresses. |
| **#17 — VirtualSRLIW ported; other shifts unchecked** | Historically, for a raw VirtualSRLIW row with value 1 and mask 0, Lean's `ctz 0 = 0` gave 1, while [Rust's lookup function][rust-srlw] and table gave 0; the reference tracer panicked with overflow checks enabled and the x86 tracer wrote 1. Rust `66f35559` now computes `(x as u32).checked_shr(mask.trailing_zeros()).unwrap_or(0)`, so a zero mask gives 0; the same commit changes the x86 tracer's emitter. [`jolt_virtual_srliw_value`](../JoltBytecode/JoltISA/Values.lean) now returns 0 for mask 0, which also updates the witness lookup output, and [ZeroMaskShift.lean](Tests/ZeroMaskShift.lean) checks value 1 with mask 0. Normal SRLIW expansion uses only nonzero masks; its equivalence proof still has no `sorryAx`. | The other `ctz`-based shifts (VirtualSRLI, VirtualSRAI, VirtualSRAIW, VirtualROTRI, VirtualROTRIW) still use `ctz 0 = 0`. Check Rust's zero-mask behavior for each before changing them. |
| **#20** | [WitnessType](witness.lean) and [honestWitness](honest_witness.lean) lack separate TrustedAdvice/UntrustedAdvice witness families. Advice bytes are overlaid into RAM, but the [Rust witness-family correspondence][rust-oracle] is not modeled. | Add the required family/binding correspondence. This is separate from repaired per-execution VirtualAdvice. |
| **#21** | Program commitments and instruction-profile configurations have no complete correspondence in this model. Rust exposes BytecodeChunk/ProgramImageInit paths and validates supported profiles. | State the supported configuration precisely, then track the required representation. This is a coverage question, not evidence that every backend intermediate must become a Lean field. |
| **#22 — old workflow concern superseded** | [ProductEqLeftInputMulRightInput](Constraints/ProductEqLeftInputMulRightInput.lean) is proved, and [LookupOutputEqInstructionReadRaf](Constraints/LookupOutputEqInstructionReadRaf.lean) retains a proved padding branch and an unfinished execution branch. | Preserve the existing proof work and review the remaining execution/table obligation; do not restore placeholders merely to follow the old workflow note. |

## Other historical Rust behavior and completeness questions

The examples below were checked against the old reference, not the Rust revision being pulled now.

| Item | Evidence and status | Action |
| --- | --- | --- |
| **Taken self-branch; constraint (16)** | The earlier Rust run of `BEQ x0, x0, 0` at `0x80000000` terminates under the repeated-PC rule and converts successfully. With a padding successor, `ShouldBranch = 1`, `NextUnexpandedPC = 0`, and `Imm = 0`, giving residual `−0x80000000` in the actual branch constraint. | Recheck the pulled fix using the [self-branch report](../bug-report/self-branch.md); [the current Lean target](Constraints/NextUnexpandedPCEqPCPlusImmIfShouldBranch.lean) remains a proposition definition until the model is updated and its claim justified. |
| **VirtualAssertEQ spoil mode; constraint (12)** | [Rust intentionally allows a nonzero immediate to suppress the runtime assertion][rust-assert]. Unequal operands can retire while the equality lookup returns zero. The current [Lean lookup](witness_helpers/lookup_output.lean) preserves this distinction. | This is intentional Rust behavior, not a newly established Rust bug. [The conditional completeness theorem](Constraints/AssertLookupOne.lean) requires equality-assertion operands to match, which is exactly when Rust's assertion lookup can satisfy the unchanged constraint. It does not claim that every tracer-permitted execution is satisfiable. |
| **RAM history, public I/O, and arithmetic** | [RamVal](witness_helpers/ram_val.lean) uses the current captured read value; [RamValFinal](witness_helpers/ram_val_final.lean) rebuilds device/final words. Device reads need not return the last stored value. Wrapping ISA address arithmetic also needs reconciliation with field equations. | Investigate constraints (01), (26), (37), and (38) after the initialization/layout/domain gaps. Preserve Rust's captured-read and finalization behavior. These are unresolved correspondence/protocol questions, not confirmed end-to-end Rust failures. |

**Correction to an earlier finding:** ordinary padding does not produce the claimed `−4` PC-update failure. Rust's decoded [Noop circuit flags][rust-noop] set `DoNotUpdateUnexpandedPC`; the current Lean [OpFlags](witness_helpers/op_flags.lean) and [fixed bytecode flags](Constraints/BytecodeReadData.lean) do too. Its contribution is `−4 + 4 = 0`. The earlier padding-bug claim is withdrawn.

## Intentional unfinished work and validation

- All **62 numbered constraint predicates** in [constraints.md](constraints.md) have corresponding files in this checkout. The earlier “only two predicates” description does not apply here.
- [lookup_table.lean](lookup_table.lean) defines AND, OR, XOR, and VirtualXORROTL1. The other **51 of 55** table kinds still use the explicit placeholder branch. These definitions remain unfinished; they are not verified merely because the project builds.
- There is no completed theorem that every honest witness satisfies all constraints; the current 48/11/3 source inventory above replaces the earlier claim that most targets remain `sorry`.

### Latest integration validation — 25 September

| Check | Result |
| --- | --- |
| `lake build JoltBytecode JoltConstraints` | **Passed**, 8,575 jobs, on the integrated sources committed as `c751079`; existing `sorry` and linter warnings remain. |
| All 11 inherited `JoltConstraints.Tests.*` modules | **Passed** when explicitly built against the integrated ISA. |
| New `JoltConstraints.Tests.NativeDispatch` module | **Passed** after its proof was corrected, and committed as `94231e2`. |
| ISA and trusted Sail source comparison | `JoltBytecode`, `LeanRV64D`, and `LeanRV64D.lean` match `fix/isa-rust-correspondence` at `8bd5438`. |
| Witness preservation | Relative to `feat/npWitness`, the constraint tree adds only `Tests/NativeDispatch.lean`; the existing proof and model files were preserved. |

The 12 regression modules are BytecodeDomain, DestinationNormalization, FinalOperands, LoadCapture, NativeDispatch, ProverPadding, RegisterEncoding, RuntimeAdvice, TraceBoundary, TraceLength, VirtualXORROTL1, and WitnessDimensions.
The first combined regression run found a proof error in the new NativeDispatch test; that proof was fixed and the module rebuilt successfully.
No Rust execution tests were rerun as part of this documentation update; the later constraint (15) audit inspected the pulled Rust source.

### ISA ports of the pulled Rust fixes — 25 September

| Check | Result |
| --- | --- |
| `lake build` and `lake build JoltBytecode JoltConstraints` | **Passed**, 8,576 jobs each, on the working tree with the uncommitted CSRRS and VirtualSRLIW ports. |
| All 13 `JoltConstraints/Tests/*.lean` modules | **Passed** with `lake env lean`, including the new ZeroMaskShift module. |
| `#print axioms` | `System.csrrsProgram_eq_sail_projected` and `srliwProgram_eq_sail` have no `sorryAx` dependency. |
| Rust checks | Not rerun; both fixes and their added Rust tests were inspected at `3cb4e24`. |

To repeat the Lean validation from the project folder:

```sh
lake build JoltBytecode JoltConstraints
for test in JoltConstraints/Tests/*.lean; do
  lake env lean "$test" || break
done
```

### Historical validation before integration

| Check | Result |
| --- | --- |
| Full `lake build` after #11 | **Passed**, 8,571 jobs; existing `sorry`/linter warnings remain. |
| TraceLength and ProverPadding regression modules | **Passed** when explicitly built. The checks cover an oversized trace, both Rust minimum lengths, exact power-of-two boundaries, and rejection of an arbitrary larger domain. |
| FinalOperands test module and regenerated expansions | **Passed** when explicitly built. Rust `jolt-lean-gen --lean` reproduced the existing `ExpansionsAutomated.lean` byte for byte; `cargo fmt --check -p jolt-lean-gen` passed. |
| TraceBoundary, RuntimeAdvice, RegisterEncoding, VirtualXORROTL1 test modules | **Passed** when explicitly built; rechecked during this review update. |
| DestinationNormalization test module | **Passed after #24** with `lake build JoltBytecode JoltConstraints JoltConstraints.Tests.DestinationNormalization` (8,572 jobs). |
| LoadCapture test module | **Passed** with `lake build JoltConstraints.Tests.LoadCapture` (3,401 jobs). The identified #8 load-capture gap is represented in the trace row. |
| WitnessDimensions test module and full build | **Passed** with `lake build JoltConstraints.Tests.WitnessDimensions` (609 jobs) and `lake build` (8,571 jobs) after the #13 dimension changes. Existing `sorry` and linter warnings remain. |
| Rust PC/expansion/advice/HostIO/duplicate-address checks | **Passed** as focused checks, including reproductions of the listed mismatches. |
| Rust XORROTL1 comparison | **Passed**, 32 execution/query/table comparisons. |
| Rust CSRRS, terminating self-branch, and raw final-row LD conversion checks | Reproduced the results described above. |
| CSRRS Lean theorem axiom inspection | No `sorryAx` dependency; this is an execution theorem, not constraint completeness. |

The earlier audit used an isolated copy of the correct checkout, checked against its source hashes. Repair #24 was then built in that copy and applied to this checkout. The #18 generator repair and regeneration were subsequently checked in this checkout. Those historical validation steps did not advance completeness proofs; later proof commits are reflected in the current inventory above.

## Next session after the Rust pull

1. Record the Rust checkout's new commit and local changes, then identify which deferred findings its fixes address.
2. Recheck the affected examples, especially the historical CSRRS and self-branch reports, zero-mask shifts (audit #17), and zero RAM chunks (audit #13) where relevant to the pulled changes.
3. Port each verified behavior change into the corresponding Lean ISA, trace, witness, or constraint code, with an explicit old/new example and an updated reference revision.
4. Update affected proofs and regression checks while preserving the reviewed PC representation, source/final-row distinction, and existing completed proofs.
5. Reassess the remaining preprocessing, initialization, completion, HostIO, device-layout, and image-validity gaps (audit #3, #6, #9, #5, #14, #16).
6. Continue the remaining table/witness coverage (audit #20 and #21) and completeness work after checking its dependencies.

Work one issue at a time and discuss each completed fix before starting another.
This order is a dependency guide, not authorization to combine all repairs.
Audit #15 is now included in the fresh-model scope, but remains unimplemented; do not assume an upstream Rust fix has supplied that missing Lean model.
Keep historical counterexamples and their revisions distinguishable from failures reproduced on the new Rust revision.
Update this handoff after each reviewed repair so the next session can see what was checked and what still remains.

## Fresh-model memory-bounds scope decision (2026-09-25)

The user approved including heap-end and stack-canary checks after reviewing
Rust at `3cb4e24361ae2006e9713ae65d58a3fa51fd0518`. This approves scope,
not any particular Lean definition. Every modeling-code change still requires
the Rust source, proposed Lean code, and justification before approval.

- Include the layout calculations and overflow rejection that determine these
  boundaries: `stack_end = RAM_START_ADDRESS + program_size`,
  `stack_start = stack_end + STACK_CANARY_SIZE + stack_size`, and
  `heap_end = stack_start + heap_size`. Rust uses checked additions in
  `common/src/jolt_device.rs`; `STACK_CANARY_SIZE` is 128 in
  `common/src/constants.rs`.
- Include the RAM acceptance checks in
  `tracer/src/emulator/mmu.rs::assert_effective_address`: with a Jolt device
  attached, checked read and write addresses must be below `heap_end`;
  checked write addresses must also lie outside
  `[stack_end, stack_end + STACK_CANARY_SIZE)`. Reads of the canary are allowed.
  The function returns without these checks when no Jolt device is attached.
- Preserve the actual access paths: the doubleword RAM fast paths call this
  check on the starting address. Do not silently strengthen this to a check
  of every byte without establishing the corresponding Rust behavior.
- Allocator implementation and tracking individual heap allocations remain
  outside this scope. These runtime bounds are distinct from witness-domain
  bounds supplied by `RamFits`.

This decision changes documentation only. No memory-bounds modeling code or
correspondence proof has been added, and the live model remains unchanged.

[rust-commit]: https://github.com/abiswas3/jolt/commit/e012da54c3bb26a6436b5ca74e86c19bb39695ad
[rust-trace-conversion]: https://github.com/abiswas3/jolt/blob/e012da54c3bb26a6436b5ca74e86c19bb39695ad/tracer/src/trace_row.rs#L53-L118
[rust-bytecode]: https://github.com/abiswas3/jolt/blob/e012da54c3bb26a6436b5ca74e86c19bb39695ad/crates/jolt-program/src/preprocess/bytecode.rs
[rust-hostio]: https://github.com/abiswas3/jolt/blob/e012da54c3bb26a6436b5ca74e86c19bb39695ad/tracer/src/instruction/virtual_host_io.rs
[rust-witness-config]: https://github.com/abiswas3/jolt/blob/e012da54c3bb26a6436b5ca74e86c19bb39695ad/crates/jolt-witness/src/backend/trace/mod.rs#L181-L205
[rust-prover-config]: https://github.com/abiswas3/jolt/blob/e012da54c3bb26a6436b5ca74e86c19bb39695ad/crates/jolt-prover/src/config.rs#L105-L123
[rust-chunks]: https://github.com/abiswas3/jolt/blob/e012da54c3bb26a6436b5ca74e86c19bb39695ad/crates/jolt-witness/src/witnesses/one_hot.rs#L19-L42
[rust-dimensions]: https://github.com/abiswas3/jolt/blob/e012da54c3bb26a6436b5ca74e86c19bb39695ad/crates/jolt-claims/src/protocols/jolt/geometry/dimensions.rs#L537-L550
[rust-ram-ra]: https://github.com/abiswas3/jolt/blob/e012da54c3bb26a6436b5ca74e86c19bb39695ad/crates/jolt-witness/src/backend/trace/ram.rs#L50-L68
[rust-ram-product]: https://github.com/abiswas3/jolt/blob/e012da54c3bb26a6436b5ca74e86c19bb39695ad/crates/jolt-claims/src/protocols/jolt/geometry/ram.rs#L163-L172
[rust-shift]: https://github.com/abiswas3/jolt/blob/e012da54c3bb26a6436b5ca74e86c19bb39695ad/crates/jolt-claims/src/protocols/jolt/relations/spartan/shift.rs#L85-L131
[rust-next-flags]: https://github.com/abiswas3/jolt/blob/e012da54c3bb26a6436b5ca74e86c19bb39695ad/crates/jolt-witness/src/witnesses/flags.rs#L84-L116
[rust-booleanity]: https://github.com/abiswas3/jolt/blob/e012da54c3bb26a6436b5ca74e86c19bb39695ad/crates/jolt-claims/src/protocols/jolt/geometry/booleanity.rs#L39-L61
[rust-device]: https://github.com/abiswas3/jolt/blob/e012da54c3bb26a6436b5ca74e86c19bb39695ad/common/src/jolt_device.rs
[rust-ram]: https://github.com/abiswas3/jolt/blob/e012da54c3bb26a6436b5ca74e86c19bb39695ad/crates/jolt-witness/src/backend/trace/ram.rs
[rust-srlw]: https://github.com/abiswas3/jolt/blob/e012da54c3bb26a6436b5ca74e86c19bb39695ad/crates/jolt-lookup-tables/src/instructions/virt/srlw.rs#L21-L28
[rust-row]: https://github.com/abiswas3/jolt/blob/e012da54c3bb26a6436b5ca74e86c19bb39695ad/crates/jolt-riscv/src/row.rs
[rust-oracle]: https://github.com/abiswas3/jolt/blob/e012da54c3bb26a6436b5ca74e86c19bb39695ad/crates/jolt-witness/src/backend/trace/oracle.rs
[rust-assert]: https://github.com/abiswas3/jolt/blob/e012da54c3bb26a6436b5ca74e86c19bb39695ad/tracer/src/instruction/virtual_assert_eq.rs#L18-L35
[rust-noop]: https://github.com/abiswas3/jolt/blob/e012da54c3bb26a6436b5ca74e86c19bb39695ad/crates/jolt-riscv/src/instructions/mod.rs#L536-L560


[rust-csr-exemption]: https://github.com/abiswas3/jolt/blob/e012da54c3bb26a6436b5ca74e86c19bb39695ad/crates/jolt-program/src/expand/operands.rs#L50-L59
[rust-csrrs]: https://github.com/abiswas3/jolt/blob/e012da54c3bb26a6436b5ca74e86c19bb39695ad/crates/jolt-program/src/expand/control_flow/csrrs.rs#L17-L23
