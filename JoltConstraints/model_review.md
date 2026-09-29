# Jolt model review

## Source of truth for Rust comparisons

Scan the local Jolt checkout at `$HOME/Work-with-A16z/jolt` when
reviewing a constraint or its witness and trace definitions. GitHub links in
`constraints.md` and Lean comments are documentation pointers; they are not a
substitute for inspecting the corresponding local Rust files. Record the local
commit and relevant worktree changes when a review depends on exact Rust
behavior.

The prior branch's longer review is preserved in
[model_review_archive_2026-09-25.md](model_review_archive_2026-09-25.md).
It records historical findings and older validation, not the current status.
Recheck its claims against the local Rust source before relying on them.

## Trace row assumptions

`JoltTrace` previously required the full `all_assumptions` bundle at every
row's pre-state. Its last conjunct, `MstatusMppMachine`, requires MPP = Machine
in the virtual `mstatus` register, but `init_state` sets every virtual register
to zero, as Rust's `Cpu::new` does. No trace could have a first row, so every
`JoltTrace` was empty and every constraint theorem quantified over traces held
vacuously. The bundle's `*VRegMatchesSail` conjuncts would also fail after any
CSR write, since Jolt rows update only the virtual CSR registers.

`JoltTrace.rowAssumptions` now requires `TraceAssumptions` in
[trace.lean](trace.lean). It keeps what the constraint proofs use:
architectural register readability, `CurPrivilegeMachine`, `MstatusMprvZero`,
and the LD/SD memory-window facts. `TraceAssumptions.of_all_assumptions` shows
it is weaker. [TraceNonempty checks](Tests/TraceNonempty.lean) build a
complete one-row trace for `jal x0, 0` from `init_state`, prove it
`Terminated`, pin its axioms with no `sorryAx`, and show `all_assumptions`
fails at its pre-state.

## Constraint (01): wrapping load address

Confirmed with a valid RV64 ELF accepted by Jolt's program builder, normal
tracer, preprocessing, and compact proof-trace backend. The local Rust witness
extractors and stage-1 R1CS matrix disagree on its load row. See
[the bug report](../bug-report/ram-address-wrap.md) for the concrete program
and observed output.

Local Rust revision reviewed: `922af71c7d7f646a336ff69dc386439b12ee0d0f`.
The relation in `crates/jolt-r1cs/src/constraints/rv64.rs` agrees with the Lean
predicate: `(Load + Store) * (RamAddress - Rs1Value - Imm) = 0`.

The unrestricted honest-witness theorem is false for a load whose 64-bit
effective address wraps. For example, `LD` with base register value
`2^64 - 8` and immediate `8` accesses address `0` in
`tracer/src/instruction/ld.rs`. The MMU allows zero-padded loads there and
records address `0` (`tracer/src/emulator/mmu.rs`); the witness converts that
raw address, the captured base, and the signed immediate directly to field
values. The guarded constraint therefore evaluates to `-2^64`, which is
nonzero in the default BN254 field.

A source-level reproducer is `ADDI x1, x0, -8` followed by `LD x2, 8(x1)`
with a Jolt device installed. A self-jump can terminate the program after the
load. The load's aligned address is zero and its captured value is zero.

Lean's `WitnessParams.RamFits` also permits raw address zero. A no-wrap premise
would exclude this accepted Rust execution, so it should not be added merely
to discharge the theorem. Resolve the Rust behavior or circuit relation before
marking (01) closed. This is a proof-completeness issue: a trace admitted by
the emulator cannot satisfy this constraint with its honest witness.

## Constraint (17): next source address on other rows

Local Rust revision reviewed: `922af71c7d7f646a336ff69dc386439b12ee0d0f`
(no tracked worktree changes; unrelated untracked `nvim.log`). The stage-1 row
in `crates/jolt-r1cs/src/constraints/rv64.rs` agrees with Lean's
`nextUnexpandedPCUpdateOtherwise`: the guard is `1 − ShouldBranch − Jump`,
and the expected next address is `UnexpandedPC + 4 − 4·DoNotUpdateUnexpandedPC
− 2·IsCompressed`. The Rust and Lean witness definitions both use the next
trace row's source address, or zero at padding. Rust's padding no-op and Lean's
padding flags both set only `DoNotUpdateUnexpandedPC` among these terms.

The honest-witness theorem is proved from the existing trace premises. Padding
and nonfinal expansion rows satisfy the equation directly. On a final row that
is neither a jump nor a taken branch, `row.executes` gives the nextPC frame:
ordinary instructions, loads, stores, and live HostIO are covered. The reusable
Sail byte-read helpers prove that a successful HostIO byte read leaves the Sail
state unchanged even when it returns a memory fault. Trace successor/layout
then identifies the next source address. For the last execution row, the
nextPC frame contradicts the tracer's repeated-PC termination condition, so
an ordinary final row cannot be last. The theorem statement has no new premise.

The trace's `SequenceLayout.addressAdvanceNoWrap` is a temporary assumption
already present in the theorem through `JoltTrace`. Rust still allows source-PC
wraparound, as tracked by [Jolt issue #1949](https://github.com/a16z/jolt/issues/1949).
Therefore this proof under the current Lean trace type does not by itself
establish unrestricted completeness for every Rust-accepted execution.

## Constraint (37): termination-word RAM history

Status: **Rust completeness issue**, reproduced at local Rust revision
`3cb4e24361ae2006e9713ae65d58a3fa51fd0518` (clean tracked worktree;
unrelated untracked `nvim.log`). See the
[reproducer and values](../bug-report/ram-val-termination/README.md). A valid
six-instruction ELF passes the Rust program builder, ordinary tracer,
preprocessing, and compact proof-trace conversion. Its `SD` to the termination
word captures old value zero and requested new value one; the following `LD`
captures zero because the device ignores termination writes and always reads
zero there. The Rust witness oracle gives `RamRa = 1`, `RamInc = 1` at the
store, but `RamVal = 0` at the later load. Constraint (37)'s preceding sum is
one. The concrete `RamValCheck` combination at `gamma = 7` has sides 7 and 8
for that address and cycle. No full prover/verifier run was performed.

The source inconsistency is between `Mmu::trace_store` recording the requested
device-store value as its post-value, `JoltDevice::store` ignoring that write,
and `TraceBackend::materialize_ram_val` advancing its accumulated image from
the captured post-value before overriding a later load with its real read.
Lean's device execution and RAM witness definitions agree with those Rust
behaviors on this case, so this is not an observed translation mismatch.
`ramAccessesValid` checks address alignment and nonzero access, not readback
coherence. Do not add a premise that excludes this accepted execution merely
to close the theorem. Keep (37) open while the Rust model and relation are
reconciled; rerun the reproducer after a fix.

## Constraint (42): register value from preceding increments

Local Rust revision reviewed: `3cb4e24361ae2006e9713ae65d58a3fa51fd0518`
(no tracked worktree changes; unrelated untracked `nvim.log`). In
`crates/jolt-witness/src/backend/trace/registers.rs`, the register witness
starts at zero, records the value before each row, and applies that row's
captured destination write afterward. Padding retains the final value.
`RdWa` selects the captured destination, and `RdInc` is the field difference
between the post-state and pre-state destination values. The Rust relation
adds selected increments from strictly earlier cycles.

The honest-witness theorem is proved with its existing premises. The
[instruction frame](Constraints/RegistersValProofHelpers.lean) shows that each
final instruction preserves every other register, including JALR's PC update,
memory operations, and live HostIO. The
[history proof](Constraints/RegistersValHistoryProofHelpers.lean) connects the
folded witness to the trace pre-state, uses row execution and trace linking to
advance it, then proves that padding adds zero. A separate finite-sum lemma
gives the same recurrence for the strict prefix sum. HostIO captures a
destination without writing it, so its selected `RdInc` is zero. No new trace
premise or heartbeat increase was introduced. The theorem's module and both
helper modules build without `sorry`. Validation: `lake build JoltConstraints`
passed (3,562 jobs), and a final targeted build of the theorem and helpers
passed (3,489 jobs). `#print axioms` for the theorem reports no `sorryAx`;
it lists the existing Sail platform axioms `load_reservation`,
`match_reservation`, `plat_term_write`, and
`sys_enable_experimental_extensions`, plus Lean's usual logical axioms.

## Fork replay and Rust correspondence — 28 September 2026

This branch retains the fork's [native row rewrite](../JoltBytecode/JoltISA/Instruction.lean),
[program expansion](program.lean), and [trace execution](trace.lean). Native
source instructions with `rd = x0` are rewritten before `execInstr`: Rust sends
side-effecting JAL, JALR, LD, advice load, and HostIO destinations to the first
temporary (`v40`), and replaces pure destination-zero writes with the canonical
`ADDI x0, x0, 0`. `JoltTraceRow.executes` uses `expandedInstruction`, so witness
capture sees the rewritten destination. `execInstr` executes the final row; it
does not decide whether a source instruction needs rewriting. The native
JAL/JALR equivalence statements now refer to rewritten instructions too.

Rust revision checked: `3cb4e24361ae2006e9713ae65d58a3fa51fd0518`.
Its checkout has no tracked worktree changes; an unrelated untracked
`nvim.log` is present. In `tick_operate`, Rust advances `cpu.pc` by the source
instruction length before JAL or JALR execution. At the Lean instruction-body
boundary, Sail `PC` represents decoded `self.address`, while Sail `nextPC`
represents that advanced `cpu.pc`. [prepareSource](program.lean) sets this pair
using the compressed or ordinary source length and does not increment it
between expansion rows.

| Instruction | Rust body | Selected Lean behavior |
| --- | --- | --- |
| JAL | Save advanced `cpu.pc` as the link, then set `cpu.pc` to `self.address + imm` with wrapping arithmetic. | Both forks use this PC mapping. Keep their common JAL execution and the fork's destination rewrite. |
| JALR | Save advanced `cpu.pc`, compute `(original rs1 + imm) & ~1`, assign it to `cpu.pc`, then write the saved link. The body does not call Sail's alignment check. | Keep this branch's direct `nextPC` write and the fork's destination rewrite. Read `rs1` before writing the link, including when `rd = rs1`. |

The fork's JALR execution called Sail `jump_to`. That can reject a target
whose bit 1 is set when Sail's compressed extension is disabled, returning a
fetch-alignment result before the link write. Rust completes the JALR body;
a later fetch decides whether the new PC is usable. The public
Sail-equivalence proof therefore has an explicit **target**
`MepcReadAligned` premise. That predicate can describe any address, not only
the `mepc` register. The fork's JALR bundle had no such premise because both
sides of its theorem used `jump_to`. The general `all_assumptions` condition
on `mepcReads` does not by itself establish alignment of an arbitrary JALR
target. Both Lean JAL execution definitions already use Rust's direct update.

Keep this branch's [HostIO execution](../JoltBytecode/JoltISA/HostIO.lean):
live calls read ABI registers x10–x13 and can append advice or inspect memory;
replay suppresses those effects. The fork's `VirtualHostIO => pure
RETIRE_SUCCESS` branch would omit live Rust behavior. The fork's row rewrite
still retains HostIO and normalizes a destination-zero source before execution.
The source-PC proof still uses an explicit `JoltTraceRow.hostIOPreservesPC`
certificate. The new Sail byte-read frame proves the live HostIO `nextPC`
property used by constraint (17), but it has not yet been wired to discharge
this separate `PC` certificate from `execInstr`. The live HostIO transition
itself remains modeled.

The three fork lookup-table commits are included. The dispatch in
[lookup_table.lean](lookup_table.lean) now defines every `LookupTableKind` entry
without `sorry`. Proving that each selected entry equals the honest execution
output remains separate deferred work. The fork's constraint (13)/(14) proofs
for lookup-result and jump-return destination writeback are also included;
their JALR proof helper was adapted to the direct Rust-style PC update.

Validation: after the six-commit fast-forward to `155ca07`,
`lake build JoltBytecode JoltConstraints` passed (8,584 jobs), and all 14
`JoltConstraints.Tests.*` modules passed as explicit Lake build targets (3,496
jobs), including native rewrite, load capture, trace boundaries,
VirtualXORROTL1, and live and replay HostIO checks. These checks do not close
the explicit source-to-row and memory-model obligations below.

## Deferred FIXME and WARNING inventory

This is every current `FIXME` or `WARNING` site under `JoltBytecode` and
`JoltConstraints`, including older comments retained during the merge. They
are **deferred work or documented modeling choices**, not established proofs.

| Site | Deferred work or decision |
| --- | --- |
| [program.lean](program.lean), two `FIXME`s | `rowValid` (including writable jump destinations, canonical x0 writes, and jumps at the end of expansions) and `noEarlyNextPCChange` use `sorry` and are false for arbitrary arrays. Connect rows to Rust source expansion and native rewrites, then prove the claims for those outputs. |
| [program.lean](program.lean), `WARNING` | Rust currently permits source-PC wraparound; `SequenceLayout.addressAdvanceNoWrap` is a temporary assumption pending the fix tracked by [Jolt issue #1949](https://github.com/a16z/jolt/issues/1949). |
| [trace.lean](trace.lean), `FIXME` | Derive `hostIOPreservesPC` from live `execInstr` using the new Sail byte-read frame; it is still an explicit trace-row obligation. |
| [LookupEntryProofHelpers.lean](Constraints/LookupEntryProofHelpers.lean), `FIXME` | Constraint (39) is proved modulo six per-table `sorry`s. `lookupEntryCorrect_{VirtualSRL,VirtualSRA,VirtualSRLW,VirtualSRAW,VirtualROTR,VirtualROTRW}` are false for arbitrary bytecode (non-bitmask mask operand; see `JoltConstraints/Tests/LookupShiftMask.lean`) and need the expander's bitmask invariant. |
| [RamValEqInitialPlusPrefixRamInc.lean](Constraints/RamValEqInitialPlusPrefixRamInc.lean), `FIXME` | Relate captured RAM reads to initialized memory and prefix RAM history. |
| [RamValFinalEqInitialPlusRamInc.lean](Constraints/RamValFinalEqInitialPlusRamInc.lean), `FIXME` | Establish Rust memory-history and terminal-state correspondence. |
| [RegisterAccess.lean](../JoltBytecode/JoltISA/RegisterAccess.lean), `WARNING` | Establish the source register range guard or proof noted by the existing comment. |
| [RiscvInstruction.lean](../JoltBytecode/RiscvInstruction.lean), six `WARNING`s | Wire equivalence for ECALL, EBREAK, LR_W, SC_W, LR_D, and SC_D; their current statement branches are `False`. |
| [Semantics.lean](../JoltBytecode/JoltISA/Semantics.lean), `WARNING` | Rust logs a warning at this execution path; logs are absent from Lean state. Revisit if logs become observable in the claimed correspondence. |

Other `TODO` and `sorry` sites remain outside this comment inventory. The
RAM-wrap discrepancy above is a confirmed Rust witness versus constraint
issue; a convenient no-wrap premise would exclude a Rust-accepted execution.
