# Jolt model review

## Source of truth for Rust comparisons

Scan the local Jolt checkout at `/Users/francis/Work-With-A16z/jolt` when
reviewing a constraint or its witness and trace definitions. GitHub links in
`constraints.md` and Lean comments are documentation pointers; they are not a
substitute for inspecting the corresponding local Rust files. Record the local
commit and relevant worktree changes when a review depends on exact Rust
behavior.

The review notes that were previously referenced by `constraints.md` were not
present in this checkout when this file was created. Reconstruct findings from
the Lean and local Rust sources rather than assuming those missing notes.

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
