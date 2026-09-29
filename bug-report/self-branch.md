# Taken self-branch: the honest witness fails the next-PC constraint

Reproduced against the local Rust Jolt checkout at `7dfe8a0f`; the relevant files are unchanged from [the reviewed `e012da54` revision](https://github.com/abiswas3/jolt/commit/e012da54c3bb26a6436b5ca74e86c19bb39695ad). This report concerns constraint (16) in our checklist, row index 15 of Rust's stage-1 R1CS matrix.

## Counterexample

Put this single instruction at `0x80000000`, start the Rust CPU at that address, and trace its execution:

```asm
beq x0, x0, 0    # 0x00000063
```

The comparison is true. [Rust's `BEQ::exec`](https://github.com/abiswas3/jolt/blob/e012da54c3bb26a6436b5ca74e86c19bb39695ad/tracer/src/instruction/beq.rs#L15-L22) sets the CPU's PC to the instruction's own address plus the immediate, which is again `0x80000000`. On the next tracer iteration, [Rust sees that the PC has not changed and stops](https://github.com/abiswas3/jolt/blob/e012da54c3bb26a6436b5ca74e86c19bb39695ad/tracer/src/lib.rs#L329-L339). The branch executes once, so the trace contains one instruction row. It does not contain a second execution of the branch. That row passes [`build_trace_rows`](https://github.com/abiswas3/jolt/blob/e012da54c3bb26a6436b5ca74e86c19bb39695ad/tracer/src/trace_row.rs#L151-L160); the prover's cycle domain then has padding after it.

## Honest witness

On the `BEQ` row, Rust's witness extractors give:

- `ShouldBranch = 1`: `BEQ` has the `Branch` instruction flag, and comparing `x0` with `x0` gives lookup output `1`. See the [`BEQ` flags](https://github.com/abiswas3/jolt/blob/e012da54c3bb26a6436b5ca74e86c19bb39695ad/crates/jolt-riscv/src/instructions/i/beq.rs#L3-L8) and [`ShouldBranch::extract`](https://github.com/abiswas3/jolt/blob/e012da54c3bb26a6436b5ca74e86c19bb39695ad/crates/jolt-witness/src/witnesses/flags.rs#L130-L141).
- `UnexpandedPC = 0x80000000`: this is the source instruction's address, recorded in the trace row and read by [`UnexpandedPc::extract`](https://github.com/abiswas3/jolt/blob/e012da54c3bb26a6436b5ca74e86c19bb39695ad/crates/jolt-witness/src/witnesses/pc.rs#L69-L77).
- `Imm = 0`: the branch's immediate, read by [`Imm::extract`](https://github.com/abiswas3/jolt/blob/e012da54c3bb26a6436b5ca74e86c19bb39695ad/crates/jolt-witness/src/witnesses/operands.rs#L135-L151).
- `NextUnexpandedPC = 0`: this column reads the source address of the **next trace row**, not the CPU's PC after executing the branch. There is no next executed instruction. The [witness backend supplies a default padding row](https://github.com/abiswas3/jolt/blob/e012da54c3bb26a6436b5ca74e86c19bb39695ad/crates/jolt-witness/src/backend/trace/cycle.rs#L111-L125), whose unexpanded PC is zero; [`NextUnexpandedPc::extract`](https://github.com/abiswas3/jolt/blob/e012da54c3bb26a6436b5ca74e86c19bb39695ad/crates/jolt-witness/src/witnesses/pc.rs#L101-L109) reads that successor.

The CPU's final PC is `0x80000000`, but that value is not copied into `NextUnexpandedPC`. The latter comes from the padding successor. Setting it to `0x80000000` would describe a second executed row that the terminating trace does not contain.

## Failed constraint

[Rust's constraint row](https://github.com/abiswas3/jolt/blob/e012da54c3bb26a6436b5ca74e86c19bb39695ad/crates/jolt-r1cs/src/constraints/rv64.rs#L297-L307) requires, over the proof field `Fr`:

```text
ShouldBranch × (NextUnexpandedPC − UnexpandedPC − Imm) = 0
```

The branch is taken, so `ShouldBranch = 1` activates this constraint. It demands `NextUnexpandedPC = UnexpandedPC + Imm = 0x80000000`. The witness instead has `NextUnexpandedPC = 0` because the next row is padding. Its local residual is:

```text
1 × (0 − 0x80000000 − 0) = −0x80000000 ≠ 0
```

The nonzero value is the residual of this individual R1CS row. It is not a claimed value for the full, challenge-weighted sumcheck.

## Why the Lean completeness theorem cannot be proved as stated

The [Lean constraint](../JoltConstraints/Constraints/NextUnexpandedPCEqPCPlusImmIfShouldBranch.lean) has the same equation. Its completeness statement includes [Rust's repeated-PC termination rule](../JoltConstraints/execution_conditions.lean) and [prover padding](../JoltConstraints/witness.lean); neither excludes a taken self-branch. The [Lean `ShouldBranch`](../JoltConstraints/witness_helpers/branch.lean), [`UnexpandedPC`](../JoltConstraints/witness_helpers/unexpanded_pc.lean), [`Imm`](../JoltConstraints/witness_helpers/imm.lean), and [`NextUnexpandedPC`](../JoltConstraints/witness_helpers/next_unexpanded_pc.lean) definitions yield the same four values on this case.

The unrestricted completeness statement is therefore false for this Rust-produced execution, rather than merely missing a proof tactic. Restricting Lean termination to `JAL` or pretending that the next row repeats the branch would erase the mismatch with Rust. The Lean statement remains a `def … : Prop`, with no proof and no admitted theorem.

A standalone Rust check ran the CPU, converted the one execution row with `build_trace_rows`, called the four witness extractors with a padding successor, and evaluated row 15 of `rv64_spartan_outer_constraints::<Fr>()`. It printed `rows=1`, `cpu_pc=0x80000000`, `should_branch=true`, `unexpanded_pc=0x80000000`, `imm=0`, `next_unexpanded_pc=0x0`, and confirmed that the R1CS residual is nonzero. An end-to-end prover/verifier run was not performed. The established issue is an honest-witness/constraint inconsistency, not acceptance of an invalid proof.
