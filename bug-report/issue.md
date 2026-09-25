# CSRRS: the honest witness fails the writeback constraint

Confirmed in [abiswas3/jolt, commit `e012da54`](https://github.com/abiswas3/jolt/commit/e012da54c3bb26a6436b5ca74e86c19bb39695ad), the remote `main` checked on 23 September 2026.

## Counterexample

Start with Rust’s `Cpu::new`, allocate 4096 bytes of RAM, place these four instructions consecutively starting at `0x80000000`, and set `PC = 0x80000000` (the address of the first `addi` instruction). After each `Cpu::tick`, compare the PC with its value immediately before that tick. Stop if the two values are equal. Witness construction supplies padding after execution ends.

```asm
addi  x1, x0, 9          # 0x00900093: x1 = 9
csrrw x0, mstatus, x1    # 0x30009073: Rust sets mstatus = 9
csrrs x0, mstatus, x0    # 0x30002073: read mstatus, discard result
jal   x0, 0              # 0x0000006f: jump to this instruction itself
```

The final `jal` is at `0x8000000c`. Its jump target is also `0x8000000c`, so the PC before and after that instruction is identical and execution stops. This matches [Rust’s tracer stopping rule](https://github.com/abiswas3/jolt/blob/e012da54c3bb26a6436b5ca74e86c19bb39695ad/tracer/src/lib.rs#L329-L339).

For the third instruction, Rust's expansion emits:

```text
ADDI x0, v39, 0
```

Here `v39` holds `mstatus`, so it contains `9`. The addition computes `9`, but writing to `x0` discards the result: `x0` remains `0`.

> [!IMPORTANT]
> **Why x0 is not replaced by a virtual register**
>
> Rust [classifies CSRRS as handling rd=x0 internally](https://github.com/abiswas3/jolt/blob/e012da54c3bb26a6436b5ca74e86c19bb39695ad/crates/jolt-program/src/expand/operands.rs#L50-L59), so the [generic side-effecting destination rewrite is skipped](https://github.com/abiswas3/jolt/blob/e012da54c3bb26a6436b5ca74e86c19bb39695ad/crates/jolt-program/src/expand/mod.rs#L134-L149).
>
> The [CSRRS expansion checks rs1=x0 first](https://github.com/abiswas3/jolt/blob/e012da54c3bb26a6436b5ca74e86c19bb39695ad/crates/jolt-program/src/expand/control_flow/csrrs.rs#L17-L23). That branch emits `ADDI rd, vCSR, 0` and returns, even when `rd = x0`. The native ADDI is [emitted directly as a final row](https://github.com/abiswas3/jolt/blob/e012da54c3bb26a6436b5ca74e86c19bb39695ad/crates/jolt-program/src/expand/grammar.rs#L372-L382); it does not pass through the generic source-instruction rewrite again. Thus this case retains `ADDI x0, v39, 0`.

## Honest witness

The honest witness must record what Rust actually executes. Using Rust's own trace conversion and witness extractors gives:

| Witness value | Value | Reason |
| --- | --- | --- |
| `WriteLookupOutputToRD` | `1` | The emitted ADDI has this flag. |
| `LookupOutput` | `9` | The lookup computes `9 + 0`. |
| `RdWriteValue` | `0` | The captured destination is x0, which remains zero. |

These values come from an actual Rust execution. The trace passes `build_trace_rows`; the witness values were not fabricated.

## Failed constraint

`RdWriteEqLookupIfWriteLookupToRd` requires, over Rust’s proof field `Fr`:

```text
WriteLookupOutputToRD × (RdWriteValue − LookupOutput) = 0
```

Substituting the honest witness gives:

```text
1 × (0 − 9) = −9 ≠ 0
```

This is constraint (13) in our list, row index 12 in Rust's R1CS matrix. Evaluating that actual Rust matrix row reproduces the nonzero residual.

## Sumcheck enforcing this constraint

This is part of **stage 1, `SpartanOuter`**. Its [first-round sumcheck starts with claim zero](https://github.com/abiswas3/jolt/blob/e012da54c3bb26a6436b5ca74e86c19bb39695ad/crates/jolt-claims/src/protocols/jolt/relations/spartan/outer_uniskip.rs#L55-L97). The [remainder sumcheck](https://github.com/abiswas3/jolt/blob/e012da54c3bb26a6436b5ca74e86c19bb39695ad/crates/jolt-claims/src/protocols/jolt/relations/spartan/outer_remainder.rs#L110-L167) reduces the challenge-weighted R1CS product to `TauKernel × Az × Bz`. The [stage-1 verifier](https://github.com/abiswas3/jolt/blob/e012da54c3bb26a6436b5ca74e86c19bb39695ad/crates/jolt-verifier/src/stages/stage1/verify.rs#L30-L82) connects these two steps.

For this constraint and execution row, the R1CS factors are `Az = 1`, `Bz = 0 − 9`, and `Cz = 0`. Thus its local R1CS residual is `−9`. This is the individual constraint failure being reported, not a claim that the full, challenge-weighted sumcheck value equals `−9`.

## Why this is a completeness bug

Completeness requires that the witness produced honestly from an allowed execution satisfy the constraints. In this example, Rust accepts the execution and proof-trace conversion, but the generated row fails this constraint. Changing the captured destination to `9` would misrepresent x0; changing the lookup output to `0` would misrepresent the addition.

The check ran the Rust CPU, `build_trace_rows`, the actual witness extractors, and row 12 of `rv64_spartan_outer_constraints::<Fr>()`. It used the emitted final instructions for bytecode preprocessing. An end-to-end prover/verifier run was not performed. The established bug is the honest-witness/constraint inconsistency; this is not evidence that an invalid proof can be accepted.

The Lean CSRRS execution-equivalence theorem can still hold: both executions correctly discard the write to x0. That theorem does not establish witness constraint satisfaction.

Rust sources at the tested commit: [CSRRS expansion](https://github.com/abiswas3/jolt/blob/e012da54c3bb26a6436b5ca74e86c19bb39695ad/crates/jolt-program/src/expand/control_flow/csrrs.rs#L17-L20), [ADDI flags](https://github.com/abiswas3/jolt/blob/e012da54c3bb26a6436b5ca74e86c19bb39695ad/crates/jolt-riscv/src/instructions/i/addi.rs#L3-L8), [writeback constraint](https://github.com/abiswas3/jolt/blob/e012da54c3bb26a6436b5ca74e86c19bb39695ad/crates/jolt-r1cs/src/constraints/rv64.rs#L265-L271).
