# Empty program: prover RAM size falls below the verifier minimum

An ELF with an empty text section and entry address 0 passes program
preprocessing and produces an empty compact trace. Rust's prover derives
`ram_K = 4`; with a 64-byte output region, Rust's verifier requires at least 16
words and rejects these parameters with `InvalidRamK`.

This is a mismatch between the prover's size derivation and the verifier's
input checks. The reproducer calls those actual Rust functions after decoding
and tracing the ELF. It does not generate a cryptographic proof or claim that
the entire proving pipeline succeeds for this program.

## Reproduce

```sh
JOLT_TRACER_CAPACITY_ROWS=64 python3 bug-report/verifier-ram-minimum/run.py /path/to/jolt
```

The runner builds the current checkout, links against exactly the artifacts
Cargo reports, and generates two ELF files: the empty program and a self-jump
control. The verifier call is `validate_inputs_from_parts` with the prover's
actual parameters. Dory may create its normal setup cache.

Observed on 2026-10-08:

```text
== empty
entry=0x0 image_bytes=0 image_words=2 trace_rows=0
trace_length=256 ram_K=4 verifier_min=16 verifier_max=32
verifier input checks: InvalidRamK { got: 4, min: 16, max: 32 }
== self_jump
entry=0x80000000 image_bytes=4 image_words=2 trace_rows=1
trace_length=256 ram_K=32 verifier_min=32 verifier_max=32
verifier input checks: accepted
```

## Why the sizes differ

For the empty image, `RAMPreprocessing::preprocess` produces two zero words
and `min_bytecode_address = 0`. No row touches RAM. `derive_from_rows` rounds
`max(0, 0 + 2 + 1)` to 4.

`compute_min_ram_k` also includes the region below `RAM_START_ADDRESS`.
The 64-byte output region plus panic and termination occupies 80 bytes,
rounded by the layout to 128 bytes: 16 words. The verifier therefore rejects
4 before inspecting the proof equations.

The Lean sizing formula gives the same 4 in this case. Its documented
`touched + 1` correction does not affect this example: `max(1, 3) = 3`.
The translated verifier bounds evaluate to `(16, 32)` as well. Thus the
disagreement in this example is present in Rust, rather than introduced by
those Lean formulas.

## Source state

The local Rust HEAD was `3cb4e24361ae2006e9713ae65d58a3fa51fd0518`, with
staged changes. The build used the working tree, not HEAD alone. SHA-256:

| File | Hash |
| --- | --- |
| `crates/jolt-prover/src/config.rs` | `49266f7338e7f4be2502e54e9c1d959c617cbb033680ce29639a549391d1268a` |
| `crates/jolt-verifier/src/verifier.rs` | `53e83c4302b5754df5ffe31435b6541559354a6f3d3a76d7b036f8a7fff0ffec` |
| `crates/jolt-program/src/preprocess/ram.rs` | `c868ffef98186086aa2daf801a3220a6e926a8774bee7f576fad03e10e2c5c82` |
| `common/src/jolt_device.rs` | `ba43ebdb8074b53bcc845770cef4b9baa88e57894e17000543341cabb48efd76` |
