# Inline probe (I0(c) and I0(f))

This probe drives Jolt's production code on hand-built one-instruction ELFs to answer questions 1 and 3 of section 10 of `docs/inline-precompiles.md` and to test SDK preconditions; the findings are in `reports/2026-11-12-inline-open-questions.md`.

```
JOLT_DIR=~/claude-work/jolt-inline-pin-a6b6 scripts/inline-open-questions/build.sh WORK_DIR
WORK_DIR/bin/inline-probe-<nofeat|depsha2|inlines> <q1|q3|alias|glv|edge>
```

`build.sh` builds three binaries one after another (no inline crate linked; `jolt-inlines-sha2` a dependency but never named; all four in-scope inline crates named), and `q1` runs on all three.
The other subcommands need the `inlines` binary.
`q3` runs one inline call with misaligned, wrapping, out-of-range and I/O-region operands; `alias` compares overlapping operand buffers with disjoint ones for all twelve inlines; `glv` checks `GLVR_ADV` with `rs3` overlapping `rs1`; `edge` runs the secp256k1 and BLAKE2 value edge cases.
Each case prints the tracer outcome (row count or the panic location and message); a successful trace means every assert row passed, because the tracer panics on a failed assert.
In `q3` a successful case also prints whether the prover's `remap_word_address` accepts every RAM access the trace records; the probe omits the prover's second check, that the remapped index is below `ram_k`.
