# `ram_K` one slot too small: still present at `8e536f19`

Already reported upstream as
[a16z/jolt#1951](https://github.com/a16z/jolt/issues/1951), item 4. This folder
only re-checks it at a newer revision, so we can tell when it is fixed.

A store to RAM word index 1023 proves; the same store 8 bytes higher, at word
index 1024, does not: Rust picks `ram_K = 1024` for both, and the witness rejects
index 1024.

Run, after building the Rust crates (see the top of `run.sh`):

```sh
sh run.sh /absolute/path/to/jolt
```

Output at `8e536f199735ac8187156aa589ed1387722a079a` (built with the 1.95 nightly):

```text
== slot1023
lowest=0x7fffffe0 stack_end=0x800012c0 heap_end=0x80003340
rows=4 panic=false
row=2 store=true load=false ram_address=0x80001fd8 slot=Ok(Some(1023))
min_bytecode_address=0x80000000 image_words=4 trace_length=256 ram_K=1024
RamRa: ok (262144 entries)
RamVal: ok (262144 entries)
== slot1024
lowest=0x7fffffe0 stack_end=0x800012c0 heap_end=0x80003340
rows=4 panic=false
row=2 store=true load=false ram_address=0x80001fe0 slot=Ok(Some(1024))
min_bytecode_address=0x80000000 image_words=4 trace_length=256 ram_K=1024
RamRa: ERROR InvalidWitnessData { label: "jolt_vm", reason: "RAM access address remapped to 1024, beyond ram_k 1024" }
RamVal: ERROR InvalidWitnessData { label: "jolt_vm", reason: "RAM access address remapped to 1024, beyond ram_k 1024" }
```

When Rust is fixed, `slot1024` should print `ram_K=2048` and both tables `ok`.
The Lean model (`HonestTrace.prover_config`) already uses the fixed formula,
marked `FIXME`.
