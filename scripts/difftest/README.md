# Differential testing: Sail RISC-V model vs Jolt's tracer

This harness runs one RISC-V ELF on two simulators and compares their
architectural state after every retired instruction:

- **Sail**: the sail-riscv C++ emulator `sail_riscv_sim`. It is built from the
  model commit, model patches and Sail compiler pinned in
  `sail-import/PROVENANCE.toml`, and run with the configuration that generates
  `LeanRV64D` (`config.used`, currently `sail-import/rv64d_jolt.json`).
- **Jolt**: the a16z/jolt tracer in trace mode. Every instruction runs its inline
  sequence, which is what the Jolt prover proves and what jolt-qed transcribes.
  `jolt-trace/` is a small driver that prints one JSON line per instruction.

The harness compares, per instruction:

- the instruction address and the address of the next instruction;
- the integer registers `x1`–`x31`;
- the six machine CSRs that Jolt keeps in virtual registers 34–39
  (`mtvec`, `mscratch`, `mepc`, `mcause`, `mtval`, `mstatus`);
- the memory bytes whose value changed.

A difference is reported at the instruction where it appears or changes, so a
value that stays different is reported once. Comparison stops at the first
control-flow difference. Sail traps and privilege changes, and Jolt RAM writes
where Sail stores nothing, are listed as notes and are not counted as
differences.

## What this does not test

The C++ emulator implements the model's external functions (memory, PMAs,
reservations, the platform) in C++. The Lean model `LeanRV64D` implements them
in `handwritten_support/RiscvExtras.lean` or leaves them as axioms. A difference
in those functions, such as the LR/SC reservation granule, is a difference
between Jolt and the C++ emulator. It need not be a difference between Jolt and
the Lean model. The harness also starts both simulators from their own reset
state and does not compare it.

## Requirements

- git, Python 3.11 or later, CMake, a C++ compiler, and Rust through rustup.
  The jolt-trace driver uses the toolchain in Jolt's `rust-toolchain.toml`.
- A Sail compiler at the pinned version. Either set `SAIL_BIN` to one, or
  provide an opam switch that can build Sail and `build.sh` builds it.
- To assemble guests: clang with the `riscv64` target (Homebrew `llvm` works;
  Apple's clang does not), and `ld.lld` or the `rust-lld` that rustup installs.

## Building

```sh
scripts/difftest/build.sh WORK_DIR
```

This builds `sail_riscv_sim` and `jolt-trace` under `WORK_DIR` and writes
`WORK_DIR/env.sh` with their paths. To test a Jolt branch, set `JOLT_DIR` to its
checkout; without it, a16z/jolt is cloned into `WORK_DIR/jolt` once.

Rerun `build.sh` after any change to `PROVENANCE.toml`. The emulator is rebuilt
when the model commit, the compiler or any listed model patch changes. A new
patch is picked up once it is listed under `[model] patches`. A configuration
change needs no rebuild, because the emulator reads the configuration at run
time.

## Running

```sh
scripts/difftest/run.sh WORK_DIR                 # every guest in guest/repro/
scripts/difftest/run.sh WORK_DIR prog.S other.elf
```

`.S` files are assembled for RV64IMAC with Zicsr and linked with
`guest/link.ld`. ELF files are used as they are. A guest must start at
`0x80000000` in M-mode and stop by writing to `tohost`. `guest/common.h` gives
the prologue, exit and trap handler that the reproducers use.

`run.sh` prints one block per guest. It writes the raw traces and a JSON result
per guest to `WORK_DIR/results/`. It exits with status 1 if any guest differs.
To compare one ELF directly, run `difftest.py --help`.

## Reproducers

`guest/repro/` holds one minimal guest per known or suspected difference,
named by the letter of the question it settles:

| File | Checks |
| --- | --- |
| `a_mret_mstatus.S` | MRET updates to `mstatus.MIE`/`MPIE`/`MPP` |
| `a2_mret_reset_mpp.S` | MRET with `MPP` as left by reset |
| `b_ecall_mpie.S`, `b2_ecall_mie0.S` | ECALL's `mstatus` update with `MIE` = 1 and `MIE` = 0 |
| `c1_warl_mstatus.S` | writing all ones, then zero, to `mstatus` |
| `c2_warl_mtvec.S`, `c4_mtvec_reserved_trap.S` | `mtvec` with reserved MODE values, and a trap through it |
| `c3_warl_mepc.S` | an odd `mepc`, then MRET |
| `d_sc_fail_write.S` | SC.W with no reservation |
| `d2_sc_granule.S`, `d3_sc_width.S` | SC.W at another word of the reserved doubleword; LR.W followed by SC.D |
| `e_lr_misaligned.S`, `e2_sc_misaligned.S` | misaligned LR.W and SC.W |
| `f_mstatus_fs.S` | setting `mstatus.FS` |
| `g_ebreak.S` | EBREAK |
| `x_csr_forms.S` | CSRRC, which Jolt does not decode |

Every guest's `mstatus` reads differ in the read-only `UXL` and `SXL` fields:
Sail reads them as 2, and Jolt's `mstatus` starts at zero. The harness reports
this once, at the first instruction.
