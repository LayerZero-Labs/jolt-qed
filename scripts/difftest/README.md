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
- the memory bytes whose value changed;

and, at the end, how each run stopped. A difference is reported at the
instruction where it appears or changes, so a value that stays different is
reported once. Comparison stops at the first control-flow difference.

A run is complete only when it stops through an HTIF exit command: a store
that makes `tohost` hold device 0, command 0 and a payload with bit 0 set.
The exit code is the payload shifted right by one. Sail's HTIF device and
Jolt's tracer (`Emulator::run_test`) both decode `tohost` this way, and
`jolt-trace` stops on the same condition. A run that reaches the instruction
limit, panics, stops at a jump to itself, or crashes is not complete.

The following are listed as notes and are not counted as differences:

- Integer registers that differ at reset (Sail's reset sets `a0` and `a1`),
  and CSR bits that differ at reset for as long as both runs keep their reset
  values. A guest sees them only by reading them, and the register, memory or
  control flow that the value reaches is compared.
- Sail traps and privilege changes.
- Jolt RAM writes where Sail stores nothing.
- Up to four instructions that Sail retires after Jolt's last one, when both
  runs exit with the same code, Jolt's last instruction stored to `tohost`,
  and those instructions are straight-line, do not trap, write no CSR and
  store only to the `tohost` doubleword. Jolt stops at the first store that
  makes `tohost` an exit command. Sail's HTIF device acts on a store to the
  high half of `tohost`, so riscv-tests, which store the low half first, retire
  two more instructions in Sail. The registers those instructions write are
  listed.

Each guest gets one of three verdicts, or a harness error:

- `AGREE`: no differences, and both runs exit through `tohost` with the same
  code.
- `POLICY`: the first difference is an SC that succeeds in Sail and fails in
  Jolt because of the reservation policy, both runs exit through `tohost`,
  and the comparison stops at the SC. Jolt reserves the exact address of the
  LR and fails an SC wider than the LR. Unpatched sail-riscv reserves the
  8-byte granule and does not check the width. The specification allows both.
  The SC and its LR must be aligned and in the same 8-byte granule, with no
  trap and no other SC between them. Sail's SC must write 0 to `rd` and store
  `rs2` at its address, and Jolt's must write 1 to `rd` and change no memory.
  Nothing else at that instruction may differ, including the next address.
  With a model patched to Jolt's policy, no guest gets this verdict.
- `DIFFER`: any other difference, including a run that is not complete.
- Harness error: the comparison could not be made. This includes output that
  the parser does not recognise, a simulator that does not start or runs past
  `TIMEOUT`, and both runs reaching the instruction limit.

`difftest.py` exits with 0 for `AGREE`, 1 for `DIFFER`, 2 for a harness error
and 3 for `POLICY`. `python3 scripts/difftest/test_difftest.py` checks these
verdicts on canned traces, including each kind of failure that must not
become `AGREE` or `POLICY`; `all.sh` runs it first.

## What this does not test

The C++ emulator implements the model's external functions (memory, PMAs,
the platform, and in unpatched sail-riscv the LR/SC reservation) in C++. The
Lean model `LeanRV64D` implements them in `handwritten_support/RiscvExtras.lean`
or leaves them as axioms. A difference in those functions is a difference
between Jolt and the C++ emulator. It need not be a difference between Jolt and
the Lean model. Both simulators start from their own reset state; reset
differences are notes (see above).

## Requirements

- git, Python 3.11 or later, CMake, a C++ compiler, and Rust through rustup.
  The jolt-trace driver uses the toolchain in Jolt's `rust-toolchain.toml`.
- GMP with its headers, which the Sail C++ runtime links against (Homebrew
  `gmp`, Debian and Ubuntu `libgmp-dev`, Fedora `gmp-devel`). The emulator
  build needs it even when `SAIL_BIN` is set.
- A Sail compiler at the pinned version. Either set `SAIL_BIN` to one, or
  provide an opam switch that can build Sail and `build.sh` builds it.
- To assemble guests: clang with the `riscv64` target (Homebrew `llvm` works;
  Apple's clang does not), and `ld.lld` or the `rust-lld` that rustup installs.
  `toolchain.sh` finds them; set `CLANG` to the clang executable or `LLD` to
  the linker executable to override. Running ready ELFs does not need them.
- To generate the architectural tests only: Docker, see [Corpora](#corpora).

## Quick start

From a jolt-qed checkout, one command builds both simulators and runs every
guest set:

```sh
JOLT_DIR=~/src/jolt scripts/difftest/all.sh WORK_DIR
```

It runs the self-test, `build.sh`, the reproducers, riscv-tests, 1000 random
guests of each mix and the ACT4 tests, in that order. Then it prints one line
per set with its verdict counts, and writes the same lines to
`WORK_DIR/summary.txt`. Each set's output goes to `WORK_DIR/NAME.log`. The
exit status is 2 if the self-test or the build fails or a set could not run,
1 if a guest differs, and 0 otherwise. Besides the variables of `build.sh`,
`run.sh` and the corpus scripts, it reads:

| Variable | Meaning |
| --- | --- |
| `SEEDS` | Random guests per mix (default 1000). |
| `LENGTH` | Items per random guest (default 200). |
| `ACT4_ELF_DIR` | A directory of ready ACT4 ELFs. Without it they are generated with Docker, and with neither the ACT4 set does not run. |

The rest of this file describes the steps one at a time.

## Building

```sh
scripts/difftest/build.sh WORK_DIR
```

This builds `sail_riscv_sim` and `jolt-trace` under `WORK_DIR` and writes
`WORK_DIR/env.sh` with their paths. To test a Jolt branch, set `JOLT_DIR` to its
checkout; without it, a16z/jolt is cloned into `WORK_DIR/jolt` once.

To compare two Jolt versions, use one work directory per version and run the
same guests in both:

```sh
scripts/difftest/build.sh before
JOLT_DIR=~/src/jolt-branch scripts/difftest/build.sh after
```

To build the emulator from another jolt-qed branch's model patches and
configuration, set `PROVENANCE_ROOT` to that branch's checkout. `build.sh` then
reads `sail-import/PROVENANCE.toml` there, and the patches and configuration it
names.

Rerun `build.sh` after any change to `PROVENANCE.toml`. The emulator is rebuilt
when the model commit, the compiler (its pinned commit and patches, or the
`SAIL_BIN` executable) or any listed model patch changes. A new patch is
picked up once it is listed under `[model] patches`. A configuration change
needs no rebuild, because the emulator reads the configuration at run time.

## Running

```sh
scripts/difftest/run.sh WORK_DIR                 # every guest in guest/repro/
scripts/difftest/run.sh WORK_DIR prog.S other.elf
```

`.S` files are assembled for RV64IMAC with Zicsr and Zifencei and linked with
`guest/link.ld`. ELF files are used as they are. A guest must start at
`0x80000000` in M-mode and stop by writing an HTIF exit command to `tohost`.
`guest/common.h` gives the prologue, exit and trap handler that the
reproducers use.

`run.sh` prints one block per guest and a count of each verdict. It writes the
raw traces and a JSON result per guest to `WORK_DIR/results/`. Its exit status
is 1 if any guest has the verdict `DIFFER`, and 2 on a harness error: a guest
that does not assemble, or a harness error from `difftest.py`, which stops the
run at that guest. To compare one ELF directly, run
`scripts/difftest/difftest.py --help`.

These environment variables change a run:

| Variable | Meaning |
| --- | --- |
| `LIMIT` | Instruction limit per guest, at least 1 (default 100000). |
| `TIMEOUT` | Seconds each simulator may run per guest (default 600). A longer run is a harness error. |
| `EXPECT_CODE` | Exit code that every guest must end with. When both runs agree on another code, the guest did not do what it should, and the result is a harness error. Unset by default; the random corpus sets it to 0. |
| `JOLT_MSTATUS_OR` | Bits that Jolt ORs into its stored `mstatus` when the guest reads it. Set it to `0x1800` for Jolt versions that store only `MIE` and `MPIE` and read `MPP` as M. The default is 0. |
| `IGNORE_BITS` | Space-separated `CSR=MASK` pairs left out of the CSR comparison, such as `mstatus=0xa00000000` for the read-only `UXL` and `SXL` fields. Registers that a guest reads a CSR into are still compared. |
| `RESULTS` | Name of the results directory under `WORK_DIR` (default `results`). |

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
| `d4_lrd_scw.S` | LR.D followed by SC.W at the same address |
| `d5_resv_ecall.S`, `d6_resv_mret.S` | the reservation across an ECALL and its MRET, and across an MRET alone |
| `d7_resv_store.S` | the reservation across a store to the reserved word by the same hart |
| `d8_sc_clears.S` | a second SC after a successful SC, and an SC after a failing SC |
| `e_lr_misaligned.S`, `e2_sc_misaligned.S` | misaligned LR.W and SC.W |
| `f_mstatus_fs.S` | setting `mstatus.FS` |
| `g_ebreak.S` | EBREAK |
| `x_csr_forms.S` | CSRRC on `mscratch`, which Jolt main (9407f93fb) does not decode |

The comments in each file describe the behaviour of Jolt main (9407f93fb)
where they name it; later Jolt versions may differ.

## Corpora

Each corpus script takes the work directory and the settings that `run.sh`
takes, and writes its results to its own directory under `WORK_DIR`.

| Script | Guests | Results |
| --- | --- | --- |
| `corpus-riscv-tests.sh WORK_DIR [SUITE ...]` | riscv-tests, at a pinned commit; by default `rv64ui`, `rv64um`, `rv64ua`, `rv64uc` and `rv64mi` | `riscv-tests-results/` |
| `corpus-random.sh WORK_DIR [FIRST_SEED [COUNT [LENGTH]]]` | random RV64IMAC guests from `gen-random.py`, 100 seeds of 200 items by default, mix from `MIX` | `random-results/`, or `random-MIX-results/` |
| `corpus-arch-test.sh WORK_DIR [ELF_DIR]` | the RV64IMAC architectural tests (ACT4) that Jolt's CI runs | `arch-test-results/` |

These variables choose the corpus inputs:

| Variable | Meaning |
| --- | --- |
| `RISCV_TESTS_COMMIT` | riscv-tests commit to test (default in `corpus-riscv-tests.sh`). |
| `MIX` | `gen-random.py` mix for `corpus-random.sh`: `base` (default) or `system`. |
| `ACT4_JOLT_DIR` | Jolt checkout that provides ACT4 and the DUT configuration when `corpus-arch-test.sh` generates the ELFs (default: the `JOLT_DIR` that `build.sh` used). |

riscv-tests are built against `guest/riscv-tests-env/riscv_test.h`, a copy of
riscv-tests' `env/p` cut down to M-mode. It touches only `mtvec`, `mstatus` and
`mcause`, so a test that fails tests the instruction, not the environment.
riscv-tests is cloned into `WORK_DIR/riscv-tests` once. Every run checks it out
at `RISCV_TESTS_COMMIT`, with its `env` submodule at the revision that commit
records, and stops with status 2 if the checkout has local changes or if any
test does not build.

`gen-random.py SEED [LENGTH [MIX]]` writes one guest. It installs a trap
handler, sets the registers to random values and then runs LENGTH random
items. An item is one instruction or a short sequence. Memory accesses are
aligned and stay inside a 256-byte buffer, control flow only goes forwards,
and the guest stays in M-mode with `mstatus.MPRV` clear. The handler returns
past an ECALL and exits with code 2 on any other trap, so `corpus-random.sh`
runs with `EXPECT_CODE=0`. The same arguments always give the same guest. In
both mixes, about 8% of items are forward branches and jumps (a JALR item is
an `la` of the target followed by the `jalr`). There are two mixes:

- `base` (the default): otherwise single instructions: arithmetic, loads and
  stores, AMOs, single LR and SC instructions, the six CSR instructions on
  `mscratch`, and compressed instructions. Nothing traps.
- `system`: weighted towards machine-mode system state: the six CSR
  instructions on `mstatus`, `mscratch`, `mepc`, `mcause` and `mtval` with
  random operands, reads of `mtvec` and writes to its MODE field, ECALL, MRET
  on its own, and LR … SC sequences that mostly reuse the LR's address and
  width, sometimes with an ECALL or a store in between. The rest are `base`
  instructions. Each `mstatus` instruction is followed by setting `MPP` to M
  and clearing `MPRV`, and each lone MRET is preceded by setting `MPP` to M,
  so that MRET stays in M-mode on a model with U-mode too.

`corpus-random.sh` takes the mix from `MIX`. A mix other than `base` writes
to `random-MIX-results/`.

`corpus-arch-test.sh` runs the ACT4 self-checking ELFs built with the DUT
configuration in Jolt's `tests/arch-tests/jolt/`. Without `ELF_DIR` it
generates them first, by running Jolt's `make bootstrap` and
`make arch-tests-generate` in an `ubuntu:24.04` container, as Jolt's CI does.
ACT4 does not build natively on macOS, because its UDB gem downloads
Linux-only binaries. On a Mac without Docker, generate the ELFs on a Linux
machine with the same two targets and pass their directory as `ELF_DIR`. The
`sail_riscv_sim` that ACT4 uses only computes the signatures baked into the
ELFs; the comparison uses the emulator that `build.sh` built.

An ACT4 test that fails its own check halts through Jolt's `RVMODEL_HALT_FAIL`
macro. Up to Jolt 3414d2def the macro wrote `(gp << 1) | 1` to `tohost`.
When `gp` sets the HTIF device byte (bits 63 to 56), that value is not an exit
command: Sail ignores it and spins until `LIMIT`, and `jolt-trace` reports a
stall after a non-exit `tohost` write. Such a test differs. Since 3414d2def
the macro writes the exit command for code 1.

With a configuration that enables S- or U-mode, every `mstatus` read differs
in the read-only `UXL` and `SXL` fields: Sail reads them as 2, and Jolt has no
such fields. An M-only configuration reads them as 0.
