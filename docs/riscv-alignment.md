# Aligning Jolt with the RISC-V specification

This note fixes the machine that jolt-qed proves Jolt equivalent to.
Each section states one decision and argues for it from the RISC-V specification and from Jolt's code.
Later work (the Sail configuration, the model patches, the step-level and whole-run theorems) implements these decisions; when it finds that one is wrong, this note changes first.

This version holds the sections on the Sail model: the hart (1), the memory map (2), the reservation policy (3) and CSR legalization (4).
The sections on EBREAK, the step-level and whole-run theorems, Jolt's custom instructions and the remaining assumptions arrive with the PRs that add those proofs.

## Sources

- RISC-V ISA manual, riscv/riscv-isa-manual at `717aeca3` (2026-11-06).
  Citations give the file under `src/` and the normative anchor, for example `priv/machine.adoc` `norm:ld_rsv_rst`.
- RISC-V Debug Specification 1.0, section 4.9.1 (`dcsr`), for EBREAK.
- Jolt, a16z/jolt at `9407f93f` (2026-11-06), for Jolt as it stands on `main`.
  jolt-qed's expansions were generated from `c6703570`.
  Every Jolt file cited below is identical at the two commits, except four added lines in `tracer/src/emulator/cpu.rs` that do not touch the code cited.
- The Jolt changes for this alignment, a16z/jolt `c336a6da7`, the head of a16z/jolt#2384 (stacked on a16z/jolt#2383, with `main` merged in after a16z/jolt#2381).
- The Sail model: abiswas3/sail-riscv at `266473f8`, as recorded in `sail-import/PROVENANCE.toml`, and upstream riscv/sail-riscv at `81184531` where this note backports a fix.

## 1. The hart: RV64IMAC, M-mode only, no interrupts

Jolt's machine is a single RV64 hart that runs only in M-mode.
Jolt's tracer starts in `PrivilegeMode::Machine` and no instruction it accepts changes privilege (`tracer/src/emulator/cpu.rs`, `Cpu::new`).
Jolt's decoder (`tracer/src/instruction/mod.rs`, `Instruction::decode`) accepts exactly:

- RV64I, without FENCE.I and without WFI: FENCE is accepted only with funct3 = 0, and the SYSTEM opcode only for ECALL, EBREAK, MRET, CSRRW and CSRRS;
- M (all of RV64M);
- A (Zalrsc and Zaamo, word and doubleword; no Zabha, no Zacas);
- Zca: `uncompress_instruction` expands C.FLD and C.FSD into F-extension words that the decoder then rejects, and treats the Zcb encodings as reserved, so neither Zcd nor Zcb is accepted;
- from Zicsr, only CSRRW and CSRRS, and only on `mstatus`, `mtvec`, `mscratch`, `mepc`, `mcause` and `mtval` (`tracer/src/utils/virtual_registers.rs`, `is_supported_csr`); the Jolt changes for this alignment (`c336a6da7`, a16z/jolt#2383 and #2384) add CSRRC, CSRRWI, CSRRSI and CSRRCI on the same six CSRs, and with them Jolt accepts all of Zicsr on those CSRs; funct3 4 stays reserved;
- Jolt's own instructions on the custom-2 major opcode `0x5B` (advice loads, `VirtualRev8W`, `VirtualAssertEQ`, `VirtualHostIO`);
- the inline opcodes `0x0B` (custom-0) and `0x2B` (custom-1), which are out of scope for now.

Every other encoding makes Jolt's tracer panic, so no run that contains one has a Jolt trace.

The Sail model is therefore configured as RV64IMAC with Zicsr and only these extensions.
S, U, F, D, V, H, B and every Zb*, Zk*, Zv*, Zf*, Zicbo*, Zicond, Zicntr, Zihpm, Zifencei, Zimop, Zcb, Zcd, Zcmop, Zawrs, Zabha, Zacas, Sstc, Sscofpmf, Smcntrpmf, Smstateen, Ssqosid and Svinval are off; `misa` is read-only.
PMP has no entries (`memory.pmp.count = 0`), so the PMP check never faults: Jolt's MMU implements no memory protection (`tracer/src/emulator/mmu.rs`).
Ziccamoa and Ziccrse stay on: they only state that main memory supports every A-extension AMO and eventual LR/SC success, which the RAM region below provides.
`memory.dtb_address` is 0; it is read only by the C++ emulator's boot code, which the theorems do not use.
Address translation is Svbare only, which is what an M-mode-only hart has: `satp` does not exist without S-mode, and Jolt's MMU never leaves `AddressingMode::None` (`tracer/src/emulator/mmu.rs`).
The specification allows an M-only hart: `priv/machine.adoc` `norm:mstatus_xpp_warl` says MPP "can hold only privilege mode _x_ and any implemented privilege mode lower than _x_", so with no lower mode MPP always reads 3.

No interrupt is ever taken.
Sail takes an M-mode interrupt only when a bit is set in both `mip` and `mie` (`priv/machine.adoc` `norm:mip_mie_enc_txt`).
Jolt's decoder rejects every access to `mie` (CSR `0x304`) and `sie`, so no Jolt run can write `mie`; the step-level proof carries the invariant `mie = 0` from the initial state.
Jolt's own tracer reaches the same conclusion from the other side: `mip` is never written, so `Cpu::tick` never calls `handle_interrupt`.
With Sstc, Sscofpmf and the counters off, no Sail-side event changes what a Jolt run can observe.
The instruction and cycle counters still advance in Sail (`minstret` in `run_hart_active`); Jolt cannot read them, so the equivalence relation ignores them.

## 2. Memory map as physical-memory attributes

The specification describes memory regions by their physical-memory attributes (PMAs, `priv/machine.adoc` section "Physical Memory Attributes"), and the Sail configuration lists regions with exactly these attributes.
Jolt's address space has two parts (`common/src/jolt_device.rs`, `MemoryLayout::new`):

- RAM starts at `RAM_START_ADDRESS = 0x8000_0000` and holds the program image, the stack and the heap.
- The I/O window `[io_start, 0x8000_0000)` lies directly below RAM.
  It holds trusted advice, untrusted advice, inputs, outputs, the panic word and the termination word, in that order; `io_start = 0x8000_0000 - 8·2^k` depends on the sizes the program is configured with.

The Sail configuration has two regions, and nothing else is readable, writable or executable:

| Region | Range | R | W | X | Atomics | Reservability |
| --- | --- | --- | --- | --- | --- | --- |
| RAM | `[0x8000_0000, 2^64)` | yes | yes | yes | AMOArithmetic | RsrvEventual |
| I/O | `[IO_BASE, 0x8000_0000)` | yes | yes | no | AMOArithmetic | RsrvNone |

`IO_BASE` is a fixed platform constant, `0x4000_0000`; the whole-run theorem assumes `IO_BASE ≤ io_start`, which every layout with an I/O window of at most 1 GiB satisfies.
The device-tree region at `0x1000` is removed, because Jolt has no device tree.
The CLINT stays where the Sail model needs it (`0x0200_0000`), outside both regions; Jolt panics on any access to it (`mmu.rs`, `load_raw` and `store_raw`), so it is not reachable from a Jolt trace.

The PR that adds the whole-run theorem also adds a Lean copy of these regions and a check in `scripts/check-sail-model.sh` that keeps the two the same.
Each region is a superset of what Jolt allows, which is the direction the whole-run theorem needs.
Jolt's tracer additionally panics on stores into the stack canary, on accesses at or above `heap_end`, on stores to the read-only parts of the I/O window, and on fetches outside the program's bytecode.
Those runs have no Jolt trace, so the theorem never has to say what Sail does on them.
Reservability and atomics are restricted the way Jolt restricts them: Jolt's LR and SC expansions assert `rs1 ≥ 0x8000_0000` before touching the reservation (`crates/jolt-program/src/expand/memory/lrw.rs`, `lrd.rs`, `shared.rs` `expand_sc_success`).
Jolt's platform allows AMOs anywhere its MMU accepts a load and a store, including the output region: its AMO expansions load and store the doubleword through the ordinary MMU.
The specification leaves a region's atomics to the platform, so the I/O region's atomics are our modelling choice, not a property of Jolt, and AMONone would be wrong for Jolt's platform.
The I/O region therefore has AMOArithmetic (`sail-import/rv64d_jolt.json`), keeping RsrvNone, which stays exact because LR and SC assert RAM.

The I/O window is not plain memory in Jolt: a store to the panic word sets a flag whatever the value, and the termination word ignores stores and always reads 0 (`JoltBytecode/JoltISA/JoltDevice.lean`, `load?` and `store?`).
The specification leaves the behaviour of I/O regions to the platform, so this is not a deviation from RISC-V; it is a difference between Jolt's platform and the Sail model's flat memory.
The whole-run theorem relates the two through the device relation already used by `DeviceMemory.lean`, and reads the panic and termination flags as "the word is nonzero"; a guest that reads back the panic or termination word after writing it is the one documented case where the two platforms differ.

## 3. Reservation policy

The Sail model holds the reservation in registers of its own, replacing the external functions of `model/sys/sys_reservation.sail`.
The policy:

1. LR records one reservation: the address `a` and the width `w` (4 or 8 bytes).
   LR to a region with reservability RsrvNone raises a load access fault.
2. SC at address `a'` with width `w'` succeeds exactly when a reservation is held, `a' = a` and `w' ≤ w`.
3. Every SC that does not raise an exception cancels the reservation, whether it succeeds or fails.
4. Reset leaves no reservation.
5. Traps, MRET and stores by the same hart keep the reservation.

Each rule is what the specification requires or one of the choices it permits:

- Rule 2: an SC "succeeds only if the reservation is still valid and the reservation set contains the bytes being written" (`unpriv/zalrsc.adoc` `norm:sc-w_success`).
  With the reservation set equal to the bytes the LR read, `w' ≤ w` at the same address is exactly containment for naturally aligned accesses.
  Failing more often is always allowed, since the specification only requires eventual success for constrained loops, which pair an LR and an SC of the same address and width.
- Rule 3: "Regardless of success or failure, executing an SC.W instruction invalidates any reservation held by this hart" (`unpriv/zalrsc.adoc` `norm:sc_reservation_invalidate`).
- Rule 4: `priv/machine.adoc` `norm:ld_rsv_rst`.
- Rule 5: xRET "is allowed to clear any outstanding LR address reservation but is not required to" (`priv/machine.adoc` `norm:xret_clr_lr_resv`).
  Nothing in the specification requires a trap or a store by the same hart to invalidate it; the SC must fail only after an intervening SC, after a store by another hart or device, or when its address is outside the reservation set (`unpriv/zalrsc.adoc` `norm:sc_addr_not_in_reservation_fail` and the two rules after it).

This is Jolt's policy as it stands.
LR.W sets the word reservation register `v32` to the address and clears the doubleword register `v33`; LR.D sets both; SC.W compares against `v32`, SC.D against `v33`; both clear both registers; nothing else writes them (`crates/jolt-program/src/expand/memory/`).
The address 0 encodes "no reservation", which is sound because LR asserts that the address is at least `0x8000_0000`.
Jolt's tracer implements the same rule as `Cpu::reservation_covers` (`tracer/src/emulator/cpu.rs`).

Upstream sail-riscv matches on the address alone (exactly or within a granule) and has no width condition.
The width condition is needed here because the reservation set is exactly the bytes of the LR: an LR.W followed by an SC.D at the same address must fail.
The model patch (`sail-import/patches/sail-riscv-jolt-hart.patch`) implements the policy with three registers, `reservation_valid`, `reservation_addr` and `reservation_width`, and three options under `platform.reservation`: upstream's `require_exact_reservation_addr` and `invalidate_on_xret`, and a new `require_width_within`, which can be proposed upstream.
The configuration sets them to `true`, `false` and `true`.
Upstream's `invalidate_on_same_hart_store` is implemented outside the model (in the C++ emulator), so it is not part of the patch; leaving it out is rule 5.

Two differences remain between Jolt and this policy, and neither changes the architectural state:

- A failed SC in Jolt stores the old value back (`scw.rs`, `scd.rs`), where the specification says a failed SC "does not write to memory" (`unpriv/zalrsc.adoc` `norm:sc-w_failure`).
  On a single hart, writing a RAM word with its own value leaves memory unchanged, so the Sail state and the Jolt state still correspond.
  The only effect is that Jolt's store checks apply to a failed SC, so Jolt rejects some runs that Sail would complete; that costs Jolt completeness, not soundness.
- A misaligned LR or SC makes Jolt's tracer panic (`mmu.rs`, `load_word`), so no Jolt trace contains one.
  The specification requires an address-misaligned or access-fault exception (`unpriv/zalrsc.adoc` `norm:lr_sc_alignment`), and LR raises the load exception (`priv/machine.adoc` `norm:mcause_exccode_ld_ldrsv`).
  So a misaligned LR or SC has no Jolt step, and the theorems state it that way: the instruction theorems assume natural alignment, and the whole-run theorem never meets the case.
  jolt-qed's generated LR and SC programs mark their inner load with `LoadFaultClass.amo`, which only selects the exception class reported on a misaligned access (`JoltBytecode/JoltISA/Instruction.lean`); on an aligned access the row is the same as the plain `LW`/`LD` that Jolt's LR and SC emit on `main`.
  Decision (step d): keep the programs as generated. With alignment a hypothesis of the LR/SC theorems, the marker is never consulted, and the row sequences otherwise match `lrw.rs`, `lrd.rs`, `scw.rs` and `scd.rs` row for row.

The Jolt state relates to the model's three registers as follows, with `w = v32` and `d = v33`:

| Sail register | Value |
| --- | --- |
| `reservation_valid` | `w ≠ 0` |
| `reservation_addr` | `w` |
| `reservation_width` | `0` if `w = 0`, else `8` if `d = w`, else `4` |

with the invariant `d = 0 ∨ d = w`, which LR.W (`w := a`, `d := 0`), LR.D (`w := d := a`) and SC (`w := d := 0`) keep, and no other instruction writes either register.
Under it, SC.W succeeds in Jolt exactly when `w = a'` and SC.D exactly when `d = a'`; since `a' ≥ 0x8000_0000 > 0`, these are rule 2 for widths 4 and 8.

For the relation to be a function of `(w, d)`, "no reservation" must have one Sail representation.
Upstream's `cancel_reservation` clears only `reservation_valid` and leaves a stale address and width, which no Jolt state can name.
Decision (step d): the model patch makes `cancel_reservation` also reset the address to 0 and the width to 0.
The address and width are read only together with `reservation_valid` (`match_reservation`), so this changes no behaviour, and the three registers then hold their reset values after every cancel, as after reset.

## 4. CSR legalization

The six CSRs Jolt accepts behave as follows on an M-only hart with Zca and without F, S, U, V, H, Zicfilp and Smdbltrp.
The Jolt-changes stream implements these sequences in Jolt; step b checks them against the regenerated model.

- `mstatus`: Jolt keeps only MIE and MPIE in `v39`, and every read returns `v39 | 0x1800`.
  The relation is `mstatus = v39 | 0x1800` with the invariant `v39 & ~0x88 = 0`; both hold at reset, where `v39 = 0` and Sail's `mstatus = 0x1800`.
  A write of `v` stores `v & 0x88` in `v39`, so the architectural value becomes `0x1800 | (v & 0x88)`.
  MPP is always 3 (`norm:mstatus_xpp_warl`).
  MIE (bit 3) and MPIE (bit 7) are writable.
  FS is read-only zero because neither F nor S is implemented (`priv/machine.adoc` `norm:mstatus_fs_acc2`), so SD is zero too (`norm:mstatus_sd_rdonly0`).
  MPRV, TW, TSR, TVM, MXR, SUM, VS, XS and the endianness and XLEN fields are read-only zero or fixed, because the modes and extensions they control are absent.
- ECALL from M-mode (trap entry, `norm:mstatus_xpie_xie_xpp_trap_op`): `mstatus := 0x1800 | ((mstatus & 0x8) << 4)`, that is, MPIE := MIE, MIE := 0, MPP := M; `mepc := pc`; `mcause := 11`; `mtval := 0`; the PC goes to the trap vector base.
- MRET (`norm:mstatus_xret_op`): `mstatus := 0x1880 | ((mstatus >> 4) & 0x8)`, that is, MIE := MPIE, MPIE := 1, MPP := M (the least-privileged implemented mode); the PC goes to `mepc`.
- `mtvec`: a write of `v` stores `v` when the mode bits are Direct (0) or Vectored (1), and `(v & ~3) | (old & 3)` when bit 1 of `v` is set, because the configuration's `xtvec_mode = Xtvec_Ignore` keeps the old mode on a reserved mode (`norm:mtvec_sz_warl_acc`, `norm:mtvec_mode_enc`).
  Every trap a Jolt run can take is synchronous, and synchronous exceptions go to the base in both modes (`norm:mtvec_mode_vectored_op`), which is what Jolt's `JALR v40, v34, 0` reaches: the JALR clears bit 0, and bit 1 is 0 in both legal modes.
- `mepc`: a write of `v` stores `v & ~1`, because with Zca IALIGN is 16 (`norm:mepc_align`).
- `mcause`, `mtval`, `mscratch`: stored as written.
  For `mcause` this is a choice: the Exception Code field is WLRL, so an implementation may store any value written, and the model at `266473f8` does (`model/core/sys_regs.sail`, `write_CSR(0x342, …)`).
  Newer upstream models legalize it (`legalize_cause` keeps the old value on an unsupported code); the pinned model does not, and Jolt stores every write raw, so the two agree.

The other five relations are equality, `mtvec = v34`, `mscratch = v35`, `mepc = v36`, `mcause = v37` and `mtval = v38`, with the invariants `v34[1] = 0` and `v36[0] = 0`.
The reset values must match as well: Sail must reset `mstatus` to `0x1800`.
The previous configuration reset MPP to U and UXL = SXL = 2, because U- and S-mode were on (difftest findings a2 and UXL/SXL).
With both off, UXL = SXL = 0 (the `mstatus` initialiser sets them only when S or U is supported), but the model's `mstatus` initialiser still set MPP to 0, a mode the hart does not have; this is a bug in the model at `266473f8` and in upstream `81184531` alike.
The model patch initialises MPP to M when U-mode is absent (`norm:mstatus_xpp_warl`), so Sail's `mstatus` resets to `0x1800`.

The Sail model at `266473f8` keeps FS writable unless Zfinx is on, which contradicts `norm:mstatus_fs_acc2`, and then computes SD from it.
Upstream fixed this in `81184531` by legalizing FS through the platform's supported values (`base.mstatus.fs_legal_states`); the model patch backports that fix, the configuration sets `ExtContext_Off`, and the `mstatus` mask above holds only with it.
