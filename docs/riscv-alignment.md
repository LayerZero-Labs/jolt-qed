# Aligning Jolt with the RISC-V specification

This note fixes the machine that jolt-qed proves Jolt equivalent to.
Each section states one decision and argues for it from the RISC-V specification and from Jolt's code.
Later work (the Sail configuration, the model patches, the step-level and whole-run theorems) implements these decisions; when it finds that one is wrong, this note changes first.

## Sources

- RISC-V ISA manual, riscv/riscv-isa-manual at `717aeca3` (2026-11-06).
  Citations give the file under `src/` and the normative anchor, for example `priv/machine.adoc` `norm:ld_rsv_rst`.
- RISC-V Debug Specification 1.0, section 4.9.1 (`dcsr`), for EBREAK.
- Jolt, a16z/jolt at `9407f93f` (2026-11-06).
  jolt-qed's expansions were generated from `c6703570`.
  Every Jolt file cited below is identical at the two commits, except four added lines in `tracer/src/emulator/cpu.rs` that do not touch the code cited.
- The Sail model: abiswas3/sail-riscv at `266473f8`, as recorded in `sail-import/PROVENANCE.toml`, and upstream riscv/sail-riscv at `81184531` where this note backports a fix.

## 1. The hart: RV64IMAC, M-mode only, no interrupts

Jolt's machine is a single RV64 hart that runs only in M-mode.
Jolt's tracer starts in `PrivilegeMode::Machine` and no instruction it accepts changes privilege (`tracer/src/emulator/cpu.rs`, `Cpu::new`).
Jolt's decoder (`tracer/src/instruction/mod.rs`, `Instruction::decode`) accepts exactly:

- RV64I, without FENCE.I and without WFI: FENCE is accepted only with funct3 = 0, and the SYSTEM opcode only for ECALL, EBREAK, MRET, CSRRW and CSRRS;
- M (all of RV64M);
- A (Zalrsc and Zaamo, word and doubleword; no Zabha, no Zacas);
- Zca: `uncompress_instruction` expands C.FLD and C.FSD into F-extension words that the decoder then rejects, and treats the Zcb encodings as reserved, so neither Zcd nor Zcb is accepted;
- from Zicsr, only CSRRW and CSRRS, and only on `mstatus`, `mtvec`, `mscratch`, `mepc`, `mcause` and `mtval` (`tracer/src/utils/virtual_registers.rs`, `is_supported_csr`);
- Jolt's own instructions on the custom-2 major opcode `0x5B` (advice loads, `VirtualRev8W`, `VirtualAssertEQ`, `VirtualHostIO`; section 7);
- the inline opcodes `0x0B` (custom-0) and `0x2B` (custom-1), which are out of scope for now.

Every other encoding makes Jolt's tracer panic, so no run that contains one has a Jolt trace.

The Sail model is therefore configured as RV64IMAC with Zicsr and only these extensions.
S, U, F, D, V, H, B and every Zb*, Zk*, Zv*, Zf*, Zicbo*, Zicond, Zicntr, Zihpm, Zifencei, Zimop, Zcb, Zcd, Zcmop, Zawrs, Zabha, Zacas, Sstc, Sscofpmf, Smcntrpmf, Smstateen, Ssqosid and Svinval are off; `misa` is read-only.
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
| RAM | `[0x8000_0000, top)`, `top` as high as the configuration format allows | yes | yes | yes | AMOArithmetic | RsrvEventual |
| I/O | `[IO_BASE, 0x8000_0000)` | yes | yes | no | AMONone | RsrvNone |

`IO_BASE` is a fixed platform constant, `0x4000_0000`; the whole-run theorem assumes `IO_BASE ≤ io_start`, which every layout with an I/O window of at most 1 GiB satisfies.
The device-tree region at `0x1000` is removed, because Jolt has no device tree.
The CLINT stays where the Sail model needs it (`0x0200_0000`), outside both regions; Jolt panics on any access to it (`mmu.rs`, `load_raw` and `store_raw`), so it is not reachable from a Jolt trace.

Each region is a superset of what Jolt allows, which is the direction the whole-run theorem needs.
Jolt's tracer additionally panics on stores into the stack canary, on accesses at or above `heap_end`, on stores to the read-only parts of the I/O window, and on fetches outside the program's bytecode.
Those runs have no Jolt trace, so the theorem never has to say what Sail does on them.
Reservability and atomics are restricted the way Jolt restricts them: Jolt's LR and SC expansions assert `rs1 ≥ 0x8000_0000` before touching the reservation (`crates/jolt-program/src/expand/memory/lrw.rs`, `lrd.rs`, `shared.rs` `expand_sc_success`).

The I/O window is not plain memory in Jolt: a store to the panic word sets a flag whatever the value, and the termination word ignores stores and always reads 0 (`JoltBytecode/JoltISA/JoltDevice.lean`, `load?` and `store?`).
The specification leaves the behaviour of I/O regions to the platform, so this is not a deviation from RISC-V; it is a difference between Jolt's platform and the Sail model's flat memory.
The whole-run theorem relates the two through the device relation already used by `DeviceMemory.lean`, and reads the panic and termination flags as "the word is nonzero"; a guest that reads back the panic or termination word after writing it is the one documented case where the two platforms differ.

Open item, settled in step f: Jolt's tracer lets a load read any address at or below `0x8000_0000 - 8` and returns 0 there (`mmu.rs`, `assert_effective_address` and `load_raw`), while Sail raises a load access fault outside the two regions.
Jolt's prover maps RAM addresses through `MemoryLayout::remap_word_address`, which rejects addresses below `io_start`, so such a load is expected to be outside every honest trace.
If step f finds an honest trace that contains one, Jolt has to fault there instead, and that goes to the Jolt-changes stream.

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
The patch offers it as an option next to upstream's `require_exact_reservation_addr`, `invalidate_on_xret` and `invalidate_on_same_hart_store`, so it can be proposed upstream.

Two differences remain between Jolt and this policy, and neither changes the architectural state:

- A failed SC in Jolt stores the old value back (`scw.rs`, `scd.rs`), where the specification says a failed SC "does not write to memory" (`unpriv/zalrsc.adoc` `norm:sc-w_failure`).
  On a single hart, writing a RAM word with its own value leaves memory unchanged, so the Sail state and the Jolt state still correspond.
  The only effect is that Jolt's store checks apply to a failed SC, so Jolt rejects some runs that Sail would complete; that costs Jolt completeness, not soundness.
- A misaligned LR or SC makes Jolt's tracer panic (`mmu.rs`, `load_word`), so no Jolt trace contains one.
  The specification requires an address-misaligned or access-fault exception (`unpriv/zalrsc.adoc` `norm:lr_sc_alignment`), and LR raises the load exception (`priv/machine.adoc` `norm:mcause_exccode_ld_ldrsv`).
  jolt-qed's generated LR programs currently tag their alignment exception as `E_SAMO_Addr_Align`; step d changes that tag to `E_Load_Addr_Align`, so that the instruction-level theorem agrees with Sail on misaligned addresses too.

## 4. EBREAK halts the run

Jolt treats EBREAK as the end of the program: `EBREAK::exec` leaves the PC unchanged, and the tracer stops when the PC does not change (`tracer/src/instruction/ebreak.rs`, `Cpu::tick`).
jolt-qed's expansion is the self-jump `JAL v40, 0`.

The RISC-V reading is the Debug Specification's `dcsr.ebreakm`: when it is 1, EBREAK in M-mode enters Debug Mode instead of raising a breakpoint exception (Debug Specification 1.0, section 4.9.1).
The prover is the external debugger that set `ebreakm` and ends the session when the hart halts.
The Sail model does not implement the debug extension, so the halt is stated outside the model: the whole-run theorem ends at the first state whose next instruction is EBREAK or C.EBREAK and does not execute it.
No model patch is needed, and the Sail model stays a plain specification of the base and privileged architecture.

The same treatment covers the other way a Jolt run stops, a jump to itself (a16z/jolt PR #2109): in Sail, executing such a jump changes only the counters, so the Sail state reached is a fixed point of the observation, and the theorem can stop there as well.

## 5. Equivalence is stated against `try_step`

The existing instruction theorems compare a Jolt expansion with Sail's `execute_X` from a state in which `nextPC` is already set.
That leaves out fetch, decode, interrupt dispatch, trap entry and the PC update, which is where several of the gaps sit (ECALL's trap entry, MRET's privilege stack).
The step-level theorems are therefore stated against `try_step` (`LeanRV64D/Step.lean`), the function the Sail emulator calls once per instruction: it dispatches interrupts, fetches, decodes with `ext_decode` or `ext_decode_compressed`, sets `nextPC`, executes, enters the trap handler on an exception, and commits the PC.

The relation between a Jolt state and a Sail state compares:

- the PC and the 31 general-purpose registers;
- RAM bytes, and the I/O window through the device relation of section 2;
- the six CSRs, read from Jolt's virtual registers `v34`-`v39`;
- the reservation, read from `v32` and `v33` (section 3);
- Jolt's platform state, the advice tape and the device, which only the custom instructions of section 7 and the I/O window touch.

It also requires the invariants: privilege is Machine, `mie = 0`, `misa` is fixed, and the read-only `mstatus` fields have the values of section 6.
Counters and Sail-internal registers are not compared.
A generic lifting lemma turns each existing `execute_X` theorem into a `try_step` theorem, by discharging fetch and decode for the instruction's encoding and the PC update once.

## 6. CSR legalization

The six CSRs Jolt accepts behave as follows on an M-only hart with Zca and without F, S, U, V, H, Zicfilp and Smdbltrp.
The Jolt-changes stream implements these sequences in Jolt; step b checks them against the regenerated model.

- `mstatus`: a write of `v` stores `0x1800 | (v & 0x88)`.
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

The Sail model at `266473f8` keeps FS writable unless Zfinx is on, which contradicts `norm:mstatus_fs_acc2`, and then computes SD from it.
Upstream fixed this in `81184531` by legalizing FS through the platform's supported values; step b backports that fix, and the `mstatus` mask above holds only with it.

## 7. Jolt's custom instructions

Jolt's guest programs may contain Jolt's own instructions on major opcode `0x5B`, which the specification's opcode map marks custom-2, reserved for custom extensions (`unpriv/rv-32-64g.adoc`, opcode map and the paragraph after it).
They are not RISC-V instructions, so the Sail model does not decode them, and patching them into the model would make the trusted model depend on Jolt.
The step-level and whole-run theorems instead use a platform step: on a `0x5B` encoding it runs a short Lean specification of Jolt's instruction, and on every other encoding it runs `try_step`.
Advice loads read from the advice tape, which the whole-run theorem quantifies over as a private input.
`VirtualAssertEQ` has no successor state when its operands differ.
`VirtualHostIO` changes no RISC-V state: it reads guest memory for the host call named in `a0`, and the advice-write call appends those bytes to the advice tape (`JoltBytecode/JoltISA/HostIO.lean`), so the tape is part of the platform state that the relation of section 5 carries.
`VirtualRev8W` reverses the bytes within each 32-bit half of a register.
The inline opcodes `0x0B` and `0x2B` are out of scope for now and are excluded the way `SourceInstruction` already excludes them.

## 8. Remaining assumptions and where they go

Step b produces a table of every assumption the instruction theorems use, classified as a configuration fact (removed), a lemma (proved), or still assumed.
Step f classifies whatever is left in the whole-run theorem as an invariant, a platform fact (sections 2, 4 and 7) or a documented deviation (the read-back of the panic and termination words in section 2, and anything the difference testing confirms).
