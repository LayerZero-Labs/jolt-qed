# Aligning Jolt with the RISC-V specification

This note fixes the machine that jolt-qed proves Jolt equivalent to.
Each section states one decision and argues for it from the RISC-V specification and from Jolt's code.
Later work (the Sail configuration, the model patches, the step-level and whole-run theorems) implements these decisions; when it finds that one is wrong, this note changes first.

## Sources

- RISC-V ISA manual, riscv/riscv-isa-manual at `717aeca3` (2026-11-06).
  Citations give the file under `src/` and the normative anchor, for example `priv/machine.adoc` `norm:ld_rsv_rst`.
- RISC-V Debug Specification 1.0, section 4.9.1 (`dcsr`), for EBREAK.
- Jolt, a16z/jolt at `9407f93f` (2026-11-06), for Jolt as it stands on `main`.
  jolt-qed's expansions were generated from `c6703570`.
  Every Jolt file cited below is identical at the two commits, except four added lines in `tracer/src/emulator/cpu.rs` that do not touch the code cited.
- The Jolt changes for this alignment, a16z/jolt `c336a6da7`, the head of a16z/jolt#2384 (stacked on a16z/jolt#2383, with `main` merged in after a16z/jolt#2381).
  The inline expansions under `crates/jolt-program/src/expand`, `crates/jolt-program/src/image/decode.rs`, `crates/jolt-program/src/image/elf.rs` (`decode_elf`) and `crates/jolt-riscv/src/uncompress.rs` are transcribed from this commit.
  It contains a16z/jolt#2381, which rejects the reserved C.LUI parcel (section 5).
  The pin moves to a16z/jolt `main` once a16z/jolt#2383 and #2384 merge.
  The system expansions (`JoltBytecode/JoltISA/Expansions/System.lean`) and the decoder (`JoltBytecode/Decode/Jolt.lean`) transcribe this revision, not `9407f93f`: there, a CSR read of `mstatus` returns `v39 | 0x1800`, MRET restores `mstatus` before it jumps, and the decoder accepts CSRRC, CSRRWI, CSRRSI and CSRRCI.
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
- Jolt's own instructions on the custom-2 major opcode `0x5B` (advice loads, `VirtualRev8W`, `VirtualAssertEQ`, `VirtualHostIO`; section 7);
- the inline opcodes `0x0B` (custom-0) and `0x2B` (custom-1). `SourceInstruction` includes twelve registered inlines (five hash, seven secp256k1) at `0x0B`, but the whole-run theorem leaves all inline rows out of scope for now (section 7).

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

The Lean side takes the regions from `JoltConstraints/WholeRun/Relation.lean` (`ioRegion`, `ramRegion`, `platformPma`), not from the json, and `scripts/check-sail-model.sh` keeps the two the same.
Each region is a superset of what Jolt allows, which is the direction the whole-run theorem needs.
Jolt's tracer additionally panics on stores into the stack canary, on accesses at or above `heap_end`, on stores to the read-only parts of the I/O window, and on fetches outside the program's bytecode.
Those runs have no Jolt trace, so the theorem never has to say what Sail does on them.
Reservability and atomics are restricted the way Jolt restricts them: Jolt's LR and SC expansions assert `rs1 ≥ 0x8000_0000` before touching the reservation (`crates/jolt-program/src/expand/memory/lrw.rs`, `lrd.rs`, `shared.rs` `expand_sc_success`).
Jolt's platform allows AMOs anywhere its MMU accepts a load and a store, including the output region: its AMO expansions load and store the doubleword through the ordinary MMU.
The specification leaves a region's atomics to the platform, so the I/O region's atomics are our modelling choice, not a property of Jolt, and AMONone would be wrong for Jolt's platform.
The I/O region therefore has AMOArithmetic (`Relation.lean` and `sail-import/rv64d_jolt.json`), keeping RsrvNone, which stays exact because LR and SC assert RAM.
Every AMO block is then in RAM or in the I/O window, and the whole-run theorem needs no premise placing AMOs in RAM: `access_classified` (`WholeRun/RunInv.lean`) classifies a block as a RAM access, an I/O load or store, or an I/O AMO (`IoAmoAccess`: a word or doubleword AMO whose containing doubleword lies below `0x8000_0000`), `block_simulates_io_amo` (`WholeRun/IoAmo.lean`) simulates the last kind, and `block_simulates_image` (`WholeRun/Decoded.lean`) combines the three.
An I/O AMO takes one deviation premise, `AmoNoFlagWord`: no byte of the doubleword it reads and writes is a byte of the panic or termination word, because Jolt's device turns a store of the panic byte into the flag and ignores every other store to those words, while Sail stores the bytes (for example `AMOADD.D` at the panic address).
The premise covers the AMO's whole doubleword, also for a word AMO, because Jolt's word AMO stores the whole doubleword back. The difference test confirms it: `AMOADD.W` on the high word of the panic doubleword sets Jolt's panic flag, and a premise on the word alone would miss it. In the same rerun, AMOs on the output region that avoid the flag words agree.
Two premises that the loads and stores need are not needed here.
First, no low-address premise: a retiring AMO stores to its doubleword, and Jolt's tracer accepts a store only at or above `output_start`, which is at least `memLow`, so the load half reads above `memLow` too.
Second, no panic-store premise: under `AmoNoFlagWord` the stored doubleword holds no flag byte, so `PanicStoreNonzero` holds trivially.
Misalignment needs no premise either: Jolt's `LD` and `SD` rows assert `addr & 7 = 0` and its word lane rows (`VirtualLoadW`, `VirtualStoreW`) assert `ea & 3 = 0`, so a misaligned I/O AMO faults in Jolt as it does in Sail (Sail checks natural alignment before the PMA), and Jolt never retires where Sail faults.

The I/O window is not plain memory in Jolt: a store to the panic word sets a flag whatever the value, and the termination word ignores stores and always reads 0 (`JoltBytecode/JoltISA/JoltDevice.lean`, `load?` and `store?`).
The specification leaves the behaviour of I/O regions to the platform, so this is not a deviation from RISC-V; it is a difference between Jolt's platform and the Sail model's flat memory.
The whole-run theorem relates the two through the device relation already used by `DeviceMemory.lean`, and reads the panic and termination flags as "the word is nonzero"; a guest that reads back the panic or termination word after writing it is the one documented case where the two platforms differ.

Open item, a premise of step f: Jolt's tracer lets a load read any address at or below `0x8000_0000 - 8` and returns 0 there (`mmu.rs`, `assert_effective_address` and `load_raw`), while Sail raises a load access fault outside the two regions.
Jolt's prover maps RAM addresses through `MemoryLayout::remap_word_address`, which rejects every nonzero address below the lowest address of the memory layout.
Step f uses that check: `HaltPrefix.traced` ties each block to its first trace row, and `Block.FirstRowAt.noLowLoad` derives `NoLowLoad` from the RAM address that row records.
One case remains.
A byte, halfword or word load records the address of its doubleword, which is 0 when the effective address is below 8, and the prover reads recorded address 0 as no access.
An LD records its own effective address: an LD at address 0 also escapes the check, and the check rejects an LD at addresses 1 to 7 when they are below the lowest address.
The whole-run theorem keeps the case as the per-block premise `NoZeroDoublewordLoad` (section 9), which asks every load, LD included, for an effective address of at least 8, to state one bound for every width.
A fault in Jolt's tracer for loads below the lowest address would remove it, and that goes to the Jolt-changes stream.

The theorem for blocks that access the I/O window (`WholeRun/Io.lean`, `block_simulates_io`) takes three deviation hypotheses, one for each difference above: `NoFlagWordLoad` (no load reads a byte of the panic or termination word), `PanicStoreNonzero` (a store that touches the panic doubleword leaves Sail's panic word nonzero, which excludes a store that zeroes the only nonzero byte of the word, because Jolt's flag is set by any such store) and `NoLowLoad` (no load reads below the lowest address Jolt's prover accepts, which the whole-run theorem derives as described above).
The theorem for AMOs on the I/O window (`WholeRun/IoAmo.lean`, `block_simulates_io_amo`) takes only `AmoNoFlagWord` (no byte of the AMO's doubleword is a byte of the panic or termination word): a retiring AMO's store already puts its address at or above `memLow`, and its store cannot set the panic flag, so `NoLowLoad` and `PanicStoreNonzero` have no counterpart.

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
- the six CSRs, read from Jolt's virtual registers `v34`-`v39` through the relations of section 6;
- the reservation, read from `v32` and `v33` (section 3);
- Jolt's device, through the I/O window.

The advice tape is platform state that only the custom instructions of section 7 touch; since those have no block theorem yet (section 9), the relation does not mention it.

It also requires the invariants: privilege is Machine, `mie = 0`, `misa` is fixed, and the read-only `mstatus` fields have the values of section 6.
Counters and Sail-internal registers are not compared.
Decision (step f): Sail's `misa` is its reset value `0x8000000000001105` (A, C, I, M), set by the relation like `pma_regions`, not copied from the `misa` that Jolt's embedded Sail state carries (`0x800000008014312f`).
Jolt accepts only the six CSRs of section 6, so no guest observes `misa`; Jolt's rows read only its C bit (in `jump_to`), which both values set (`NonInterference.lean`, `execProgram_withMisa`).
A generic lifting lemma turns each existing `execute_X` theorem into a `try_step` theorem, by discharging fetch and decode for the instruction's encoding and the PC update once.

### What step c proves

The files are under `JoltBytecode/Step/`.

- `TryStep.lean` splits `try_step` on Jolt's hart.
  Under `StepInvariant`, when fetch returns a 32-bit word or a 16-bit parcel that decodes to `ast`, `try_step` equals the prelude (`minstret_increment`, then `nextPC := PC + len`), then `execute ast`, then the finish (`stepFinish`, a verbatim copy of `try_step`'s tail).
  `StepInvariant` says: every register is present, the hart is active in M-mode, `mie = 0`, `mideleg = 0`, `misa.C = 1`, and no landing pad is expected.
  With `mie = 0` the interrupt dispatch finds nothing pending; with `misa.C = 1` compressed parcels are legal.
- `Lift.lean` defines one Jolt step, `joltStep len bits prog`: Sail's prelude, the Jolt rows `prog`, then Sail's finish.
  The prelude and a retiring finish touch no CSR that Jolt keeps in virtual registers (`OverlayLocal`), so they commute with the CSR projection `systemProject`.
  `joltStep_base` and `joltStep_compressed` then give: if the rows agree with `execute ast` on the projected state after the prelude, and `ast` retires, the Jolt step projects to `try_step`.
  For a compressed parcel, `ast` is the base instruction the parcel abbreviates, not the compressed AST Sail decodes: Sail's `C_ADDI` executes as `pure (ExecuteAs (ITYPE …))`, and `try_step` then runs the `ITYPE`.
  `joltStep_compressed` takes the decoded compressed AST `cast` and the base AST `base` together with the fact that they agree under `executeFull` (step e proves it for every parcel Jolt accepts).
  Decision: an earlier version required `Matches i cast` for the compressed AST itself, which no Jolt instruction satisfies, so that theorem was vacuous.
- `Instructions.lean` states `joltRun_eq_execute`: `joltRun i` agrees with `execute ast` for each retiring instruction and matching Sail AST (`Matches i ast`).
  It covers arithmetic, branches, loads, stores, AMOs, FENCE, all six CSR forms, MRET, LR.W, SC.W, LR.D and SC.D.
  Their system-program specifications and Sail bridges are in `InstructionEquivalence/Instructions/System/`.
  LR/SC bundles include natural alignment, populated RAM windows, Jolt's RAM checks and Sail's exact reserved-access PMP/PMA permissions; SC also requires the reservation-pair invariant from section 3.
  These facts ensure a failed SC's write-back preserves memory.
  EBREAK remains outside `Lifted`: section 4 stops the whole-run theorem before its first occurrence.
  `Step/Ecall.lean` proves `RiscvInstruction.joltStep_eq_try_step_ecall` for a 32-bit ECALL fetch using `Step.joltEcallStep`: the prelude, `ecallProgram` and the non-retiring trap finish.
  Its additional hypotheses `hm` and `ht` require the persistent raw mstatus mask and legal mtvec mode; for example, mtvec `0x101` enters the handler at `0x100` without retiring ECALL.
  Decision (step d): the execute-level dispatcher was retired because `joltRun_eq_execute` and the ECALL step theorem replace it.
  `joltRun_eq_execute` calls the proved program theorems directly, and the step corollaries compose it with the fetch/decode lift.
  Their `#print axioms` lists only `propext`, `Classical.choice` and `Quot.sound`.
  FENCE matches every Sail FENCE and FENCE_TSO, since Jolt runs all of them as one no-op row.
  Atomics match with their own `aq` and `rl` bits: `AmoFlags.lean` supplies the generic memory-flag erasure used by AMOs and LR/SC, because the sequential memory model ignores the request's `access_kind`.
  The division and remainder expansions need their advice operand to be the honest value (`AdviceHonest`); the soundness half of those theorems shows a retiring run with `rd ≠ 0` has no other choice.
  `joltStep_eq_try_step_base` and `joltStep_eq_try_step_compressed` combine `joltRun_eq_execute` with the step theorem.
- `Frame.lean` proves that Jolt rows write only `x1`-`x31` and `nextPC` among Sail's registers, and remove none, on success and on error.
- `Invariant.lean` proves that a retiring Jolt step preserves `StepInvariant`: the prelude writes `minstret_increment` and `nextPC`, the rows stay in their frame, and the finish writes `PC` and `minstret`.
  `RiscvInstruction.joltStep_stepInvariant` states it per instruction.

Counters are unobservable: no Jolt row reads `minstret`, `minstret_increment` or `mcycle`, and the bookkeeping that writes them is Sail's own code run on the embedded state, so the two sides cannot disagree on them.

The step theorems keep three hypotheses that step f discharges from the run: the instruction's assumption bundle at the state after the prelude (its parts are classified in section 8), Sail's fetch and decode results at that state (step e relates them to Jolt's decoder), and that `execute ast` retires.
The separate ECALL theorem follows trap entry through the writes to `mepc`, `mcause`, `mtval` and `mstatus` and commits the handler PC without retirement.
The retiring theorems retain their retirement hypothesis; natural alignment excludes the LR/SC faults that are outside Jolt's step handoff.

### What step e proves

The files are under `JoltBytecode/Decode/`.
`Jolt.lean` transcribes Jolt's decoder (`joltDecode` for a 32-bit word with its advice, `joltUncompress` for a 16-bit parcel), and the two agreement theorems relate it to Sail's decoders on every state that satisfies `StepInvariant` and has `misa` at its reset value:

- `Agreement.lean`, `Decode.joltDecode_agrees`: if Jolt decodes a 32-bit word `w` to `i`, then `ext_decode w` returns an AST `ast` with `Matches i ast`.
  Jolt accepts no 32-bit word that Sail rejects.
- `Compressed.lean`, `Decode.joltDecode_compressed_agrees`: if Jolt decodes the expansion of a 16-bit parcel `h` to `i`, then `ext_decode_compressed h` returns a compressed AST `cast`, and there is a base AST `base` with `Matches i base` such that `executeFull cast` and `executeFull base` agree on every `StepInvariant` state.
  This is the hypothesis `joltStep_compressed` takes.

Decision: FENCE.TSO (`0x8330000f`) is decoded by Sail as `FENCE_TSO` and by Jolt as an ordinary FENCE.
`Matches .FENCE` accepts both Sail ASTs, because Jolt runs every fence as one no-op row and Sail's sequential memory model gives both the same effect, so the theorem needs no special case.

Resolved deviation: the parcel `0x6001` is C.LUI with `rd = x0` and a zero immediate, which the specification reserves (`unpriv/zca.adoc` `norm:c-lui_rsv`: "The code points with imm=0 are reserved").
Sail decodes it as `C_ILLEGAL` and raises an illegal-instruction exception.
Jolt used to expand it to `ADDI x0, x0, 0` and run it as a no-op.
Since a16z/jolt#2381, both of Jolt's decompressors return the invalid word for it.
The image decoder then rejects it as `MalformedImage`, and the tracer panics.
The transcribed `joltUncompress` includes that change: Jolt accepts no reserved parcel, and `joltDecode_compressed_agrees` takes no premise about one.

The proofs use no `bv_decide` and no `decide +kernel`.
The first versions of both files proved bit-vector side conditions with `bv_decide`, which in Lean 4.35 adds one auxiliary axiom per call; they now go through `omega` and `simp` on `BitVec.toNat`, and the two theorems' axioms are only `propext`, `Classical.choice` and `Quot.sound`.

## 6. CSR legalization

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

## 7. Jolt's custom instructions

Jolt's guest programs may contain Jolt's own instructions on major opcode `0x5B`, which the specification's opcode map marks custom-2, reserved for custom extensions (`unpriv/rv-32-64g.adoc`, opcode map and the paragraph after it).
They are not RISC-V instructions, so the Sail model does not decode them, and patching them into the model would make the trusted model depend on Jolt.
The plan is a platform step: on a `0x5B` encoding it runs a short Lean specification of Jolt's instruction, and on every other encoding it runs `try_step`.
It is not built yet: the whole-run theorem runs `try_step` only, and `BlockConforms.riscv` restricts it to RISC-V rows (section 9), so the rest of this section describes the planned extension.
Advice loads read from the advice tape, which the whole-run theorem quantifies over as a private input.
`VirtualAssertEQ` has no successor state when its operands differ.
`VirtualHostIO` changes no RISC-V state: it reads guest memory for the host call named in `a0`, and the advice-write call appends those bytes to the advice tape (`JoltBytecode/JoltISA/HostIO.lean`), so the tape is part of the platform state that the relation of section 5 carries.
`VirtualRev8W` reverses the bytes within each 32-bit half of a register.
Inline rows are out of scope for the whole-run theorem for now. `SourceInstruction` includes twelve registered inlines (five hash, seven secp256k1) at `0x0B` (`docs/inline-precompiles.md`), and `BlockConforms.riscv` excludes them from the whole-run theorem, as it excludes Jolt's custom instructions. Opcode `0x2B` and every other `0x0B` encoding are outside `SourceInstruction`.

## 8. Remaining assumptions and where they go

The instruction theorems take their hypotheses from `JoltBytecode/Assumptions.lean`, collected in `JoltBytecode/Bundles.lean`.
After the regeneration of step b each of them is one of:

- **configuration fact**: true in every Sail state of the regenerated model, proved in `JoltBytecode/HartConfig.lean`, and removed from the theorems;
- **invariant**: true in every state the whole-run theorem reaches from its initial state, proved once in step c and then discharged;
- **relation**: part of the Jolt–Sail state relation of section 5;
- **Jolt fact**: a property of Jolt's state that holds on every honest trace because Jolt's tracer panics otherwise; it stays a hypothesis of the step theorems and becomes a property of the trace in step f;
- **removed in step d**: a hypothesis that compensated for Jolt's old CSR sequences, which the jolt-changes sequences make unnecessary.

| Assumption | Status | Reason |
| --- | --- | --- |
| `ZicfilpDisabled` | configuration fact | Zicfilp is off: `HartConfig.currentlyEnabled_Zicfilp_run` |
| `MisaUserEnabled` | removed | It asked for `misa.U = 1`, which the M-only hart does not have; MRET now reads `currentlyEnabled Ext_U = false` (`HartConfig.currentlyEnabled_U_run`) whatever `misa` holds |
| PMP half of `LoadPmpOk`, `StorePmpOk`, `AtomicPmpOk` and their windows | configuration fact | No PMP entries: `HartConfig.pmpCheck_run` |
| PMA half of the same | invariant | `pma_regions` equals the configured list (only reset writes it) and the address is in RAM |
| `NotReadableMmio`, `NotWritableMmio` and their windows | invariant | The CLINT lies below RAM, and `htif_tohost_base` is `none` (only the C++ ELF loader sets it) |
| `CurPrivilegeMachine` | invariant | No mode below M exists, so every trap and MRET lands in M; carried by `Step.StepInvariant.machine` and preserved by every retiring step (`Step.joltStep_stepInvariant`) |
| `MstatusMprvZero` | invariant | MPRV resets to 0 and is read-only zero without U-mode |
| `SailRegReadable`, `XRegReadable`, the source-read bundles | invariant | Every register is present in the initial state and no step removes one (`Step.StepInvariant.present`, kept by `Step.RegFrame.present` and the Sail frames) |
| `DwordPresent` | invariant | The initial state's memory map covers RAM and the I/O window |
| `MstatusVRegMatchesSail` and the five other `…VRegMatchesSail` | relation | Section 6 |
| `JoltRamLoadOk`, `JoltRamStoreOk` | Jolt fact | Jolt's MMU panics at or above `heap_end` and on stores into the stack canary |
| `MstatusWriteLegalized`, `MtvecWriteDirectMode`, `MepcWriteLegalized` | removed in step d | The jolt-changes sequences legalize the written value the way Sail does |
| `MstatusMppMachine` | removed in step d | `v39` no longer holds MPP; every read adds `MPP = 3` |
| `MepcReadAligned` | invariant (step d) | `v36[0] = 0`, kept by the `mepc` write mask |

The model's own axioms (`LeanRV64D/RiscvExtras.lean`) after the regeneration:

| Axiom | Status |
| --- | --- |
| `load_reservation`, `match_reservation`, `cancel_reservation`, `valid_reservation` | removed: model registers (section 3) |
| `sys_enable_experimental_extensions` | removed: a definition, `false` |
| `plat_term_write`, `plat_term_read` | removed: definitions; the platform has no console |
| `get_16_random_bits` | removed: an opaque function (unspecified entropy). It is the entropy source behind the Zkr `seed` CSR. Zkr is off, and Jolt rejects the CSR, so no Jolt step reaches it; as an opaque constant it adds no axiom and proofs cannot assume anything about its result |
| floating-point operations (`riscv_f16Add` and the rest) | not reached: F and D are off and their instruction modules are not generated |

The generated model is checked at Lean's default limits (200000 heartbeats, `maxRecDepth` 512), with no file-wide `set_option`; `scripts/regen-sail-model.sh` removes the two header lines Sail writes and splits each 256-entry S-box table into two 128-entry halves.
Only the declarations below carry a limit, as `set_option … in` directly before the declaration; each limit is the smallest passing value rounded up to the next 50 (next 50000 for heartbeats).
The first five are in the closure of `JoltInstance.sail_soundness`, which therefore depends on those options for the model, though not on any file-wide one.

| Declaration | Limit | Reason | In the closure |
| --- | --- | --- | --- |
| `is_CSR_accessible` (`SysControl`) | `maxRecDepth` 900 | generated if-chain over every CSR address | yes |
| `read_CSR`, `write_CSR` (`ZicsrInsts`) | `maxRecDepth` 900 | the same chain, for reads and writes | yes |
| `encdec_backwards` (`InstsEnd`) | `maxRecDepth` 1450, `maxHeartbeats` 250000 | decoder mapping over every instruction | yes |
| `encdec_compressed_backwards` (`InstsEnd`) | `maxRecDepth` 550 | the same mapping for compressed instructions | yes |
| `encdec_backwards_matches` (`InstsEnd`) | `maxRecDepth` 1400, `maxHeartbeats` 250000 | the same mapping, returning a `Bool` | no |
| `encdec_compressed_backwards_matches` (`InstsEnd`) | `maxRecDepth` 550 | the same mapping, returning a `Bool` | no |
| `print_rvfi_exec` (`RvfiDii`) | `maxHeartbeats` 1000000000 | debug printer for the RVFI trace format | no |

The follow-up is for Sail's Lean backend to split long if-chains and mappings into helper definitions, so that these options, and the S-box rewrite, can be dropped from the regeneration.
The proofs unfold the CSR chains and the decoder mapping, so the chains are not split by hand.

`#print axioms` on `JoltInstance.soundness` and on every instruction theorem that is fully proved gives only `propext`, `Classical.choice` and `Quot.sound`.
The headline theorems, including `Decode.joltDecode_compressed_agrees` and the block theorems of section 9, use only these three standard axioms, although the generic CSR read in their closure mentions `get_16_random_bits`.
None of these, and nothing `JoltInstance.soundness` uses, lists `sorryAx`; the sorries left are in `JoltConstraints/Completeness/`, some of them waiting on a16z/jolt#1949.

Step f classifies whatever is left in the whole-run theorem as an invariant, a platform fact (sections 2, 4 and 7) or a documented deviation (the read-back of the panic and termination words in section 2, and anything the difference testing confirms); the classified list is in section 9, "What step f proves".
The per-block deviations of `JoltInstance.sail_soundness` are premises on the trace that `soundness` extracts, so they are checked on that trace; `HonestTrace.sail_reproduces` states the same for any honest trace given in advance.
Of the low-address loads of jolt-qed#37, only loads from the doubleword at address 0 remain a premise (`NoZeroDoublewordLoad`); the prover's address check excludes the others.

## 9. Whole-run system invariant

`WholeRun.SystemInv` is a run invariant: raw mstatus contains only MIE/MPIE, mtvec has mode 0 or 1, mepc is even, and the reservation registers form a legal pair.
It holds initially and is preserved by every source block, including CSR writes, MRET, LR/SC and ECALL, assuming the separately supplied run invariant that the source PC is even.
`WholeRun.block_simulates` combines these facts with the platform RAM assumptions and fetch/decode results to simulate every RISC-V block before EBREAK by one Sail `try_step`.
`WholeRun.block_simulates_decoded` removes the fetch and decode premises: Sail's `fetch` and decode at the block's PC come from the program image (`WholeRun/Decoded.lean`).
`ImageDecoded` says that each RISC-V row of the image is what Jolt's decoder (`joltDecode`, and `joltUncompress` for a compressed row) gives for the bytes `memory_init` loads at its address.
No constraint checks it, because it describes how the bytecode was produced.
The whole-run theorems derive it from the platform premise `DecodedFrom` (`WholeRun/Elf.lean`): the program agrees with what Jolt's `decode_elf` builds from the sections of the guest ELF.
`DecodedFrom` fixes the layout and every RISC-V row, and every program Jolt builds satisfies it; it does not fix which of Jolt's own instructions a row holds.
`ElfSections.layout?` transcribes `decode_elf` up to the call of `decode_instruction`: the loaded sections, `memory_init`, `program_end`, `merge_ranges` and `decode_text_section`.
`decode_elf` reads a merged text range from its byte map with `unwrap_or(0)`.
The `object` crate reports a section as text only when it is `SHT_PROGBITS`, and it gives such a section exactly `sh_size` bytes of data or fails.
`ElfSection.text_data_length` records this for every text section `decode_elf` loads, that is, at or above `RAM_START_ADDRESS`.
Every address of a merged text range therefore has a byte, and `DecodedFrom.imageDecoded` proves that the default 0 never applies.
The parsing of the ELF file into its sections (`object::File::parse`, section kinds, `entry`) stays outside Lean and is trusted.
`CodeIntact` says Sail's memory still holds those bytes at every row; it holds at `sailInit` (`codeIntact_sailInit`).
Its Jolt-side version `JoltCodeIntact` (`WholeRun/CodeInv.lean`) is a run invariant under the documented deviation `NoCodeStore`: the block stores into no instruction byte, counting the whole doubleword Jolt's narrow stores rewrite.
Jolt does not forbid a store into the code, and its tracer keeps fetching the committed bytecode afterwards, while Sail's model fetches coherently from memory; without Zifencei the specification permits either (`unpriv/zifencei.adoc`).

Platform premise `JoltInstance.HeapNoWrap`: the memory layout ends at least eight bytes below `2^64` (`heap_end ≤ 2^64 - 8`).
`MemoryLayout.new` checks its additions but rounds only the stack and heap sizes to eight bytes, so a `program_end` near `2^64` gives `heap_end = 2^64 - 1`; real ELFs end far below that.
The layout never changes during a run, so the premise on the instance holds at every block.

### What step f proves

`HonestTrace.sail_reproduces` (`WholeRun/Top.lean`) is the run-level theorem.
It applies to every honest trace and every `HaltPrefix` of it, where `HaltPrefix` names the blocks `pre` before the trace's first EBREAK, ending at the state `halt`.
If Jolt's prover accepts the trace and every block of `pre` satisfies `BlockConforms`, then `sailRun n (sailInit trace.initialState)` succeeds at a Sail state `s` with four properties:
- `s` is related to `halt` (`Related`), through the register projection and memory conditions that [`whole-run-theorem.md`](whole-run-theorem.md) describes;
- its trimmed output bytes are those of the trace's final state;
- its panic word is nonzero exactly when the final state's panic flag is set;
- either `PC` names an EBREAK row of the image (`SailHalted`), or the trace ended without an EBREAK at `halt`.

`JoltInstance.sail_soundness` composes it with `JoltInstance.soundness`.
Every instance the constraints accept has an honest trace that satisfies the three conjuncts of `InLanguage`.
For that trace the same conclusion holds, and the outputs and panic flag are the instance's claimed ones.
The trace is the one `soundness` extracts from the witness, so conformance has to be checked on that trace.
Alternatively, it can be argued from Jolt's determinism when the trace is unique for the given inputs.

The relation carried along the run is `RunRel = Related ∧ RunInv ∧ JoltCodeIntact`.
The premises, by class:

| Premise | Class | Where |
| --- | --- | --- |
| `hcfg` (`sail_reproduces` only) | prover acceptance | Jolt's prover accepts the trace; `sail_soundness` obtains it from `soundness` |
| `DecodedFrom` | platform | the program agrees with what Jolt's `decode_elf` builds from the sections of the guest ELF; `ImageDecoded` follows from it |
| `RowsAligned` | platform | every row address is even; Jolt's ELF loader does not check that the text section starts at an even address |
| `HeapNoWrap` | platform | the layout ends at least eight bytes below `2^64` |
| `BlockConforms.amo_no_flag_word` | documented deviation | an AMO on the I/O window touches no panic or termination byte (section 2) |
| `BlockConforms.no_code_store` | documented deviation | stores into the code, above |
| `BlockConforms.no_flag_word_load`, `no_zero_doubleword_load`, `panic_store_nonzero` | documented deviation | the I/O window (section 2) |
| `BlockConforms.riscv` | scope | Jolt's own instructions (section 7) have no block theorem yet |

The per-block premises are stated on the blocks of the trace's halt prefix, not on the whole program image.
In `sail_soundness` that trace is existentially quantified, and a reader who sees only the instance cannot inspect its blocks.
To obtain the Sail run, the reader has to prove the premises for the returned halt prefix; proving them for every run the program can take, on every private input, is one sufficient way.
[`whole-run-theorem.md`](whole-run-theorem.md) explains this and lists what the theorems do not say.
jolt-qed#37 lists low-address loads as an open question.
`HaltPrefix.traced` links each block to its first trace row, and the prover's check of the recorded `ram_address` (`prover_config`) gives `NoLowLoad` for every load at or above address 8.
A byte, halfword or word load below address 8 records address 0, which the prover does not check, and `NoZeroDoublewordLoad` remains a premise for it; an LD at address 0 escapes the check as well, and for one bound across widths the premise excludes every LD below 8.
`#print axioms` on `JoltInstance.sail_soundness` and `HonestTrace.sail_reproduces` gives `propext`, `Classical.choice` and `Quot.sound`.
