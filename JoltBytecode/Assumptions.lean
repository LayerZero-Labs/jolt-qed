/-
Copyright (c) 2026 Ari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ari 
-/

import JoltBytecode.JoltISA.SystemProjection
import JoltBytecode.JoltISA.DeviceMemory
import JoltBytecode.JoltISA.Values

open LeanRV64D
/-!
# Jolt proof assumptions

This file is the top-level index of primitive assumptions used by the
instruction-equivalence proofs. 
See: https://randomwalks.xyz/blog/jolt-qed/assumptions/
for a detailed justification of these assumptions. 

NOTE: The control status register assumptions could be tightened
in the rust code. Till then, those assumptions are fine.
-/

set_option linter.unusedVariables false

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail LeanRV64D LeanRV64D.Functions
open virtaddr MemoryAccessType mem_payload

set_option autoImplicit true

noncomputable section

namespace Assumptions

-- ============================================================================
-- Register assumptions
-- ============================================================================

/-- General purpose registers are readable, with some value.
In Lean, as SAIL register file is a hashmap, we need this to 
say that key exists in the hashmap.

So we right two assumptions: 
1. The key is in the hashmap. 
2. The rx_bits api call returns the value in the register.
-/
structure SailRegReadable (r : Register) (s : SailState) : Prop where
  exists_value : ∃ value : RegisterType r, s.regs.get? r = some value

structure XRegReadable (r : regidx) (s : SailState) : Prop where
  exists_value : ∃ value : BitVec 64, rX_bits r s = .ok value s


/-- Assumptions for an instruction that reads one architectural source register. 
Instructions like ADDI will use only one source register.
-/
structure UnarySourceReadAssumptions (rs1 : regidx) (s : SailState) where
  rs1_val : BitVec 64
  rs1_read : rX_bits rs1 s = .ok rs1_val s

/-- Assumptions for an instruction that reads two architectural source registers. 
Instructions like ADD use two source registers.
-/
structure BinarySourceReadAssumptions
    (rs2 rs1 : regidx) (s : SailState) where
  rs1_val : BitVec 64
  rs1_read : rX_bits rs1 s = .ok rs1_val s
  rs2_val : BitVec 64
  rs2_read : rX_bits rs2 s = .ok rs2_val s

-- ============================================================================
-- Memory assumptions
-- ============================================================================

/-- The 8-byte dword beginning at `addr` is present in Sail's finite memory map.

Rust source: `tracer/src/emulator/memory.rs:38-63`,
`tracer/src/emulator/memory.rs:136-196`.

Much like the SAIL register file, we need to say keys are populated 
in the hashmap. 
Jolt's memory is just an array, and we can always read off values. 
Furthermore, as the Jolt ISA only has the LD instruction, we must 
always say that all 64 bits enclosing the addr are readable.
-/
structure DwordPresent (addr : BitVec 64) (s : SailState) : Prop where
  bytes :
    ∃ bytes : Fin 8 → BitVec 8,
      ∀ k : Fin 8, s.mem.get? (addr.toNat + k.val) = some (bytes k)

/-- Machine-mode PMP accepts a data load from `addr` for `width` bytes.

The SAIL side models every decision that a memory load must make 
before it actually reaches data bytes.

Rust source: `tracer/src/emulator/mmu.rs:13-18`.
Jolt's Rust MMU explicitly says memory protection is not implemented. This
predicate constrains generated Sail to the corresponding no-PMP-fault path.

We wnt to say this not only the data located at the addres + width, but the 
entire d-word window.
-/
abbrev LoadPmpOk (addr : BitVec 64) (width : Nat) (s : SailState) : Prop :=
  phys_access_check (Load Data) Privilege.Machine
    (physaddr.Physaddr addr) width false s = .ok none s

/-- Machine-mode PMP accepts every explicit sub-load inside a memory window. -/
structure LoadPmpOkWindow
    (base : BitVec 64) (width : Nat) (s : SailState) : Prop where
  ok :
    ∀ offset accessWidth : Nat, 0 < accessWidth → offset + accessWidth ≤ width →
      LoadPmpOk (base + BitVec.ofNat 64 offset) accessWidth s

/-- Machine-mode PMP accepts a data store to `addr` for `width` bytes.

Rust source: `tracer/src/emulator/mmu.rs:13-18`.

Jolt's Rust MMU explicitly says memory protection is not implemented. This
predicate constrains generated Sail to the corresponding no-PMP-fault path.
-/
abbrev StorePmpOk (addr : BitVec 64) (width : Nat) (s : SailState) : Prop :=
  phys_access_check (Store Data) Privilege.Machine
    (physaddr.Physaddr addr) width false s = .ok none s

/-- Machine-mode PMP accepts every explicit sub-store inside a memory window. -/
structure StorePmpOkWindow
    (base : BitVec 64) (width : Nat) (s : SailState) : Prop where
  ok :
    ∀ offset accessWidth : Nat, 0 < accessWidth → offset + accessWidth ≤ width →
      StorePmpOk (base + BitVec.ofNat 64 offset) accessWidth s

/-- Machine-mode PMP accepts an AMO at `addr` for `width` bytes.

Rust source: `tracer/src/emulator/mmu.rs:13-18`.

Jolt's Rust MMU explicitly says memory protection is not implemented. This
predicate constrains generated Sail to the corresponding no-PMP-fault path.
-/
abbrev AtomicPmpOk
    (op : amoop) (addr : BitVec 64) (width : Nat) (s : SailState) : Prop :=
  phys_access_check (Atomic (op, Data, Data)) Privilege.Machine
    (physaddr.Physaddr addr) width true s = .ok none s

/-- Machine-mode PMP accepts every explicit sub-AMO inside a memory window. -/
structure AtomicPmpOkWindow
    (op : amoop) (base : BitVec 64) (width : Nat) (s : SailState) : Prop where
  ok :
    ∀ offset accessWidth : Nat, 0 < accessWidth → offset + accessWidth ≤ width →
      AtomicPmpOk op (base + BitVec.ofNat 64 offset) accessWidth s

abbrev LoadReservedPmpOk (addr : BitVec 64) (width : Nat) (s : SailState) : Prop :=
  phys_access_check (LoadReserved Data) Privilege.Machine
    (physaddr.Physaddr addr) width true s = .ok none s

abbrev StoreConditionalPmpOk (addr : BitVec 64) (width : Nat) (s : SailState) : Prop :=
  phys_access_check (StoreConditional Data) Privilege.Machine
    (physaddr.Physaddr addr) width true s = .ok none s

structure LrScAligned (double : Bool) (addr : BitVec 64) : Prop where
  aligned : addr &&& (if double then 7#64 else 3#64) = 0#64

/-- The physical range is not readable MMIO.

Rust source: `tracer/src/emulator/mmu.rs:139-213`.

Rust has a device/I/O address branch and an ordinary RAM branch. The flat-memory
proofs using this predicate are intentionally about the ordinary RAM path, not
device I/O.
-/
structure NotReadableMmio (addr : BitVec 64) (width : Nat) (s : SailState) : Prop where
  -- Rust: [device/RAM split](/Users/ari.biswas/Work-with-A16z/jolt/tracer/src/emulator/mmu.rs:523).
  -- Excluding Sail's devices alone does not exclude Jolt's device address region.
  ram : JoltISA.RAM_START_ADDRESS ≤ addr.toNat
  sail : within_mmio_readable (physaddr.Physaddr addr) width s = .ok false s

/-- Every explicit sub-load inside a memory window avoids readable MMIO. -/
structure NotReadableMmioWindow
    (base : BitVec 64) (width : Nat) (s : SailState) : Prop where
  ok :
    ∀ offset accessWidth : Nat, 0 < accessWidth → offset + accessWidth ≤ width →
      NotReadableMmio (base + BitVec.ofNat 64 offset) accessWidth s

/-- The physical range is not writable MMIO.

Rust source: `tracer/src/emulator/mmu.rs:139-213`.

Rust has a device/I/O address branch and an ordinary RAM branch. The flat-memory
proofs using this predicate are intentionally about the ordinary RAM path, not
device I/O.
-/
structure NotWritableMmio (addr : BitVec 64) (width : Nat) (s : SailState) : Prop where
  -- The ordinary-RAM equivalence proofs exclude both Jolt and Sail devices.
  ram : JoltISA.RAM_START_ADDRESS ≤ addr.toNat
  sail : within_mmio_writable (physaddr.Physaddr addr) width s = .ok false s

/-- Every explicit sub-store inside a memory window avoids writable MMIO. -/
structure NotWritableMmioWindow
    (base : BitVec 64) (width : Nat) (s : SailState) : Prop where
  ok :
    ∀ offset accessWidth : Nat, 0 < accessWidth → offset + accessWidth ≤ width →
      NotWritableMmio (base + BitVec.ofNat 64 offset) accessWidth s

-- ============================================================================
-- Jolt RAM assumptions
-- ============================================================================

structure JoltRamLoadOk (addr : BitVec 64) (js : SailJoltState) : Prop where
  below_backing_end : addr.toNat < JoltISA.Mmu.ram_backing_end js.jolt_device

structure JoltRamStoreOk (addr : BitVec 64) (js : SailJoltState)
    (value : BitVec 64) (width : Nat) : Prop where
  below_backing_end : addr.toNat < JoltISA.Mmu.ram_backing_end js.jolt_device
  preserves_protected : JoltISA.Mmu.assert_write_protected_store js addr.toNat value width = true

structure JoltStoreOk (ea rs2_val : BitVec 64) (width : Nat) (js : SailJoltState) : Prop where
  ram_store :
    JoltRamStoreOk (ea &&& -8) js
      (JoltISA.storeDwordValue width ea
        (JoltISA.Mmu.ram_doubleword js.sail.mem (ea &&& -8).toNat) rs2_val) 8

structure JoltAmoDwordStoreOk (op : amoop) (ea rs2_val : BitVec 64) (js : SailJoltState) : Prop where
  ram_store :
    JoltRamStoreOk ea js
      (JoltISA.amoDwordStoreValue op (JoltISA.Mmu.ram_doubleword js.sail.mem ea.toNat) rs2_val) 8

structure JoltAmoWordStoreOk (op : amoop) (ea rs2_val : BitVec 64) (js : SailJoltState) : Prop where
  ram_store :
    JoltRamStoreOk (ea &&& -8) js
      (JoltISA.amoWordStoreValue op ea
        (JoltISA.Mmu.ram_doubleword js.sail.mem (ea &&& -8).toNat) rs2_val) 8

structure JoltScDwordStoreOk (ea rs2_val : BitVec 64) (js : SailJoltState) : Prop where
  ram_store :
    let old := JoltISA.Mmu.ram_doubleword js.sail.mem ea.toNat
    let success : BitVec 64 := if js.vregs JoltISA.reservationDReg = ea then 1 else 0
    JoltRamStoreOk ea js (old + success * (rs2_val - old)) 8

structure JoltScWordStoreOk (ea rs2_val : BitVec 64) (js : SailJoltState) : Prop where
  ram_store :
    let original := JoltISA.Mmu.ram_doubleword js.sail.mem (ea &&& -8).toNat
    let old := jolt_virtual_pext_signed_value original (jolt_virtual_window_mask_w_value ea 0)
    let success : BitVec 64 := if js.vregs JoltISA.reservationWReg = ea then 1 else 0
    JoltRamStoreOk (ea &&& -8) js
      (JoltISA.storeDwordValue 4 ea original (old + success * (rs2_val - old))) 8

-- ============================================================================
-- System/CSR register assumptions
-- ============================================================================

/-- The current generated-Sail privilege register is Machine mode.

Jolt source: `jolt/tracer/src/emulator/cpu.rs:443-449` at `5def437f`
```rust
privilege_mode: PrivilegeMode::Machine,
```
-/
structure CurPrivilegeMachine (s : SailState) : Prop where
  value : s.regs.get? Register.cur_privilege =
    some (Privilege.Machine : RegisterType Register.cur_privilege)

/-- The Sail `mstatus` register is readable and has MPRV=0.

Rust source: `tracer/src/emulator/mmu.rs:870-898`.

Rust's address translation returns the address unchanged in Machine mode when
`mstatus.MPRV = 0`. The memory-family proofs assume that envelope so Sail does
not take an MPRV remapping path that Jolt's bytecode proof is not modeling.
-/
structure MstatusMprvZero (s : SailState) : Prop where
  value : ∃ mval : RegisterType Register.mstatus,
    s.regs.get? Register.mstatus = some mval ∧
    _get_Mstatus_MPRV mval = 0#1

-- vreg == sail.csr begins  here 

/-- Sail `mstatus` agrees with Jolt's `mstatus` virtual register v39, once the MPP bits are added.
Sail and Jolt store `mstatus` differently.
Sail keeps the whole register, including MPP = `11` (bits 12:11), so for example `0x1888`.
Jolt keeps only the MIE and MPIE bits in v39, so for example `0x88`.
Jolt never stores the MPP bits; it adds them only when a program reads `mstatus`, with
`ORI rd, v39, 0x1800` (`crates/jolt-program/src/expand/control_flow/csr.rs`, `emit_csr_read`,
at Jolt `504dd78a2`). -/
structure MstatusVRegMatchesSail (js : SailJoltState) : Prop where
  value_eq :
    js.sail.regs.get? Register.mstatus =
      some (js.vregs JoltISA.mstatusVReg ||| 0x1800#64)

/-- Sail `mtvec` agrees with Jolt's persistent trap-handler virtual register. -/
structure MtvecVRegMatchesSail (js : SailJoltState) : Prop where
  value_eq :
    js.sail.regs.get? Register.mtvec =
      some (js.vregs JoltISA.trapHandlerVReg)

/-- Sail `mscratch` agrees with Jolt's persistent `mscratch` virtual register. -/
structure MscratchVRegMatchesSail (js : SailJoltState) : Prop where
  value_eq :
    js.sail.regs.get? Register.mscratch =
      some (js.vregs JoltISA.mscratchVReg)

/-- Sail `mepc` agrees with Jolt's persistent `mepc` virtual register. -/
structure MepcVRegMatchesSail (js : SailJoltState) : Prop where
  value_eq :
    js.sail.regs.get? Register.mepc =
      some (js.vregs JoltISA.mepcVReg)

/-- Sail `mcause` agrees with Jolt's persistent `mcause` virtual register. -/
structure McauseVRegMatchesSail (js : SailJoltState) : Prop where
  value_eq :
    js.sail.regs.get? Register.mcause =
      some (js.vregs JoltISA.mcauseVReg)

/-- Sail `mtval` agrees with Jolt's persistent `mtval` virtual register. -/
structure MtvalVRegMatchesSail (js : SailJoltState) : Prop where
  value_eq :
    js.sail.regs.get? Register.mtval =
      some (js.vregs JoltISA.mtvalVReg)

/-- Sail's LR/SC reservation agrees with Jolt's reservation virtual registers v32 and v33.
Sail keeps the reservation in three registers, valid, address and width.
Jolt needs only two, because each one just saves the reserved address.
LR.W saves it in v32 and sets v33 to 0, LR.D saves it in both, and every SC sets both to 0
(`crates/jolt-program/src/expand/memory/`, `lrw.rs`, `lrd.rs`, `scw.rs`, `scd.rs`, at Jolt `504dd78a2`).
So Sail's valid is v32 ≠ 0, its address is v32, and its width is `reservationWidth v32 v33`.
For example, after `LR.W a` we have v32 = a and v33 = 0, which reads as valid, address a, width 4. -/
structure ReservationVRegsMatchSail (js : SailJoltState) : Prop where
  valid_eq :
    js.sail.regs.get? Register.reservation_valid =
      some (js.vregs JoltISA.reservationWReg != 0#64)
  addr_eq :
    js.sail.regs.get? Register.reservation_addr = some (js.vregs JoltISA.reservationWReg)
  width_eq :
    js.sail.regs.get? Register.reservation_width =
      some (System.reservationWidth (js.vregs JoltISA.reservationWReg)
        (js.vregs JoltISA.reservationDReg))

/-- Only MIE and MPIE can be set in v39; for example, v39 = 0x88 is legal. -/
structure MstatusVRegLegal (js : SailJoltState) : Prop where
  mstatus_bits : js.vregs JoltISA.mstatusVReg &&& ~~~(0x88#64) = 0#64

/-- Bit 1 of mtvec is clear, so its mode is not reserved; for example, mtvec = 0x101 is legal. -/
structure MtvecVRegLegal (js : SailJoltState) : Prop where
  mtvec_mode : (js.vregs JoltISA.trapHandlerVReg).getLsbD 1 = false

/-- Bit 0 of mepc is clear; for example, mepc = 16 is legal. -/
structure MepcVRegLegal (js : SailJoltState) : Prop where
  mepc_align : (js.vregs JoltISA.mepcVReg).getLsbD 0 = false

/-- v33 is zero or equals v32; for example, v32 = v33 = 0 is legal. -/
structure ReservationVRegsLegal (js : SailJoltState) : Prop where
  reservation_pair :
    js.vregs JoltISA.reservationDReg = 0#64 ∨
      js.vregs JoltISA.reservationDReg = js.vregs JoltISA.reservationWReg

-- vreg == sail.csr ends here 


/-- A stored `mepc` value is already aligned for Sail's read-side `align_pc`.

Current ZeroOS/Jolt targets are compressed-capable (`+c` / RV64IMAC), so the
relevant invariant is `mepc[0] = 0`. 
-/
structure MepcReadAligned (value : BitVec 64) (s : SailState) : Prop where
  value_eq : align_pc value s = .ok value s

end Assumptions

export Assumptions (
  CurPrivilegeMachine
  MstatusMprvZero
  XRegReadable
  SailRegReadable
  DwordPresent
  LoadPmpOk
  LoadPmpOkWindow
  StorePmpOk
  StorePmpOkWindow
  AtomicPmpOk
  AtomicPmpOkWindow
  LoadReservedPmpOk
  StoreConditionalPmpOk
  NotReadableMmio
  NotReadableMmioWindow
  NotWritableMmio
  NotWritableMmioWindow
  JoltRamLoadOk
  JoltRamStoreOk
)

end
