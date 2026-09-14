/-
Copyright (c) 2026 Ari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ari 
-/

import JoltBytecode.JoltISA.VirtualRegisters
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

open Sail PreSail LeanRV64D.Functions
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
    ∀ offset accessWidth : Nat, offset + accessWidth ≤ width →
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
    ∀ offset accessWidth : Nat, offset + accessWidth ≤ width →
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
    ∀ offset accessWidth : Nat, offset + accessWidth ≤ width →
      AtomicPmpOk op (base + BitVec.ofNat 64 offset) accessWidth s

/-- The physical range is not readable MMIO.

Rust source: `tracer/src/emulator/mmu.rs:139-213`.

Rust has a device/I/O address branch and an ordinary RAM branch. The flat-memory
proofs using this predicate are intentionally about the ordinary RAM path, not
device I/O.
-/
abbrev NotReadableMmio (addr : BitVec 64) (width : Nat) (s : SailState) : Prop :=
  within_mmio_readable (physaddr.Physaddr addr) width s = .ok false s

/-- Every explicit sub-load inside a memory window avoids readable MMIO. -/
structure NotReadableMmioWindow
    (base : BitVec 64) (width : Nat) (s : SailState) : Prop where
  ok :
    ∀ offset accessWidth : Nat, offset + accessWidth ≤ width →
      NotReadableMmio (base + BitVec.ofNat 64 offset) accessWidth s

/-- The physical range is not writable MMIO.

Rust source: `tracer/src/emulator/mmu.rs:139-213`.

Rust has a device/I/O address branch and an ordinary RAM branch. The flat-memory
proofs using this predicate are intentionally about the ordinary RAM path, not
device I/O.
-/
abbrev NotWritableMmio (addr : BitVec 64) (width : Nat) (s : SailState) : Prop :=
  within_mmio_writable (physaddr.Physaddr addr) width s = .ok false s

/-- Every explicit sub-store inside a memory window avoids writable MMIO. -/
structure NotWritableMmioWindow
    (base : BitVec 64) (width : Nat) (s : SailState) : Prop where
  ok :
    ∀ offset accessWidth : Nat, offset + accessWidth ≤ width →
      NotWritableMmio (base + BitVec.ofNat 64 offset) accessWidth s

-- ============================================================================
-- System/CSR register assumptions
-- ============================================================================

/-- The current generated-Sail privilege register is Machine mode.

Rust source: `tracer/src/emulator/cpu.rs:329-353`
```rust
privilege_mode: PrivilegeMode::Machine,
```
-/
structure CurPrivilegeMachine (s : SailState) : Prop where
  value : s.regs.get? Register.cur_privilege =
    some (Privilege.Machine : RegisterType Register.cur_privilege)

/-- The generated `misa` CSR is present and has the U extension bit set.

Rust source:
`/Users/ari.biswas/Work-with-A16z/jolt/tracer/src/emulator/cpu.rs:399`.
Generated Sail source: `LeanRV64D/Types.lean:381-382`.

Rust initializes `misa` to `0x800000008014312f`; generated Sail's
`_get_Misa_U` reads bit 20, which is set in that value.
-/
structure MisaUserEnabled (s : SailState) : Prop where
  exists_value : ∃ misa : BitVec 64,
    s.regs.get? Register.misa = some (misa : RegisterType Register.misa) ∧
    _get_Misa_U misa = 1#1

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

/-- The generated Sail Zicfilp landing-pad extension is disabled.

Jolt does not model the generated Sail `elp` register or Zicfilp landing-pad
state.
-/
structure ZicfilpDisabled (s : SailState) : Prop where
  value : currentlyEnabled extension.Ext_Zicfilp s = .ok false s

-- vreg == sail.csr begins  here 

/-- Sail `mstatus` agrees with Jolt's persistent `mstatus` virtual register. -/
structure MstatusVRegMatchesSail (js : SailJoltState) : Prop where
  value_eq :
    js.sail.regs.get? Register.mstatus =
      some (js.vregs JoltISA.mstatusVReg)

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

-- vreg == sail.csr ends here 


/-- A value written to `mtvec` uses Direct mode, so Sail's `legalize_tvec`
accepts it unchanged.

The ZeroOS/Jolt boot path writes `_trap_handler` to `mtvec` with `csrw mtvec,
t0`; ZeroOS defines `_trap_handler` under `.align 2`, which gives 4-byte
alignment, so the lower two bits are `00`. 
-/
structure MtvecWriteDirectMode (value : BitVec 64) : Prop where
  mode_eq : _get_Mtvec_Mode value = 0b00#2


/-- A stored `mepc` value is already aligned for Sail's read-side `align_pc`.

Current ZeroOS/Jolt targets are compressed-capable (`+c` / RV64IMAC), so the
relevant invariant is `mepc[0] = 0`. 
-/
structure MepcReadAligned (value : BitVec 64) (s : SailState) : Prop where
  value_eq : align_pc value s = .ok value s

/-- A value written to `mepc` is already legal, so Sail's `legalize_xepc`
accepts it unchanged.

This is the write-side counterpart of `MepcReadAligned`: CSRRW writes the new
`rs1` value, so the assumption must be about that source value rather than only
the old stored `mepc`.
-/
structure MepcWriteLegalized (value : BitVec 64) : Prop where
  value_eq : legalize_xepc value = value

/-- A value written to `mstatus` is already legal in the current Sail state, so

This assumption is the proof boundary that the ZeroOS/Jolt `mstatus` value is
stable under that generated-Sail legalizer. -/
structure MstatusWriteLegalized
    (old value : BitVec 64) (s : SailState) : Prop where
  value_eq : legalize_mstatus old value s = .ok value s

/-- Jolt's fixed `mstatus` virtual register has `MPP = Machine`.

Rust source:
`/Users/ari.biswas/Work-with-A16z/jolt/tracer/src/instruction/mret.rs:7-18`;
-/
structure MstatusMppMachine (js : SailJoltState) : Prop where
  value_eq :
    _get_Mstatus_MPP (js.vregs JoltISA.mstatusVReg) =
      privLevel_to_bits Privilege.Machine

end Assumptions

export Assumptions (
  CurPrivilegeMachine
  MstatusMprvZero
  ZicfilpDisabled
  XRegReadable
  SailRegReadable
  MisaUserEnabled
  MtvecWriteDirectMode
  MstatusMppMachine
  DwordPresent
  LoadPmpOk
  LoadPmpOkWindow
  StorePmpOk
  StorePmpOkWindow
  AtomicPmpOk
  AtomicPmpOkWindow
  NotReadableMmio
  NotReadableMmioWindow
  NotWritableMmio
  NotWritableMmioWindow
)

end
