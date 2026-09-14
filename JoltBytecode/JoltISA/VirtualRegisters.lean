/-
Copyright (c) 2026 Ari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ari 
-/
import JoltBytecode.JoltISA.Core

/-!
# Rust virtual-register allocation layout

The Lean Jolt-ISA programs use the same absolute virtual-register numbers as
`tracer/src/utils/virtual_registers.rs`.

Rust reserves virtual registers `32..39` for control status registers,
uses `40..47` for the per-instruction `allocate()` scratch pool, and starts
larger inline allocations at `48`.

This file holds **definitions only** — the register-address types, the
layout constants, the persistent CSR aliases, the slot classifier, the
allocator model, and the named `inlineTmp0..7` scratch aliases.

Proof-side facts about this layout (distinctness, protection, `rfl`-projections,
allocator decide-theorems) live in
`InstructionEquivalence/VirtualRegisterProofSupport.lean`.
-/

namespace JoltISA

/-- A Jolt virtual register address: Jolt uses a 7-bit (2⁷ = 128) register
address space.  All facts about the virtual-register space live in this file. -/
abbrev VReg := BitVec 7

/-- Number of architectural RISC-V integer registers; virtual registers start
immediately after this base.

Rust name/source: `RISCV_REGISTER_COUNT`,
`common/src/constants.rs:2`.
-/
def riscvRegisterCount : Nat := 32

/-- Number of Jolt virtual registers after the architectural register block.
Rust name/source: `VIRTUAL_REGISTER_COUNT`,
`common/src/constants.rs:3`.
-/
def virtualRegisterCount : Nat := 96

/-- Total Jolt register-address space. Rust keeps this at `128`, a power of two.

Rust name/source: `REGISTER_COUNT`,
`common/src/constants.rs:5`.
-/
def totalRegisterCount : Nat := riscvRegisterCount + virtualRegisterCount

/-- Number of persistent virtual registers skipped by both Rust allocators.

Rust name/source: `NUM_RESERVED_VIRTUAL_REGISTERS`,
`tracer/src/utils/virtual_registers.rs:48-52`,
`crates/jolt-program/src/expand/allocator.rs:8`.
-/
def numReservedVirtualRegisters : Nat := 8

/-- Number of short-lived instruction virtual registers.

Rust name/source: `NUM_VIRTUAL_INSTRUCTION_REGISTERS`,
`tracer/src/utils/virtual_registers.rs:6-10`,
`crates/jolt-program/src/expand/allocator.rs:6`.
-/
def numVirtualInstructionRegisters : Nat := 8

/-- Number of virtual registers available to `allocate_for_inline()`.

Rust name/source: `NUM_INLINE_REGISTERS`,
`crates/jolt-program/src/expand/allocator.rs:9-13`.
-/
def numLargeInlineRegisters : Nat :=
  virtualRegisterCount - numReservedVirtualRegisters -
    numVirtualInstructionRegisters

/-- First Jolt virtual register.

Rust name/source: `RISCV_REGISTER_BASE`,
`tracer/src/utils/virtual_registers.rs:11`,
`crates/jolt-program/src/expand/allocator.rs:7`.
-/
def riscvRegisterBase : Nat := riscvRegisterCount

/-- First virtual register reserved for instruction-local temporaries.

Rust source: `allocate()` skips `NUM_RESERVED_VIRTUAL_REGISTERS`,
`tracer/src/utils/virtual_registers.rs:132-144`,
`crates/jolt-program/src/expand/allocator.rs:133-143`.
-/
def inlineRegisterBase : Nat := riscvRegisterBase + numReservedVirtualRegisters

/-- First virtual register reserved for larger inline allocations.

Rust name/source: `FIRST_INLINE_REGISTER`,
`crates/jolt-program/src/expand/allocator.rs:9-13`;
tracer `allocate_for_inline()` skips reserved and instruction registers at
`tracer/src/utils/virtual_registers.rs:157-164`.
-/
def largeInlineRegisterBase : Nat :=
  inlineRegisterBase + numVirtualInstructionRegisters

/-- Rust allocator's word-reservation virtual register, register 32.

Rust names/source: `RESERVATION_W_REGISTER`, `reservation_w_register()`,
`tracer/src/utils/virtual_registers.rs:37`, `:70-72`,
`crates/jolt-program/src/expand/allocator.rs:16`, `:32-34`.
-/
def reservationWReg : VReg := BitVec.ofNat 7 (riscvRegisterBase + 0)

/-- Rust allocator's dword-reservation virtual register, register 33.

Rust names/source: `RESERVATION_D_REGISTER`, `reservation_d_register()`,
`tracer/src/utils/virtual_registers.rs:38`, `:75-77`,
`crates/jolt-program/src/expand/allocator.rs:17`, `:36-38`.
-/
def reservationDReg : VReg := BitVec.ofNat 7 (riscvRegisterBase + 1)

/-- Rust allocator's trap-handler/`mtvec` virtual register, register 34.

Rust names/source: `TRAP_HANDLER_REGISTER`, `trap_handler_register()`,
`tracer/src/utils/virtual_registers.rs:41`, `:80-82`,
`crates/jolt-program/src/expand/allocator.rs:18`, `:40-42`.
-/
def trapHandlerVReg : VReg := BitVec.ofNat 7 (riscvRegisterBase + 2)

/-- Rust allocator's `mscratch` virtual register, register 35.

Rust names/source: `MSCRATCH_REGISTER`, `mscratch_register()`,
`tracer/src/utils/virtual_registers.rs:42`, `:85-87`,
`crates/jolt-program/src/expand/allocator.rs:19`, `:72-74`.
-/
def mscratchVReg : VReg := BitVec.ofNat 7 (riscvRegisterBase + 3)

/-- Rust allocator's `mepc` virtual register, register 36.

Rust names/source: `MEPC_REGISTER`, `mepc_register()`,
`tracer/src/utils/virtual_registers.rs:43`, `:90-92`,
`crates/jolt-program/src/expand/allocator.rs:20`, `:44-46`.
-/
def mepcVReg : VReg := BitVec.ofNat 7 (riscvRegisterBase + 4)

/-- Rust allocator's `mcause` virtual register, register 37.

Rust names/source: `MCAUSE_REGISTER`, `mcause_register()`,
`tracer/src/utils/virtual_registers.rs:44`, `:95-97`,
`crates/jolt-program/src/expand/allocator.rs:21`, `:48-50`.
-/
def mcauseVReg : VReg := BitVec.ofNat 7 (riscvRegisterBase + 5)

/-- Rust allocator's `mtval` virtual register, register 38.

Rust names/source: `MTVAL_REGISTER`, `mtval_register()`,
`tracer/src/utils/virtual_registers.rs:45`, `:100-102`,
`crates/jolt-program/src/expand/allocator.rs:22`, `:52-54`.
-/
def mtvalVReg : VReg := BitVec.ofNat 7 (riscvRegisterBase + 6)

/-- Rust allocator's `mstatus` virtual register, register 39.

Rust names/source: `MSTATUS_REGISTER`, `mstatus_register()`,
`tracer/src/utils/virtual_registers.rs:46`, `:105-107`,
`crates/jolt-program/src/expand/allocator.rs:23`, `:56-58`.
-/
def mstatusVReg : VReg := BitVec.ofNat 7 (riscvRegisterBase + 7)

/-- The `n`th register returned by Rust `allocate()`, starting at register 40.

Rust name/source: `allocate()`,
`tracer/src/utils/virtual_registers.rs:132-144`,
`crates/jolt-program/src/expand/allocator.rs:133-143`.
-/
def inlineTmp (n : Nat) : VReg := BitVec.ofNat 7 (inlineRegisterBase + n)

/-- The `n`th register returned by Rust `allocate_for_inline()`, starting at
register 48.

Rust name/source: `allocate_for_inline()`,
`tracer/src/utils/virtual_registers.rs:157-164`,
`crates/jolt-program/src/expand/allocator.rs:146-156`.
-/
def largeInlineTmp (n : Nat) : VReg := BitVec.ofNat 7 (largeInlineRegisterBase + n)

/-!
## Total Jolt register-address map

Rust uses one 7-bit register address space:

* `0..31` are architectural RISC-V integer registers;
* `32..39` are persistent virtual registers never returned by an allocator;
* `40..47` are the short-lived `allocate()` pool;
* `48..127` are the `allocate_for_inline()` pool.

The definition below is the single total classifier for that address space.
Projection, preservation, and allocator lemmas should be derived from it.
-/

/-- Meaning of one address in Jolt's 7-bit register space. -/
inductive JoltRegisterSlot where
  | xreg (idx : regidx)
  | reservationW
  | reservationD
  | mtvec
  | mscratch
  | mepc
  | mcause
  | mtval
  | mstatus
  | instructionTmp (idx : Nat)
  | largeInlineTmp (idx : Nat)

/-- Total Rust/Jolt register-address classifier for every `BitVec 7`. -/
def joltRegisterSlot (r : VReg) : JoltRegisterSlot :=
  match r.toNat with
  | 0 => .xreg (regidx.Regidx (BitVec.ofNat 5 0))
  | 1 => .xreg (regidx.Regidx (BitVec.ofNat 5 1))
  | 2 => .xreg (regidx.Regidx (BitVec.ofNat 5 2))
  | 3 => .xreg (regidx.Regidx (BitVec.ofNat 5 3))
  | 4 => .xreg (regidx.Regidx (BitVec.ofNat 5 4))
  | 5 => .xreg (regidx.Regidx (BitVec.ofNat 5 5))
  | 6 => .xreg (regidx.Regidx (BitVec.ofNat 5 6))
  | 7 => .xreg (regidx.Regidx (BitVec.ofNat 5 7))
  | 8 => .xreg (regidx.Regidx (BitVec.ofNat 5 8))
  | 9 => .xreg (regidx.Regidx (BitVec.ofNat 5 9))
  | 10 => .xreg (regidx.Regidx (BitVec.ofNat 5 10))
  | 11 => .xreg (regidx.Regidx (BitVec.ofNat 5 11))
  | 12 => .xreg (regidx.Regidx (BitVec.ofNat 5 12))
  | 13 => .xreg (regidx.Regidx (BitVec.ofNat 5 13))
  | 14 => .xreg (regidx.Regidx (BitVec.ofNat 5 14))
  | 15 => .xreg (regidx.Regidx (BitVec.ofNat 5 15))
  | 16 => .xreg (regidx.Regidx (BitVec.ofNat 5 16))
  | 17 => .xreg (regidx.Regidx (BitVec.ofNat 5 17))
  | 18 => .xreg (regidx.Regidx (BitVec.ofNat 5 18))
  | 19 => .xreg (regidx.Regidx (BitVec.ofNat 5 19))
  | 20 => .xreg (regidx.Regidx (BitVec.ofNat 5 20))
  | 21 => .xreg (regidx.Regidx (BitVec.ofNat 5 21))
  | 22 => .xreg (regidx.Regidx (BitVec.ofNat 5 22))
  | 23 => .xreg (regidx.Regidx (BitVec.ofNat 5 23))
  | 24 => .xreg (regidx.Regidx (BitVec.ofNat 5 24))
  | 25 => .xreg (regidx.Regidx (BitVec.ofNat 5 25))
  | 26 => .xreg (regidx.Regidx (BitVec.ofNat 5 26))
  | 27 => .xreg (regidx.Regidx (BitVec.ofNat 5 27))
  | 28 => .xreg (regidx.Regidx (BitVec.ofNat 5 28))
  | 29 => .xreg (regidx.Regidx (BitVec.ofNat 5 29))
  | 30 => .xreg (regidx.Regidx (BitVec.ofNat 5 30))
  | 31 => .xreg (regidx.Regidx (BitVec.ofNat 5 31))
  | 32 => .reservationW
  | 33 => .reservationD
  | 34 => .mtvec
  | 35 => .mscratch
  | 36 => .mepc
  | 37 => .mcause
  | 38 => .mtval
  | 39 => .mstatus
  | 40 => .instructionTmp 0
  | 41 => .instructionTmp 1
  | 42 => .instructionTmp 2
  | 43 => .instructionTmp 3
  | 44 => .instructionTmp 4
  | 45 => .instructionTmp 5
  | 46 => .instructionTmp 6
  | 47 => .instructionTmp 7
  | n => .largeInlineTmp (n - largeInlineRegisterBase)

/-- The generated Sail register materialized by this Jolt register address, if
any. Most Jolt register addresses do not project into a generated Sail register. -/
def JoltRegisterSlot.sailRegister? : JoltRegisterSlot → Option Register
  | .mtvec => some Register.mtvec
  | .mscratch => some Register.mscratch
  | .mepc => some Register.mepc
  | .mcause => some Register.mcause
  | .mtval => some Register.mtval
  | .mstatus => some Register.mstatus
  | _ => none

/-- The CSR address represented by this Jolt register address, if any. -/
def JoltRegisterSlot.csrAddress? : JoltRegisterSlot → Option (BitVec 12)
  | .mstatus => some 0x300#12
  | .mtvec => some 0x305#12
  | .mscratch => some 0x340#12
  | .mepc => some 0x341#12
  | .mcause => some 0x342#12
  | .mtval => some 0x343#12
  | _ => none

/-- Projection target for one Jolt register address, derived from
`joltRegisterSlot`. -/
def joltRegisterSailTarget? (r : VReg) : Option Register :=
  (joltRegisterSlot r).sailRegister?

/-- CSR address for one Jolt register address, derived from `joltRegisterSlot`. -/
def joltRegisterCsrAddress? (r : VReg) : Option (BitVec 12) :=
  (joltRegisterSlot r).csrAddress?

/-- TODO: Docs -/
def JoltRegisterSlot.isProtected : JoltRegisterSlot → Bool
  | .xreg _ => false
  -- LR/SC reservation virtual registers are Jolt bookkeeping, not RISC-visible
  -- architectural state. LR/SC proofs will need their own reservation contract.
  | .reservationW => false
  | .reservationD => false
  | .mtvec => true
  | .mscratch => true
  | .mepc => true
  | .mcause => true
  | .mtval => true
  | .mstatus => true
  | .instructionTmp _ => false
  | .largeInlineTmp _ => false

/-- Jolt register addresses that must not be clobbered by instruction-local
scratch use. This hides the Rust allocator range split behind the total
register-address classifier. -/
def IsProtectedJoltRegister (r : VReg) : Prop :=
  (joltRegisterSlot r).isProtected = true

/-!
## Tiny model of Rust virtual-register allocation

Rust's `VirtualRegisterAllocator::allocate()` scans the instruction-local pool
`40..47` and returns the first non-live register.  `VirtualRegisterGuard::drop`
marks that register free again, which is why nested inline expansions can reuse
the same scratch after the recursive call returns.

The model below tracks live indices relative to each Rust pool:
`0` denotes register `40` for `allocate()` and register `48` for
`allocate_for_inline()`.
-/

/-- Live indices for Rust `allocate()`, relative to register 40. -/
abbrev InstructionLiveSet := List Nat

/-- Live indices for Rust `allocate_for_inline()`, relative to register 48. -/
abbrev LargeInlineLiveSet := List Nat

/-- First free instruction-local index, matching Rust `allocate()`'s scan. -/
def firstFreeInstructionIndex (live : InstructionLiveSet) : Option Nat :=
  (List.range numVirtualInstructionRegisters).find? fun n =>
    !live.contains n

/-- Rust `allocate()` on the small instruction-local pool. -/
def allocateInstructionRegister
    (live : InstructionLiveSet) : Option (VReg × InstructionLiveSet) :=
  match firstFreeInstructionIndex live with
  | some n => some (inlineTmp n, n :: live)
  | none => none

/-- Rust `VirtualRegisterGuard::drop` for a small instruction-local register. -/
def dropInstructionRegister (n : Nat) (live : InstructionLiveSet) :
    InstructionLiveSet :=
  live.erase n

/-- Rust `allocate_for_inline()` scans the large inline pool from register 48. -/
def firstFreeLargeInlineIndex (live : LargeInlineLiveSet) : Nat :=
  (List.range live.length).foldl (fun candidate n =>
    if live.contains candidate then n + 1 else candidate) 0

/-- Rust `allocate_for_inline()` on the large inline pool. -/
def allocateLargeInlineRegister
    (live : LargeInlineLiveSet) : VReg × LargeInlineLiveSet :=
  let n := firstFreeLargeInlineIndex live
  (largeInlineTmp n, n :: live)

/-- Rust `VirtualRegisterGuard::drop` for a large inline register. -/
def dropLargeInlineRegister (n : Nat) (live : LargeInlineLiveSet) :
    LargeInlineLiveSet :=
  live.erase n

/-! ## Named Rust `allocate()` scratch aliases (registers 40–47) -/

/-- First Rust `allocate()` scratch register, register 40. -/
def inlineTmp0 : VReg := inlineTmp 0

/-- Second Rust `allocate()` scratch register, register 41. -/
def inlineTmp1 : VReg := inlineTmp 1

/-- Third Rust `allocate()` scratch register, register 42. -/
def inlineTmp2 : VReg := inlineTmp 2

/-- Fourth Rust `allocate()` scratch register, register 43. -/
def inlineTmp3 : VReg := inlineTmp 3

/-- Fifth Rust `allocate()` scratch register, register 44. -/
def inlineTmp4 : VReg := inlineTmp 4

/-- Sixth Rust `allocate()` scratch register, register 45. -/
def inlineTmp5 : VReg := inlineTmp 5

/-- Seventh Rust `allocate()` scratch register, register 46. -/
def inlineTmp6 : VReg := inlineTmp 6

/-- Eighth Rust `allocate()` scratch register, register 47. -/
def inlineTmp7 : VReg := inlineTmp 7

end JoltISA
