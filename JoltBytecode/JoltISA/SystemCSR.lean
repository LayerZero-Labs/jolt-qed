/-
Copyright (c) 2026 Ari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ari 
-/
import JoltBytecode.JoltISA.VirtualRegisters

/-!
# Supported System CSR whitelist

This file contains the lightweight CSR whitelist/type shared by decoded
RISC-V instructions, proof bundles, and the System expansion programs.

Proof-side `@[simp]` rfl-projection laws against the underlying virtual-register
projectors live in `InstructionEquivalence/ProofSupport/SystemCSR.lean`.
-/

namespace JoltISA

/-- Machine-mode CSRs supported by Jolt's SYSTEM CSR expansion whitelist.

Rust evidence:
* `tracer/src/utils/virtual_registers.rs:120-128`
  `VirtualRegisterAllocator::csr_to_virtual_register` maps exactly these six
  CSR addresses to persistent virtual registers.
* `tracer/src/utils/virtual_registers.rs:234-238`
  `is_supported_csr` is exactly this six-address whitelist.
* `tracer/src/instruction/mod.rs:1166-1174`
  CSRRW decode rejects any CSR address outside `is_supported_csr`.
* `crates/jolt-program/src/expand/allocator.rs:60-68`
  the program expander's `virtual_register_for_csr` has the same six-address
  whitelist and returns `None` otherwise.
-/
inductive SystemCSR where
  | mstatus
  | mtvec
  | mscratch
  | mepc
  | mcause
  | mtval
  deriving Repr, DecidableEq

namespace SystemCSR

/-- Rust CSR address used by the decoded SYSTEM instruction. -/
def address : SystemCSR → BitVec 12
  | .mstatus => 0x300
  | .mtvec => 0x305
  | .mscratch => 0x340
  | .mepc => 0x341
  | .mcause => 0x342
  | .mtval => 0x343

/-- Reserved virtual register used as the proof/trace source of truth for a CSR. -/
def vreg : SystemCSR → VReg
  | .mstatus => mstatusVReg
  | .mtvec => trapHandlerVReg
  | .mscratch => mscratchVReg
  | .mepc => mepcVReg
  | .mcause => mcauseVReg
  | .mtval => mtvalVReg

/-- Generated Sail register represented by the reserved virtual register for
this supported System CSR. This is Jolt ISA layout, not an assumption. -/
def sailRegister : SystemCSR → Register
  | .mstatus => Register.mstatus
  | .mtvec => Register.mtvec
  | .mscratch => Register.mscratch
  | .mepc => Register.mepc
  | .mcause => Register.mcause
  | .mtval => Register.mtval

end SystemCSR

end JoltISA
