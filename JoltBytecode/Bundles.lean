/-
Copyright (c) 2026 Ari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ari 
-/

import JoltBytecode.Assumptions
import JoltBytecode.JoltISA.MemoryAccess
import JoltBytecode.JoltISA.SystemCSR

/-!
# Jolt proof bundles

A bundle is just a subset of assumptions from Assumptions.lean.
Each main equivalence theorem gets a bundle, which states everything 
we must assume to prove the theorem. 
A bundle should NEVER invent assumptions, it can only import them from 
Assumptions.lean.

Thus, the entire assumption surface lives in Assumption.lean.
We could have passed the entire list of assumptions to every theorem, 
but then it is not clear which theorems use which assumptions.
The bundles are a clean way to show that memory equivalence proofs 
require far more assumptions than ALU expansions.

TODO: (Ari) Eventually clean up the CSRRW assumptions. 
They are fine for now.
-/

set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions
open virtaddr MemoryAccessType mem_payload

set_option autoImplicit true

noncomputable section

-- ============================================================================
-- Source-register bundles
-- ============================================================================

/-- Assumptions for an instruction that reads one architectural source register. -/
abbrev UnarySourceReadAssumptions (rs1 : regidx) (js : SailJoltState) :=
  Assumptions.UnarySourceReadAssumptions rs1 js.sail

/-- Assumptions for an instruction that reads two architectural source registers. -/
abbrev BinarySourceReadAssumptions
    (rs2 rs1 : regidx) (js : SailJoltState) :=
  Assumptions.BinarySourceReadAssumptions rs2 rs1 js.sail

-- ============================================================================
-- CSR-link bundles
-- ============================================================================

/-- Persistent CSR virtual registers agree with Sail's architectural CSR state. -/
abbrev LinkedCSRs (js : SailJoltState) : Prop :=
  Assumptions.MstatusVRegMatchesSail js ∧
  Assumptions.MtvecVRegMatchesSail js ∧
  Assumptions.MscratchVRegMatchesSail js ∧
  Assumptions.MepcVRegMatchesSail js ∧
  Assumptions.McauseVRegMatchesSail js ∧
  Assumptions.MtvalVRegMatchesSail js

/-- Fieldwise carrier for the public linked-CSR invariant. -/
private structure LinkedCSRRegisterAssumptions (js : SailJoltState) where
  mstatus_matches : Assumptions.MstatusVRegMatchesSail js
  mtvec_matches : Assumptions.MtvecVRegMatchesSail js
  mscratch_matches : Assumptions.MscratchVRegMatchesSail js
  mepc_matches : Assumptions.MepcVRegMatchesSail js
  mcause_matches : Assumptions.McauseVRegMatchesSail js
  mtval_matches : Assumptions.MtvalVRegMatchesSail js

/-- No source-register reads, plus persistent CSR virtual-register agreement. -/
structure NoSourceReadWithLinkedCSRs
    (js : SailJoltState) : Type
    extends LinkedCSRRegisterAssumptions js

/-- One source-register read plus persistent CSR virtual-register agreement. -/
structure UnarySourceReadWithLinkedCSRs
    (rs1 : regidx) (js : SailJoltState)
    extends UnarySourceReadAssumptions rs1 js,
      LinkedCSRRegisterAssumptions js

/-- Two source-register reads plus persistent CSR virtual-register agreement. -/
structure BinarySourceReadWithLinkedCSRs
    (rs2 rs1 : regidx) (js : SailJoltState)
    extends BinarySourceReadAssumptions rs2 rs1 js,
      LinkedCSRRegisterAssumptions js

def LinkedCSRRegisterAssumptions.linkedCSRs
    {js : SailJoltState}
    (h : LinkedCSRRegisterAssumptions js) :
    LinkedCSRs js :=
  ⟨h.mstatus_matches, h.mtvec_matches, h.mscratch_matches, h.mepc_matches,
    h.mcause_matches, h.mtval_matches⟩

def NoSourceReadWithLinkedCSRs.linkedCSRs
    {js : SailJoltState}
    (h : NoSourceReadWithLinkedCSRs js) :
    LinkedCSRs js :=
  h.toLinkedCSRRegisterAssumptions.linkedCSRs

def UnarySourceReadWithLinkedCSRs.linkedCSRs
    {rs1 : regidx} {js : SailJoltState}
    (h : UnarySourceReadWithLinkedCSRs rs1 js) :
    LinkedCSRs js :=
  h.toLinkedCSRRegisterAssumptions.linkedCSRs

def BinarySourceReadWithLinkedCSRs.linkedCSRs
    {rs2 rs1 : regidx} {js : SailJoltState}
    (h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) :
    LinkedCSRs js :=
  h.toLinkedCSRRegisterAssumptions.linkedCSRs

-- ============================================================================
-- Native control-flow theorem bundles
-- ============================================================================

/-- Public assumptions for native JAL equivalence.

`MepcReadAligned` is a predicate on any address: Sail's `align_pc` succeeds
without changing that address or the state. Applied to the JAL target, it
supplies both the alignment condition and the successful configuration read.
The target is computed from the PC value supplied by `pc_readable`.
-/
structure JalInstrEqSailAssumptions (imm : BitVec 21) (js : SailJoltState)
    extends NoSourceReadWithLinkedCSRs js where
  -- We assume all Sail registers are readable in the modeled machine state.
  -- Record the nextPC and PC instances explicitly for this proof.
  nextPC_readable : Assumptions.SailRegReadable Register.nextPC js.sail
  pc_readable : Assumptions.SailRegReadable Register.PC js.sail
  target_aligned : Assumptions.MepcReadAligned
    (pc_readable.exists_value.choose + sign_extend (m := 64) imm) js.sail

def JalInstrEqSailAssumptions.linkedCSRs
    {imm : BitVec 21} {js : SailJoltState}
    (h : JalInstrEqSailAssumptions imm js) :
    LinkedCSRs js :=
  h.toNoSourceReadWithLinkedCSRs.linkedCSRs

/-- Public assumptions for native JALR equivalence.

Generated Sail runs `update_elp_state rs1` before the ordinary JALR body; Jolt
does not model Zicfilp/ELP state, so this bundle records that the generated
Zicfilp hook is disabled in the Jolt profile.
-/
structure JalrInstrEqSailAssumptions (rs1 : regidx) (js : SailJoltState)
    extends UnarySourceReadWithLinkedCSRs rs1 js where
  zicfilp_disabled : Assumptions.ZicfilpDisabled js.sail

def JalrInstrEqSailAssumptions.linkedCSRs
    {rs1 : regidx} {js : SailJoltState}
    (h : JalrInstrEqSailAssumptions rs1 js) :
    LinkedCSRs js :=
  h.toUnarySourceReadWithLinkedCSRs.linkedCSRs

-- ============================================================================
-- Memory-window bundles
-- ============================================================================

/-- Primitive assumptions for a Jolt dword-backed memory read window. -/
structure DwordReadWindowAssumptions (base : BitVec 64) (s : SailState) : Prop where
  dword_present : Assumptions.DwordPresent base s
  load_pmp : Assumptions.LoadPmpOkWindow base 8 s
  not_readable_mmio : Assumptions.NotReadableMmioWindow base 8 s

/-- Primitive assumptions for a Jolt dword-backed memory write window. -/
structure DwordWriteWindowAssumptions (base : BitVec 64) (s : SailState) : Prop where
  store_pmp : Assumptions.StorePmpOkWindow base 8 s
  not_writable_mmio : Assumptions.NotWritableMmioWindow base 8 s

/-- Primitive assumptions for a Jolt dword-backed read-modify-write window. -/
structure DwordReadWriteWindowAssumptions (base : BitVec 64) (s : SailState) : Prop
    extends DwordReadWindowAssumptions base s,
      DwordWriteWindowAssumptions base s

/-- Primitive assumptions for a Jolt dword-backed AMO window. -/
structure DwordAtomicWindowAssumptions
    (op : amoop) (base : BitVec 64) (s : SailState) : Prop
    extends DwordReadWriteWindowAssumptions base s where
  atomic_pmp : Assumptions.AtomicPmpOkWindow op base 8 s

-- ============================================================================
-- Load/store theorem bundles
-- ============================================================================

/-- Public assumptions for load-family equivalence theorems.

Load expansions read the enclosing Jolt dword. Native Sail's narrower access is
derived from this same read window in the instruction proof. -/
structure LoadProgramEqSailAssumptions (imm : BitVec 12) (rs1 : regidx)
    (js : SailJoltState)
    extends UnarySourceReadWithLinkedCSRs rs1 js,
      DwordReadWindowAssumptions
        (compute_aligned_dword_base_address rs1_val imm) js.sail where
  cur_privilege : Assumptions.CurPrivilegeMachine js.sail
  mstatus_mprv : Assumptions.MstatusMprvZero js.sail

def LoadProgramEqSailAssumptions.linkedCSRs
    {imm : BitVec 12} {rs1 : regidx} {js : SailJoltState}
    (h : LoadProgramEqSailAssumptions imm rs1 js) :
    Assumptions.MstatusVRegMatchesSail js ∧
    Assumptions.MtvecVRegMatchesSail js ∧
    Assumptions.MscratchVRegMatchesSail js ∧
    Assumptions.MepcVRegMatchesSail js ∧
    Assumptions.McauseVRegMatchesSail js ∧
    Assumptions.MtvalVRegMatchesSail js :=
  h.toUnarySourceReadWithLinkedCSRs.linkedCSRs

/-- Public assumptions for store-family equivalence theorems.

Stores reuse the load-family enclosing-dword read assumptions, then add the
second source register and write-side memory window. -/
structure StoreProgramEqSailAssumptions
    (imm : BitVec 12) (rs2 rs1 : regidx) (js : SailJoltState)
    extends LoadProgramEqSailAssumptions imm rs1 js,
      DwordWriteWindowAssumptions
        (compute_aligned_dword_base_address rs1_val imm) js.sail where
  rs2_val : BitVec 64
  rs2_read : rX_bits rs2 js.sail = .ok rs2_val js.sail

def StoreProgramEqSailAssumptions.linkedCSRs
    {imm : BitVec 12} {rs2 rs1 : regidx} {js : SailJoltState}
    (h : StoreProgramEqSailAssumptions imm rs2 rs1 js) :
    Assumptions.MstatusVRegMatchesSail js ∧
    Assumptions.MtvecVRegMatchesSail js ∧
    Assumptions.MscratchVRegMatchesSail js ∧
    Assumptions.MepcVRegMatchesSail js ∧
    Assumptions.McauseVRegMatchesSail js ∧
    Assumptions.MtvalVRegMatchesSail js :=
  h.toLoadProgramEqSailAssumptions.linkedCSRs

-- ============================================================================
-- Fence theorem bundles
-- ============================================================================

/-- Public assumptions for native FENCE equivalence.

Machine mode makes Sail's FIOM check reduce without reading environment CSRs;
the remaining Sail barrier is pure in the generated Lean backend. -/
structure FenceProgramEqSailAssumptions (js : SailJoltState)
    extends NoSourceReadWithLinkedCSRs js where
  cur_privilege : Assumptions.CurPrivilegeMachine js.sail

-- ============================================================================
-- Atomic theorem bundles
-- ============================================================================

/-- The enclosing dword used by `.W` AMO expansions. -/
abbrev amoWordBase (addr : BitVec 64) : BitVec 64 :=
  addr &&& (-8 : BitVec 64)

/-- Register assumptions shared by dword and word AMO equivalence theorems. -/
private structure AmoRegisterAssumptions
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    extends BinarySourceReadWithLinkedCSRs rs2 rs1 js where
  rd_readable : Assumptions.XRegReadable rd js.sail

/-- Public assumptions for dword AMO equivalence theorems. -/
structure AmoDwordProgramEqSailAssumptions
    (op : amoop) (rs2 rs1 rd : regidx) (js : SailJoltState)
    extends AmoRegisterAssumptions rs2 rs1 rd js,
      DwordAtomicWindowAssumptions op rs1_val js.sail where
  cur_privilege : Assumptions.CurPrivilegeMachine js.sail
  mstatus_mprv : Assumptions.MstatusMprvZero js.sail

def AmoDwordProgramEqSailAssumptions.rdReadable
    {op : amoop} {rs2 rs1 rd : regidx} {js : SailJoltState}
    (h : AmoDwordProgramEqSailAssumptions op rs2 rs1 rd js) :
    Assumptions.XRegReadable rd js.sail :=
  h.toAmoRegisterAssumptions.rd_readable

/-- TODO: Docs -/
def AmoDwordProgramEqSailAssumptions.linkedCSRs
    {op : amoop} {rs2 rs1 rd : regidx} {js : SailJoltState}
    (h : AmoDwordProgramEqSailAssumptions op rs2 rs1 rd js) :
    LinkedCSRs js :=
  h.toAmoRegisterAssumptions.toBinarySourceReadWithLinkedCSRs.linkedCSRs

/-- Public assumptions for word AMO equivalence theorems. -/
structure AmoWordProgramEqSailAssumptions
    (op : amoop) (rs2 rs1 rd : regidx) (js : SailJoltState)
    extends AmoRegisterAssumptions rs2 rs1 rd js,
      DwordAtomicWindowAssumptions op (amoWordBase rs1_val) js.sail where
  cur_privilege : Assumptions.CurPrivilegeMachine js.sail
  mstatus_mprv : Assumptions.MstatusMprvZero js.sail

def AmoWordProgramEqSailAssumptions.rdReadable
    {op : amoop} {rs2 rs1 rd : regidx} {js : SailJoltState}
    (h : AmoWordProgramEqSailAssumptions op rs2 rs1 rd js) :
    Assumptions.XRegReadable rd js.sail :=
  h.toAmoRegisterAssumptions.rd_readable

/-- TODO: Docs -/
def AmoWordProgramEqSailAssumptions.linkedCSRs
    {op : amoop} {rs2 rs1 rd : regidx} {js : SailJoltState}
    (h : AmoWordProgramEqSailAssumptions op rs2 rs1 rd js) :
    LinkedCSRs js :=
  h.toAmoRegisterAssumptions.toBinarySourceReadWithLinkedCSRs.linkedCSRs

-- ============================================================================
-- System theorem bundles
-- ============================================================================

namespace System

/-- Public assumptions for MRET equivalence while the proof shape is being
validated.

The bundle records the generated-Sail register lookups needed by MRET together
with the machine-mode precondition required by Sail's `execute_MRET` path. -/
structure MretProgramEqSailAssumptions (js : SailJoltState) : Type where
  nextPC_readable : Assumptions.SailRegReadable Register.nextPC js.sail
  cur_privilege_machine : Assumptions.CurPrivilegeMachine js.sail
  pc_readable : Assumptions.SailRegReadable Register.PC js.sail
  misa_readable : Assumptions.SailRegReadable Register.misa js.sail
  misa_user_enabled : Assumptions.MisaUserEnabled js.sail
  mstatus_mpp_machine : Assumptions.MstatusMppMachine js
  mepc_read_aligned :
    Assumptions.MepcReadAligned (js.vregs JoltISA.mepcVReg) js.sail

/-- Public assumptions for CSRRW equivalence over the supported System CSR
whitelist.

This bundle keeps only the real public inputs: the source register value, the
machine-mode execution envelope, and the decoded six-CSR whitelist carried by
`csr : JoltISA.SystemCSR`. Register non-aliasing, CSR permission checks,
callback neutrality, and projected `rd` writeback are derived in the CSRRW proof
file. -/
structure CsrrwSystemAssumptions
    (js : SailJoltState) (csr : JoltISA.SystemCSR) (rs1 rd : regidx)
    extends Assumptions.UnarySourceReadAssumptions rs1 js.sail where
  mtvec_write_direct :
    csr = JoltISA.SystemCSR.mtvec →
      Assumptions.MtvecWriteDirectMode rs1_val
  mepc_read_aligned :
    csr = JoltISA.SystemCSR.mepc →
      Assumptions.MepcReadAligned (js.vregs JoltISA.mepcVReg) js.sail
  mepc_write_legalized :
    csr = JoltISA.SystemCSR.mepc →
      Assumptions.MepcWriteLegalized rs1_val
  mstatus_write_legalized :
    csr = JoltISA.SystemCSR.mstatus →
      Assumptions.MstatusWriteLegalized
        (js.vregs JoltISA.mstatusVReg) rs1_val js.sail
  cur_privilege_machine : Assumptions.CurPrivilegeMachine js.sail
  linked_csrs :
    Assumptions.MstatusVRegMatchesSail js ∧
    Assumptions.MtvecVRegMatchesSail js ∧
    Assumptions.MscratchVRegMatchesSail js ∧
    Assumptions.MepcVRegMatchesSail js ∧
    Assumptions.McauseVRegMatchesSail js ∧
    Assumptions.MtvalVRegMatchesSail js

/-- Public assumptions for CSRRS equivalence over the supported System CSR
whitelist.

This has the same envelope as `CsrrwSystemAssumptions`, except CSRRS writes
`old CSR | rs1` when `rs1 != x0`, so write-side legalization assumptions are
stated over that read-set value. -/
structure CsrrsSystemAssumptions
    (js : SailJoltState) (csr : JoltISA.SystemCSR) (rs1 rd : regidx)
    extends Assumptions.UnarySourceReadAssumptions rs1 js.sail where
  mtvec_write_direct :
    csr = JoltISA.SystemCSR.mtvec →
      (rs1 == zreg) = false →
        Assumptions.MtvecWriteDirectMode
          (js.vregs (JoltISA.SystemCSR.vreg csr) ||| rs1_val)
  mepc_read_aligned :
    csr = JoltISA.SystemCSR.mepc →
      Assumptions.MepcReadAligned (js.vregs JoltISA.mepcVReg) js.sail
  mepc_write_legalized :
    csr = JoltISA.SystemCSR.mepc →
      (rs1 == zreg) = false →
        Assumptions.MepcWriteLegalized
          (js.vregs (JoltISA.SystemCSR.vreg csr) ||| rs1_val)
  mstatus_write_legalized :
    csr = JoltISA.SystemCSR.mstatus →
      (rs1 == zreg) = false →
        Assumptions.MstatusWriteLegalized
          (js.vregs JoltISA.mstatusVReg)
          (js.vregs (JoltISA.SystemCSR.vreg csr) ||| rs1_val)
          js.sail
  cur_privilege_machine : Assumptions.CurPrivilegeMachine js.sail
  linked_csrs :
    Assumptions.MstatusVRegMatchesSail js ∧
    Assumptions.MtvecVRegMatchesSail js ∧
    Assumptions.MscratchVRegMatchesSail js ∧
    Assumptions.MepcVRegMatchesSail js ∧
    Assumptions.McauseVRegMatchesSail js ∧
    Assumptions.MtvalVRegMatchesSail js

end System

end
