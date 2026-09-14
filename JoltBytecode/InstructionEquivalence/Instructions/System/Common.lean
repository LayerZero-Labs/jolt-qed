import JoltBytecode.Assumptions
import JoltBytecode.JoltISA.Expansions.System
import JoltBytecode.JoltISA.SystemProjection
import JoltBytecode.InstructionEquivalence.ProofSupport.BundleLemmas
import JoltBytecode.InstructionEquivalence.ProofSupport.InstructionLemmas.ADDI
import JoltBytecode.InstructionEquivalence.ProofSupport.InstructionLemmas.VirtualMULI

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Shared system-instruction proof surface

System instructions are the first place where the Rust Jolt expansion keeps
architectural machine CSR state in persistent virtual registers.  The plain
`projectResult` used by ordinary ALU and memory proofs drops those virtual
registers, so it is the wrong projection for MRET/CSR proofs.

The definitions here make that bridge explicit: `systemProject` overlays the
Jolt virtual CSR registers onto the corresponding generated Sail CSR registers.
The Sail side is still computed by Sail helpers such as `exception_handler`,
`set_next_pc`, `tvec_addr`, `_get_Mstatus_*`, and `_update_Mstatus_*`.
-/

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace System

/-- Jolt's concrete MRET return target: `JALR` reads virtual `mepc` and clears
bit 0. -/
def mretReturnTarget (js : SailJoltState) : BitVec 64 :=
  BitVec.update (js.vregs JoltISA.mepcVReg) 0 0#1

/-- Re-inserting a dependent-map value that is already present leaves the map
unchanged. -/
theorem extDHashMap_insert_eq_self_of_get? {α : Type} [BEq α] [Hashable α]
    [LawfulBEq α] {β : α → Type} (m : Std.ExtDHashMap α β) (k : α)
    (v : β k) (h : m.get? k = some v) :
    m.insert k v = m := by
  apply Std.ExtDHashMap.ext_get?
  intro a
  rw [Std.ExtDHashMap.get?_insert]
  split
  · rename_i hbeq
    have heq : k = a := LawfulBEq.eq_of_beq hbeq
    cases heq
    rw [h]
    rw [cast_eq]
  · rfl

/-- If the linked CSR virtual registers agree with the generated Sail CSR
registers, materializing those virtual registers is the same state as the plain
projection. This is the global linked-register invariant made explicit. -/
theorem systemProject_eq_project_of_compatible
    (js : SailJoltState)
    (h : LinkedCSRs js) :
    systemProject js = project js := by
  have hMstatus := h.1
  have hMtvec := h.2.1
  have hMscratch := h.2.2.1
  have hMepc := h.2.2.2.1
  have hMcause := h.2.2.2.2.1
  have hMtval := h.2.2.2.2.2
  unfold systemProject project
  simp only
  congr
  rw [extDHashMap_insert_eq_self_of_get? js.sail.regs Register.mtvec
    (js.vregs JoltISA.trapHandlerVReg) hMtvec.value_eq]
  rw [extDHashMap_insert_eq_self_of_get? js.sail.regs Register.mscratch
    (js.vregs JoltISA.mscratchVReg) hMscratch.value_eq]
  rw [extDHashMap_insert_eq_self_of_get? js.sail.regs Register.mepc
    (js.vregs JoltISA.mepcVReg) hMepc.value_eq]
  rw [extDHashMap_insert_eq_self_of_get? js.sail.regs Register.mcause
    (js.vregs JoltISA.mcauseVReg) hMcause.value_eq]
  rw [extDHashMap_insert_eq_self_of_get? js.sail.regs Register.mtval
    (js.vregs JoltISA.mtvalVReg) hMtval.value_eq]
  rw [extDHashMap_insert_eq_self_of_get? js.sail.regs Register.mstatus
    (js.vregs JoltISA.mstatusVReg) hMstatus.value_eq]

/-- Reading after inserting a different key returns the old read. -/
theorem extDHashMap_get?_insert_of_ne {α : Type} [BEq α] [Hashable α]
    [LawfulBEq α] {β : α → Type} (m : Std.ExtDHashMap α β)
    {written read : α} (v : β written) (h : written ≠ read) :
    (m.insert written v).get? read = m.get? read := by
  rw [Std.ExtDHashMap.get?_insert]
  have hfalse : (written == read) = false := beq_false_of_ne h
  simp only [hfalse, Bool.false_eq_true]
  rw [dif_neg (by intro hf; cases hf)]

/-- Two writes to one dependent-map key do not affect reads from a different
key. -/
theorem extDHashMap_get?_insert_twice_of_ne {α : Type} [BEq α] [Hashable α]
    [LawfulBEq α] {β : α → Type} (m : Std.ExtDHashMap α β)
    {written read : α} (v1 v2 : β written) (h : written ≠ read) :
    ((m.insert written v1).insert written v2).get? read = m.get? read := by
  rw [extDHashMap_get?_insert_of_ne (h := h)]
  rw [extDHashMap_get?_insert_of_ne (h := h)]

/-- A later write to the same dependent-map key overwrites the earlier write. -/
theorem extDHashMap_insert_insert_same {α : Type} [BEq α] [Hashable α]
    [LawfulBEq α] {β : α → Type} (m : Std.ExtDHashMap α β)
    (k : α) (v1 v2 : β k) :
    (m.insert k v1).insert k v2 = m.insert k v2 := by
  apply Std.ExtDHashMap.ext_get?
  intro a
  by_cases ha : a = k
  · subst a
    rw [Std.ExtDHashMap.get?_insert_self]
    rw [Std.ExtDHashMap.get?_insert_self]
  · rw [extDHashMap_get?_insert_of_ne (h := by intro hk; exact ha hk.symm)]
    rw [extDHashMap_get?_insert_of_ne (h := by intro hk; exact ha hk.symm)]
    rw [extDHashMap_get?_insert_of_ne (h := by intro hk; exact ha hk.symm)]

/-- Inserts at distinct dependent-map keys commute. -/
theorem extDHashMap_insert_comm_of_ne {α : Type} [BEq α] [Hashable α]
    [LawfulBEq α] {β : α → Type} (m : Std.ExtDHashMap α β)
    {k1 k2 : α} (v1 : β k1) (v2 : β k2) (h : k1 ≠ k2) :
    (m.insert k1 v1).insert k2 v2 =
      (m.insert k2 v2).insert k1 v1 := by
  apply Std.ExtDHashMap.ext_get?
  intro a
  by_cases ha1 : a = k1
  · subst a
    rw [extDHashMap_get?_insert_of_ne (h := h.symm)]
    rw [Std.ExtDHashMap.get?_insert_self]
    rw [Std.ExtDHashMap.get?_insert_self]
  · by_cases ha2 : a = k2
    · subst a
      rw [Std.ExtDHashMap.get?_insert_self]
      rw [extDHashMap_get?_insert_of_ne (h := h)]
      rw [Std.ExtDHashMap.get?_insert_self]
    · rw [extDHashMap_get?_insert_of_ne (h := by intro hk; exact ha2 hk.symm)]
      rw [extDHashMap_get?_insert_of_ne (h := by intro hk; exact ha1 hk.symm)]
      rw [extDHashMap_get?_insert_of_ne (h := by intro hk; exact ha1 hk.symm)]
      rw [extDHashMap_get?_insert_of_ne (h := by intro hk; exact ha2 hk.symm)]

/-- A successful generated Sail register read from a populated key is a pure
read of the current state. -/
theorem sail_readReg_run
    (s : SailState) (reg : Register) (value : RegisterType reg)
    (h : s.regs.get? reg = some value) :
    (Sail.readReg reg : SailM (RegisterType reg)) s = .ok value s := by
  unfold Sail.readReg PreSail.readReg
  simp only [h, bind, EStateM.bind, pure, EStateM.pure,
    get, getThe, MonadStateOf.get, EStateM.get]

/-- A generated Sail register write only inserts the new register value. -/
theorem sail_writeReg_run
    (s : SailState) (reg : Register) (value : RegisterType reg) :
    (Sail.writeReg reg value : SailM Unit) s =
      .ok () { s with regs := s.regs.insert reg value } := by
  unfold Sail.writeReg PreSail.writeReg
  simp only [modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]

/-- Reading a non-overlaid register through `systemProject` reads the original
Sail register map. -/
theorem systemProject_get_unmodified
    (js : SailJoltState) (reg : Register)
    (hmstatus : (Register.mstatus == reg) = false)
    (hmtval : (Register.mtval == reg) = false)
    (hmcause : (Register.mcause == reg) = false)
    (hmepc : (Register.mepc == reg) = false)
    (hmscratch : (Register.mscratch == reg) = false)
    (hmtvec : (Register.mtvec == reg) = false) :
    (systemProject js).regs.get? reg = js.sail.regs.get? reg := by
  unfold systemProject
  simp only [Std.ExtDHashMap.get?_insert, hmstatus, hmtval, hmcause, hmepc,
    hmscratch, hmtvec, Bool.false_eq_true]
  repeat rw [dif_neg (by intro h; cases h)]

/-- `systemProject` preserves architectural integer-register reads: it overlays
only machine CSR registers, never `x0`-`x31`. -/
theorem systemProject_rX_bits
    (js : SailJoltState) (rs : regidx) (value : BitVec 64)
    (h_read : rX_bits rs js.sail = .ok value js.sail) :
    rX_bits rs (systemProject js) = .ok value (systemProject js) := by
  unfold rX_bits rX regval_from_reg at h_read ⊢
  simp only [Sail.BitVec.toNatInt, Int.ofNat_eq_natCast, Int.toNat_natCast,
    bind, EStateM.bind, pure, EStateM.pure] at h_read ⊢
  obtain ⟨i⟩ := rs
  have hi : i.toNat < 32 := i.isLt
  have hcases : i.toNat = 0 ∨ i.toNat = 1 ∨ i.toNat = 2 ∨ i.toNat = 3 ∨
      i.toNat = 4 ∨ i.toNat = 5 ∨ i.toNat = 6 ∨ i.toNat = 7 ∨
      i.toNat = 8 ∨ i.toNat = 9 ∨ i.toNat = 10 ∨ i.toNat = 11 ∨
      i.toNat = 12 ∨ i.toNat = 13 ∨ i.toNat = 14 ∨ i.toNat = 15 ∨
      i.toNat = 16 ∨ i.toNat = 17 ∨ i.toNat = 18 ∨ i.toNat = 19 ∨
      i.toNat = 20 ∨ i.toNat = 21 ∨ i.toNat = 22 ∨ i.toNat = 23 ∨
      i.toNat = 24 ∨ i.toNat = 25 ∨ i.toNat = 26 ∨ i.toNat = 27 ∨
      i.toNat = 28 ∨ i.toNat = 29 ∨ i.toNat = 30 ∨ i.toNat = 31 := by
    omega
  rcases hcases with hidx | hidx | hidx | hidx | hidx | hidx | hidx | hidx |
      hidx | hidx | hidx | hidx | hidx | hidx | hidx | hidx |
      hidx | hidx | hidx | hidx | hidx | hidx | hidx | hidx |
      hidx | hidx | hidx | hidx | hidx | hidx | hidx | hidx
  · simp only [hidx] at h_read ⊢
    cases h_read
    rfl
  all_goals
    simp only [hidx] at h_read ⊢
    unfold Sail.readReg PreSail.readReg at h_read ⊢
    simp only [bind, EStateM.bind, get, getThe, MonadStateOf.get,
      EStateM.get, pure] at h_read ⊢
    rw [systemProject_get_unmodified]
    · generalize hget : js.sail.regs.get? _ = lookup at h_read ⊢
      cases lookup with
      | none =>
          simp only [throw, throwThe, MonadExceptOf.throw,
            EStateM.throw] at h_read
          cases h_read
      | some regVal =>
          simp only at h_read ⊢
          cases h_read
          rfl
    all_goals decide

/-- `systemProject` preserves the architectural `PC` read. -/
theorem systemProject_pc_read
    (js : SailJoltState) (pc : BitVec 64)
    (hpc : js.sail.regs.get? Register.PC =
      some (pc : RegisterType Register.PC)) :
    (systemProject js).regs.get? Register.PC =
      some (pc : RegisterType Register.PC) := by
  rw [systemProject_get_unmodified]
  exact hpc
  all_goals decide

/-- `systemProject` preserves the architectural `nextPC` read. -/
theorem systemProject_nextPC_read
    (js : SailJoltState) (nextPC : BitVec 64)
    (hnextPC : js.sail.regs.get? Register.nextPC =
      some (nextPC : RegisterType Register.nextPC)) :
    (systemProject js).regs.get? Register.nextPC =
      some (nextPC : RegisterType Register.nextPC) := by
  rw [systemProject_get_unmodified]
  exact hnextPC
  all_goals decide

/-- `systemProject` preserves the machine-mode privilege read. -/
theorem systemProject_cur_privilege_read
    (js : SailJoltState)
    (hpriv : js.sail.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege)) :
    (systemProject js).regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege) := by
  rw [systemProject_get_unmodified]
  exact hpriv
  all_goals decide

/-- `systemProject` preserves the `medeleg` read used by Sail delegation. -/
theorem systemProject_medeleg_read
    (js : SailJoltState) (medeleg : BitVec 64)
    (hmedeleg : js.sail.regs.get? Register.medeleg =
      some (medeleg : RegisterType Register.medeleg)) :
    (systemProject js).regs.get? Register.medeleg =
      some (medeleg : RegisterType Register.medeleg) := by
  rw [systemProject_get_unmodified]
  exact hmedeleg
  all_goals decide

/-- `systemProject` preserves the `misa` read used by Sail extension checks. -/
theorem systemProject_misa_read
    (js : SailJoltState) (misa : BitVec 64)
    (hmisa : js.sail.regs.get? Register.misa =
      some (misa : RegisterType Register.misa)) :
    (systemProject js).regs.get? Register.misa =
      some (misa : RegisterType Register.misa) := by
  rw [systemProject_get_unmodified]
  exact hmisa
  all_goals decide

/-- `systemProject` preserves the `elp = 0` read used by Zicfilp trap
bookkeeping. -/
theorem systemProject_elp_read
    (js : SailJoltState)
    (help : js.sail.regs.get? Register.elp =
      some (0#1 : RegisterType Register.elp)) :
    (systemProject js).regs.get? Register.elp =
      some (0#1 : RegisterType Register.elp) := by
  rw [systemProject_get_unmodified]
  exact help
  all_goals decide

/-- `systemProject` materializes virtual `mstatus` at the Sail `mstatus` key. -/
theorem systemProject_mstatus_read
    (js : SailJoltState) :
    (systemProject js).regs.get? Register.mstatus =
      some (js.vregs JoltISA.mstatusVReg : RegisterType Register.mstatus) := by
  unfold systemProject
  simp only [Std.ExtDHashMap.get?_insert_self]

/-- `systemProject` materializes virtual `mtvec` at the Sail `mtvec` key. -/
theorem systemProject_mtvec_read
    (js : SailJoltState) :
    (systemProject js).regs.get? Register.mtvec =
      some (js.vregs JoltISA.trapHandlerVReg : RegisterType Register.mtvec) := by
  unfold systemProject
  rw [extDHashMap_get?_insert_of_ne (h := by decide)]
  rw [extDHashMap_get?_insert_of_ne (h := by decide)]
  rw [extDHashMap_get?_insert_of_ne (h := by decide)]
  rw [extDHashMap_get?_insert_of_ne (h := by decide)]
  rw [extDHashMap_get?_insert_of_ne (h := by decide)]
  rw [Std.ExtDHashMap.get?_insert_self]

/-- `systemProject` materializes virtual `mscratch` at the Sail `mscratch` key. -/
theorem systemProject_mscratch_read
    (js : SailJoltState) :
    (systemProject js).regs.get? Register.mscratch =
      some (js.vregs JoltISA.mscratchVReg : RegisterType Register.mscratch) := by
  unfold systemProject
  rw [extDHashMap_get?_insert_of_ne (h := by decide)]
  rw [extDHashMap_get?_insert_of_ne (h := by decide)]
  rw [extDHashMap_get?_insert_of_ne (h := by decide)]
  rw [extDHashMap_get?_insert_of_ne (h := by decide)]
  rw [Std.ExtDHashMap.get?_insert_self]

/-- `systemProject` materializes virtual `mepc` at the Sail `mepc` key. -/
theorem systemProject_mepc_read
    (js : SailJoltState) :
    (systemProject js).regs.get? Register.mepc =
      some (js.vregs JoltISA.mepcVReg : RegisterType Register.mepc) := by
  unfold systemProject
  rw [extDHashMap_get?_insert_of_ne (h := by decide)]
  rw [extDHashMap_get?_insert_of_ne (h := by decide)]
  rw [extDHashMap_get?_insert_of_ne (h := by decide)]
  rw [Std.ExtDHashMap.get?_insert_self]

/-- `systemProject` materializes virtual `mcause` at the Sail `mcause` key. -/
theorem systemProject_mcause_read
    (js : SailJoltState) :
    (systemProject js).regs.get? Register.mcause =
      some (js.vregs JoltISA.mcauseVReg : RegisterType Register.mcause) := by
  unfold systemProject
  rw [extDHashMap_get?_insert_of_ne (h := by decide)]
  rw [extDHashMap_get?_insert_of_ne (h := by decide)]
  rw [Std.ExtDHashMap.get?_insert_self]

/-- `systemProject` materializes virtual `mtval` at the Sail `mtval` key. -/
theorem systemProject_mtval_read
    (js : SailJoltState) :
    (systemProject js).regs.get? Register.mtval =
      some (js.vregs JoltISA.mtvalVReg : RegisterType Register.mtval) := by
  unfold systemProject
  rw [extDHashMap_get?_insert_of_ne (h := by decide)]
  rw [Std.ExtDHashMap.get?_insert_self]

/-- Replace one Jolt virtual register in a register-file function. -/
def vregWrite (vregs : BitVec 7 → BitVec 64) (vr : JoltISA.VReg)
    (value : BitVec 64) : BitVec 7 → BitVec 64 :=
  fun r => if r = vr then value else vregs r

/-- Replace one Jolt virtual register in the full Jolt state. -/
def joltSetVReg (js : SailJoltState) (vr : JoltISA.VReg)
    (value : BitVec 64) : SailJoltState :=
  { js with vregs := vregWrite js.vregs vr value }

/-- Final state for the CSRRW write-only `csrw csr, rs1` case. -/
def csrrwAfterCsrWrite
    (js : SailJoltState) (csr : JoltISA.SystemCSR) (rs1Val : BitVec 64) :
    SailJoltState :=
  joltSetVReg js (JoltISA.SystemCSR.vreg csr) rs1Val

/-- Final CSRRW state after `rd` receives the old CSR value and the virtual CSR
receives `rs1`. -/
def csrrwAfterReadWrite
    (js : SailJoltState) (csr : JoltISA.SystemCSR) (rd : regidx)
    (oldCsr rs1Val : BitVec 64) : SailJoltState :=
  joltSetVReg { js with sail := stateAfterWrite js.sail rd oldCsr }
    (JoltISA.SystemCSR.vreg csr) rs1Val

/-- Final CSRRW state for the `rd = rs1` branch: the source is preserved in
scratch, the old CSR is written to `rd`, then the preserved value is restored
to the CSR virtual register. -/
def csrrwAfterSameReg
    (js : SailJoltState) (csr : JoltISA.SystemCSR) (rd : regidx)
    (oldCsr rs1Val : BitVec 64) : SailJoltState :=
  joltSetVReg
    { joltSetVReg js JoltISA.systemScratchVReg rs1Val with
      sail := stateAfterWrite js.sail rd oldCsr }
    (JoltISA.SystemCSR.vreg csr) rs1Val

/-- The concrete final Jolt state selected by Rust's CSRRW expansion branches. -/
def csrrwJoltFinal
    (js : SailJoltState) (csr : JoltISA.SystemCSR) (rs1 rd : regidx)
    (rs1Val : BitVec 64) : SailJoltState :=
  if JoltISA.isX0 rd then
    csrrwAfterCsrWrite js csr rs1Val
  else if JoltISA.sameXReg rd rs1 then
    csrrwAfterSameReg js csr rd
      (js.vregs (JoltISA.SystemCSR.vreg csr)) rs1Val
  else
    csrrwAfterReadWrite js csr rd
      (js.vregs (JoltISA.SystemCSR.vreg csr)) rs1Val

/-- Sail state after writing `nextPC`; used by Jolt `JALR` and Sail trap entry. -/
def setNextPCState (s : SailState) (target : BitVec 64) : SailState :=
  { s with regs := s.regs.insert Register.nextPC target }

/-- Projecting after a Sail `nextPC` write is the same as writing `nextPC`
after projecting Jolt's virtual CSR registers. -/
theorem systemProject_setNextPCState
    (js : SailJoltState) (target : BitVec 64) :
    systemProject { js with sail := setNextPCState js.sail target } =
      { systemProject js with
        regs := (systemProject js).regs.insert Register.nextPC target } := by
  unfold systemProject setNextPCState
  simp only
  congr 1
  calc
    (((((((js.sail.regs.insert Register.nextPC target).insert Register.mtvec
                    (js.vregs JoltISA.trapHandlerVReg)).insert Register.mscratch
                  (js.vregs JoltISA.mscratchVReg)).insert Register.mepc
                (js.vregs JoltISA.mepcVReg)).insert Register.mcause
              (js.vregs JoltISA.mcauseVReg)).insert Register.mtval
            (js.vregs JoltISA.mtvalVReg)).insert Register.mstatus
          (js.vregs JoltISA.mstatusVReg))
        = (((((((js.sail.regs.insert Register.mtvec
                    (js.vregs JoltISA.trapHandlerVReg)).insert Register.nextPC target).insert Register.mscratch
                  (js.vregs JoltISA.mscratchVReg)).insert Register.mepc
                (js.vregs JoltISA.mepcVReg)).insert Register.mcause
              (js.vregs JoltISA.mcauseVReg)).insert Register.mtval
            (js.vregs JoltISA.mtvalVReg)).insert Register.mstatus
          (js.vregs JoltISA.mstatusVReg)) := by
          rw [extDHashMap_insert_comm_of_ne
            (m := js.sail.regs)
            (k1 := Register.nextPC) (k2 := Register.mtvec)
            (v1 := target) (v2 := js.vregs JoltISA.trapHandlerVReg)
            (h := by decide)]
    _ = (((((((js.sail.regs.insert Register.mtvec
                    (js.vregs JoltISA.trapHandlerVReg)).insert Register.mscratch
                  (js.vregs JoltISA.mscratchVReg)).insert Register.nextPC target).insert Register.mepc
                (js.vregs JoltISA.mepcVReg)).insert Register.mcause
              (js.vregs JoltISA.mcauseVReg)).insert Register.mtval
            (js.vregs JoltISA.mtvalVReg)).insert Register.mstatus
          (js.vregs JoltISA.mstatusVReg)) := by
          rw [extDHashMap_insert_comm_of_ne
            (m := (js.sail.regs.insert Register.mtvec
              (js.vregs JoltISA.trapHandlerVReg)))
            (k1 := Register.nextPC) (k2 := Register.mscratch)
            (v1 := target) (v2 := js.vregs JoltISA.mscratchVReg)
            (h := by decide)]
    _ = (((((((js.sail.regs.insert Register.mtvec
                    (js.vregs JoltISA.trapHandlerVReg)).insert Register.mscratch
                  (js.vregs JoltISA.mscratchVReg)).insert Register.mepc
                (js.vregs JoltISA.mepcVReg)).insert Register.nextPC target).insert Register.mcause
              (js.vregs JoltISA.mcauseVReg)).insert Register.mtval
            (js.vregs JoltISA.mtvalVReg)).insert Register.mstatus
          (js.vregs JoltISA.mstatusVReg)) := by
          rw [extDHashMap_insert_comm_of_ne
            (m := ((js.sail.regs.insert Register.mtvec
              (js.vregs JoltISA.trapHandlerVReg)).insert Register.mscratch
              (js.vregs JoltISA.mscratchVReg)))
            (k1 := Register.nextPC) (k2 := Register.mepc)
            (v1 := target) (v2 := js.vregs JoltISA.mepcVReg)
            (h := by decide)]
    _ = (((((((js.sail.regs.insert Register.mtvec
                    (js.vregs JoltISA.trapHandlerVReg)).insert Register.mscratch
                  (js.vregs JoltISA.mscratchVReg)).insert Register.mepc
                (js.vregs JoltISA.mepcVReg)).insert Register.mcause
              (js.vregs JoltISA.mcauseVReg)).insert Register.nextPC target).insert Register.mtval
            (js.vregs JoltISA.mtvalVReg)).insert Register.mstatus
          (js.vregs JoltISA.mstatusVReg)) := by
          rw [extDHashMap_insert_comm_of_ne
            (m := (((js.sail.regs.insert Register.mtvec
              (js.vregs JoltISA.trapHandlerVReg)).insert Register.mscratch
              (js.vregs JoltISA.mscratchVReg)).insert Register.mepc
              (js.vregs JoltISA.mepcVReg)))
            (k1 := Register.nextPC) (k2 := Register.mcause)
            (v1 := target) (v2 := js.vregs JoltISA.mcauseVReg)
            (h := by decide)]
    _ = (((((((js.sail.regs.insert Register.mtvec
                    (js.vregs JoltISA.trapHandlerVReg)).insert Register.mscratch
                  (js.vregs JoltISA.mscratchVReg)).insert Register.mepc
                (js.vregs JoltISA.mepcVReg)).insert Register.mcause
              (js.vregs JoltISA.mcauseVReg)).insert Register.mtval
            (js.vregs JoltISA.mtvalVReg)).insert Register.nextPC target).insert Register.mstatus
          (js.vregs JoltISA.mstatusVReg)) := by
          rw [extDHashMap_insert_comm_of_ne
            (m := ((((js.sail.regs.insert Register.mtvec
              (js.vregs JoltISA.trapHandlerVReg)).insert Register.mscratch
              (js.vregs JoltISA.mscratchVReg)).insert Register.mepc
              (js.vregs JoltISA.mepcVReg)).insert Register.mcause
              (js.vregs JoltISA.mcauseVReg)))
            (k1 := Register.nextPC) (k2 := Register.mtval)
            (v1 := target) (v2 := js.vregs JoltISA.mtvalVReg)
            (h := by decide)]
    _ = (((((((js.sail.regs.insert Register.mtvec
                    (js.vregs JoltISA.trapHandlerVReg)).insert Register.mscratch
                  (js.vregs JoltISA.mscratchVReg)).insert Register.mepc
                (js.vregs JoltISA.mepcVReg)).insert Register.mcause
              (js.vregs JoltISA.mcauseVReg)).insert Register.mtval
            (js.vregs JoltISA.mtvalVReg)).insert Register.mstatus
          (js.vregs JoltISA.mstatusVReg)).insert Register.nextPC target) := by
          rw [extDHashMap_insert_comm_of_ne
            (m := (((((js.sail.regs.insert Register.mtvec
              (js.vregs JoltISA.trapHandlerVReg)).insert Register.mscratch
              (js.vregs JoltISA.mscratchVReg)).insert Register.mepc
              (js.vregs JoltISA.mepcVReg)).insert Register.mcause
              (js.vregs JoltISA.mcauseVReg)).insert Register.mtval
              (js.vregs JoltISA.mtvalVReg)))
            (k1 := Register.nextPC) (k2 := Register.mstatus)
            (v1 := target) (v2 := js.vregs JoltISA.mstatusVReg)
            (h := by decide)]

/-- Projecting after an architectural x-register write is the same as applying
that write after projecting Jolt's virtual CSR registers. -/
theorem systemProject_stateAfterWrite
    (js : SailJoltState) (rd : regidx) (value : BitVec 64) :
    systemProject { js with sail := stateAfterWrite js.sail rd value } =
      stateAfterWrite (systemProject js) rd value := by
  unfold systemProject stateAfterWrite wX_update_regs regval_into_reg
  obtain ⟨rdBits⟩ := rd
  reg_cases (regidx.Regidx rdBits) <;>
    simp_all [extDHashMap_insert_comm_of_ne]

/-- Running generated Sail `set_next_pc` through `systemProject` is the same
projected state as Jolt's final `JALR` Sail-state update. -/
theorem set_next_pc_systemProject_run
    (js : SailJoltState) (target : BitVec 64) :
    (set_next_pc target).run (systemProject js) =
      .ok () (systemProject { js with sail := setNextPCState js.sail target }) := by
  unfold set_next_pc sail_branch_announce redirect_callback
  unfold Sail.writeReg PreSail.writeReg
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]
  rw [← systemProject_setNextPCState]

/-- Writing a virtual register and reading that same register returns the new
value. -/
theorem vregWrite_self (vregs : BitVec 7 → BitVec 64) (vr : JoltISA.VReg)
    (value : BitVec 64) :
    vregWrite vregs vr value vr = value := by
  unfold vregWrite
  exact if_pos rfl

/-- Writing one virtual register leaves every different virtual register alone. -/
theorem vregWrite_other (vregs : BitVec 7 → BitVec 64)
    (written read : JoltISA.VReg) (value : BitVec 64)
    (h_ne : read ≠ written) :
    vregWrite vregs written value read = vregs read := by
  unfold vregWrite
  exact if_neg h_ne

/-- `ADDI x, 0` leaves a 64-bit Jolt value unchanged. -/
theorem addi_zero_value (x : BitVec 64) :
    x + sign_extend (m := 64) (0 : BitVec 12) = x := by
  have hzero : sign_extend (m := 64) (0 : BitVec 12) = 0#64 := by
    decide
  rw [hzero]
  norm_num

/-- Sail's compressed-extension query reads `misa` and otherwise leaves state
unchanged.  `jump_to` evaluates this even when the trap target's bit 1 is
already clear. -/
theorem currentlyEnabled_Ext_C_run
    (s : SailState) (misa : BitVec 64)
    (hmisa : s.regs.get? Register.misa =
      some (misa : RegisterType Register.misa)) :
    (currentlyEnabled extension.Ext_C) s =
      .ok (hartSupports extension.Ext_C && ((_get_Misa_C misa) == 1#1)) s := by
  unfold currentlyEnabled Sail.readReg PreSail.readReg
  simp only [hmisa, bind, EStateM.bind, pure, EStateM.pure,
    MonadStateOf.get, EStateM.get, getThe, get]

/-- Literal callback map lookup for the generated `mstatus` CSR name. -/
theorem csr_name_map_backwards_mstatus_run (s : SailState) :
    csr_name_map_backwards "mstatus" s = .ok (0x300#12) s := by
  rfl

/-- Literal callback map lookup for the generated `mcause` CSR name. -/
theorem csr_name_map_backwards_mcause_run (s : SailState) :
    csr_name_map_backwards "mcause" s = .ok (0x342#12) s := by
  rfl

/-- Literal callback map lookup for the generated `mtval` CSR name. -/
theorem csr_name_map_backwards_mtval_run (s : SailState) :
    csr_name_map_backwards "mtval" s = .ok (0x343#12) s := by
  rfl

/-- Literal callback map lookup for the generated `mepc` CSR name. -/
theorem csr_name_map_backwards_mepc_run (s : SailState) :
    csr_name_map_backwards "mepc" s = .ok (0x341#12) s := by
  rfl

/-- The generated CSR-name write callback for `mstatus` is state-neutral. -/
theorem csr_name_write_callback_mstatus_run
    (s : SailState) (value : BitVec 64) :
    csr_name_write_callback "mstatus" value s = .ok () s := by
  unfold csr_name_write_callback csr_full_write_callback
  simp only [bind, EStateM.bind, csr_name_map_backwards_mstatus_run,
    pure, EStateM.pure]

/-- The generated CSR-name write callback for `mcause` is state-neutral. -/
theorem csr_name_write_callback_mcause_run
    (s : SailState) (value : BitVec 64) :
    csr_name_write_callback "mcause" value s = .ok () s := by
  unfold csr_name_write_callback csr_full_write_callback
  simp only [bind, EStateM.bind, csr_name_map_backwards_mcause_run,
    pure, EStateM.pure]

/-- The generated CSR-name write callback for `mtval` is state-neutral. -/
theorem csr_name_write_callback_mtval_run
    (s : SailState) (value : BitVec 64) :
    csr_name_write_callback "mtval" value s = .ok () s := by
  unfold csr_name_write_callback csr_full_write_callback
  simp only [bind, EStateM.bind, csr_name_map_backwards_mtval_run,
    pure, EStateM.pure]

/-- The generated CSR-name write callback for `mepc` is state-neutral. -/
theorem csr_name_write_callback_mepc_run
    (s : SailState) (value : BitVec 64) :
    csr_name_write_callback "mepc" value s = .ok () s := by
  unfold csr_name_write_callback csr_full_write_callback
  simp only [bind, EStateM.bind, csr_name_map_backwards_mepc_run,
    pure, EStateM.pure]

/-- The generated long-CSR callback for `mstatus` is state-neutral. -/
theorem long_csr_write_callback_mstatus_run
    (s : SailState) (value : BitVec 64) :
    long_csr_write_callback "mstatus" "mstatush" value s = .ok () s := by
  unfold long_csr_write_callback
  rw [csr_name_write_callback_mstatus_run]

end System

end
