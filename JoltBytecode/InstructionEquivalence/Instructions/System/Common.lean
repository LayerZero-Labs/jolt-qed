import JoltBytecode.Bundles
import JoltBytecode.JoltISA.SystemProjection
import JoltBytecode.InstructionEquivalence.ProofSupport.RegisterAccess

open LeanRV64D

set_option linter.unusedSimpArgs false

/-!
# Shared system-instruction proof surface

The projection materializes six machine CSRs and the reservation registers
from Jolt's persistent virtual registers, forcing `mstatus.MPP` to Machine.
These helpers connect that projection to ordinary integer-register and PC
writes and to the generated Sail trap callbacks.
-/

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail LeanRV64D LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace System

/-- The extension CSR check accepts every access. Stated for the same reason as
`sail_not_true` in ProofSupport/Lemmas.lean. -/
theorem ext_check_CSR_true (csrno : BitVec 12) (p : Privilege) (access : CSRAccessType) :
    ext_check_CSR csrno p access = true := rfl

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
  have hMtval := h.2.2.2.2.2.1
  have hReservation := h.2.2.2.2.2.2
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
    (js.vregs JoltISA.mstatusVReg ||| 0x1800#64) hMstatus.value_eq]
  rw [extDHashMap_insert_eq_self_of_get? js.sail.regs Register.reservation_valid
    _ hReservation.valid_eq]
  rw [extDHashMap_insert_eq_self_of_get? js.sail.regs Register.reservation_addr
    _ hReservation.addr_eq]
  rw [extDHashMap_insert_eq_self_of_get? js.sail.regs Register.reservation_width
    _ hReservation.width_eq]

/-- Reading after inserting a different key returns the old read. -/
theorem extDHashMap_get?_insert_of_ne {α : Type} [BEq α] [Hashable α]
    [LawfulBEq α] {β : α → Type} (m : Std.ExtDHashMap α β)
    {written read : α} (v : β written) (h : written ≠ read) :
    (m.insert written v).get? read = m.get? read := by
  rw [Std.ExtDHashMap.get?_insert]
  have hfalse : (written == read) = false := beq_false_of_ne h
  simp only [hfalse, Bool.false_eq_true]
  rw [dif_neg (by intro hf; cases hf)]

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
  repeat rw [extDHashMap_insert_comm_of_ne (k1 := Register.nextPC) (h := by decide)]

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
  exact csr_name_write_callback_mstatus_run s _

end System

end
