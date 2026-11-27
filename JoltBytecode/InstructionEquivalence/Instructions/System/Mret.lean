import JoltBytecode.Bundles
import JoltBytecode.InstructionEquivalence.Instructions.System.Common
import JoltBytecode.InstructionEquivalence.ProofSupport.SailTrap
import JoltBytecode.InstructionEquivalence.ProofSupport.BitVecMasks
import JoltBytecode.JoltISA.ExpansionsAutomated
import JoltBytecode.JoltISA.Semantics

open LeanRV64D

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail LeanRV64D LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace System

/-- Jolt's MRET rows shift MPIE into MIE, set MPIE, and jump to the saved exception PC.
The old fall-through PC is saved in scratch v40; for example, a saved PC of
16 makes the new `nextPC` equal to 16.
Jolt: `crates/jolt-program/src/expand/control_flow/mret.rs` at `504dd78a2`.
Based on Quang Dao's `mretProgram_run` in PR #73. -/
theorem mretProgram_run (js : SailJoltState) (next : BitVec 64)
    (hn : js.sail.regs.get? Register.nextPC = some next) :
    JoltISA.execProgram JoltISA.mretProgramAuto js =
      .ok RETIRE_SUCCESS
        { js with
          sail := setNextPCState js.sail
            (jolt_jalr_target64 (js.vregs JoltISA.mepcVReg) 0#64)
          vregs := fun r =>
            if r = JoltISA.inlineTmp0 then next
            else if r = JoltISA.mstatusVReg then
              (js.vregs JoltISA.mstatusVReg >>> 4) ||| 0x80#64
            else js.vregs r } := by
  have h0 : sign_extend (m := 64) (0#12) = 0#64 := by decide
  have h128 : sign_extend (m := 64) (128#12) = 128#64 := by decide
  simp (config := { contextual := true }) [h0, h128, RETIRE_SUCCESS, JoltISA.mretProgramAuto,
    JoltISA.execProgram, JoltISA.execInstr,
    JoltISA.readSrc, readVReg, JoltISA.writeDst, writeVReg,
    JoltISA.mstatusVReg, JoltISA.mepcVReg, JoltISA.inlineTmp0,
    JoltISA.srliBitmask, jolt_virtual_srli_value, ctz,
    Riscv.ori, liftSail, readReg_eq_of_get? _ _ _ hn,
    bind, EStateM.bind, pure, EStateM.pure, get, getThe, MonadStateOf.get,
    EStateM.get, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet,
    Step.writeReg_run, Step.setReg, setNextPCState,
    JoltISA.riscvRegisterBase, JoltISA.riscvRegisterCount, JoltISA.inlineTmp,
    JoltISA.inlineRegisterBase, JoltISA.numReservedVirtualRegisters]
  rfl

/-- When v39 holds only MIE and MPIE, Jolt's MRET shift is Sail's privilege-stack update.
For example, v39 = 0x80 (MPIE set) produces architectural mstatus `0x1888`.
Based on Quang Dao's version in PR #73. -/
theorem mretMstatus_eq (m : BitVec 64) (hm : m &&& ~~~(0x88#64) = 0#64) :
    ((m >>> 4) ||| 0x80#64) ||| 0x1800#64 = Step.mretMstatus (m ||| 0x1800#64) := by
  have hmasked : m &&& 0x88#64 = m := by
    simpa using BitVec.and_not_eq_self_of_and_eq_zero m (~~~(0x88#64)) hm
  conv_lhs => rw [← hmasked]
  conv_rhs => rw [← hmasked]
  simp [Step.mretMstatus, BitVec.and_or_distrib_right, BitVec.and_assoc,
    BitVec.ushiftRight_and_distrib]

/-- The projected mstatus always has MPP = Machine, because the projection adds 0x1800.
For example, v39 = 0 projects to mstatus `0x1800`.
Based on Quang Dao's version in PR #73. -/
theorem mstatus_mpp_machine (raw : BitVec 64) :
    (raw ||| 0x1800#64) &&& 0x1800#64 = 0x1800#64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_or]
  cases raw.getLsbD i <;> cases (0x1800#64).getLsbD i <;> rfl

/-- MRET equivalence statement.

Generated Sail's `execute_MRET` performs the trap-return postlude internally by
calling `exception_handler` for `CTL_MRET` and then `set_next_pc`. -/
def mretProgramEqSailStatement
    (js : SailJoltState) (_h : MretProgramEqSailAssumptions js) : Prop :=
  systemProjectResult ((JoltISA.execProgram JoltISA.mretProgramAuto).run js) =
    (execute_MRET ()).run (systemProject js)

theorem mretProgram_eq_sail_projected
    (js : SailJoltState) (h : MretProgramEqSailAssumptions js) :
    mretProgramEqSailStatement js h := by
  unfold mretProgramEqSailStatement
  obtain ⟨next, hn⟩ := h.nextPC_readable.exists_value
  obtain ⟨pc, hpc⟩ := h.pc_readable.exists_value
  obtain ⟨misa, hmisa⟩ := h.misa_readable.exists_value
  have hpriv : (systemProject js).regs.get? Register.cur_privilege =
      some Privilege.Machine := by
    rw [systemProject_get?_of_not_overlaid js _ (by decide)]
    exact h.cur_privilege_machine.value
  have hpcp : (systemProject js).regs.get? Register.PC = some pc := by
    rw [systemProject_get?_of_not_overlaid js _ (by decide)]
    exact hpc
  have hmisap : (systemProject js).regs.get? Register.misa = some misa := by
    rw [systemProject_get?_of_not_overlaid js _ (by decide)]
    exact hmisa
  have hm : (systemProject js).regs.get? Register.mstatus =
      some (js.vregs JoltISA.mstatusVReg ||| 0x1800#64) := by
    simp [systemProject, Std.ExtDHashMap.get?_insert]
  have he : (systemProject js).regs.get? Register.mepc =
      some (js.vregs JoltISA.mepcVReg) := by
    simp [systemProject, Std.ExtDHashMap.get?_insert]
  have halign : align_pc (js.vregs JoltISA.mepcVReg) (systemProject js) =
      .ok (js.vregs JoltISA.mepcVReg) (systemProject js) :=
    Step.align_pc_of_misa hmisa hmisap h.mepc_read_aligned.value_eq
  simp only [EStateM.run]
  rw [Step.execute_MRET_machine _ _ _ misa pc hpriv hpcp hm he hmisap halign
      (mstatus_mpp_machine _),
    mretProgram_run js next hn]
  have ht : jolt_jalr_target64 (js.vregs JoltISA.mepcVReg) 0#64 = js.vregs JoltISA.mepcVReg := by
    rw [jalr_zero_target]
    apply BitVec.and_not_eq_self_of_and_eq_zero
    rw [BitVec.and_one_eq_setWidth_ofBool_getLsbD, h.mepc_legal.mepc_align]
    rfl
  simp only [systemProjectResult]
  rw [ht, ← mretMstatus_eq _ h.mstatus_legal.mstatus_bits]
  simp [systemProject, Step.setReg, setNextPCState,
    JoltISA.mstatusVReg, JoltISA.trapHandlerVReg, JoltISA.mscratchVReg,
    JoltISA.mepcVReg, JoltISA.mcauseVReg, JoltISA.mtvalVReg,
    JoltISA.reservationWReg, JoltISA.reservationDReg, JoltISA.inlineTmp0,
    JoltISA.riscvRegisterBase, JoltISA.riscvRegisterCount, JoltISA.inlineTmp,
    JoltISA.inlineRegisterBase, JoltISA.numReservedVirtualRegisters,
    extDHashMap_insert_insert_same, extDHashMap_insert_comm_of_ne]

end System

end
