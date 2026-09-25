import JoltBytecode.Bundles
import JoltBytecode.InstructionEquivalence.Instructions.System.Common

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace System

/-- Writing the MRET link value to Jolt's system scratch virtual register
succeeds and updates only the virtual-register file. -/
private theorem writeDst_systemScratchVReg_run
    (js : SailJoltState) (nextPC target : BitVec 64) :
    JoltISA.writeDst (JoltISA.Dst.vreg JoltISA.systemScratchVReg) nextPC
        { js with sail := setNextPCState js.sail target } =
      .ok ()
        { js with
          sail := setNextPCState js.sail target,
          vregs := fun r =>
            if r = JoltISA.systemScratchVReg then nextPC else js.vregs r } := by
  unfold JoltISA.writeDst
  exact writeVReg_run_of_writable JoltISA.systemScratchVReg nextPC
    { js with sail := setNextPCState js.sail target }
    (by
      unfold JoltISA.systemScratchVReg JoltISA.inlineTmp0 JoltISA.inlineTmp
        WritableVReg JoltISA.inlineRegisterBase JoltISA.riscvRegisterBase
        JoltISA.riscvRegisterCount JoltISA.numReservedVirtualRegisters
      decide)

/-- The Jolt-side MRET expansion runs through its JALR row and terminates with
`RETIRE_SUCCESS`. -/
private theorem mretProgram_jolt_run
    (js : SailJoltState) (nextPC : BitVec 64)
    (hNextPCReadable :
      js.sail.regs.get? Register.nextPC =
        some (nextPC : RegisterType Register.nextPC)) :
    (JoltISA.execProgram JoltISA.mretProgram).run js =
      .ok RETIRE_SUCCESS
        { js with
          sail := setNextPCState js.sail
            (BitVec.update
              (js.vregs JoltISA.mepcVReg + sign_extend (m := 64) (0 : BitVec 12))
              0 0#1),
          vregs := fun r =>
            if r = JoltISA.systemScratchVReg then nextPC else js.vregs r } := by
  simp only [EStateM.run, JoltISA.execProgram, JoltISA.mretProgram,
    JoltISA.execInstr, bind, EStateM.bind]
  -- Read sail register next_pc successfully (use assumptions that it's readable)
  have hGetNextPC : liftSail (Sail.readReg Register.nextPC) js = .ok nextPC js := by
    unfold liftSail
    rw [readReg_eq_of_get? Register.nextPC js.sail nextPC hNextPCReadable]
  simp only [hGetNextPC]
  -- Read virtual register mepc
  have hReadMepc : JoltISA.readSrc (JoltISA.Src.vreg JoltISA.mepcVReg) js =
        .ok (js.vregs JoltISA.mepcVReg) js := by
    simp only [JoltISA.readSrc_vreg, readVReg_run]
  simp only [hReadMepc, jolt_jalr_target64, JoltISA.addWide_low]
  -- Rust's JALR writes its target directly to cpu.pc, represented by nextPC.
  have hWriteNextPC :
      liftSail (Sail.writeReg Register.nextPC
        (BitVec.update
          (js.vregs JoltISA.mepcVReg + sign_extend (m := 64) (0 : BitVec 12))
          0 0#1)) js =
      .ok () { js with
        sail := setNextPCState js.sail
          (BitVec.update
            (js.vregs JoltISA.mepcVReg + sign_extend (m := 64) (0 : BitVec 12))
            0 0#1) } := by
    rfl
  simp only [hWriteNextPC]
  -- Write to DST scratchVreg succeeds the contents of NextPC
  have hWriteScratch :=
    writeDst_systemScratchVReg_run js nextPC
      (BitVec.update
        (js.vregs JoltISA.mepcVReg + sign_extend (m := 64) (0 : BitVec 12))
        0 0#1)
  simp only [hWriteScratch, pure, EStateM.pure, RETIRE_SUCCESS]

/-- MRET's final local scratch write does not affect `systemProject`; only the
embedded Sail `nextPC` write is projected. -/
private theorem systemProject_mretJoltFinal
    (js : SailJoltState) (nextPC target : BitVec 64) :
    systemProject
        { js with
          sail := setNextPCState js.sail target,
          vregs := fun r =>
            if r = JoltISA.systemScratchVReg then nextPC else js.vregs r } =
      { systemProject js with
        regs := (systemProject js).regs.insert Register.nextPC target } := by
  have hMtvec : JoltISA.trapHandlerVReg ≠ JoltISA.systemScratchVReg := by
    decide
  have hMscratch : JoltISA.mscratchVReg ≠ JoltISA.systemScratchVReg := by
    decide
  have hMepc : JoltISA.mepcVReg ≠ JoltISA.systemScratchVReg := by
    decide
  have hMcause : JoltISA.mcauseVReg ≠ JoltISA.systemScratchVReg := by
    decide
  have hMtval : JoltISA.mtvalVReg ≠ JoltISA.systemScratchVReg := by
    decide
  have hMstatus : JoltISA.mstatusVReg ≠ JoltISA.systemScratchVReg := by
    decide
  have hScratchIgnored :
      systemProject
          { js with
            sail := setNextPCState js.sail target,
            vregs := fun r =>
              if r = JoltISA.systemScratchVReg then nextPC else js.vregs r } =
        systemProject { js with sail := setNextPCState js.sail target } := by
    unfold systemProject
    simp only [hMtvec, hMscratch, hMepc, hMcause, hMtval, hMstatus,
      if_false]
  rw [hScratchIgnored]
  exact systemProject_setNextPCState js target

/-- MRET equivalence statement.

Generated Sail's `execute_MRET` performs the trap-return postlude internally by
calling `exception_handler` for `CTL_MRET` and then `set_next_pc`. -/
def mretProgramEqSailStatement
    (js : SailJoltState) (_h : MretProgramEqSailAssumptions js) : Prop :=
  systemProjectResult
      ((JoltISA.execProgram JoltISA.mretProgram).run js) =
    (execute_MRET ()).run (systemProject js)

theorem mretProgram_eq_sail_projected
    (js : SailJoltState) (h : MretProgramEqSailAssumptions js) :
    mretProgramEqSailStatement js h := by
  unfold mretProgramEqSailStatement
  obtain ⟨nextPC, hNextPCReadable⟩ := h.nextPC_readable.exists_value
  rw [mretProgram_jolt_run js nextPC hNextPCReadable]
  simp only [EStateM.run, execute_MRET, bind, EStateM.bind]
  -- First step read reg curr privilege issucceeds 
  have hCurPrivilegeProject :
      (systemProject js).regs.get? Register.cur_privilege =
        some (Privilege.Machine : RegisterType Register.cur_privilege) := by
    exact systemProject_cur_privilege_read js h.cur_privilege_machine.value
  simp only [readReg_eq_of_get? Register.cur_privilege (systemProject js)
    Privilege.Machine hCurPrivilegeProject]
  -- Second setep tat it's machine so else the lese block. 
  have hMachineNeFalse :
      (!instBEqPrivilege.beq Privilege.Machine Privilege.Machine) = false := by
    decide
  simp only [bne, BEq.beq, hMachineNeFalse, ext_check_xret_priv,
    LeanRV64D.Functions.not, Bool.false_eq_true, if_false]
  -- Read current privilege again inside the MRET trap-return postlude.
  simp only [Bool.not_true, Bool.false_eq_true, if_false]
  simp only [EStateM.bind, readReg_eq_of_get? Register.cur_privilege
    (systemProject js) Privilege.Machine hCurPrivilegeProject]
  -- Read PC successfully before entering the MRET exception handler.
  obtain ⟨pc, hPCReadable⟩ := h.pc_readable.exists_value
  have hPCProject :
      (systemProject js).regs.get? Register.PC =
        some (pc : RegisterType Register.PC) := by
    exact systemProject_pc_read js pc hPCReadable
  simp only [readReg_eq_of_get? Register.PC (systemProject js) pc hPCProject]
  -- TODO: prove the real generated-Sail MRET postlude state, or weaken this
  -- statement so it does not require Sail's architectural `mstatus` updates to
  -- equal Jolt's restricted `pc := mepc` model.
  unfold exception_handler
  sorry 
end System

end
