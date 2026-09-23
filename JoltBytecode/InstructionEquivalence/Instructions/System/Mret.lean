import JoltBytecode.Bundles
import JoltBytecode.InstructionEquivalence.Instructions.System.Common

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace System

/-- MRET's lowered JALR immediate is zero. -/
private theorem mret_zero_imm (v : BitVec 64) :
    v + sign_extend (m := 64) (0 : BitVec 12) = v := by
  have hzero : sign_extend (m := 64) (0 : BitVec 12) = 0#64 := by
    decide
  rw [hzero]
  simp

/-- MRET's lowered JALR target clears bit 0. -/
private theorem mretReturnTarget_bit0_zero (v : BitVec 64) :
    BitVec.access (BitVec.update v 0 0#1) 0 = 0#1 := by
  unfold Sail.BitVec.access Sail.BitVec.update Sail.BitVec.updateSubrange'
  rw [getElem!_pos (h := by decide)]
  norm_num
  rfl

/-- If `align_pc` in the compressed-disabled branch leaves `mepc` unchanged,
then MRET's JALR-cleared target also passes the bit-1 alignment check. -/
private theorem mretReturnTarget_bit1_zero_of_align_pc_no_zca
    (v : BitVec 64)
    (h :
      Sail.BitVec.updateSubrange v 1 0
          (zeros (n := (1 -i (0 -i 1)))) = v) :
    bit_to_bool (BitVec.access (BitVec.update v 0 0#1) 1) = false := by
  rw [← h]
  unfold bit_to_bool bool_bit_backwards
  unfold Sail.BitVec.access Sail.BitVec.update Sail.BitVec.updateSubrange
    Sail.BitVec.updateSubrange' zeros
  simp

/-- In this generated model, `Ext_Zca` is enabled exactly when the `misa.C` bit
is set. -/
private theorem currentlyEnabled_Ext_Zca_run
    (s : SailState) (misa : BitVec 64)
    (hmisa : s.regs.get? Register.misa =
      some (misa : RegisterType Register.misa)) :
    currentlyEnabled extension.Ext_Zca s =
      .ok ((_get_Misa_C misa) == 1#1) s := by
  have hExtC := currentlyEnabled_Ext_C_run s misa hmisa
  unfold currentlyEnabled
  simp [hExtC, hartSupports, LeanRV64D.Functions.not,
    LeanRV64D.Functions.xlen, bind, EStateM.bind, pure, EStateM.pure]

/-- Running `set_next_pc` writes Sail `nextPC` to the corresponding concrete
state. -/
private theorem set_next_pc_run (s : SailState) (target : BitVec 64) :
    set_next_pc target s = .ok () (setNextPCState s target) := by
  unfold set_next_pc setNextPCState redirect_callback
  unfold Sail.writeReg PreSail.writeReg
  simp only [bind, EStateM.bind, pure, EStateM.pure, modify, modifyGet,
    MonadStateOf.modifyGet, EStateM.modifyGet]

/-- The successful `jump_to` path: control-check passes, bit 0 passes, no
compressed-disabled alignment fault, and Sail writes `nextPC`. -/
private theorem jump_to_success_run
    (s : SailState) (target : BitVec 64) (zca : Bool)
    (hZca : currentlyEnabled extension.Ext_Zca s = .ok zca s)
    (hbit0 : (BitVec.access target 0 == 0#1) = true)
    (hAlignOk :
      (bit_to_bool (BitVec.access target 1) &&
          LeanRV64D.Functions.not zca) = false) :
    jump_to target s = .ok RETIRE_SUCCESS (setNextPCState s target) := by
  unfold jump_to ext_control_check_pc SailME.run PreSail.PreSailME.run
  unfold set_next_pc setNextPCState redirect_callback
  unfold Sail.assert PreSail.assert Sail.writeReg PreSail.writeReg
  simp only [hbit0, hZca, hAlignOk, Bool.false_eq_true, if_true,
    if_false, bind, EStateM.bind, pure, EStateM.pure,
    ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont,
    ExceptT.pure, ExceptT.lift, MonadLift.monadLift, monadLift, liftM,
    EStateM.map, Functor.map, modify, modifyGet, MonadStateOf.modifyGet,
    EStateM.modifyGet]

/-- Jolt's MRET expansion jumps to the virtual `mepc` value, after the ordinary
JALR bit-0 clearing, and records that jump by writing Sail `nextPC`. -/
private theorem jump_to_mret_vreg_run
    (js : SailJoltState)
    (h : MretProgramEqSailAssumptions js) :
    liftSail
        (jump_to
          (BitVec.update
            (js.vregs JoltISA.mepcVReg + sign_extend (m := 64) (0 : BitVec 12))
            0 0#1)) js =
      .ok RETIRE_SUCCESS
        { js with
          sail := setNextPCState js.sail
            (BitVec.update
              (js.vregs JoltISA.mepcVReg + sign_extend (m := 64) (0 : BitVec 12))
              0 0#1) } := by
  obtain ⟨misa, hmisa⟩ := h.misa_readable.exists_value
  have hZca := currentlyEnabled_Ext_Zca_run js.sail misa hmisa
  have hAligned := h.mepc_read_aligned.value_eq
  rw [mret_zero_imm (js.vregs JoltISA.mepcVReg)]
  unfold align_pc at hAligned
  simp only [hZca, bind, EStateM.bind, pure] at hAligned
  have hbit0 :
      (BitVec.access (BitVec.update (js.vregs JoltISA.mepcVReg) 0 0#1) 0
          == 0#1) = true := by
    rw [mretReturnTarget_bit0_zero]
    decide
  have hAlignOk :
      (bit_to_bool
            (BitVec.access (BitVec.update (js.vregs JoltISA.mepcVReg) 0 0#1) 1) &&
          LeanRV64D.Functions.not ((_get_Misa_C misa) == 1#1)) =
        false := by
    by_cases hC : (_get_Misa_C misa == 1#1) = true
    · simp only [hC, LeanRV64D.Functions.not, Bool.not_true, Bool.and_false]
    · have hCFalse : (_get_Misa_C misa == 1#1) = false := by
        cases hCValue : (_get_Misa_C misa == 1#1)
        · rfl
        · exact False.elim (hC hCValue)
      have hAlignedNoZca :
          Sail.BitVec.updateSubrange (js.vregs JoltISA.mepcVReg) 1 0
              (zeros (n := (1 -i (0 -i 1)))) =
            js.vregs JoltISA.mepcVReg := by
        simpa [hCFalse, pure, EStateM.pure] using hAligned
      have hbit1 :=
        mretReturnTarget_bit1_zero_of_align_pc_no_zca
          (js.vregs JoltISA.mepcVReg) hAlignedNoZca
      simp only [hCFalse, LeanRV64D.Functions.not, Bool.not_false,
        hbit1, Bool.false_and]
  have hJump :=
    jump_to_success_run js.sail
      (BitVec.update (js.vregs JoltISA.mepcVReg) 0 0#1)
      ((_get_Misa_C misa) == 1#1) hZca hbit0 hAlignOk
  unfold liftSail
  simp only [hJump]

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
    (h : MretProgramEqSailAssumptions js)
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
  have hGetNextPC : liftSail (get_next_pc ()) js = .ok nextPC js := by
    unfold liftSail get_next_pc
    rw [readReg_eq_of_get? Register.nextPC js.sail nextPC hNextPCReadable]
  simp only [hGetNextPC]
  -- Read virtual register mepc
  have hReadMepc : JoltISA.readSrc (JoltISA.Src.vreg JoltISA.mepcVReg) js =
        .ok (js.vregs JoltISA.mepcVReg) js := by
    simp only [JoltISA.readSrc_vreg, readVReg_run]
  simp only [hReadMepc, jolt_jalr_target64, jolt_jalr_target, JoltISA.addWide_low]
  -- The next instruction is to jump_to mepc value roughly cos we are adding 0 and we want to show that succeeds.
  have hJump := jump_to_mret_vreg_run js h
  simp only [hJump]
  simp only [RETIRE_SUCCESS, EStateM.bind]
  -- Write to DST scratchVreg succeeds the contents of NextPC
  have hWriteScratch :=
    writeDst_systemScratchVReg_run js nextPC
      (BitVec.update
        (js.vregs JoltISA.mepcVReg + sign_extend (m := 64) (0 : BitVec 12))
        0 0#1)
  simp only [hWriteScratch, pure, EStateM.pure]

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
  rw [mretProgram_jolt_run js nextPC h hNextPCReadable]
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
