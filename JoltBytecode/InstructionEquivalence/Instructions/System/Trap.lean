import JoltBytecode.JoltISA.Expansions.System
import JoltBytecode.InstructionEquivalence.ProofSupport.Projection
import JoltBytecode.Step.SailTrap
import JoltBytecode.Step.Lift
import JoltBytecode.InstructionEquivalence.ProofSupport.BitVecMasks

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail
open LeanRV64D LeanRV64D.Functions

noncomputable section

namespace SystemProofs

/-- MRET shifts MPIE into MIE, sets MPIE, and jumps to the saved exception PC.
The old fall-through PC is saved in scratch v40; for example, a saved PC of
16 makes the new `nextPC` equal to 16. -/
theorem mretProgram_run (js : SailJoltState) (next : BitVec 64)
    (hn : js.sail.regs.get? Register.nextPC = some next) :
    JoltISA.execProgram JoltISA.mretProgram js =
      .ok RETIRE_SUCCESS
        { js with
          sail := System.setNextPCState js.sail
            (jolt_jalr_target64 (js.vregs JoltISA.mepcVReg) 0#64)
          vregs := fun r =>
            if r = JoltISA.inlineTmp0 then next
            else if r = JoltISA.mstatusVReg then
              (js.vregs JoltISA.mstatusVReg >>> 4) ||| 0x80#64
            else js.vregs r } := by
  simp (config := { contextual := true }) [RETIRE_SUCCESS, JoltISA.mretProgram, JoltISA.execProgram, JoltISA.execInstr,
    JoltISA.readSrc, readVReg, JoltISA.writeDst, writeVReg,
    JoltISA.mstatusVReg, JoltISA.mepcVReg, JoltISA.inlineTmp0,
    JoltISA.srliBitmask, jolt_virtual_srli_value, ctz,
    Riscv.ori, liftSail, readReg_eq_of_get? _ _ _ hn,
    bind, EStateM.bind, pure, EStateM.pure, get, getThe, MonadStateOf.get,
    EStateM.get, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet,
    Step.writeReg_run, Step.setReg, System.setNextPCState,
    JoltISA.riscvRegisterBase, JoltISA.riscvRegisterCount, JoltISA.inlineTmp,
    JoltISA.inlineRegisterBase, JoltISA.numReservedVirtualRegisters]
  rfl

/-- Under Jolt's two-bit mstatus invariant, its MRET shift is Sail's privilege
stack update.
For example, raw MPIE = 128 produces architectural mstatus `0x1888`. -/
theorem mretMstatus_eq (m : BitVec 64) (hm : m &&& ~~~(0x88#64) = 0#64) :
    ((m >>> 4) ||| 0x80#64) ||| 0x1800#64 = Step.mretMstatus (m ||| 0x1800#64) := by
  have hmasked : m &&& 0x88#64 = m := by
    simpa using BitVec.and_not_eq_self_of_and_eq_zero m (~~~(0x88#64)) hm
  conv_lhs => rw [← hmasked]
  conv_rhs => rw [← hmasked]
  simp [Step.mretMstatus, BitVec.and_or_distrib_right, BitVec.and_assoc,
    BitVec.ushiftRight_and_distrib]

/-- The fixed read-only bits in a projected mstatus always encode Machine MPP.
For example, a raw value of zero projects to mstatus `0x1800`. -/
theorem mstatus_mpp_machine (raw : BitVec 64) :
    (raw ||| 0x1800#64) &&& 0x1800#64 = 0x1800#64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_or]
  cases raw.getLsbD i <;> cases (0x1800#64).getLsbD i <;> rfl

/-- A zero-offset JALR clears bit zero of its target.
For example, target 17 becomes 16. -/
theorem jalr_zero_target (v : BitVec 64) :
    jolt_jalr_target64 v 0#64 = v &&& ~~~(1#64) := by
  simp only [jolt_jalr_target64, JoltISA.addWide_low, BitVec.add_zero]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases hz : i = 0
  · subst i
    simp [Sail.BitVec.update, Sail.BitVec.updateSubrange']
  · simp [Sail.BitVec.update, Sail.BitVec.updateSubrange', hi, hz, Bool.and_comm]

/-- Jolt's MRET program projects to Sail's MRET state update.
The hart invariant supplies M-mode and its configuration registers, while
legal virtual registers supply the mstatus mask and aligned mepc.
For example, a saved mepc of 16 becomes the next instruction address. -/
theorem mretProgram_eq_execute (js : SailJoltState)
    (hinv : Step.StepInvariant (System.systemProject js))
    (hstatus : js.vregs JoltISA.mstatusVReg &&& ~~~(0x88#64) = 0#64)
    (hepc : (js.vregs JoltISA.mepcVReg).getLsbD 0 = false) :
    System.systemProjectResult (JoltISA.execProgram JoltISA.mretProgram js) =
      execute (.MRET ()) (System.systemProject js) := by
  obtain ⟨next, hn⟩ := (hinv.present Register.nextPC).exists_value
  rw [Step.systemProject_get?_of_not_overlaid js (by simp [Step.Overlaid])] at hn
  have hm : (System.systemProject js).regs.get? Register.mstatus =
      some (js.vregs JoltISA.mstatusVReg ||| 0x1800#64) := by
    simp [System.systemProject, Std.ExtDHashMap.get?_insert]
  have he : (System.systemProject js).regs.get? Register.mepc =
      some (js.vregs JoltISA.mepcVReg) := by
    simp [System.systemProject, Std.ExtDHashMap.get?_insert]
  have hpp := mstatus_mpp_machine (js.vregs JoltISA.mstatusVReg)
  rw [Step.execute_MRET_machine _ hinv _ _ hm he hepc hpp,
    mretProgram_run js next hn]
  have ht : jolt_jalr_target64 (js.vregs JoltISA.mepcVReg) 0#64 = js.vregs JoltISA.mepcVReg := by
    rw [jalr_zero_target]
    apply BitVec.and_not_eq_self_of_and_eq_zero
    rw [BitVec.and_one_eq_setWidth_ofBool_getLsbD, hepc]
    rfl
  simp only [System.systemProjectResult]
  rw [ht]
  rw [← mretMstatus_eq _ hstatus]
  simp [System.systemProject,
    Step.setReg, System.setNextPCState,
    JoltISA.mstatusVReg, JoltISA.trapHandlerVReg, JoltISA.mscratchVReg,
    JoltISA.mepcVReg, JoltISA.mcauseVReg, JoltISA.mtvalVReg,
    JoltISA.reservationWReg, JoltISA.reservationDReg, JoltISA.inlineTmp0,
    JoltISA.riscvRegisterBase, JoltISA.riscvRegisterCount, JoltISA.inlineTmp,
    JoltISA.inlineRegisterBase, JoltISA.numReservedVirtualRegisters,
    System.extDHashMap_insert_insert_same, System.extDHashMap_insert_comm_of_ne]

end SystemProofs
