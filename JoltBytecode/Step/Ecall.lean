import JoltBytecode.InstructionEquivalence.Instructions.System.Csr

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail
open LeanRV64D LeanRV64D.Functions

noncomputable section

namespace SystemProofs

/-- The state written by Jolt's ECALL rows before the step tail.
For example, an ECALL at address 16 saves 16 in v36 and exception code 11 in v37. -/
def ecallPost (js : SailJoltState) (pc next : BitVec 64) : SailJoltState :=
  { js with
    sail := System.setNextPCState js.sail
      (jolt_jalr_target64 (js.vregs JoltISA.trapHandlerVReg) 0#64)
    vregs := fun r =>
      if r = JoltISA.inlineTmp0 then next
      else if r = JoltISA.mstatusVReg then (js.vregs JoltISA.mstatusVReg &&& 8#64) * 16#64
      else if r = JoltISA.mtvalVReg then 0#64
      else if r = JoltISA.mcauseVReg then 11#64
      else if r = JoltISA.mepcVReg then pc
      else js.vregs r }

/-- Jolt's ECALL program saves the current address, writes the machine trap
CSRs and jumps to the trap vector.
For example, the fall-through address is retained only in scratch v40. -/
theorem ecallProgram_run (js : SailJoltState) (pc next : BitVec 64)
    (hpc : js.sail.regs.get? Register.PC = some pc)
    (hn : js.sail.regs.get? Register.nextPC = some next) :
    JoltISA.execProgram JoltISA.ecallProgram js = .ok RETIRE_SUCCESS (ecallPost js pc next) := by
  have hz (s : SailState) : rX_bits zreg s = .ok 0#64 s := rX_bits_regidx_zero s
  simp (config := { contextual := true }) [ecallPost, JoltISA.ecallProgram,
    JoltISA.execProgram, JoltISA.execInstr, JoltISA.readSrc, JoltISA.writeDst,
    readVReg, writeVReg, liftSail, get_arch_pc,
    readReg_eq_of_get? _ _ _ hpc, readReg_eq_of_get? _ _ _ hn,
    hz, JoltISA.addWide_low, Riscv.andi, jolt_virtual_muli_value,
    RETIRE_SUCCESS, bind, EStateM.bind, pure, EStateM.pure,
    get, getThe, MonadStateOf.get, EStateM.get, modify, modifyGet,
    MonadStateOf.modifyGet, EStateM.modifyGet, Step.writeReg_run, Step.setReg,
    System.setNextPCState, JoltISA.mstatusVReg, JoltISA.mepcVReg,
    JoltISA.mcauseVReg, JoltISA.mtvalVReg, JoltISA.inlineTmp0,
    JoltISA.trapHandlerVReg, JoltISA.riscvRegisterBase, JoltISA.riscvRegisterCount,
    JoltISA.inlineTmp, JoltISA.inlineRegisterBase, JoltISA.numReservedVirtualRegisters]
  rfl

/-- ECALL's raw mstatus update is Sail's trap-entry privilege-stack update.
For example, raw MIE = 8 produces architectural mstatus `0x1880`. -/
theorem ecall_mstatus (raw : BitVec 64) (hm : raw &&& ~~~(0x88#64) = 0#64) :
    (raw &&& 8#64) * 16#64 ||| 0x1800#64 = Step.trapMstatus (raw ||| 0x1800#64) := by
  have hmask : raw &&& 0x88#64 = raw := by
    simpa using BitVec.and_not_eq_self_of_and_eq_zero raw (~~~(0x88#64)) hm
  rw [← hmask]
  simp [Step.trapMstatus, BitVec.and_or_distrib_right, BitVec.and_assoc,
    shiftLeft_eq_mul_pow2]

/-- Projecting the ECALL program's result gives Sail's handled trap state,
including its next address.
For example, direct and vectored mtvec values `0x100` and `0x101` both select `0x100`. -/
theorem systemProject_ecallPost (js : SailJoltState) (pc next : BitVec 64)
    (hm : js.vregs JoltISA.mstatusVReg &&& ~~~(0x88#64) = 0#64)
    (ht : (js.vregs JoltISA.trapHandlerVReg).getLsbD 1 = false) :
    System.systemProject (ecallPost js pc next) =
      Step.setReg (Step.ecallState (System.systemProject js)
        (js.vregs JoltISA.mstatusVReg ||| 0x1800#64) pc) Register.nextPC
        (js.vregs JoltISA.trapHandlerVReg &&& ~~~(3#64)) := by
  have htarget : jolt_jalr_target64 (js.vregs JoltISA.trapHandlerVReg) 0#64 =
      js.vregs JoltISA.trapHandlerVReg &&& ~~~(3#64) := by
    rw [jalr_zero_target]
    have hclear := clearSingleBit_self (js.vregs JoltISA.trapHandlerVReg) 1 ht
    change js.vregs JoltISA.trapHandlerVReg &&& ~~~(2#64) = _ at hclear
    rw [show 3#64 = 2#64 ||| 1#64 from rfl, BitVec.not_or,
      ← BitVec.and_assoc, hclear]
  have ht' : jolt_jalr_target64 (js.vregs 34#7) 0#64 =
      js.vregs 34#7 &&& ~~~(3#64) := htarget
  have hm' : (js.vregs 39#7 &&& 8#64) * 16#64 ||| 0x1800#64 =
      Step.trapMstatus (js.vregs 39#7 ||| 0x1800#64) := ecall_mstatus _ hm
  simp [ecallPost, System.systemProject, Step.ecallState, Step.setReg,
    System.setNextPCState, ht', hm',
    JoltISA.mstatusVReg, JoltISA.trapHandlerVReg, JoltISA.mscratchVReg,
    JoltISA.mepcVReg, JoltISA.mcauseVReg, JoltISA.mtvalVReg,
    JoltISA.reservationWReg, JoltISA.reservationDReg, JoltISA.inlineTmp0,
    JoltISA.riscvRegisterBase, JoltISA.riscvRegisterCount, JoltISA.inlineTmp,
    JoltISA.inlineRegisterBase, JoltISA.numReservedVirtualRegisters,
    System.extDHashMap_insert_insert_same, System.extDHashMap_insert_comm_of_ne]

end SystemProofs

namespace Step

/-- A Jolt ECALL step uses the ordinary four-byte prelude, runs its trap-entry
rows and finishes without retiring.
For example, it preserves minstret even when instruction counting is enabled. -/
def joltEcallStep : JoltMonad Bool := do
  liftSail (stepPrelude 4)
  let _ ← JoltISA.execProgram JoltISA.ecallProgram
  liftSail trapFinish

/-- The non-retiring trap tail reads and writes no projected system register.
For example, advancing PC commutes with projecting the saved mepc. -/
theorem overlayLocal_trapFinish : OverlayLocal trapFinish := by
  unfold trapFinish
  refine OverlayLocal.bind (OverlayLocal.readReg (by simp [Overlaid])) fun h => ?_
  cases h with
  | HART_WAITING _ => exact OverlayLocal.pure _
  | HART_ACTIVE u =>
    cases u
    unfold tick_pc
    overlay_local

end Step

namespace RiscvInstruction

/-- A four-byte ECALL fetch on Jolt's active Machine-mode hart agrees with
Sail's complete trap step.
The hypotheses `hm` (only MIE/MPIE in raw mstatus) and `ht` (mtvec mode 0 or 1)
are the persistent CSR invariants;
for example, mtvec `0x101` enters the handler at `0x100` without retiring ECALL. -/
theorem joltStep_eq_try_step_ecall (n : Nat) (js : SailJoltState)
    (hinv : Step.StepInvariant (System.systemProject js))
    (inc : Bool) (hinc : should_inc_minstret Privilege.Machine js.sail = .ok inc js.sail)
    (pc : BitVec 64) (hpc : js.sail.regs.get? Register.PC = some pc)
    (w : BitVec 32)
    (hfetch : fetch () (Step.setReg (System.systemProject js) Register.minstret_increment inc) =
      .ok (.F_Base w) (Step.setReg (System.systemProject js) Register.minstret_increment inc))
    (hdec : ext_decode w (Step.setReg (System.systemProject js) Register.minstret_increment inc) =
      .ok (.ECALL ()) (Step.setReg (System.systemProject js) Register.minstret_increment inc))
    (hm : js.vregs JoltISA.mstatusVReg &&& ~~~(0x88#64) = 0#64)
    (ht : (js.vregs JoltISA.trapHandlerVReg).getLsbD 1 = false) :
    System.systemProjectResult (Step.joltEcallStep js) =
      try_step n false (System.systemProject js) := by
  have hpcp : (System.systemProject js).regs.get? Register.PC = some pc := by
    rw [Step.systemProject_get?_of_not_overlaid js (by simp [Step.Overlaid])]
    exact hpc
  rw [Step.try_step_base n _ hinv inc (Step.should_inc_minstret_systemProject js inc hinc)
    pc hpcp w (.ECALL ()) hfetch hdec]
  let jp := Step.preludeJolt js inc pc 4
  have hp : liftSail (Step.stepPrelude 4) js = .ok () jp := by
    unfold liftSail jp Step.preludeJolt
    rw [Step.stepPrelude_run 4 js.sail inc hinc pc hpc]
  have hi : Step.StepInvariant (System.systemProject jp) := by
    rw [Step.systemProject_preludeJolt]
    exact (hinv.setReg Register.minstret_increment inc (by simp [Step.invariantReg])).setReg
      Register.nextPC _ (by simp [Step.invariantReg])
  have hpcj : jp.sail.regs.get? Register.PC = some pc := by
    simpa [jp, Step.preludeJolt, Step.preludeState, Step.setReg_get?_ne] using hpc
  have hpcjp : (System.systemProject jp).regs.get? Register.PC = some pc := by
    rw [Step.systemProject_get?_of_not_overlaid jp (by simp [Step.Overlaid])]
    exact hpcj
  have hn : jp.sail.regs.get? Register.nextPC = some (BitVec.addInt pc 4) := by
    simp [jp, Step.preludeJolt, Step.preludeState, Step.setReg]
  rw [← Step.systemProject_preludeJolt]
  change System.systemProjectResult (Step.joltEcallStep js) =
    Step.executeAndFinish (.ECALL ()) _ (System.systemProject jp)
  unfold Step.executeAndFinish Step.executeFull
  simp only [bind, EStateM.bind, Step.execute_ECALL_machine _ hi pc hpcjp,
    pure, EStateM.pure]
  rw [Step.stepFinish_trap]
  have hs := Step.exception_handler_ecall (System.systemProject jp) hi
    (jp.vregs JoltISA.mstatusVReg ||| 0x1800#64) (jp.vregs JoltISA.trapHandlerVReg) pc
    (by simp [System.systemProject, Std.ExtDHashMap.get?_insert])
    (by simp [System.systemProject, Std.ExtDHashMap.get?_insert]) ht
  unfold Step.joltEcallStep
  simp only [bind, EStateM.bind, hp]
  rw [SystemProofs.ecallProgram_run jp pc _ hpcj hn]
  simp only [bind, EStateM.bind, hs, set_next_pc, Step.writeReg_run]
  have hproj := Step.overlayLocal_trapFinish.run (SystemProofs.ecallPost jp pc (BitVec.addInt pc 4))
  rw [SystemProofs.systemProject_ecallPost jp pc _ hm ht] at hproj
  exact hproj

end RiscvInstruction
