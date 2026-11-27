import JoltBytecode.Bundles
import JoltBytecode.InstructionEquivalence.Instructions.System.Common
import JoltBytecode.InstructionEquivalence.ProofSupport.SailTrap
import JoltBytecode.InstructionEquivalence.ProofSupport.BitVecMasks
import JoltBytecode.InstructionEquivalence.ProofSupport.ValueLemmas
import JoltBytecode.JoltISA.ExpansionsAutomated
import JoltBytecode.JoltISA.Semantics
import JoltBytecode.JoltISA.SystemProjection

open Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Functions

noncomputable section

namespace System

/-- Sail's ECALL followed by its trap entry.
`execute_ECALL` only returns `Trap`; Sail's step function `try_step` then runs
`set_next_pc (← exception_handler priv ctl pc)` (`LeanRV64D/Step.lean`, the `.Trap` branch).
For example, at PC 16 with mtvec `0x101`, mepc becomes 16, mcause 11, and nextPC `0x100`.
The last branch never runs, because `execute_ECALL` always returns `Trap`. -/
def sailEcall : SailM Unit := do
  match ← execute_ECALL () with
  | .Trap (priv, ctl, pc) => set_next_pc (← exception_handler priv ctl pc)
  | _ => pure ()

/-- ECALL equivalence statement.

Jolt's ECALL rows, projected to Sail's state, end in the same state as `sailEcall`.
Only states are compared: Jolt's rows end in `RETIRE_SUCCESS`, while Sail's
`execute_ECALL` returns `Trap`.
Jolt: `crates/jolt-program/src/expand/control_flow/ecall.rs` (`expand_ecall`) at `504dd78a2`. -/
def ecallProgramEqSailStatement
    (js : SailJoltState) (_h : EcallProgramEqSailAssumptions js) : Prop :=
  --  a *> b is a >>= fun _ => b (new lean notation that AI picked out)
  systemProjectResult ((JoltISA.execProgram JoltISA.ecallProgramAuto *> pure ()).run js) =
    sailEcall.run (systemProject js)

/-- Jolt's ECALL rows save the current address in v36, write exception code 11
to v37 and zero to v38, move MIE to MPIE in v39, and jump to mtvec (v34).
The old fall-through address is kept only in scratch v40; for example, an ECALL
at address 16 leaves 16 in v36.
Based on Quang Dao's `ecallProgram_run` in PR #73. -/
theorem ecallProgram_run (js : SailJoltState) (pc next : BitVec 64)
    (hpc : js.sail.regs.get? Register.PC = some pc)
    (hn : js.sail.regs.get? Register.nextPC = some next) :
    JoltISA.execProgram JoltISA.ecallProgramAuto js =
      .ok RETIRE_SUCCESS
        { js with
          sail := setNextPCState js.sail
            (jolt_jalr_target64 (js.vregs JoltISA.trapHandlerVReg) 0#64)
          vregs := fun r =>
            if r = JoltISA.inlineTmp0 then next
            else if r = JoltISA.mstatusVReg then (js.vregs JoltISA.mstatusVReg &&& 8#64) * 16#64
            else if r = JoltISA.mtvalVReg then 0#64
            else if r = JoltISA.mcauseVReg then 11#64
            else if r = JoltISA.mepcVReg then pc
            else js.vregs r } := by
  have h0 : sign_extend (m := 64) (0#12) = 0#64 := by decide
  have h8 : sign_extend (m := 64) (8#12) = 8#64 := by decide
  have h11 : sign_extend (m := 64) (11#12) = 11#64 := by decide
  have hz' (s : SailState) : rX_bits (regidx.Regidx (0#5)) s = .ok 0#64 s := rX_bits_regidx_zero s
  simp (config := { contextual := true }) [h0, h8, h11, hz', JoltISA.slliMultiplier, RETIRE_SUCCESS,
    JoltISA.ecallProgramAuto, JoltISA.execProgram, JoltISA.execInstr,
    JoltISA.readSrc, readVReg, JoltISA.writeDst, writeVReg, liftSail, get_arch_pc,
    readReg_eq_of_get? _ _ _ hpc, readReg_eq_of_get? _ _ _ hn,
    JoltISA.addWide_low, Riscv.andi, jolt_virtual_muli_value,
    bind, EStateM.bind, pure, EStateM.pure, get, getThe, MonadStateOf.get,
    EStateM.get, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet,
    Step.writeReg_run, Step.setReg, setNextPCState,
    JoltISA.mstatusVReg, JoltISA.mepcVReg, JoltISA.mcauseVReg, JoltISA.mtvalVReg,
    JoltISA.inlineTmp0, JoltISA.trapHandlerVReg,
    JoltISA.riscvRegisterBase, JoltISA.riscvRegisterCount, JoltISA.inlineTmp,
    JoltISA.inlineRegisterBase, JoltISA.numReservedVirtualRegisters]
  rfl

/-- When v39 holds only MIE and MPIE, Jolt's ECALL mstatus update is Sail's
trap-entry privilege-stack update.
For example, v39 = 8 (MIE set) produces architectural mstatus `0x1880`.
Based on Quang Dao's `ecall_mstatus` in PR #73. -/
theorem ecall_mstatus (raw : BitVec 64) (hm : raw &&& ~~~(0x88#64) = 0#64) :
    (raw &&& 8#64) * 16#64 ||| 0x1800#64 = Step.trapMstatus (raw ||| 0x1800#64) := by
  have hmask : raw &&& 0x88#64 = raw := by
    simpa using BitVec.and_not_eq_self_of_and_eq_zero raw (~~~(0x88#64)) hm
  rw [← hmask]
  simp [Step.trapMstatus, BitVec.and_or_distrib_right, BitVec.and_assoc,
    shiftLeft_eq_mul_pow2]

/-- With bit 1 of mtvec clear, Jolt's zero-offset JALR through mtvec lands
where Sail's trap entry does, at mtvec with its two low bits cleared.
For example, mtvec `0x101` gives `0x100` on both sides. -/
theorem ecall_target (t : BitVec 64) (ht1 : t.getLsbD 1 = false) :
    jolt_jalr_target64 t 0#64 = t &&& ~~~(3#64) := by
  rw [jalr_zero_target]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_ofNat, hi,
    decide_true, Bool.true_and]
  rcases (show i = 0 ∨ i = 1 ∨ 2 ≤ i from by omega) with rfl | rfl | h2
  · rfl
  · have h1 : t[1] = false := by simpa using ht1
    simp [h1]
  · have hp : 4 ≤ 2 ^ i := by
      calc 4 = 2 ^ 2 := rfl
        _ ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) h2
    rw [Nat.testBit_lt_two_pow (by omega : 1 < 2 ^ i),
      Nat.testBit_lt_two_pow (by omega : 3 < 2 ^ i)]

/-- Jolt's ECALL rows, projected, end where Sail's ECALL and trap entry end.
Based on Quang Dao's `joltStep_eq_try_step_ecall` in PR #73, which stated it
for the whole step. -/
theorem ecallProgram_eq_sail_projected
    (js : SailJoltState) (h : EcallProgramEqSailAssumptions js) :
    ecallProgramEqSailStatement js h := by
  unfold ecallProgramEqSailStatement
  obtain ⟨next, hn⟩ := h.nextPC_readable.exists_value
  obtain ⟨pc, hpc⟩ := h.pc_readable.exists_value
  obtain ⟨d, hd⟩ := h.medeleg_readable.exists_value
  have hpriv : (systemProject js).regs.get? Register.cur_privilege =
      some Privilege.Machine := by
    rw [systemProject_get?_of_not_overlaid js _ (by decide)]
    exact h.cur_privilege_machine.value
  have hpcp : (systemProject js).regs.get? Register.PC = some pc := by
    rw [systemProject_get?_of_not_overlaid js _ (by decide)]
    exact hpc
  have hdp : (systemProject js).regs.get? Register.medeleg = some d := by
    rw [systemProject_get?_of_not_overlaid js _ (by decide)]
    exact hd
  have hc : (systemProject js).regs.get? Register.mcause =
      some (js.vregs JoltISA.mcauseVReg) := by
    simp [systemProject, Std.ExtDHashMap.get?_insert]
  have hm : (systemProject js).regs.get? Register.mstatus =
      some (js.vregs JoltISA.mstatusVReg ||| 0x1800#64) := by
    simp [systemProject, Std.ExtDHashMap.get?_insert]
  have ht : (systemProject js).regs.get? Register.mtvec =
      some (js.vregs JoltISA.trapHandlerVReg) := by
    simp [systemProject, Std.ExtDHashMap.get?_insert]
  have hsail : sailEcall (systemProject js) =
      .ok () (Step.setReg
        (Step.ecallState (systemProject js) (js.vregs JoltISA.mstatusVReg ||| 0x1800#64) pc)
        Register.nextPC (js.vregs JoltISA.trapHandlerVReg &&& ~~~(3#64))) := by
    unfold sailEcall
    simp only [bind, EStateM.bind, Step.execute_ECALL_machine _ pc hpriv hpcp,
      Step.exception_handler_ecall _ d _ _ _ pc hpriv hdp hc hm ht h.mtvec_legal.mtvec_mode,
      set_next_pc, Step.writeReg_run, pure, EStateM.pure]
  simp only [EStateM.run, SeqRight.seqRight, EStateM.seqRight,
    ecallProgram_run js pc next hpc hn, hsail, systemProjectResult, pure, EStateM.pure,
    Step.ecallState]
  rw [ecall_target _ h.mtvec_legal.mtvec_mode,
    ← ecall_mstatus _ h.mstatus_legal.mstatus_bits]
  simp [systemProject, Step.setReg, setNextPCState,
    JoltISA.mstatusVReg, JoltISA.trapHandlerVReg, JoltISA.mscratchVReg,
    JoltISA.mepcVReg, JoltISA.mcauseVReg, JoltISA.mtvalVReg,
    JoltISA.reservationWReg, JoltISA.reservationDReg, JoltISA.inlineTmp0,
    JoltISA.riscvRegisterBase, JoltISA.riscvRegisterCount, JoltISA.inlineTmp,
    JoltISA.inlineRegisterBase, JoltISA.numReservedVirtualRegisters,
    extDHashMap_insert_insert_same, extDHashMap_insert_comm_of_ne]

end System
