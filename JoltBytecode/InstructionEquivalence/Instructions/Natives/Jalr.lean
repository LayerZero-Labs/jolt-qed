import JoltBytecode.Bundles
import JoltBytecode.InstructionEquivalence.ProofSupport.NativeDispatch

open Sail PreSail LeanRV64D.Functions

noncomputable section

namespace Natives

/-- Full native JALR execution, including the temporary write when rd is x0.
The target uses the original rs1 value even when rd and rs1 are equal. -/
theorem jalrNative_run (imm : BitVec 12) (rs1 rd : regidx) (js : SailJoltState)
    (rustPC baseValue : BitVec 64)
    (hNextPC : js.sail.regs.get? Register.nextPC = some rustPC)
    (hBase : rX_bits rs1 js.sail = .ok baseValue js.sail) :
    (JoltISA.execInstr (JoltISA.jalrNativeInstr rd rs1 imm)).run js =
      .ok RETIRE_SUCCESS
        (NativeDispatch.afterDst
          { js with
            sail := System.setNextPCState js.sail
              (BitVec.update (baseValue + sign_extend (m := 64) imm) 0 0#1) }
          rd rustPC) := by
  unfold JoltISA.jalrNativeInstr
  simp only [EStateM.run, JoltISA.execInstr]
  -- Save Rust's old cpu.pc before reading rs1 or writing either destination.
  have hReadRustPC : liftSail (Sail.readReg Register.nextPC) js = .ok rustPC js := by
    unfold liftSail
    rw [readReg_eq_of_get? Register.nextPC js.sail rustPC hNextPC]
  have hReadBase : JoltISA.readSrc (.xreg rs1) js = .ok baseValue js := by
    simp only [JoltISA.readSrc, liftSail, hBase]
  simp only [bind, EStateM.bind, hReadRustPC, hReadBase,
    jolt_jalr_target64, JoltISA.addWide_low]
  -- Rust first updates cpu.pc, then writes the saved value to the destination.
  have hWritePC :
      liftSail (Sail.writeReg Register.nextPC
        (BitVec.update (baseValue + sign_extend (m := 64) imm) 0 0#1)) js =
      .ok () { js with
        sail := System.setNextPCState js.sail
          (BitVec.update (baseValue + sign_extend (m := 64) imm) 0 0#1) } := by
    rfl
  simp only [hWritePC, NativeDispatch.writeDst_run, pure, EStateM.pure]

/-- Native source JALR equivalence, including Rust's destination-zero dispatch. -/
def jalrInstrEqSailStatement
    (imm : BitVec 12) (rs1 rd : regidx) (js : SailJoltState)
    (_h : JalrInstrEqSailAssumptions imm rs1 js) : Prop :=
  System.systemProjectResult
    ((JoltISA.execInstr (JoltISA.jalrNativeInstr rd rs1 imm)).run js) =
    ((execute_JALR imm rs1 rd).run js.sail)

theorem jalrInstr_eq_sail
    (imm : BitVec 12) (rs1 rd : regidx) (js : SailJoltState)
    (h : JalrInstrEqSailAssumptions imm rs1 js) :
    jalrInstrEqSailStatement imm rs1 rd js h := by
  unfold jalrInstrEqSailStatement
  obtain ⟨rustPC, hNextPC⟩ := h.nextPC_readable.exists_value
  -- Establish Rust's full state update before applying the Sail projection.
  rw [jalrNative_run imm rs1 rd js rustPC h.rs1_val hNextPC h.rs1_read]
  -- The disabled Zicfilp hook leaves the Sail state unchanged.
  have hUpdate : update_elp_state rs1 js.sail = .ok () js.sail := by
    simp only [update_elp_state, h.zicfilp_disabled.value, bind, EStateM.bind,
      Bool.false_eq_true, if_false, pure, EStateM.pure]
  -- The bundle guarantees that Sail accepts Rust's bit-0-cleared target.
  simp only [execute_JALR, EStateM.run, bind, EStateM.bind, hUpdate, get_next_pc,
    readReg_eq_of_get? Register.nextPC js.sail rustPC hNextPC, h.rs1_read,
    pure, EStateM.pure, Projection.jump_to_of_aligned _ _ h.target_aligned,
    RETIRE_SUCCESS, wX_bits_stateAfterWrite]
  -- Projection retains nextPC and the architectural destination write.
  simp only [System.systemProjectResult, NativeDispatch.systemProject_afterDst,
    System.systemProject_setNextPCState,
    Projection.systemProject_eq_sail_of_compatible js h.linkedCSRs]
  rfl

end Natives

end
