import JoltBytecode.Bundles
import JoltBytecode.InstructionEquivalence.ProofSupport.NativeDispatch

open Sail PreSail LeanRV64D.Functions

noncomputable section

namespace Natives

/-- Full native JAL execution, including the temporary write when rd is x0.
No target-alignment assumption is needed to execute Rust's instruction body. -/
theorem jalNative_run (imm : BitVec 21) (rd : regidx) (js : SailJoltState)
    (rustPC instructionAddress : BitVec 64)
    (hNextPC : js.sail.regs.get? Register.nextPC = some rustPC)
    (hPC : js.sail.regs.get? Register.PC = some instructionAddress) :
    (JoltISA.execInstr (JoltISA.jalNativeInstr rd imm)).run js =
      .ok RETIRE_SUCCESS
        (NativeDispatch.afterDst
          { js with
            sail := System.setNextPCState js.sail
              (instructionAddress + sign_extend (m := 64) imm) } rd rustPC) := by
  unfold JoltISA.jalNativeInstr
  simp only [EStateM.run, JoltISA.execInstr]
  -- nextPC represents Rust's already advanced cpu.pc.
  have hReadRustPC : liftSail (Sail.readReg Register.nextPC) js = .ok rustPC js := by
    unfold liftSail
    rw [readReg_eq_of_get? Register.nextPC js.sail rustPC hNextPC]
  -- PC represents self.address, the decoded instruction's address.
  have hReadAddress : liftSail (Sail.readReg Register.PC) js =
      .ok instructionAddress js := by
    unfold liftSail
    rw [readReg_eq_of_get? Register.PC js.sail instructionAddress hPC]
  simp only [bind, EStateM.bind, hReadRustPC, hReadAddress, NativeDispatch.writeDst_run]
  -- Rust writes the destination before updating cpu.pc.
  change (EStateM.Result.ok RETIRE_SUCCESS
    { NativeDispatch.afterDst js rd rustPC with
      sail := System.setNextPCState (NativeDispatch.afterDst js rd rustPC).sail
        (instructionAddress + sign_extend (m := 64) imm) } :
      EStateM.Result (Error exception) SailJoltState ExecutionResult) = _
  rw [NativeDispatch.afterDst_setNextPC]

/-- Native source JAL equivalence, including Rust's destination-zero dispatch. -/
def jalInstrEqSailStatement
    (imm : BitVec 21) (rd : regidx) (js : SailJoltState)
    (_h : JalInstrEqSailAssumptions imm js) : Prop :=
  System.systemProjectResult
    ((JoltISA.execInstr (JoltISA.jalNativeInstr rd imm)).run js) =
    ((execute_JAL imm rd).run js.sail)

theorem jalInstr_eq_sail
    (imm : BitVec 21) (rd : regidx) (js : SailJoltState)
    (h : JalInstrEqSailAssumptions imm js) :
    jalInstrEqSailStatement imm rd js h := by
  unfold jalInstrEqSailStatement
  obtain ⟨rustPC, hNextPC⟩ := h.nextPC_readable.exists_value
  obtain ⟨instructionAddress, hPC⟩ := h.pc_readable.exists_value
  -- First establish the full Jolt state, including the native destination write.
  rw [jalNative_run imm rd js rustPC instructionAddress hNextPC hPC]
  have hPCValue : h.pc_readable.exists_value.choose = instructionAddress :=
    Option.some.inj (h.pc_readable.exists_value.choose_spec.symm.trans hPC)
  have hTargetAligned : Assumptions.MepcReadAligned
      (instructionAddress + sign_extend (m := 64) imm) js.sail := by
    simpa only [hPCValue] using h.target_aligned
  -- Sail checks alignment before updating nextPC and writing rd.
  simp only [execute_JAL, EStateM.run, bind, EStateM.bind, get_next_pc,
    readReg_eq_of_get? Register.nextPC js.sail rustPC hNextPC,
    readReg_eq_of_get? Register.PC js.sail instructionAddress hPC,
    Projection.jump_to_of_aligned _ _ hTargetAligned, RETIRE_SUCCESS,
    wX_bits_stateAfterWrite, pure, EStateM.pure]
  -- Projection keeps the architectural write and drops the scratch write for x0.
  simp only [System.systemProjectResult, NativeDispatch.systemProject_afterDst,
    System.systemProject_setNextPCState,
    Projection.systemProject_eq_sail_of_compatible js h.linkedCSRs]
  rfl

end Natives

end
