import JoltBytecode.Bundles
import JoltBytecode.InstructionEquivalence.ProofSupport.Projection

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true
set_option linter.unusedSimpArgs false

noncomputable section

namespace Natives

/-- Main native `JAL` equivalence statement. -/
def jalInstrEqSailStatement
    (imm : BitVec 21)
    (rd : regidx)
    (js : SailJoltState)
    (_h : JalInstrEqSailAssumptions imm js) : Prop :=
  System.systemProjectResult
    ((JoltISA.execInstr (JoltISA.Encoded.JAL (.xreg rd) imm)).run js) =
    ((execute_JAL imm rd).run js.sail)

theorem jalInstr_eq_sail
    (imm : BitVec 21)
    (rd : regidx)
    (js : SailJoltState)
    (h : JalInstrEqSailAssumptions imm js) :
    jalInstrEqSailStatement imm rd js h := by
  unfold jalInstrEqSailStatement
  simp only [EStateM.run, JoltISA.execInstr]
  -- nextPC represents Rust's already advanced cpu.pc at the instruction-body boundary.
  obtain ⟨rustPC, hNextPC⟩ := h.nextPC_readable.exists_value
  have hReadRustPC : liftSail (Sail.readReg Register.nextPC) js = .ok rustPC js := by
    unfold liftSail
    rw [readReg_eq_of_get? Register.nextPC js.sail rustPC hNextPC]
  simp only [bind, EStateM.bind, hReadRustPC]
  -- PC represents Rust's self.address, the decoded instruction's address.
  obtain ⟨instructionAddress, hPC⟩ := h.pc_readable.exists_value
  have hReadInstructionAddress :
      liftSail (Sail.readReg Register.PC) js = .ok instructionAddress js := by
    unfold liftSail
    rw [readReg_eq_of_get? Register.PC js.sail instructionAddress hPC]
  simp only [hReadInstructionAddress]
  -- Rust first writes the old cpu.pc to rd; writing x0 leaves the state unchanged.
  let afterDst : SailJoltState := { js with sail := stateAfterWrite js.sail rd rustPC }
  have hWriteDst : JoltISA.writeDst (.xreg rd) rustPC js = .ok () afterDst := by
    simp only [JoltISA.writeDst, liftSail, wX_bits_stateAfterWrite]
    rfl
  simp only [hWriteDst]
  -- After writing the destination register, we write Rust's cpu.pc to the jump target.
  -- In this representation that updates Sail nextPC; Sail PC retains self.address.
  have hWriteRustPC :
      liftSail (Sail.writeReg Register.nextPC
        (instructionAddress + sign_extend (m := 64) imm)) afterDst =
      .ok () { afterDst with
        sail := System.setNextPCState afterDst.sail
          (instructionAddress + sign_extend (m := 64) imm) } := by
    rfl
  simp only [hWriteRustPC]

  -- Sail side: resolve the same register reads, then its checked jump.
  simp only [execute_JAL, bind, EStateM.bind, get_next_pc]
  simp only [readReg_eq_of_get? Register.nextPC js.sail rustPC hNextPC,
    readReg_eq_of_get? Register.PC js.sail instructionAddress hPC]
  have hPCValue : h.pc_readable.exists_value.choose = instructionAddress :=
    Option.some.inj (h.pc_readable.exists_value.choose_spec.symm.trans hPC)
  have hTargetAligned : Assumptions.MepcReadAligned
      (instructionAddress + sign_extend (m := 64) imm) js.sail := by
    simpa only [hPCValue] using h.target_aligned
  simp only [Projection.jump_to_of_aligned _ _ hTargetAligned, RETIRE_SUCCESS,
    bind, EStateM.bind, wX_bits_stateAfterWrite, pure, EStateM.pure]
  -- Sail writes nextPC before rd; these writes commute.
  rw [Projection.stateAfterWrite_setNextPCState]
  -- We only changed rd and nextPC; the six CSRs still equal their virtual-register copies.
  -- systemProject therefore writes back values that are already there and changes nothing.
  -- The projected Jolt state is consequently equal to the Sail state.
  simp only [System.systemProjectResult, EStateM.Result.ok.injEq, true_and]
  exact Projection.systemProject_eq_sail_of_preservesSystemProjectRegs js _ h.linkedCSRs
    -- Combine CSR preservation across the two writes.
    (Projection.preservesSystemProjectRegs_trans
      -- Writing rd preserves the six CSRs.
      (Projection.stateAfterWrite_preservesSystemProjectRegs js.sail rd rustPC)
      -- Writing nextPC also preserves the six CSRs.
      (Projection.setNextPCState_preservesSystemProjectRegs _ _))

end Natives

end
