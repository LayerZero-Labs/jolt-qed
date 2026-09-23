import JoltBytecode.Bundles
import JoltBytecode.InstructionEquivalence.ProofSupport.Projection
import JoltBytecode.InstructionEquivalence.ProofSupport.InstructionLemmas
import JoltBytecode.InstructionEquivalence.ProofSupport.RegisterAccess

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
    (_h : NoSourceReadWithLinkedCSRs js) : Prop :=
  System.systemProjectResult
    ((JoltISA.execInstr (JoltISA.Encoded.JAL (.xreg rd) imm)).run js) =
    ((execute_JAL imm rd).run js.sail)

private abbrev jalJumpSailStep (imm : BitVec 21) : SailM ExecutionResult := do
  let pc ← Sail.readReg Register.PC
  jump_to (pc + sign_extend (m := 64) imm)

private theorem getNextPC_preservesSystemProjectRegs
    (s : SailState) :
    Projection.ResultPreservesSystemProjectRegs s ((get_next_pc ()) s) := by
  unfold get_next_pc
  exact Projection.readReg_preservesSystemProjectRegs Register.nextPC s

private theorem jalJump_preservesSystemProjectRegs
    (imm : BitVec 21)
    (s : SailState) :
    Projection.ResultPreservesSystemProjectRegs s ((jalJumpSailStep imm) s) := by
  unfold jalJumpSailStep
  exact Projection.bind_preservesSystemProjectRegs
    (Projection.readReg_preservesSystemProjectRegs Register.PC s)
    (fun pc s1 _hread =>
      Projection.jump_to_preservesSystemProjectRegs
        (pc + sign_extend (m := 64) imm) s1)

private theorem stateAfterWrite_preservesSystemProjectRegs
    (s : SailState)
    (rd : regidx)
    (value : BitVec 64) :
    Projection.PreservesSystemProjectRegs s (stateAfterWrite s rd value) := by
  refine
    { mstatus := ?_
      mtvec := ?_
      mscratch := ?_
      mepc := ?_
      mcause := ?_
      mtval := ?_ }
  all_goals
    reg_cases rd <;>
      simp_all [stateAfterWrite, wX_update_regs, Std.ExtDHashMap.get?_insert]

private theorem wX_bits_preservesSystemProjectRegs
    (rd : regidx)
    (value : BitVec 64)
    (s : SailState) :
    Projection.ResultPreservesSystemProjectRegs s ((wX_bits rd value) s) := by
  obtain ⟨s', hwrite⟩ := wX_shape rd value s
  simp only [hwrite, Projection.ResultPreservesSystemProjectRegs]
  rw [wX_bits_eq_stateAfterWrite rd value s s' hwrite]
  exact stateAfterWrite_preservesSystemProjectRegs s rd value

private theorem executeJAL_preservesSystemProjectRegs
    (imm : BitVec 21)
    (rd : regidx)
    (s : SailState) :
    Projection.ResultPreservesSystemProjectRegs s ((execute_JAL imm rd) s) := by
  unfold execute_JAL
  exact Projection.bind_preservesSystemProjectRegs
    (getNextPC_preservesSystemProjectRegs s)
    (fun link s1 _hlink =>
      Projection.bind_preservesSystemProjectRegs
        (Projection.readReg_preservesSystemProjectRegs Register.PC s1)
        (fun pc s2 _hreadPC =>
          Projection.bind_preservesSystemProjectRegs
            (Projection.jump_to_preservesSystemProjectRegs
              (pc + sign_extend (m := 64) imm) s2)
            (fun result s3 _hjump => by
              cases result with
              | Retire_Success u =>
                  cases u
                  exact Projection.bind_preservesSystemProjectRegs
                    (wX_bits_preservesSystemProjectRegs rd link s3)
                    (fun _ s4 _hwrite =>
                      Projection.pure_preservesSystemProjectRegs s4 RETIRE_SUCCESS)
              | ExecuteAs instr =>
                  exact Projection.pure_preservesSystemProjectRegs s3
                    (ExecutionResult.ExecuteAs instr)
              | Enter_Wait reason =>
                  exact Projection.pure_preservesSystemProjectRegs s3
                    (ExecutionResult.Enter_Wait reason)
              | Illegal_Instruction u =>
                  exact Projection.pure_preservesSystemProjectRegs s3
                    (ExecutionResult.Illegal_Instruction u)
              | Virtual_Instruction u =>
                  exact Projection.pure_preservesSystemProjectRegs s3
                    (ExecutionResult.Virtual_Instruction u)
              | Trap trap =>
                  exact Projection.pure_preservesSystemProjectRegs s3
                    (ExecutionResult.Trap trap)
              | Memory_Exception ex =>
                  exact Projection.pure_preservesSystemProjectRegs s3
                    (ExecutionResult.Memory_Exception ex)
              | Ext_CSR_Check_Failure u =>
                  exact Projection.pure_preservesSystemProjectRegs s3
                    (ExecutionResult.Ext_CSR_Check_Failure u)
              | Ext_ControlAddr_Check_Failure err =>
                  exact Projection.pure_preservesSystemProjectRegs s3
                    (ExecutionResult.Ext_ControlAddr_Check_Failure err)
              | Ext_DataAddr_Check_Failure err =>
                  exact Projection.pure_preservesSystemProjectRegs s3
                    (ExecutionResult.Ext_DataAddr_Check_Failure err)
              | Ext_XRET_Priv_Failure u =>
                  exact Projection.pure_preservesSystemProjectRegs s3
                    (ExecutionResult.Ext_XRET_Priv_Failure u))))

theorem jalInstr_eq_sail
    (imm : BitVec 21)
    (rd : regidx)
    (js : SailJoltState)
    (h : NoSourceReadWithLinkedCSRs js) :
    jalInstrEqSailStatement imm rd js h := by
  unfold jalInstrEqSailStatement
  have hExec :
      JoltISA.execInstr (JoltISA.Encoded.JAL (.xreg rd) imm) =
        liftSail (execute_JAL imm rd) := by
    funext js
    unfold JoltISA.execInstr execute_JAL JoltISA.writeDst liftSail
    simp only [JoltISA.addWide_low]
    simp only [bind, EStateM.bind]
    cases hlink : (get_next_pc ()) js.sail with
    | error e s1 =>
        simp only [hlink]
    | ok link s1 =>
        simp only [hlink]
        cases hpc : Sail.readReg Register.PC s1 with
        | error e s2 =>
            simp only [hpc]
        | ok pc s2 =>
            simp only [hpc]
            cases hjump : jump_to (pc + sign_extend (m := 64) imm) s2 with
            | error e s3 =>
                simp only [hjump]
            | ok result s3 =>
                simp only [hjump]
                cases result with
                | Retire_Success u =>
                    cases u
                    simp only [bind, EStateM.bind, pure, EStateM.pure]
                    cases hw : wX_bits rd link s3 with
                    | ok _ _ =>
                        simp only [hw, bind, EStateM.bind, pure, EStateM.pure]
                        unfold RETIRE_SUCCESS
                        rfl
                    | error _ _ =>
                        simp only [hw, bind, EStateM.bind, pure, EStateM.pure]
                | ExecuteAs instr =>
                    simp only [bind, EStateM.bind, pure, EStateM.pure]
                | Enter_Wait reason =>
                    simp only [bind, EStateM.bind, pure, EStateM.pure]
                | Illegal_Instruction u =>
                    simp only [bind, EStateM.bind, pure, EStateM.pure]
                | Virtual_Instruction u =>
                    simp only [bind, EStateM.bind, pure, EStateM.pure]
                | Trap trap =>
                    simp only [bind, EStateM.bind, pure, EStateM.pure]
                | Memory_Exception ex =>
                    simp only [bind, EStateM.bind, pure, EStateM.pure]
                | Ext_CSR_Check_Failure u =>
                    simp only [bind, EStateM.bind, pure, EStateM.pure]
                | Ext_ControlAddr_Check_Failure err =>
                    simp only [bind, EStateM.bind, pure, EStateM.pure]
                | Ext_DataAddr_Check_Failure err =>
                    simp only [bind, EStateM.bind, pure, EStateM.pure]
                | Ext_XRET_Priv_Failure u =>
                    simp only [bind, EStateM.bind, pure, EStateM.pure]
  rw [hExec]
  exact Projection.systemProjectResult_liftSail_eq_of_preservesSystemProjectRegs
    h.linkedCSRs
    (executeJAL_preservesSystemProjectRegs imm rd js.sail)

end Natives

end
