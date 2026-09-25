import JoltBytecode.Bundles
import JoltBytecode.InstructionEquivalence.ProofSupport.Projection
import JoltBytecode.InstructionEquivalence.ProofSupport.InstructionLemmas
import JoltBytecode.InstructionEquivalence.ProofSupport.RegisterAccess

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true
set_option linter.unusedSimpArgs false

noncomputable section

namespace Natives

/-- Main native `JALR` equivalence statement. -/
def jalrInstrEqSailStatement
    (imm : BitVec 12)
    (rs1 rd : regidx)
    (js : SailJoltState)
    (_h : JalrInstrEqSailAssumptions rs1 js) : Prop :=
  System.systemProjectResult
    ((JoltISA.execInstr (.JALR (.xreg rd) (.xreg rs1) imm)).run js) =
    ((execute_JALR imm rs1 rd).run js.sail)

private theorem updateELP_noop
    (rs1 : regidx)
    (s : SailState)
    (h : Assumptions.ZicfilpDisabled s) :
    update_elp_state rs1 s = .ok () s := by
  unfold update_elp_state
  simp only [h.value, bind, EStateM.bind, Bool.false_eq_true, if_false,
    pure, EStateM.pure]

private theorem getNextPC_preservesSystemProjectRegs
    (s : SailState) :
    Projection.ResultPreservesSystemProjectRegs s ((get_next_pc ()) s) := by
  unfold get_next_pc
  exact Projection.readReg_preservesSystemProjectRegs Register.nextPC s

private theorem updateELP_preservesSystemProjectRegs
    (rs1 : regidx)
    (s : SailState)
    (h : Assumptions.ZicfilpDisabled s) :
    Projection.ResultPreservesSystemProjectRegs s ((update_elp_state rs1) s) := by
  rw [updateELP_noop rs1 s h]
  exact Projection.preservesSystemProjectRegs_refl s

private theorem readRegBindPure_preservesSystemProjectRegs
    (reg : Register)
    (f : RegisterType reg → α)
    (s : SailState) :
    Projection.ResultPreservesSystemProjectRegs s
      (((Sail.readReg reg >>= fun value => pure (f value)) : SailM α) s) := by
  exact Projection.bind_preservesSystemProjectRegs
    (Projection.readReg_preservesSystemProjectRegs reg s)
    (fun value s1 _hread =>
      Projection.pure_preservesSystemProjectRegs s1 (f value))

private theorem rX_bits_preservesSystemProjectRegs
    (rs1 : regidx)
    (s : SailState) :
    Projection.ResultPreservesSystemProjectRegs s ((rX_bits rs1) s) := by
  unfold rX_bits rX regval_from_reg
  simp only [Sail.BitVec.toNatInt, Int.ofNat_eq_natCast, Int.toNat_natCast,
    bind, EStateM.bind, pure, EStateM.pure]
  reg_cases rs1 <;> simp_all
  · exact Projection.pure_preservesSystemProjectRegs s zero_reg
  all_goals
    first
    | exact readRegBindPure_preservesSystemProjectRegs Register.x1
        (fun value => regval_from_reg value) s
    | exact readRegBindPure_preservesSystemProjectRegs Register.x2
        (fun value => regval_from_reg value) s
    | exact readRegBindPure_preservesSystemProjectRegs Register.x3
        (fun value => regval_from_reg value) s
    | exact readRegBindPure_preservesSystemProjectRegs Register.x4
        (fun value => regval_from_reg value) s
    | exact readRegBindPure_preservesSystemProjectRegs Register.x5
        (fun value => regval_from_reg value) s
    | exact readRegBindPure_preservesSystemProjectRegs Register.x6
        (fun value => regval_from_reg value) s
    | exact readRegBindPure_preservesSystemProjectRegs Register.x7
        (fun value => regval_from_reg value) s
    | exact readRegBindPure_preservesSystemProjectRegs Register.x8
        (fun value => regval_from_reg value) s
    | exact readRegBindPure_preservesSystemProjectRegs Register.x9
        (fun value => regval_from_reg value) s
    | exact readRegBindPure_preservesSystemProjectRegs Register.x10
        (fun value => regval_from_reg value) s
    | exact readRegBindPure_preservesSystemProjectRegs Register.x11
        (fun value => regval_from_reg value) s
    | exact readRegBindPure_preservesSystemProjectRegs Register.x12
        (fun value => regval_from_reg value) s
    | exact readRegBindPure_preservesSystemProjectRegs Register.x13
        (fun value => regval_from_reg value) s
    | exact readRegBindPure_preservesSystemProjectRegs Register.x14
        (fun value => regval_from_reg value) s
    | exact readRegBindPure_preservesSystemProjectRegs Register.x15
        (fun value => regval_from_reg value) s
    | exact readRegBindPure_preservesSystemProjectRegs Register.x16
        (fun value => regval_from_reg value) s
    | exact readRegBindPure_preservesSystemProjectRegs Register.x17
        (fun value => regval_from_reg value) s
    | exact readRegBindPure_preservesSystemProjectRegs Register.x18
        (fun value => regval_from_reg value) s
    | exact readRegBindPure_preservesSystemProjectRegs Register.x19
        (fun value => regval_from_reg value) s
    | exact readRegBindPure_preservesSystemProjectRegs Register.x20
        (fun value => regval_from_reg value) s
    | exact readRegBindPure_preservesSystemProjectRegs Register.x21
        (fun value => regval_from_reg value) s
    | exact readRegBindPure_preservesSystemProjectRegs Register.x22
        (fun value => regval_from_reg value) s
    | exact readRegBindPure_preservesSystemProjectRegs Register.x23
        (fun value => regval_from_reg value) s
    | exact readRegBindPure_preservesSystemProjectRegs Register.x24
        (fun value => regval_from_reg value) s
    | exact readRegBindPure_preservesSystemProjectRegs Register.x25
        (fun value => regval_from_reg value) s
    | exact readRegBindPure_preservesSystemProjectRegs Register.x26
        (fun value => regval_from_reg value) s
    | exact readRegBindPure_preservesSystemProjectRegs Register.x27
        (fun value => regval_from_reg value) s
    | exact readRegBindPure_preservesSystemProjectRegs Register.x28
        (fun value => regval_from_reg value) s
    | exact readRegBindPure_preservesSystemProjectRegs Register.x29
        (fun value => regval_from_reg value) s
    | exact readRegBindPure_preservesSystemProjectRegs Register.x30
        (fun value => regval_from_reg value) s
    | exact readRegBindPure_preservesSystemProjectRegs Register.x31
        (fun value => regval_from_reg value) s

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

private theorem executeJALR_preservesSystemProjectRegs
    (imm : BitVec 12)
    (rs1 rd : regidx)
    (s : SailState)
    (hZicfilp : Assumptions.ZicfilpDisabled s) :
    Projection.ResultPreservesSystemProjectRegs s ((execute_JALR imm rs1 rd) s) := by
  unfold execute_JALR
  exact Projection.bind_preservesSystemProjectRegs
    (updateELP_preservesSystemProjectRegs rs1 s hZicfilp)
    (fun _ s0 hUpdate =>
      Projection.bind_preservesSystemProjectRegs
        (getNextPC_preservesSystemProjectRegs s0)
        (fun link s1 _hlink =>
          Projection.bind_preservesSystemProjectRegs
            (rX_bits_preservesSystemProjectRegs rs1 s1)
            (fun targetBase s2 _hread =>
              Projection.bind_preservesSystemProjectRegs
                (Projection.pure_preservesSystemProjectRegs s2
                  (targetBase + sign_extend (m := 64) imm))
                (fun target s3 _htarget =>
                  Projection.bind_preservesSystemProjectRegs
                    (Projection.jump_to_preservesSystemProjectRegs
                      (BitVec.update target 0 0#1) s3)
                    (fun result s4 _hjump => by
                      cases result with
                      | Retire_Success u =>
                          cases u
                          exact Projection.bind_preservesSystemProjectRegs
                            (wX_bits_preservesSystemProjectRegs rd link s4)
                            (fun _ s5 _hwrite =>
                              Projection.pure_preservesSystemProjectRegs s5 RETIRE_SUCCESS)
                      | ExecuteAs instr =>
                          exact Projection.pure_preservesSystemProjectRegs s4
                            (ExecutionResult.ExecuteAs instr)
                      | Enter_Wait reason =>
                          exact Projection.pure_preservesSystemProjectRegs s4
                            (ExecutionResult.Enter_Wait reason)
                      | Illegal_Instruction u =>
                          exact Projection.pure_preservesSystemProjectRegs s4
                            (ExecutionResult.Illegal_Instruction u)
                      | Virtual_Instruction u =>
                          exact Projection.pure_preservesSystemProjectRegs s4
                            (ExecutionResult.Virtual_Instruction u)
                      | Trap trap =>
                          exact Projection.pure_preservesSystemProjectRegs s4
                            (ExecutionResult.Trap trap)
                      | Memory_Exception ex =>
                          exact Projection.pure_preservesSystemProjectRegs s4
                            (ExecutionResult.Memory_Exception ex)
                      | Ext_CSR_Check_Failure u =>
                          exact Projection.pure_preservesSystemProjectRegs s4
                            (ExecutionResult.Ext_CSR_Check_Failure u)
                      | Ext_ControlAddr_Check_Failure err =>
                          exact Projection.pure_preservesSystemProjectRegs s4
                            (ExecutionResult.Ext_ControlAddr_Check_Failure err)
                      | Ext_DataAddr_Check_Failure err =>
                          exact Projection.pure_preservesSystemProjectRegs s4
                            (ExecutionResult.Ext_DataAddr_Check_Failure err)
                      | Ext_XRET_Priv_Failure u =>
                          exact Projection.pure_preservesSystemProjectRegs s4
                            (ExecutionResult.Ext_XRET_Priv_Failure u))))))

theorem jalrInstr_eq_sail
    (imm : BitVec 12)
    (rs1 rd : regidx)
    (js : SailJoltState)
    (h : JalrInstrEqSailAssumptions rs1 js) :
    jalrInstrEqSailStatement imm rs1 rd js h := by
  unfold jalrInstrEqSailStatement
  have hUpdate := updateELP_noop rs1 js.sail h.zicfilp_disabled
  have hExec :
      (JoltISA.execInstr (.JALR (.xreg rd) (.xreg rs1) imm)).run js =
    (liftSail (execute_JALR imm rs1 rd)) js := by
    unfold JoltISA.execInstr execute_JALR JoltISA.readSrc JoltISA.writeDst liftSail
    simp only [jolt_jalr_target, JoltISA.addWide_low]
    simp only [hUpdate, bind, EStateM.bind, pure, EStateM.pure, EStateM.run]
    cases hlink : (get_next_pc ()) js.sail with
    | error e s1 =>
        simp only [hlink, EStateM.run]
    | ok link s1 =>
        simp only [hlink, EStateM.run]
        cases hread : rX_bits rs1 s1 with
        | error e s2 =>
            simp only [hread, EStateM.run]
        | ok targetBase s2 =>
            simp only [hread, pure, EStateM.pure, bind, EStateM.bind, EStateM.run]
            cases hjump :
                jump_to (BitVec.update (targetBase + sign_extend (m := 64) imm) 0 0#1) s2 with
            | error e s3 =>
                simp only [hjump, EStateM.run]
            | ok result s3 =>
                simp only [hjump, EStateM.run]
                cases result with
                | Retire_Success u =>
                    cases u
                    simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run]
                    cases hw : wX_bits rd link s3 with
                    | ok _ _ =>
                        simp only [hw, bind, EStateM.bind, pure, EStateM.pure, EStateM.run]
                        unfold RETIRE_SUCCESS
                        rfl
                    | error _ _ =>
                        simp only [hw, bind, EStateM.bind, pure, EStateM.pure, EStateM.run]
                | ExecuteAs instr =>
                    simp only [hlink, hread, hjump, bind, EStateM.bind, pure, EStateM.pure,
                      EStateM.run]
                | Enter_Wait reason =>
                    simp only [hlink, hread, hjump, bind, EStateM.bind, pure, EStateM.pure,
                      EStateM.run]
                | Illegal_Instruction u =>
                    simp only [hlink, hread, hjump, bind, EStateM.bind, pure, EStateM.pure,
                      EStateM.run]
                | Virtual_Instruction u =>
                    simp only [hlink, hread, hjump, bind, EStateM.bind, pure, EStateM.pure,
                      EStateM.run]
                | Trap trap =>
                    simp only [hlink, hread, hjump, bind, EStateM.bind, pure, EStateM.pure,
                      EStateM.run]
                | Memory_Exception ex =>
                    simp only [hlink, hread, hjump, bind, EStateM.bind, pure, EStateM.pure,
                      EStateM.run]
                | Ext_CSR_Check_Failure u =>
                    simp only [hlink, hread, hjump, bind, EStateM.bind, pure, EStateM.pure,
                      EStateM.run]
                | Ext_ControlAddr_Check_Failure err =>
                    simp only [hlink, hread, hjump, bind, EStateM.bind, pure, EStateM.pure,
                      EStateM.run]
                | Ext_DataAddr_Check_Failure err =>
                    simp only [hlink, hread, hjump, bind, EStateM.bind, pure, EStateM.pure,
                      EStateM.run]
                | Ext_XRET_Priv_Failure u =>
                    simp only [hlink, hread, hjump, bind, EStateM.bind, pure, EStateM.pure,
                      EStateM.run]
  rw [hExec]
  exact Projection.systemProjectResult_liftSail_eq_of_preservesSystemProjectRegs
    h.linkedCSRs
    (executeJALR_preservesSystemProjectRegs imm rs1 rd js.sail h.zicfilp_disabled)

end Natives

end
