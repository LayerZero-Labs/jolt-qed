import JoltBytecode.Bundles
import JoltBytecode.InstructionEquivalence.ProofSupport.Projection
import JoltBytecode.InstructionEquivalence.ProofSupport.InstructionLemmas
import JoltBytecode.InstructionEquivalence.ProofSupport.RegisterAccess

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true
set_option linter.unusedSimpArgs false

noncomputable section

namespace Natives

/-- Main native `AUIPC` equivalence statement. -/
def auipcInstrEqSailStatement
    (imm : BitVec 20)
    (rd : regidx)
    (js : SailJoltState)
    (_h : NoSourceReadWithLinkedCSRs js) : Prop :=
  System.systemProjectResult
    ((JoltISA.execInstr (JoltISA.Encoded.AUIPC (.xreg rd) imm)).run js) =
    ((execute_UTYPE imm rd uop.AUIPC).run js.sail)

private theorem getArchPC_preservesSystemProjectRegs
    (s : SailState) :
    Projection.ResultPreservesSystemProjectRegs s ((get_arch_pc ()) s) := by
  unfold get_arch_pc
  exact Projection.readReg_preservesSystemProjectRegs Register.PC s

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

private theorem executeAUIPC_preservesSystemProjectRegs
    (imm : BitVec 20)
    (rd : regidx)
    (s : SailState) :
    Projection.ResultPreservesSystemProjectRegs s ((execute_UTYPE imm rd uop.AUIPC) s) := by
  unfold execute_UTYPE
  simp only
  exact Projection.bind_preservesSystemProjectRegs
    (Projection.bind_preservesSystemProjectRegs
      (getArchPC_preservesSystemProjectRegs s)
      (fun pc s0 _hpc =>
        Projection.pure_preservesSystemProjectRegs s0
          (pc + sign_extend (m := 64) (imm +++ (0x000#12 : BitVec 12)))))
    (fun value s1 _hvalue =>
      Projection.bind_preservesSystemProjectRegs
        (wX_bits_preservesSystemProjectRegs rd value s1)
        (fun _ s2 _hwrite =>
          Projection.pure_preservesSystemProjectRegs s2 RETIRE_SUCCESS))

/-- Native `AUIPC` agrees with Sail `execute_UTYPE ... AUIPC`. -/
theorem auipcInstr_eq_sail
    (imm : BitVec 20)
    (rd : regidx)
    (js : SailJoltState)
    (h : NoSourceReadWithLinkedCSRs js) :
    auipcInstrEqSailStatement imm rd js h := by
  unfold auipcInstrEqSailStatement
  have hExec :
      JoltISA.execInstr (JoltISA.Encoded.AUIPC (.xreg rd) imm) =
        liftSail (execute_UTYPE imm rd uop.AUIPC) := by
    funext js
    unfold JoltISA.execInstr execute_UTYPE JoltISA.writeDst liftSail get_arch_pc
    simp only [JoltISA.addWide_low]
    simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run]
    cases hpc : Sail.readReg Register.PC js.sail with
    | error e s1 =>
        simp only [hpc, EStateM.run]
    | ok pc s1 =>
        simp only [hpc, EStateM.run]
        cases hw :
            wX_bits rd
              (pc + sign_extend (m := 64) (imm +++ (0x000#12 : BitVec 12))) s1 with
        | ok _ _ =>
            simp only [hw, bind, EStateM.bind, pure, EStateM.pure, EStateM.run]
        | error _ _ =>
            simp only [hw, bind, EStateM.bind, pure, EStateM.pure, EStateM.run]
  rw [hExec]
  exact Projection.systemProjectResult_liftSail_eq_of_preservesSystemProjectRegs
    h.linkedCSRs
    (executeAUIPC_preservesSystemProjectRegs imm rd js.sail)

end Natives

end
