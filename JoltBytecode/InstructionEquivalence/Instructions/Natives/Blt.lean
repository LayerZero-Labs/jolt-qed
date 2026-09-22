import JoltBytecode.Bundles
import JoltBytecode.InstructionEquivalence.ProofSupport.Projection
import JoltBytecode.InstructionEquivalence.ProofSupport.InstructionLemmas
import JoltBytecode.InstructionEquivalence.ProofSupport.RegisterAccess

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace Natives

/-- Main native `BLT` equivalence statement. -/
def bltInstrEqSailStatement
    (imm : BitVec 13)
    (rs2 rs1 : regidx)
    (js : SailJoltState)
    (_h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) : Prop :=
  System.systemProjectResult
    ((JoltISA.execInstr (.BLT (.xreg rs1) (.xreg rs2) imm)).run js) =
    ((execute_BTYPE imm rs2 rs1 bop.BLT).run js.sail)

abbrev branchJumpSailStep (imm : BitVec 13) : SailM ExecutionResult := do
  let pc ← Sail.readReg Register.PC
  jump_to (pc + sign_extend (m := 64) imm)

/-- The branch jump block does not touch the six Sail registers used by
`System.systemProject`: reading `PC` preserves them, and `jump_to` preserves
them. -/
theorem branchJump_preservesSystemProjectRegs
    (imm : BitVec 13)
    (js : SailJoltState) :
    Projection.ResultPreservesSystemProjectRegs js.sail
      ((branchJumpSailStep imm) js.sail) := by
  unfold branchJumpSailStep
  exact Projection.bind_preservesSystemProjectRegs
    (Projection.readReg_preservesSystemProjectRegs Register.PC js.sail)
    (fun pc s1 _hread =>
      Projection.jump_to_preservesSystemProjectRegs
        (pc + sign_extend (m := 64) imm) s1)

theorem bltInstr_eq_sail
    (imm : BitVec 13)
    (rs2 rs1 : regidx)
    (js : SailJoltState)
    (h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) :
    bltInstrEqSailStatement imm rs2 rs1 js h := by
 unfold bltInstrEqSailStatement
 -- RHS 
 simp only [execute_BTYPE]
 simp only [EStateM.run, bind, EStateM.bind]
 simp only [h.rs1_read, h.rs2_read]
 simp only [pure, EStateM.pure]
 -- LHS 
 simp only [JoltISA.execInstr, JoltISA.branchDecisionPure,
   bind, EStateM.bind, pure,
   JoltISA.readSrc_xreg_run_of_read rs1 js h.rs1_val h.rs1_read,
   JoltISA.readSrc_xreg_run_of_read rs2 js h.rs2_val h.rs2_read]
 cases h_taken : zopz0zI_s h.rs1_val h.rs2_val
 · -- not taken
   simp only [Bool.false_eq_true, if_false]
   exact Projection.systemProjectResult_pure_retire js h.linkedCSRs 
 · -- taken
   simp only [if_true]
   simpa only [Projection.liftSail_bind] using
     (Projection.systemProjectResult_liftSail_eq_of_preservesSystemProjectRegs
       h.linkedCSRs
       (branchJump_preservesSystemProjectRegs imm js))

end Natives

end
