import JoltBytecode.Bundles
import JoltBytecode.InstructionEquivalence.ProofSupport.Projection
import JoltBytecode.InstructionEquivalence.ProofSupport.InstructionLemmas
import JoltBytecode.InstructionEquivalence.Instructions.Natives.Blt

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace Natives

/-- Main native `BEQ` equivalence statement. -/
def beqInstrEqSailStatement
    (imm : BitVec 13)
    (rs2 rs1 : regidx)
    (js : SailJoltState)
    (_h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) : Prop :=
  System.systemProjectResult
    ((JoltISA.execInstr (JoltISA.Encoded.BEQ (.xreg rs1) (.xreg rs2) imm)).run js) =
    ((execute_BTYPE imm rs2 rs1 bop.BEQ).run js.sail)

theorem beqInstr_eq_sail
    (imm : BitVec 13)
    (rs2 rs1 : regidx)
    (js : SailJoltState)
    (h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) :
    beqInstrEqSailStatement imm rs2 rs1 js h := by
  unfold beqInstrEqSailStatement
  -- RHS
  simp only [execute_BTYPE]
  simp only [EStateM.run, bind, EStateM.bind]
  simp only [h.rs1_read, h.rs2_read]
  simp only [pure, EStateM.pure]
  -- LHS
  simp only [JoltISA.execInstr, encoded_branch_offset, JoltISA.branchDecisionPure,
    bind, EStateM.bind, pure,
    JoltISA.readSrc_xreg_run_of_read rs1 js h.rs1_val h.rs1_read,
    JoltISA.readSrc_xreg_run_of_read rs2 js h.rs2_val h.rs2_read]
  by_cases h_eq : h.rs1_val = h.rs2_val
  · -- taken
    simp only [beq_iff_eq, h_eq, ↓reduceIte]
    simpa only [Projection.liftSail_bind] using
      (Projection.systemProjectResult_liftSail_eq_of_preservesSystemProjectRegs
        h.linkedCSRs
        (branchJump_preservesSystemProjectRegs imm js))
  · -- not taken
    simp only [beq_iff_eq, h_eq, ↓reduceIte]
    exact Projection.systemProjectResult_pure_retire js h.linkedCSRs

end Natives

end
