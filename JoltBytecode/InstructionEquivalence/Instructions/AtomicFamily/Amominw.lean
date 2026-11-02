import JoltBytecode.InstructionEquivalence.Instructions.AtomicFamily.WordSelectRust
import JoltBytecode.JoltISA.ExpansionsAutomated

set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions
open virtaddr

set_option autoImplicit true

noncomputable section

namespace AtomicFamily

theorem amominwProgram_doesNotWriteProtectedVRegs
    (rs2 rs1 rd : regidx) :
    JoltISA.ProgramWritesNoProtectedVReg
      (JoltISA.amominwProgramAuto rd rs1 rs2) := by
  unfold JoltISA.amominwProgramAuto
  split <;>
    simp only [JoltISA.ProgramWritesNoProtectedVReg,
      JoltISA.InstrWritesNoProtectedVReg, JoltISA.DstWritesNoProtectedVReg,
      true_and, and_true] <;>
    repeat' apply And.intro
  all_goals exact JoltISA.not_protected_of_instructionTmp rfl

/-- The generated select is the shared LaneWindow instance; for example,
the unsigned variants sign-extend both comparison operands before SLTU. -/
private theorem amominwProgramAuto_eq_core (rs2 rs1 rd : regidx) :
    JoltISA.amominwProgramAuto rd rs1 rs2 =
      JoltISA.amoWordSelectRustProgram
        (fun dst src => .VirtualSignExtendWord dst src)
        (fun dst lhs rhs => .SLT dst lhs rhs)
        (.vreg (JoltISA.amoWordNewVRegFor rd))
        (.vreg (JoltISA.amoWordOldVRegFor rd)) rs2 rs1 rd := by
  cases hrd : JoltISA.isX0 rd <;>
    simp only [JoltISA.amominwProgramAuto, JoltISA.amoWordSelectRustProgram,
      JoltISA.amoPre64Program, JoltISA.amoPre64ProgramWithScratch,
      JoltISA.amoWordMergeProgram, JoltISA.laneWindowOpen, JoltISA.laneWindowExtract,
      JoltISA.laneWindowMerge, JoltISA.amoWordOldVRegFor, JoltISA.amoWordNewVRegFor,
      JoltISA.amoWordDwordVRegFor, JoltISA.amoWordLaneVRegFor, JoltISA.amoWordTakeVRegFor,
      JoltISA.amoVRegFor, JoltISA.amoDstFor, JoltISA.sideEffectingRdZeroDst,
      hrd, Bool.false_eq_true, if_false, if_true] <;> rfl

private theorem amominwProgramCore_doesNotWriteProtectedVRegs
    (rs2 rs1 rd : regidx) :
    JoltISA.ProgramWritesNoProtectedVReg
      (JoltISA.amoWordSelectRustProgram
        (fun dst src => .VirtualSignExtendWord dst src)
        (fun dst lhs rhs => .SLT dst lhs rhs)
        (.vreg (JoltISA.amoWordNewVRegFor rd))
        (.vreg (JoltISA.amoWordOldVRegFor rd))
        rs2 rs1 rd) := by
  rw [← amominwProgramAuto_eq_core]
  exact amominwProgram_doesNotWriteProtectedVRegs rs2 rs1 rd

/-- Sail's generated `AMOMIN.W` result expression reduces to signed word min. -/
theorem amominw_sail_result (rs2Val : BitVec 64) (loaded : BitVec 32) :
    amoWordSailResult amoop.AMOMIN
      (show BitVec (4 * 8) from
        trunc (m := (((4 : Nat) : Int) * (8 : Int)).toNat) rs2Val)
      (BitVec.setWidth (4 * 8) loaded) =
    if (zopz0zI_s
        (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32)
        loaded : Bool) then
      (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32)
    else
      loaded := by
  rw [amo_word_trunc_4x8_eq_extract]
  rw [amo_word_setWidth_4x8_eq_self]

/-- Main public theorem for `AMOMIN.W`.

The theorem takes one primitive-only atomic bundle. Exact memory facts are
derived internally from that bundle. -/
private theorem amominwProgram_core_eq_sail
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (h : AmoWordProgramEqSailAssumptions amoop.AMOMIN rs2 rs1 rd js) :
    System.systemProjectResult ((JoltISA.execProgram
      (JoltISA.amoWordSelectRustProgram
        (fun dst src => .VirtualSignExtendWord dst src)
        (fun dst lhs rhs => .SLT dst lhs rhs)
        (.vreg (JoltISA.amoWordNewVRegFor rd))
        (.vreg (JoltISA.amoWordOldVRegFor rd))
        rs2 rs1 rd
        )).run js) =
      (execute_AMO amoop.AMOMIN false false rs2 rs1 4 rd).run js.sail := by
  exact amo_word_select_eq_sail amoop.AMOMIN
    (fun dst lhs rhs => .SLT dst lhs rhs) zopz0zI_s false
    amo_word_slt_run_vreg_vreg_vreg
    (by
      intro new old
      simp only [amoWordSelectFlag, Bool.false_eq_true, if_false,
        amoWordSailResult, zopz0zI_s, amo_word_toInt_signExtend32_64]
      rfl)
    (by decide) rs2 rs1 rd js h (amominwProgramCore_doesNotWriteProtectedVRegs rs2 rs1 rd)

/-- Main public theorem for `AMOMIN.W`. -/
def amominwProgramEqSailStatement
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (_h : AmoWordProgramEqSailAssumptions amoop.AMOMIN rs2 rs1 rd js) : Prop :=
  System.systemProjectResult
      ((JoltISA.execProgram
        (JoltISA.amominwProgramAuto rd rs1 rs2)).run js) =
    (execute_AMO amoop.AMOMIN false false rs2 rs1 4 rd).run js.sail

theorem amominwProgram_eq_sail
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (h : AmoWordProgramEqSailAssumptions amoop.AMOMIN rs2 rs1 rd js) :
    amominwProgramEqSailStatement rs2 rs1 rd js h := by
  unfold amominwProgramEqSailStatement
  rw [amominwProgramAuto_eq_core]
  exact amominwProgram_core_eq_sail rs2 rs1 rd js h

end AtomicFamily

end
