import JoltBytecode.InstructionEquivalence.Instructions.AtomicFamily.WordSelectRust
import JoltBytecode.JoltISA.ExpansionsAutomated

set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions
open virtaddr

set_option autoImplicit true

noncomputable section

namespace AtomicFamily

theorem amomaxuwProgram_doesNotWriteProtectedVRegs
    (rs2 rs1 rd : regidx) :
    JoltISA.ProgramWritesNoProtectedVReg
      (JoltISA.amomaxuwProgramAuto rd rs1 rs2) := by
  unfold JoltISA.amomaxuwProgramAuto
  split <;>
    simp only [JoltISA.ProgramWritesNoProtectedVReg,
      JoltISA.InstrWritesNoProtectedVReg, JoltISA.DstWritesNoProtectedVReg,
      true_and, and_true] <;>
    repeat' apply And.intro
  all_goals exact JoltISA.not_protected_of_instructionTmp rfl

/-- The generated select is the shared LaneWindow instance; for example,
the unsigned variants sign-extend both comparison operands before SLTU. -/
private theorem amomaxuwProgramAuto_eq_core (rs2 rs1 rd : regidx) :
    JoltISA.amomaxuwProgramAuto rd rs1 rs2 =
      JoltISA.amoWordSelectRustProgram
        (fun dst src => .VirtualSignExtendWord dst src)
        (fun dst lhs rhs => .SLTU dst lhs rhs)
        (.vreg (JoltISA.amoWordOldVRegFor rd))
        (.vreg (JoltISA.amoWordNewVRegFor rd)) rs2 rs1 rd := by
  cases hrd : JoltISA.isX0 rd <;>
    simp only [JoltISA.amomaxuwProgramAuto, JoltISA.amoWordSelectRustProgram,
      JoltISA.amoPre64Program, JoltISA.amoPre64ProgramWithScratch,
      JoltISA.amoWordMergeProgram, JoltISA.laneWindowOpen, JoltISA.laneWindowExtract,
      JoltISA.laneWindowMerge, JoltISA.amoWordOldVRegFor, JoltISA.amoWordNewVRegFor,
      JoltISA.amoWordDwordVRegFor, JoltISA.amoWordLaneVRegFor, JoltISA.amoWordTakeVRegFor,
      JoltISA.amoVRegFor, JoltISA.amoDstFor, JoltISA.sideEffectingRdZeroDst,
      hrd, Bool.false_eq_true, if_false, if_true] <;> rfl

private theorem amomaxuwProgramCore_doesNotWriteProtectedVRegs
    (rs2 rs1 rd : regidx) :
    JoltISA.ProgramWritesNoProtectedVReg
      (JoltISA.amoWordSelectRustProgram
        (fun dst src => .VirtualSignExtendWord dst src)
        (fun dst lhs rhs => .SLTU dst lhs rhs)
        (.vreg (JoltISA.amoWordOldVRegFor rd))
        (.vreg (JoltISA.amoWordNewVRegFor rd))
        rs2 rs1 rd) := by
  rw [← amomaxuwProgramAuto_eq_core]
  exact amomaxuwProgram_doesNotWriteProtectedVRegs rs2 rs1 rd

/-- Sail's generated `AMOMAXU.W` result expression reduces to unsigned word max. -/
theorem amomaxuw_sail_result (rs2Val : BitVec 64) (loaded : BitVec 32) :
    amoWordSailResult amoop.AMOMAXU
      (show BitVec (4 * 8) from
        trunc (m := (((4 : Nat) : Int) * (8 : Int)).toNat) rs2Val)
      (BitVec.setWidth (4 * 8) loaded) =
    if (zopz0zK_u
        (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32)
        loaded : Bool) then
      (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32)
    else
      loaded := by
  rw [amo_word_trunc_4x8_eq_extract]
  rw [amo_word_setWidth_4x8_eq_self]

/-- Main public theorem for `AMOMAXU.W`.

The theorem takes one primitive-only atomic bundle. Exact memory facts are
derived internally from that bundle. -/
private theorem amomaxuwProgram_core_eq_sail
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (h : AmoWordProgramEqSailAssumptions amoop.AMOMAXU rs2 rs1 rd js) :
    System.systemProjectResult ((JoltISA.execProgram
      (JoltISA.amoWordSelectRustProgram
        (fun dst src => .VirtualSignExtendWord dst src)
        (fun dst lhs rhs => .SLTU dst lhs rhs)
        (.vreg (JoltISA.amoWordOldVRegFor rd))
        (.vreg (JoltISA.amoWordNewVRegFor rd))
        rs2 rs1 rd
        )).run js) =
      (execute_AMO amoop.AMOMAXU false false rs2 rs1 4 rd).run js.sail := by
  exact amo_word_select_eq_sail amoop.AMOMAXU
    (fun dst lhs rhs => .SLTU dst lhs rhs) zopz0zI_u true
    amo_word_sltu_run_vreg_vreg_vreg
    (by
      intro new old
      simp only [amoWordSelectFlag, if_true,
        amo_word_sltu_sign_extend, amoWordSailResult]
      rfl)
    (by decide) rs2 rs1 rd js h (amomaxuwProgramCore_doesNotWriteProtectedVRegs rs2 rs1 rd)

/-- Main public theorem for `AMOMAXU.W`. -/
def amomaxuwProgramEqSailStatement
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (_h : AmoWordProgramEqSailAssumptions amoop.AMOMAXU rs2 rs1 rd js) : Prop :=
  System.systemProjectResult
      ((JoltISA.execProgram
        (JoltISA.amomaxuwProgramAuto rd rs1 rs2)).run js) =
    (execute_AMO amoop.AMOMAXU false false rs2 rs1 4 rd).run js.sail

theorem amomaxuwProgram_eq_sail
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (h : AmoWordProgramEqSailAssumptions amoop.AMOMAXU rs2 rs1 rd js) :
    amomaxuwProgramEqSailStatement rs2 rs1 rd js h := by
  unfold amomaxuwProgramEqSailStatement
  rw [amomaxuwProgramAuto_eq_core]
  exact amomaxuwProgram_core_eq_sail rs2 rs1 rd js h

end AtomicFamily

end
