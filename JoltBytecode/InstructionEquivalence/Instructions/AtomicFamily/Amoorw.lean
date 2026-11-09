import JoltBytecode.InstructionEquivalence.Instructions.AtomicFamily.WordProgram
import JoltBytecode.JoltISA.ExpansionsAutomated

open LeanRV64D

set_option linter.unusedVariables false

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail LeanRV64D LeanRV64D.Functions
open virtaddr

set_option autoImplicit true

noncomputable section

namespace AtomicFamily

theorem amoorwProgram_doesNotWriteProtectedVRegs
    (rs2 rs1 rd : regidx) :
    JoltISA.ProgramWritesNoProtectedVReg
      (JoltISA.amoorwProgramAuto rd rs1 rs2) := by
  unfold JoltISA.amoorwProgramAuto
  split <;>
    simp only [JoltISA.ProgramWritesNoProtectedVReg,
      JoltISA.InstrWritesNoProtectedVReg, JoltISA.DstWritesNoProtectedVReg,
      true_and, and_true] <;>
    repeat' apply And.intro
  all_goals exact JoltISA.not_protected_of_instructionTmp rfl

/-- The generated OR word-AMO rows are the shared LaneWindow binop instance.
For example, the result register is temporary slot three. -/
private theorem amoorwProgramAuto_eq_core (rs2 rs1 rd : regidx) :
    JoltISA.amoorwProgramAuto rd rs1 rs2 =
      JoltISA.amoWordBinopProgram (fun dst lhs rhs => .OR dst lhs rhs) rs2 rs1 rd := by
  cases hrd : JoltISA.isX0 rd <;>
    simp only [JoltISA.amoorwProgramAuto, JoltISA.amoWordBinopProgram,
      JoltISA.amoPre64Program, JoltISA.amoPre64ProgramWithScratch,
      JoltISA.amoWordMergeProgram, JoltISA.laneWindowOpen, JoltISA.laneWindowExtract,
      JoltISA.laneWindowMerge, JoltISA.amoWordOldVRegFor, JoltISA.amoWordNewVRegFor,
      JoltISA.amoWordDwordVRegFor, JoltISA.amoWordLaneVRegFor,
      JoltISA.amoVRegFor, JoltISA.amoDstFor, JoltISA.sideEffectingRdZeroDst,
      hrd, Bool.false_eq_true, if_false, if_true] <;> rfl

private theorem amoorwProgramCore_doesNotWriteProtectedVRegs
    (rs2 rs1 rd : regidx) :
    JoltISA.ProgramWritesNoProtectedVReg
      (JoltISA.amoWordBinopProgram
        (fun dst lhs rhs => .OR dst lhs rhs) rs2 rs1 rd) := by
  rw [← amoorwProgramAuto_eq_core]
  exact amoorwProgram_doesNotWriteProtectedVRegs rs2 rs1 rd

/-- Sail's generated `AMOOR.W` result expression reduces to word bitwise-or. -/
theorem amoorw_sail_result (rs2Val : BitVec 64) (loaded : BitVec 32) :
    amoWordSailResult amoop.AMOOR
      (show BitVec (4 * 8) from
        trunc (m := (((4 : Nat) : Int) * (8 : Int)).toNat) rs2Val)
      (BitVec.setWidth (4 * 8) loaded) =
    (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32) ||| loaded := by
  rw [amo_word_trunc_4x8_eq_extract]
  rw [amo_word_setWidth_4x8_eq_self]

/-- Main public theorem for `AMOOR.W`.

The theorem takes one primitive-only atomic bundle. Exact memory facts are
derived internally from that bundle. -/
private theorem amoorwProgram_core_eq_sail
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (h : AmoWordProgramEqSailAssumptions amoop.AMOOR rs2 rs1 rd js) :
    System.systemProjectResult ((JoltISA.execProgram
      (JoltISA.amoWordBinopProgram
        (fun dst lhs rhs => .OR dst lhs rhs) rs2 rs1 rd)).run js) =
      (execute_AMO amoop.AMOOR false false rs2 rs1 4 rd).run js.sail := by
  exact amo_word_binop_eq_sail amoop.AMOOR
    (fun dst lhs rhs => .OR dst lhs rhs) (fun new old => new ||| old)
    amo_word_or_middle_run_into
    (by intro new old; rw [amo_word_extract_or_low];
        exact congrArg (fun word => (Sail.BitVec.extractLsb new 31 0 : BitVec 32) ||| word)
          (sign_extend_64_setWidth_32 old))
    (by decide) rs2 rs1 rd js h (amoorwProgramCore_doesNotWriteProtectedVRegs rs2 rs1 rd)

/-- Main public theorem for `AMOOR.W`. -/
def amoorwProgramEqSailStatement
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (_h : AmoWordProgramEqSailAssumptions amoop.AMOOR rs2 rs1 rd js) : Prop :=
  System.systemProjectResult
      ((JoltISA.execProgram
        (JoltISA.amoorwProgramAuto rd rs1 rs2)).run js) =
    (execute_AMO amoop.AMOOR false false rs2 rs1 4 rd).run js.sail

theorem amoorwProgram_eq_sail
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (h : AmoWordProgramEqSailAssumptions amoop.AMOOR rs2 rs1 rd js) :
    amoorwProgramEqSailStatement rs2 rs1 rd js h := by
  unfold amoorwProgramEqSailStatement
  rw [amoorwProgramAuto_eq_core]
  exact amoorwProgram_core_eq_sail rs2 rs1 rd js h

end AtomicFamily

end
