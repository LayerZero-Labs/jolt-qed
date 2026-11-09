import JoltBytecode.InstructionEquivalence.Instructions.AtomicFamily.WordProgram
import JoltBytecode.JoltISA.ExpansionsAutomated

open LeanRV64D

set_option linter.unusedVariables false

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail LeanRV64D LeanRV64D.Functions
open virtaddr

set_option autoImplicit true

noncomputable section

namespace AtomicFamily

theorem amoxorwProgram_doesNotWriteProtectedVRegs
    (rs2 rs1 rd : regidx) :
    JoltISA.ProgramWritesNoProtectedVReg
      (JoltISA.amoxorwProgramAuto rd rs1 rs2) := by
  unfold JoltISA.amoxorwProgramAuto
  split <;>
    simp only [JoltISA.ProgramWritesNoProtectedVReg,
      JoltISA.InstrWritesNoProtectedVReg, JoltISA.DstWritesNoProtectedVReg,
      true_and, and_true] <;>
    repeat' apply And.intro
  all_goals exact JoltISA.not_protected_of_instructionTmp rfl

/-- The generated XOR word-AMO rows are the shared LaneWindow binop instance.
For example, the result register is temporary slot three. -/
private theorem amoxorwProgramAuto_eq_core (rs2 rs1 rd : regidx) :
    JoltISA.amoxorwProgramAuto rd rs1 rs2 =
      JoltISA.amoWordBinopProgram (fun dst lhs rhs => .XOR dst lhs rhs) rs2 rs1 rd := by
  cases hrd : JoltISA.isX0 rd <;>
    simp only [JoltISA.amoxorwProgramAuto, JoltISA.amoWordBinopProgram,
      JoltISA.amoPre64Program, JoltISA.amoPre64ProgramWithScratch,
      JoltISA.amoWordMergeProgram, JoltISA.laneWindowOpen, JoltISA.laneWindowExtract,
      JoltISA.laneWindowMerge, JoltISA.amoWordOldVRegFor, JoltISA.amoWordNewVRegFor,
      JoltISA.amoWordDwordVRegFor, JoltISA.amoWordLaneVRegFor,
      JoltISA.amoVRegFor, JoltISA.amoDstFor, JoltISA.sideEffectingRdZeroDst,
      hrd, Bool.false_eq_true, if_false, if_true] <;> rfl

private theorem amoxorwProgramCore_doesNotWriteProtectedVRegs
    (rs2 rs1 rd : regidx) :
    JoltISA.ProgramWritesNoProtectedVReg
      (JoltISA.amoWordBinopProgram
        (fun dst lhs rhs => .XOR dst lhs rhs) rs2 rs1 rd) := by
  rw [← amoxorwProgramAuto_eq_core]
  exact amoxorwProgram_doesNotWriteProtectedVRegs rs2 rs1 rd

/-- Sail's generated `AMOXOR.W` result expression reduces to word bitwise-xor. -/
theorem amoxorw_sail_result (rs2Val : BitVec 64) (loaded : BitVec 32) :
    amoWordSailResult amoop.AMOXOR
      (show BitVec (4 * 8) from
        trunc (m := (((4 : Nat) : Int) * (8 : Int)).toNat) rs2Val)
      (BitVec.setWidth (4 * 8) loaded) =
    (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32) ^^^ loaded := by
  rw [amo_word_trunc_4x8_eq_extract]
  rw [amo_word_setWidth_4x8_eq_self]

/-- Main public theorem for `AMOXOR.W`.

The theorem takes one primitive-only atomic bundle. Exact memory facts are
derived internally from that bundle. -/
private theorem amoxorwProgram_core_eq_sail
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (h : AmoWordProgramEqSailAssumptions amoop.AMOXOR rs2 rs1 rd js) :
    System.systemProjectResult ((JoltISA.execProgram
      (JoltISA.amoWordBinopProgram
        (fun dst lhs rhs => .XOR dst lhs rhs) rs2 rs1 rd)).run js) =
      (execute_AMO amoop.AMOXOR false false rs2 rs1 4 rd).run js.sail := by
  exact amo_word_binop_eq_sail amoop.AMOXOR
    (fun dst lhs rhs => .XOR dst lhs rhs) (fun new old => new ^^^ old)
    amo_word_xor_middle_run_into
    (by intro new old; rw [amo_word_extract_xor_low];
        exact congrArg (fun word => (Sail.BitVec.extractLsb new 31 0 : BitVec 32) ^^^ word)
          (sign_extend_64_setWidth_32 old))
    (by decide) rs2 rs1 rd js h (amoxorwProgramCore_doesNotWriteProtectedVRegs rs2 rs1 rd)

/-- Main public theorem for `AMOXOR.W`. -/
def amoxorwProgramEqSailStatement
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (_h : AmoWordProgramEqSailAssumptions amoop.AMOXOR rs2 rs1 rd js) : Prop :=
  System.systemProjectResult
      ((JoltISA.execProgram
        (JoltISA.amoxorwProgramAuto rd rs1 rs2)).run js) =
    (execute_AMO amoop.AMOXOR false false rs2 rs1 4 rd).run js.sail

theorem amoxorwProgram_eq_sail
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (h : AmoWordProgramEqSailAssumptions amoop.AMOXOR rs2 rs1 rd js) :
    amoxorwProgramEqSailStatement rs2 rs1 rd js h := by
  unfold amoxorwProgramEqSailStatement
  rw [amoxorwProgramAuto_eq_core]
  exact amoxorwProgram_core_eq_sail rs2 rs1 rd js h

end AtomicFamily

end
