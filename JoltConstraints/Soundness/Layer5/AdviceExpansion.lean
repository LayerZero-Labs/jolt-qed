import JoltConstraints.Soundness.Layer5.Program
import JoltConstraints.Soundness.Layer5.NarrowAdvice
import JoltBytecode.InstructionEquivalence.ProofSupport.NativeDispatch
import JoltConstraints.expansions

/-! Full execution of the generated narrow-advice expansions. The source-level
x0 case writes temporary register 40; the ordinary case writes the requested
architectural register. No initial register-presence assumption is needed:
the load writes the register before either arithmetic row reads it. -/

set_option autoImplicit false

namespace JoltConstraints.Soundness

open Sail PreSail LeanRV64D.Functions JoltISA

/-- The source operand for the register used by a side-effecting destination rewrite. -/
def adviceReadSource (rd : regidx) : Src :=
  if isX0 rd then .vreg rdZeroRewriteVReg else .xreg rd

/-- The three rows shared by the narrow-advice expansions. The generated
program equalities below establish their actual widths and operands. -/
def narrowAdviceProgram (rd : regidx) (byteCount : BitVec 64) (width : Nat) : Program :=
  .instr (.VirtualAdviceLoad (sideEffectingRdZeroDst rd) byteCount) <|
  .instr (.VirtualMULI (sideEffectingRdZeroDst rd) (adviceReadSource rd)
    (slliMultiplier (BitVec.ofNat 6 (64 - width)))) <|
  .instr (.VirtualSRAI (sideEffectingRdZeroDst rd) (adviceReadSource rd)
    (sraiBitmask (BitVec.ofNat 6 (64 - width)))) <|
  .done RETIRE_SUCCESS

/-- Advance the tape cursor and perform the expansion's final destination
write. All other state components are retained by the existing write model. -/
noncomputable def afterAdviceLoad (pre : SailJoltState) (rd : regidx)
    (byteCount : Nat) (value : BitVec 64) : SailJoltState :=
  NativeDispatch.afterDst
    { pre with adviceTape :=
      { pre.adviceTape with readPosition := pre.adviceTape.readPosition + byteCount } } rd value

private theorem read_afterDst (rd : regidx) (value : BitVec 64) (pre : SailJoltState) :
    readSrc (adviceReadSource rd) (NativeDispatch.afterDst pre rd value) =
      .ok value (NativeDispatch.afterDst pre rd value) := by
  unfold adviceReadSource NativeDispatch.afterDst
  split
  · simp only [readSrc_vreg, readVReg_run, ↓reduceIte]
  · rename_i nonzero
    have rdNe : rd ≠ regidx.Regidx 0 := by
      intro zero
      subst rd
      exact nonzero rfl
    simp only [readSrc_xreg, liftSail, rX_after_stateAfterWrite rd value pre.sail rdNe]

private theorem afterDst_afterDst (rd : regidx) (first last : BitVec 64)
    (pre : SailJoltState) :
    NativeDispatch.afterDst (NativeDispatch.afterDst pre rd first) rd last =
      NativeDispatch.afterDst pre rd last := by
  unfold NativeDispatch.afterDst
  split
  · congr 1
    funext register
    by_cases same : register = rdZeroRewriteVReg <;> simp only [same, ite_true, ite_false]
  · simp only [stateAfterWrite_stateAfterWrite]

private theorem adviceLoad_step (rd : regidx) (byteCount answer : BitVec 64)
    (pre : SailJoltState)
    (valid : byteCount.toNat = 1 ∨ byteCount.toNat = 2 ∨
      byteCount.toNat = 4 ∨ byteCount.toNat = 8) :
    execWithTapeAnswer (.VirtualAdviceLoad (sideEffectingRdZeroDst rd) byteCount) answer pre =
      .ok RETIRE_SUCCESS (afterAdviceLoad pre rd byteCount.toNat answer) := by
  simp only [execWithTapeAnswer, valid, ↓reduceIte, bind, EStateM.bind,
    NativeDispatch.writeDst_run, pure, EStateM.pure, afterAdviceLoad]

private theorem muli_afterDst (rd : regidx) (value multiplier ignored : BitVec 64)
    (pre : SailJoltState) :
    execWithTapeAnswer
      (.VirtualMULI (sideEffectingRdZeroDst rd) (adviceReadSource rd) multiplier)
      ignored (NativeDispatch.afterDst pre rd value) =
      .ok RETIRE_SUCCESS (NativeDispatch.afterDst pre rd (jolt_virtual_muli_value value multiplier)) := by
  simp only [execWithTapeAnswer, execInstr, bind, EStateM.bind, read_afterDst,
    NativeDispatch.writeDst_run, pure, EStateM.pure, afterDst_afterDst]

private theorem srai_afterDst (rd : regidx) (value ignored : BitVec 64)
    (mask : Nat) (pre : SailJoltState) :
    execWithTapeAnswer
      (.VirtualSRAI (sideEffectingRdZeroDst rd) (adviceReadSource rd) mask)
      ignored (NativeDispatch.afterDst pre rd value) =
      .ok RETIRE_SUCCESS (NativeDispatch.afterDst pre rd (jolt_virtual_srai_value value mask)) := by
  simp only [execWithTapeAnswer, execInstr, bind, EStateM.bind, read_afterDst,
    NativeDispatch.writeDst_run, pure, EStateM.pure, afterDst_afterDst]

/-- The load/multiply/shift sequence succeeds and retains exactly the signed
low-width part of its first answer. Later answers have no effect. -/
theorem narrowAdviceProgram_exec (rd : regidx) (byteCount : BitVec 64) (width : Nat)
    (valid : byteCount.toNat = 1 ∨ byteCount.toNat = 2 ∨
      byteCount.toNat = 4 ∨ byteCount.toNat = 8)
    (positive : 0 < width) (fits : width ≤ 64)
    (answers : Nat → BitVec 64) (pre : SailJoltState) :
    execProgramWithTapeAnswers (narrowAdviceProgram rd byteCount width) answers pre =
      .ok RETIRE_SUCCESS
        (afterAdviceLoad pre rd byteCount.toNat ((answers 0).setWidth width |>.signExtend 64)) := by
  unfold narrowAdviceProgram
  rw [execProgramWithTapeAnswers_cons _ _ answers pre _
    (adviceLoad_step rd byteCount (answers 0) pre valid)]
  unfold afterAdviceLoad
  rw [execProgramWithTapeAnswers_cons _ _ _ _ _ (muli_afterDst ..)]
  rw [execProgramWithTapeAnswers_cons _ _ _ _ _ (srai_afterDst ..)]
  simp only [execProgramWithTapeAnswers, pure, EStateM.pure,
    narrowAdvice_value _ width positive fits]

private theorem advicelb_program (rd : regidx) :
    advicelbProgramAuto rd = narrowAdviceProgram rd 1 8 := by
  unfold advicelbProgramAuto narrowAdviceProgram sideEffectingRdZeroDst adviceReadSource
  split <;> rfl

private theorem advicelh_program (rd : regidx) :
    advicelhProgramAuto rd = narrowAdviceProgram rd 2 16 := by
  unfold advicelhProgramAuto narrowAdviceProgram sideEffectingRdZeroDst adviceReadSource
  split <;> rfl

private theorem advicelw_program (rd : regidx) :
    advicelwProgramAuto rd = narrowAdviceProgram rd 4 32 := by
  unfold advicelwProgramAuto narrowAdviceProgram sideEffectingRdZeroDst adviceReadSource
  split <;> rfl

/-- AdviceLB expands to the load and two arithmetic rows, including when its
destination is x0. The expansion is a sequence, not a discarded write. -/
theorem advicelb_expansion (rd : regidx) :
    SourceInstruction.expand (.jolt (.AdviceLB rd)) =
      some (.sequence (narrowAdviceProgram rd 1 8).instrs) := by
  change some (ExpandedSource.ofProgram (advicelbProgramAuto rd)) = _
  rw [advicelb_program]
  rfl

/-- AdviceLH's generated sequence reads two bytes and uses a 16-bit result. -/
theorem advicelh_expansion (rd : regidx) :
    SourceInstruction.expand (.jolt (.AdviceLH rd)) =
      some (.sequence (narrowAdviceProgram rd 2 16).instrs) := by
  change some (ExpandedSource.ofProgram (advicelhProgramAuto rd)) = _
  rw [advicelh_program]
  rfl

/-- AdviceLW's generated sequence reads four bytes and uses a 32-bit result. -/
theorem advicelw_expansion (rd : regidx) :
    SourceInstruction.expand (.jolt (.AdviceLW rd)) =
      some (.sequence (narrowAdviceProgram rd 4 32).instrs) := by
  change some (ExpandedSource.ofProgram (advicelwProgramAuto rd)) = _
  rw [advicelw_program]
  rfl

/-- The actual AdviceLB program succeeds, advances by one byte, and writes
the sign-extended low byte to its rewritten destination. -/
theorem advicelb_exec (rd : regidx) (answers : Nat → BitVec 64) (pre : SailJoltState) :
    execProgramWithTapeAnswers (advicelbProgramAuto rd) answers pre =
      .ok RETIRE_SUCCESS (afterAdviceLoad pre rd 1 ((answers 0).setWidth 8 |>.signExtend 64)) := by
  rw [advicelb_program]
  exact narrowAdviceProgram_exec rd 1 8 (by decide) (by decide) (by decide) answers pre

/-- The actual AdviceLH program succeeds, advances by two bytes, and writes
the sign-extended low halfword to its rewritten destination. -/
theorem advicelh_exec (rd : regidx) (answers : Nat → BitVec 64) (pre : SailJoltState) :
    execProgramWithTapeAnswers (advicelhProgramAuto rd) answers pre =
      .ok RETIRE_SUCCESS (afterAdviceLoad pre rd 2 ((answers 0).setWidth 16 |>.signExtend 64)) := by
  rw [advicelh_program]
  exact narrowAdviceProgram_exec rd 2 16 (by decide) (by decide) (by decide) answers pre

/-- The actual AdviceLW program succeeds, advances by four bytes, and writes
the sign-extended low word to its rewritten destination. -/
theorem advicelw_exec (rd : regidx) (answers : Nat → BitVec 64) (pre : SailJoltState) :
    execProgramWithTapeAnswers (advicelwProgramAuto rd) answers pre =
      .ok RETIRE_SUCCESS (afterAdviceLoad pre rd 4 ((answers 0).setWidth 32 |>.signExtend 64)) := by
  rw [advicelw_program]
  exact narrowAdviceProgram_exec rd 4 32 (by decide) (by decide) (by decide) answers pre

end JoltConstraints.Soundness
