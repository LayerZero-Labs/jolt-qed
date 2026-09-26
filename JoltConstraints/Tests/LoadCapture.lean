import JoltConstraints.trace

set_option autoImplicit false

namespace LoadCaptureChecks

-- A load to x0 captures its result in the rewritten virtual destination.
example (preState postState : SailJoltState)
    (readNine : JoltISA.memoryWord? preState
      (JoltISA.sourceValue (.vreg 41) preState) = some 9)
    (capturedZero : postState.vregs JoltISA.rdZeroRewriteVReg = 0) :
    ¬ ((JoltISA.Instr.LD .normal (.xreg (.Regidx 0)) (.vreg 41) 0).rewriteNative).LoadCaptureMatches
      preState postState := by
  intro hMatches
  have hRead : JoltISA.memoryWord? preState (preState.vregs (41#7)) =
      some (9#64) := by
    simpa [JoltISA.sourceValue] using readNine
  simp [JoltISA.Instr.rewriteNative, JoltISA.Instr.LoadCaptureMatches,
    JoltISA.sourceValue, HonestWitness.capturedDestinationValue,
    HonestWitness.capturedDestination, JoltISA.sideEffectingDst,
    JoltISA.sideEffectingRdZeroDst, JoltISA.isX0, capturedZero, hRead] at hMatches

-- The row type requires that virtual destination to hold the loaded word.
example {program : JoltProgram} (row : JoltTraceRow program)
    (isLoad : program.expandedBytecode[row.rowIndex].expandedInstruction =
      .LD .normal (.vreg JoltISA.rdZeroRewriteVReg) (.vreg 41) 0)
    (readNine : JoltISA.memoryWord? row.preState
      (JoltISA.sourceValue (.vreg 41) row.preState) = some 9) :
    row.postState.vregs JoltISA.rdZeroRewriteVReg = 9 := by
  have captured := row.loadCaptureMatches
  rw [isLoad] at captured
  have hRead : JoltISA.memoryWord? row.preState
      (row.preState.vregs (41#7)) = some (9#64) := by
    simpa [JoltISA.sourceValue] using readNine
  simp [JoltISA.Instr.LoadCaptureMatches, JoltISA.sourceValue,
    HonestWitness.capturedDestinationValue, HonestWitness.capturedDestination] at captured
  simp [hRead] at captured
  exact captured.symm

-- A virtual destination with the captured word is accepted.
example (preState postState : SailJoltState)
    (readNine : JoltISA.memoryWord? preState
      (JoltISA.sourceValue (.vreg 41) preState) = some 9)
    (writtenNine : postState.vregs 40 = 9) :
    (JoltISA.Instr.LD .normal (.vreg 40) (.vreg 41) 0).LoadCaptureMatches
      preState postState := by
  simpa [JoltISA.Instr.LoadCaptureMatches, JoltISA.sourceValue] using
    (readNine.trans (congrArg some writtenNine.symm))

-- Loading zero into x0 passes when the virtual destination also holds zero.
example (preState postState : SailJoltState)
    (readZero : JoltISA.memoryWord? preState
      (JoltISA.sourceValue (.vreg 41) preState) = some 0)
    (capturedZero : postState.vregs JoltISA.rdZeroRewriteVReg = 0) :
    ((JoltISA.Instr.LD .normal (.xreg (.Regidx 0)) (.vreg 41) 0).rewriteNative).LoadCaptureMatches
      preState postState := by
  simpa [JoltISA.Instr.rewriteNative, JoltISA.Instr.LoadCaptureMatches,
    JoltISA.sourceValue, HonestWitness.capturedDestinationValue,
    HonestWitness.capturedDestination, JoltISA.sideEffectingDst,
    JoltISA.sideEffectingRdZeroDst, JoltISA.isX0, capturedZero] using readZero

-- The conversion check alone does not exclude a synthetic ADDI x0, vreg row.
example (preState postState : SailJoltState) :
    (JoltISA.Encoded.ADDI (.xreg (.Regidx 0)) (.vreg 39) 0).LoadCaptureMatches
      preState postState := True.intro

end LoadCaptureChecks
