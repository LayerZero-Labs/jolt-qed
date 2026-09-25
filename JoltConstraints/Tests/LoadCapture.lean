import JoltConstraints.trace

set_option autoImplicit false

namespace LoadCaptureChecks

-- Rust rejects a successful raw LD x0 when memory contains a nonzero word:
-- the captured destination is zero, while the captured RAM value is nine.
example (preState postState : SailJoltState)
    (readNine : JoltISA.memoryWord? preState
      (JoltISA.sourceValue (.vreg 41) preState) = some 9) :
    ¬ (JoltISA.Instr.LD .normal (.xreg (.Regidx 0)) (.vreg 41) 0).LoadCaptureMatches
      preState postState := by
  simp [JoltISA.Instr.LoadCaptureMatches, JoltISA.sourceValue] at readNine ⊢
  simp [readNine]

-- The condition is enforced by the row type, not merely stated as a helper.
example {program : JoltProgram} (row : JoltTraceRow program)
    (isLoad : program.expandedBytecode[row.rowIndex].instruction =
      .LD .normal (.xreg (.Regidx 0)) (.vreg 41) 0)
    (readNine : JoltISA.memoryWord? row.preState
      (JoltISA.sourceValue (.vreg 41) row.preState) = some 9) : False := by
  have captured := row.loadCaptureMatches
  rw [isLoad] at captured
  simp [JoltISA.Instr.LoadCaptureMatches, JoltISA.sourceValue] at captured readNine
  rw [readNine] at captured
  contradiction

-- A virtual destination with the captured word is accepted.
example (preState postState : SailJoltState)
    (readNine : JoltISA.memoryWord? preState
      (JoltISA.sourceValue (.vreg 41) preState) = some 9)
    (writtenNine : postState.vregs 40 = 9) :
    (JoltISA.Instr.LD .normal (.vreg 40) (.vreg 41) 0).LoadCaptureMatches
      preState postState := by
  simpa [JoltISA.Instr.LoadCaptureMatches, JoltISA.sourceValue] using
    (readNine.trans (congrArg some writtenNine.symm))

-- Loading zero into x0 passes the same conversion check.
example (preState postState : SailJoltState)
    (readZero : JoltISA.memoryWord? preState
      (JoltISA.sourceValue (.vreg 41) preState) = some 0) :
    (JoltISA.Instr.LD .normal (.xreg (.Regidx 0)) (.vreg 41) 0).LoadCaptureMatches
      preState postState := by
  simpa [JoltISA.Instr.LoadCaptureMatches, JoltISA.sourceValue] using readZero

-- The conversion check does not exclude Rust's CSRRS-generated ADDI x0 row.
example (preState postState : SailJoltState) :
    (JoltISA.Encoded.ADDI (.xreg (.Regidx 0)) (.vreg 39) 0).LoadCaptureMatches
      preState postState := True.intro

end LoadCaptureChecks
