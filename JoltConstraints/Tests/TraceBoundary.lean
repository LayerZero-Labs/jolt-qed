import JoltConstraints.trace
import Mathlib.Tactic.NormNum

set_option autoImplicit false

namespace TraceBoundaryChecks

-- Regression: an ordinary FENCE cannot be followed by the same fetched row.
example {program : JoltProgram} (trace : JoltTrace program)
    (twoRows : 1 < trace.rows.size)
    (ordinary : program.expandedBytecode[(trace.rows[0]'(by omega)).rowIndex].virtualSequenceRemaining = none)
    (sameIndex : (trace.rows[1]'twoRows).rowIndex = (trace.rows[0]'(by omega)).rowIndex) : False := by
  have step := trace.successor 0 (by omega) twoRows
  simp only [JoltProgramRow.continues, ordinary, Option.getD_none, ne_eq] at step
  exact step.2.2 (congrArg (fun index => program.expandedBytecode[index].address) sameIndex)

-- A compressed source expands into two rows: only its last row is compressed.
def virtualFirst : JoltProgramRow :=
  { instruction := .FENCE
    registerOperandsCanonical := rfl
    isBytecodeTemplate := True.intro
    address := 8
    virtualSequenceRemaining := some 1
    isFirstInSequence := true
    isCompressed := false }

def virtualLast : JoltProgramRow :=
  { instruction := .FENCE
    registerOperandsCanonical := rfl
    isBytecodeTemplate := True.intro
    address := 8
    virtualSequenceRemaining := some 0
    isFirstInSequence := false
    isCompressed := true }

def compressedProgram (state : SailJoltState) : JoltProgram :=
  { expandedBytecode := #[virtualFirst, virtualLast]
    initialState := state }

-- The first helper must seed nextPC with 10, not 12: it uses the source length.
example (state : SailJoltState) (layout : (compressedProgram state).SequenceLayout) :
    (compressedProgram state).sourceLength layout ⟨0, by simp [compressedProgram]⟩ = 2 := by
  rfl

example (state : SailJoltState) (layout : (compressedProgram state).SequenceLayout) :
    ((compressedProgram state).prepareSource layout ⟨0, by simp [compressedProgram]⟩ state).sail.regs.get?
      Register.nextPC = some 10 := by
  simp [JoltProgram.prepareSource, JoltProgram.sourceLength, compressedProgram, virtualFirst,
    virtualLast]

-- Both rows see the same source byte length, with no second PC increment.
example (state : SailJoltState) (layout : (compressedProgram state).SequenceLayout) :
    (compressedProgram state).sourceLength layout ⟨1, by simp [compressedProgram]⟩ = 2 := by
  rfl

-- Within a virtual sequence the complete ISA post-state passes through unchanged.
example {program : JoltProgram} (trace : JoltTrace program)
    (twoRows : 1 < trace.rows.size)
    (continues : program.expandedBytecode[(trace.rows[0]'(by omega)).rowIndex].continues = true) :
    (trace.rows[1]'twoRows).preState = (trace.rows[0]'(by omega)).postState := by
  simpa only [continues, ↓reduceIte] using trace.linked 0 (by omega) twoRows

end TraceBoundaryChecks
