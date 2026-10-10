import JoltConstraints.honest_trace
import JoltConstraints.expansions

/-! Runtime-advice agreement is automatic for rows other than VirtualAdvice.
PR #2039 removes every such row from both SC expansions. These facts do not
interpret virtual registers as emulator reservations. -/

set_option autoImplicit false

namespace JoltConstraints.Soundness

open Sail PreSail LeanRV64D.Functions JoltISA

private theorem withRuntimeAdvice_noAdvice (instruction : Instr)
    (advice : instruction.RuntimeAdvice) (absent : instruction.adviceValue? = none) :
    (instruction.withRuntimeAdvice advice).adviceValue? = none := by
  cases instruction <;> first | exact absent | cases absent

/-- A row without VirtualAdvice has no recorded or honest runtime-advice value,
independently of how the trace prefix was constructed. -/
theorem runtimeAdvice_agrees_of_noAdvice (program : Rv64ProgramImage SourceInstruction)
    {bytecode : Array JoltInstructionRow} (rows : Array (TraceRow bytecode))
    (n : Fin rows.size)
    (absent : bytecode[rows[n].rowIndex].instruction.adviceValue? = none) :
    rows[n].someTracerAdvice? = honestTracerAdviceAtStepN program rows n := by
  have recorded := withRuntimeAdvice_noAdvice _ rows[n].runtimeAdvice absent
  change (bytecode[rows[n].rowIndex].instruction.withRuntimeAdvice
    rows[n].runtimeAdvice).adviceValue? = _
  rw [recorded]
  simp only [honestTracerAdviceAtStepN, Array.getElem?_eq_getElem n.isLt,
    bind, Option.bind_some]
  change none = bytecode[rows[n].rowIndex].instruction.adviceValue?.bind _
  rw [absent]
  rfl

/-- Every row of the generated SC.W expansion has no runtime advice, for either
destination branch and all source-register aliases. -/
theorem scw_noAdvice (rd rs1 rs2 : regidx) (instruction : Instr)
    (member : instruction ∈ (scwProgramAuto rd rs1 rs2).instrs) :
    instruction.adviceValue? = none := by
  have all : ((scwProgramAuto rd rs1 rs2).instrs.all
      fun instruction => instruction.adviceValue?.isNone) = true := by
    unfold scwProgramAuto
    split <;> rfl
  exact Option.isNone_iff_eq_none.mp (List.all_eq_true.mp all instruction member)

/-- Every row of the generated SC.D expansion has no runtime advice, for either
destination branch and all source-register aliases. -/
theorem scd_noAdvice (rd rs1 rs2 : regidx) (instruction : Instr)
    (member : instruction ∈ (scdProgramAuto rd rs1 rs2).instrs) :
    instruction.adviceValue? = none := by
  have all : ((scdProgramAuto rd rs1 rs2).instrs.all
      fun instruction => instruction.adviceValue?.isNone) = true := by
    unfold scdProgramAuto
    split <;> rfl
  exact Option.isNone_iff_eq_none.mp (List.all_eq_true.mp all instruction member)

end JoltConstraints.Soundness
