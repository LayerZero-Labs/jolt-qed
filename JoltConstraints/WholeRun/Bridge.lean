import JoltConstraints.WholeRun.Basic

/-!
The bytecode image and the instruction step theorems use the same generated
programs, with the image's advice placeholders replaced by honest runtime advice.
Jolt's tracer supplies that advice in `tracer/src/instruction/mod.rs`
(`trace_inline_sequence_with_advice`) at the pin recorded in `methods/soundness.md`.
-/

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail
  LeanRV64D LeanRV64D.Functions

set_option autoImplicit false

noncomputable section

namespace WholeRun

/-- Replace a division or remainder instruction's advice operand by the value
computed by `SourceInstruction.honestTracerAdvice` in the starting state `js`.
For example, `DIV rd rs1 rs2 q` receives the signed quotient of `rs1` and `rs2`,
independently of its placeholder `q`; instructions such as `ADD` are unchanged. -/
def honestInstr (i : RiscvInstruction) (js : SailJoltState) : RiscvInstruction :=
  match i with
  | .DIV rd rs1 rs2 _ => .DIV rd rs1 rs2
      (sail_div_value (JoltISA.sourceValue (.xreg rs1) js)
        (JoltISA.sourceValue (.xreg rs2) js) false)
  | .DIVU rd rs1 rs2 _ => .DIVU rd rs1 rs2
      (sail_div_value (JoltISA.sourceValue (.xreg rs1) js)
        (JoltISA.sourceValue (.xreg rs2) js) true)
  | .REM rd rs1 rs2 _ => .REM rd rs1 rs2
      (rem_advice_value (JoltISA.sourceValue (.xreg rs1) js)
        (JoltISA.sourceValue (.xreg rs2) js))
  | .REMU rd rs1 rs2 _ => .REMU rd rs1 rs2
      (sail_div_value (JoltISA.sourceValue (.xreg rs1) js)
        (JoltISA.sourceValue (.xreg rs2) js) true)
  | .DIVW rd rs1 rs2 _ => .DIVW rd rs1 rs2
      (divw_advice_value (JoltISA.sourceValue (.xreg rs1) js)
        (JoltISA.sourceValue (.xreg rs2) js))
  | .DIVUW rd rs1 rs2 _ => .DIVUW rd rs1 rs2
      (sail_divuw_advice (JoltISA.sourceValue (.xreg rs1) js)
        (JoltISA.sourceValue (.xreg rs2) js))
  | .REMW rd rs1 rs2 _ => .REMW rd rs1 rs2
      (remw_advice_value (JoltISA.sourceValue (.xreg rs1) js)
        (JoltISA.sourceValue (.xreg rs2) js))
  | .REMUW rd rs1 rs2 _ => .REMUW rd rs1 rs2
      (sail_divuw_advice (JoltISA.sourceValue (.xreg rs1) js)
        (JoltISA.sourceValue (.xreg rs2) js))
  | other => other

/-- Honest advice depends on the opcode and source operands, so replacing the
placeholder by that advice leaves the advice list unchanged.
For example, both versions of `DIV rd rs1 rs2 q` request the same quotient. -/
theorem honestTracerAdvice_eq (i : RiscvInstruction) (js : SailJoltState) :
    (SourceInstruction.riscv i).honestTracerAdvice js =
      (SourceInstruction.riscv (honestInstr i js)).honestTracerAdvice js := by
  cases i <;> rfl

/-- Forget expansion metadata, retaining the rows in execution order.
For example, a native `ADD` becomes the singleton list containing that `ADD`. -/
private def expandedInstrs : ExpandedSource → List JoltISA.Instr
  | .native instruction => [instruction]
  | .sequence instructions => instructions

private theorem stamp_instructions (address : BitVec 64) (compressed : Bool)
    (instrs : List JoltISA.Instr) :
    (stamp_sequence address compressed instrs).map (·.instruction) = instrs := by
  simp only [stamp_sequence, List.map_map, Function.comp_def]
  exact List.zipIdx_map_fst 0 instrs

private theorem blockInstrs_eq {row : SourceInstructionRow SourceInstruction}
    {expanded : ExpandedSource} (he : row.instruction.expand = some expanded)
    {js : SailJoltState} {instrs : List JoltISA.Instr}
    (h : blockInstrs row js = some instrs) :
    instrs = patchAdvice (row.instruction.honestTracerAdvice js) (expandedInstrs expanded) := by
  cases expanded with
  | native instruction =>
      simpa only [blockInstrs, expand_instruction, he, Option.map_some,
        List.map_cons, List.map_nil, Option.some.injEq, expandedInstrs] using h.symm
  | sequence instructions =>
      simp only [blockInstrs, expand_instruction, he] at h
      split at h
      · cases h
      · simpa only [Option.map_some, stamp_instructions, Option.some.injEq,
          expandedInstrs] using h.symm

private theorem exec_singleton (instruction : JoltISA.Instr) (js : SailJoltState) :
    JoltISA.execProgram (JoltISA.Program.seq [instruction]) js =
      JoltISA.execInstr instruction js := by
  simp only [JoltISA.Program.seq, List.foldr, JoltISA.execProgram,
    bind, EStateM.bind, pure]
  cases JoltISA.execInstr instruction js with
  | error e state => rfl
  | ok result state => cases result <;> rfl

private theorem patchAdvice_nil (instrs : List JoltISA.Instr) :
    patchAdvice [] instrs = instrs := by
  induction instrs with
  | nil => rfl
  | cons instruction rest ih =>
      unfold patchAdvice
      split <;> simp_all only [List.headD_nil, List.tail_nil, List.cons.injEq, and_self]

-- Every generated pure program already includes the destination-zero no-op.
-- The remaining comparison is syntactic, so execution errors agree as well.
private theorem expanded_exec (i : RiscvInstruction) (js : SailJoltState)
    (expanded : ExpandedSource) (he : (SourceInstruction.riscv i).expand = some expanded) :
    JoltISA.execProgram (JoltISA.Program.seq
      (patchAdvice ((SourceInstruction.riscv i).honestTracerAdvice js)
        (expandedInstrs expanded))) js =
      RiscvInstruction.joltRun (honestInstr i js) js := by
  cases i <;> simp only [SourceInstruction.expand, Option.some.injEq] at he <;> subst expanded
  all_goals
    simp only [honestInstr, SourceInstruction.honestTracerAdvice, RiscvInstruction.joltRun,
      JoltISA.execLUI, ExpandedSource.ofNative, ExpandedSource.ofProgram,
      ExpandedSource.ofPureProgram,
      JoltISA.divProgramAuto, JoltISA.divuProgramAuto, JoltISA.lbProgramAuto,
      JoltISA.lbuProgramAuto, JoltISA.lhProgramAuto, JoltISA.lhuProgramAuto,
      JoltISA.lwProgramAuto, JoltISA.mulhProgramAuto, JoltISA.mulhsuProgramAuto,
      JoltISA.remProgramAuto, JoltISA.remuProgramAuto, JoltISA.sbProgramAuto,
      JoltISA.shProgramAuto, JoltISA.sllProgramAuto, JoltISA.slliProgramAuto,
      JoltISA.sraProgramAuto, JoltISA.sraiProgramAuto, JoltISA.srlProgramAuto,
      JoltISA.srliProgramAuto, JoltISA.swProgramAuto, JoltISA.slliwProgramAuto,
      JoltISA.srliwProgramAuto, JoltISA.sraiwProgramAuto, JoltISA.sllwProgramAuto,
      JoltISA.srlwProgramAuto, JoltISA.srawProgramAuto, JoltISA.lwuProgramAuto,
      JoltISA.divuwProgramAuto, JoltISA.divwProgramAuto, JoltISA.remuwProgramAuto,
      JoltISA.remwProgramAuto, JoltISA.lrwProgramAuto, JoltISA.scwProgramAuto,
      JoltISA.amoswapwProgramAuto, JoltISA.amoaddwProgramAuto, JoltISA.amoandwProgramAuto,
      JoltISA.amoorwProgramAuto, JoltISA.amoxorwProgramAuto, JoltISA.amominwProgramAuto,
      JoltISA.amomaxwProgramAuto, JoltISA.amominuwProgramAuto, JoltISA.amomaxuwProgramAuto,
      JoltISA.lrdProgramAuto, JoltISA.scdProgramAuto, JoltISA.amoswapdProgramAuto,
      JoltISA.amoadddProgramAuto, JoltISA.amoanddProgramAuto, JoltISA.amoordProgramAuto,
      JoltISA.amoxordProgramAuto, JoltISA.amomindProgramAuto, JoltISA.amomaxdProgramAuto,
      JoltISA.amominudProgramAuto, JoltISA.amomaxudProgramAuto,
      JoltISA.ecallProgram, JoltISA.ebreakProgram, JoltISA.mretProgram,
      JoltISA.csrrwProgram, JoltISA.csrrsProgram, JoltISA.pureWritebackRdZeroProgram]
  all_goals
    (try split_ifs) <;>
      simp only [expandedInstrs, JoltISA.Program.instrs, patchAdvice_nil, patchAdvice,
        JoltISA.Program.seq, List.foldr, List.headD_cons]
  all_goals exact exec_singleton _ _

/-- Running a source instruction's expanded rows with honest advice has the same
result after CSR projection as its instruction theorem's `joltRun` program.
For example, an image `DIV` with a placeholder quotient runs exactly the rows
of `joltRun` with the quotient computed from `js`, including any execution error. -/
theorem blockInstrs_project (i : RiscvInstruction) (address : BitVec 64) (compressed : Bool)
    (js : SailJoltState) (instrs : List JoltISA.Instr)
    (h : blockInstrs ⟨address, .riscv i, compressed⟩ js = some instrs) :
    System.systemProjectResult (JoltISA.execProgram (JoltISA.Program.seq instrs) js) =
      System.systemProjectResult (RiscvInstruction.joltRun (honestInstr i js) js) := by
  cases he : (SourceInstruction.riscv i).expand with
  | none => simp only [blockInstrs, expand_instruction, he, Option.map_none] at h; cases h
  | some expanded =>
      rw [blockInstrs_eq he h, expanded_exec i js expanded he]

end WholeRun
