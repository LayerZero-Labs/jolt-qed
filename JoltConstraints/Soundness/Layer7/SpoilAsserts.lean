import JoltConstraints.Soundness.Layer7.StallSuffix
import JoltConstraints.Soundness.Layer5.AssertionsBinary

set_option autoImplicit false

open Sail PreSail LeanRV64D.Functions JoltISA

namespace JoltInstance

/-- A spoil assert is an equality assertion with a nonzero immediate.
Every operand of such a row in one source instruction's expansion lies outside
instruction temporaries 40–47; for example, a guest's custom assertion reads x1
and x2, whereas built-in expansions introduce no nonzero-immediate assertions.
See jolt/crates/jolt-program/src/image/decode.rs (`decode_custom`,
`format_b_operands`) and jolt/crates/jolt-program/src/asm.rs
(`__jolt_asm_stmt!`, `assert_eq`) at 5def437f. -/
theorem source_spoil_assert_read_not_temporary
    (source : SourceInstructionRow SourceInstruction) (rows : List JoltInstructionRow)
    (expanded : expand_instruction source = some rows)
    (row : JoltInstructionRow) (member : row ∈ rows)
    (lhs rhs : Src) (imm : BitVec 128)
    (instructionIs : row.instruction = .VirtualAssertEQ lhs rhs imm)
    (nonzero : imm ≠ 0) :
    ∀ operand ∈ [lhs, rhs],
      ¬ IsInstructionTemporary (TraceWitness.sourceRegisterAddress operand) := by
  sorry

/-- Every spoil-assert operand in expanded bytecode lies outside instruction
temporaries 40–47, independently of any witness or execution.
For example, a guest assertion's x1 operand remains architectural after stamping.
See jolt/crates/jolt-program/src/expand/materialize.rs
(`ExpansionState::dispatch_source`) at 5def437f. -/
theorem expanded_spoil_assert_read_not_temporary
    (program : Rv64ProgramImage SourceInstruction) (bytecode : Array JoltInstructionRow)
    (expanded : expand_program program = some bytecode)
    (row : JoltInstructionRow) (member : row ∈ bytecode.toList)
    (lhs rhs : Src) (imm : BitVec 128)
    (instructionIs : row.instruction = .VirtualAssertEQ lhs rhs imm)
    (nonzero : imm ≠ 0) :
    ∀ operand ∈ [lhs, rhs],
      ¬ IsInstructionTemporary (TraceWitness.sourceRegisterAddress operand) := by
  obtain ⟨source, _, rows, sourceExpanded, rowIn⟩ :=
    expand_program_source_of_row program bytecode expanded row member
  exact source_spoil_assert_read_not_temporary source rows sourceExpanded row rowIn
    lhs rhs imm instructionIs nonzero

/-- Represented source values and the selected assertion's constraints make
every spoil assert pass in a relaxed-answer run.
Representation compares operands outside instruction temporaries; the expansion
fact above supplies precisely that condition.
For example, an executed custom equality assertion with immediate 2 must read
equal pre-state words even though the tracer would only warn if they differed.
See jolt/tracer/src/instruction/virtual_assert_eq.rs (`VirtualAssertEQ::exec`)
and jolt/crates/jolt-riscv/src/instructions/assert/assert_eq.rs (`AssertEq`)
at 5def437f. -/
theorem represented_spoil_asserts_pass
    {F : Type} [Field F] (joltField : JoltField F)
    (joltInstance : JoltInstance SourceInstruction)
    {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (equations : JoltConstraints.ConstraintEquations context.bytecode context.initialRam
      context.io context.entry witness)
    (run : JoltConstraints.Soundness.UntrustedAnswerRun joltInstance privateInputs)
    (bytecodeEq : run.bytecode = context.bytecode)
    (represented : RepresentsRows witness run.toTrace) :
    run.toTrace.SpoilAssertsPass := by
  intro traceRow member lhs rhs imm instructionIs nonzero
  obtain ⟨index, inRun, rfl⟩ := Array.mem_iff_getElem.mp member
  let cycle : Fin params.traceLength :=
    ⟨index, lt_of_lt_of_le inRun represented.rowsBound⟩
  have selected := selected_represented_row joltField joltInstance privateInputs
    witness context equations run bytecodeEq represented cycle inRun
  have rowIs : JoltConstraints.bytecodeRow context.bytecode
      (run.rows[index].rowIndex.val + 1) = some run.bytecode[run.rows[index].rowIndex] := by
    rw [← bytecodeEq]
    simp [JoltConstraints.bytecodeRow]
  have nonTemporary := expanded_spoil_assert_read_not_temporary joltInstance.program
    run.bytecode run.expands run.bytecode[run.rows[index].rowIndex]
    (Array.getElem_mem_toList run.rows[index].rowIndex.isLt)
    lhs rhs imm instructionIs nonzero
  have left := represented.rs1 cycle inRun (by
    simpa only [cycle, instructionIs, JoltConstraints.bytecodeRs1Register,
      Option.mem_some_iff, forall_eq'] using nonTemporary lhs (by simp))
  have right := represented.rs2 cycle inRun (by
    simpa only [cycle, instructionIs, JoltConstraints.bytecodeRs2Register,
      Option.mem_some_iff, forall_eq'] using nonTemporary rhs (by simp))
  simp only [TraceWitness.Rs1Value, TraceWitness.Rs2Value, cycle,
    inRun, ↓reduceDIte, ← Fin.getElem_fin, instructionIs] at left right
  have inputs := JoltConstraints.Soundness.instructionInputs_of_selected_bytecode
    (JoltConstraints.Soundness.two_pow_127_lt_char joltField)
    context equations cycle _ selected _ rowIs
  simp only [instructionIs, JoltMetadata.instructionFlag, Bool.false_eq_true,
    ↓reduceIte, add_zero] at inputs
  exact JoltConstraints.Soundness.binaryAssertion_passes_of_inputs joltField
    context equations selected rowIs .eq instructionIs
    (sourceValue lhs run.rows[index].preState) (sourceValue rhs run.rows[index].preState)
    (inputs.1.trans left) (inputs.2.trans right)

end JoltInstance
