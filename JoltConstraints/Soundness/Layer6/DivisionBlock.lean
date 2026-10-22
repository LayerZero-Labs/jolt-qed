import JoltConstraints.Soundness.Layer6.DivisionAppend

/-! Complete the division block from witness and honest generated runs. -/

set_option autoImplicit false

namespace JoltInstance

open JoltConstraints.Soundness
open Sail PreSail LeanRV64D.Functions JoltISA

/-- Construct the honest generated run from the same prepared state, using
`*Program_concrete`, and compare its final state with the witness-advice run.
The supplied Sail result is step 3; the remaining equalities require frames
for this arithmetic-only program, including virtual registers outside 40–47.
Use `StatePreservation.Preserves` for those frames; the general device-setup
frame alone does not establish equality of every device field.
For example, REM of 7 by zero with witness quotient 5 is replaced by quotient
0, preserving destination 7, PC, RAM, device, tape and persistent registers. -/
theorem division_program_honest (kind : DivisionKind) (rd rs1 rs2 : regidx)
    (nonzero : rd ≠ .Regidx 0) (q : BitVec 64) (pre witnessPost : SailJoltState)
    (present : AllRegistersPresent pre.sail)
    (runs : Program.Run (kind.program rd rs1 rs2 q) pre witnessPost)
    (result : witnessPost.sail = stateAfterWrite pre.sail rd
      (kind.result (sourceValue (.xreg rs1) pre) (sourceValue (.xreg rs2) pre))) :
    ∃ honestPost : SailJoltState,
      Program.Run (kind.program rd rs1 rs2 (kind.honestAdvice rd rs1 rs2 pre)) pre honestPost ∧
      DivisionFinalAgreement witnessPost honestPost := by
  sorry

/-- Split the certified honest program run into rows and append them to the
original prefix, transferring the candidate's represented observations and
completed expansion invariant.
Only persistent operands are compared inside the block; division programs
write their architectural destination last, and both executions share the
prepared start and their final state outside temporaries.
The source lookup identifies the honest advice at every appended row, and
retaining the old rows preserves their honest-advice values.
For example, the new nine REM rows carry quotient 0 instead of 5 while their
PCs, RAM addresses and non-temporary operands still match the witness. -/
theorem division_append_honest {F : Type} [Field F]
    {joltInstance : JoltInstance SourceInstruction} {params : WitnessParams}
    {privateInputs : JoltPrivateInputs} (witness : WitnessType F params)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (run candidate : UntrustedAnswerRun joltInstance privateInputs)
    (first : Fin context.bytecode.size)
    (state : ExpansionState witness context run first 0)
    (kind : DivisionKind) (rd rs1 rs2 : regidx) (placeholder : BitVec 64)
    (nonzero : rd ≠ .Regidx 0)
    (source : joltInstance.program.instructionAt context.bytecode[first].address =
      some (kind.source rd rs1 rs2 placeholder))
    (count : (expansionInstructions context.bytecode first).length =
      expansionRowCount context.bytecode first)
    (shape : ArithmeticAdviceSequence (expansionInstructions context.bytecode first)
      (kind.program rd rs1 rs2))
    (pre honestPost : SailJoltState)
    (entry : ∃ next : Fin run.bytecode.size, next.val = first.val ∧ run.NextStep next pre)
    (extendsRun : RunExtends run candidate)
    (size : candidate.rows.size = run.rows.size + expansionRowCount context.bytecode first)
    (complete : ExpansionState witness context candidate first
      (expansionRowCount context.bytecode first))
    (honestRun : Program.Run
      (kind.program rd rs1 rs2 (kind.honestAdvice rd rs1 rs2 pre)) pre honestPost)
    (same : DivisionFinalAgreement (TraceWitness.finalTraceState candidate.toTrace) honestPost) :
    ∃ run' : UntrustedAnswerRun joltInstance privateInputs,
      RunExtends run run' ∧
      run'.rows.size = run.rows.size + expansionRowCount context.bytecode first ∧
      ExpansionState witness context run' first (expansionRowCount context.bytecode first) ∧
      (∀ n : Fin run'.rows.size, run'.rows[n].someTracerAdvice? =
        honestTracerAdviceAtStepN joltInstance.program run'.rows n) := by
  obtain ⟨replay, replayed⟩ := division_replay_rows witness context run first state
    kind rd rs1 rs2 count shape pre honestPost entry honestRun
  have completed := division_replay_complete witness context run candidate replay first state
    kind rd rs1 rs2 count shape pre honestPost entry extendsRun size complete same replayed
  have oldAdvice : ∀ n : Fin run.rows.size, run.rows[n].someTracerAdvice? =
      honestTracerAdviceAtStepN joltInstance.program run.rows n := by
    obtain ⟨_, _, ready⟩ := entry
    exact ready.honestRuntimeAdvice
  refine ⟨replay, replayed.extendsRun, replayed.size, completed, ?_⟩
  intro n
  by_cases before : n.val < run.rows.size
  · exact RunExtends.honestAdvice_before run replay replayed.extendsRun oldAdvice n before
  · exact division_replay_honest_new witness context run replay first state.starts
      kind rd rs1 rs2 placeholder source count shape pre honestPost replayed n (by omega)

/-- Append an entire advice-bearing division expansion, using honest advice in
the returned run and restoring agreement outside instruction temporaries.
The input is before the expansion, so a later proof may separately execute
witness advice, apply the matching division soundness theorem, and construct
honest rows using its concrete-execution theorem.
For example, REM with divisor zero may use witness quotient 5 while the returned
nine rows use quotient 0 and still produce the same architectural result.
See jolt/crates/jolt-program/src/expand/division/rem.rs (`expand_rem`) at 5def437f. -/
theorem division_block {F : Type} [Field F] (joltField : JoltField F)
    {joltInstance : JoltInstance SourceInstruction} {params : WitnessParams}
    {privateInputs : JoltPrivateInputs} (witness : WitnessType F params)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (equations : JoltConstraints.ConstraintEquations context.bytecode context.initialRam
      context.io context.entry witness)
    (run : UntrustedAnswerRun joltInstance privateInputs)
    (first : Fin context.bytecode.size)
    (state : ExpansionState witness context run first 0)
    (honestAdvice : ∀ n : Fin run.rows.size, run.rows[n].someTracerAdvice? =
      honestTracerAdviceAtStepN joltInstance.program run.rows n)
    (hasAdvice : ExpansionHasAdvice context.bytecode first) :
    ∃ run' : UntrustedAnswerRun joltInstance privateInputs,
      RunExtends run run' ∧
      run'.rows.size = run.rows.size + expansionRowCount context.bytecode first ∧
      ExpansionState witness context run' first (expansionRowCount context.bytecode first) ∧
      (∀ n : Fin run'.rows.size, run'.rows[n].someTracerAdvice? =
        honestTracerAdviceAtStepN joltInstance.program run'.rows n) := by
  obtain ⟨slots, preprocessed, _⟩ := context.entryIsRust
  obtain ⟨kind, rd, rs1, rs2, placeholder, nonzero, source, count, shape⟩ :=
    division_expansion_layout joltInstance.program context.bytecode context.expands
      ⟨slots, preprocessed⟩ first state.starts hasAdvice
  obtain ⟨q, pre, candidate, entry, present, extendsRun, size, complete, runs⟩ :=
    arithmetic_advice_sequence_run joltField witness context equations run first state
      honestAdvice (kind.program rd rs1 rs2) count shape
  have result := division_program_result kind rd rs1 rs2 nonzero q pre
    (TraceWitness.finalTraceState candidate.toTrace) present runs
  obtain ⟨honestPost, honestRun, same⟩ := division_program_honest kind rd rs1 rs2 nonzero
    q pre (TraceWitness.finalTraceState candidate.toTrace) present runs result
  exact division_append_honest witness context run candidate first state kind rd rs1 rs2
    placeholder nonzero source count shape pre honestPost entry extendsRun size complete
    honestRun same

end JoltInstance
