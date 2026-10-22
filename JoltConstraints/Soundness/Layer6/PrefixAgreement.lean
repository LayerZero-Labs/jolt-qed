import JoltConstraints.Soundness.Layer6.ExecutionPrefix
import JoltConstraints.Soundness.Layer6.BytecodePC
import JoltConstraints.Soundness.Layer5.Registers

/-! Execution-prefix reconstruction by induction over complete source instructions.
The boundary obligations are staged for review before their proofs are attempted. -/

set_option autoImplicit false

namespace JoltInstance

open JoltConstraints.Soundness

/-- Agreement after `run.rows.size` witness cycles, at a source-instruction boundary.
`represents` compares retained row observations and RAM outside the termination word;
`real` excludes retained padding and `noEarlierStop` excludes a stall before the last row.
`honestAdvice` records the honest tracer's advice at every retained row, while
`atBoundary` says the last row, if present, completes its source instruction.
`registers` compares all non-instruction-temporary registers at the next witness cycle
with the run's final state and retains the presence of every Sail register.
`terminationWord` keeps the termination RAM word zero until a store touches it.
`ready` supplies the next selected bytecode row and its prepared execution state when
the witness has another real cycle and the run has not reached a stable stall.
For example, after `rem a0, a1, zero`, witness quotient 5 and honest quotient 0 may
differ in temporary 40, while `a0`, other persistent registers and RAM still agree.
See jolt/crates/jolt-program/src/expand/division/rem.rs:15-24 and
jolt/tracer/src/instruction/rem.rs:44-58 at 5def437f. -/
structure BoundaryState {F : Type} [Field F] {params : WitnessParams}
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (witness : WitnessType F params)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (run : UntrustedAnswerRun joltInstance privateInputs) : Prop where
  represents : RepresentsPrefix witness run.toTrace
  real : ∀ t : Fin params.traceLength,
    t.val < run.rows.size → witness.InstructionFlags .IsNoop t = 0
  noEarlierStop : ∀ (i : Nat) (current next : TraceRow run.bytecode),
    run.rows[i]? = some current → run.rows[i + 1]? = some next →
    ¬ current.StableStall
  honestAdvice : ∀ n : Fin run.rows.size,
    run.rows[n].someTracerAdvice? =
      honestTracerAdviceAtStepN joltInstance.program run.rows n
  atBoundary : ∀ last ∈ run.rows.back?,
    run.bytecode[last.rowIndex].virtual_sequence_remaining.getD 0 = 0
  registers : ∀ bound : run.rows.size < params.traceLength,
    RegisterAgreementOn (fun register => ¬ IsInstructionTemporary register)
      witness ⟨run.rows.size, bound⟩ (TraceWitness.finalTraceState run.toTrace)
  terminationWord : ∀ bound : run.rows.size < params.traceLength,
    (¬ ∃ i : Fin run.rows.size, run.StoresTerminationAt i) →
    ∀ address : Fin params.ramSize,
      address.val = (run.initialState.jolt_device.memory_layout.termination.toNat -
        JoltConstraints.ramLowestAddress run.initialState.jolt_device.memory_layout) / 8 →
      witness.RamVal address ⟨run.rows.size, bound⟩ = 0
  ready : ∀ bound : run.rows.size < params.traceLength,
    witness.InstructionFlags .IsNoop ⟨run.rows.size, bound⟩ = 0 →
    (∀ last ∈ run.rows.back?, ¬ last.StableStall) →
    ∃ (next : Fin run.bytecode.size) (pre : SailJoltState)
      (slot : Fin (2 ^ params.logBytecodeK)),
      JoltConstraints.bytecodeRa witness slot ⟨run.rows.size, bound⟩ = 1 ∧
      slot.val = next.val + 1 ∧ run.NextStep next pre

/-- The instance's initialized state admits an empty run satisfying the boundary
invariant at witness cycle zero. The run's `initialized` certificate identifies
its state with the state supplied by `context.initialized`.
For example, before an entry ADDI, registers and nontermination RAM agree with
their initial tables, and the selected entry row supplies `ready` if it is real. -/
theorem boundaryState_empty {F : Type} [Field F] (joltField : JoltField F)
    {joltInstance : JoltInstance SourceInstruction} {params : WitnessParams}
    {privateInputs : JoltPrivateInputs} (witness : WitnessType F params)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (equations : JoltConstraints.ConstraintEquations context.bytecode context.initialRam
      context.io context.entry witness) :
    ∃ run : UntrustedAnswerRun joltInstance privateInputs,
      run.rows = #[] ∧ BoundaryState witness context run := by
  sorry

/-- The row at `first` plus the rows left in its sequence stamp.
When `first` starts a source instruction, this is that instruction's full row count;
for example, a nonzero-destination REM has nine rows and a native ADDI has one.
See jolt/crates/jolt-program/src/expand/metadata.rs (`stamp_sequence_metadata`)
at 5def437f. -/
def expansionRowCount (bytecode : Array JoltInstructionRow)
    (first : Fin bytecode.size) : Nat :=
  (bytecode[first].virtual_sequence_remaining.getD 0).toNat + 1

/-- Some row of the block beginning at `first`, within its stamped row count,
is a VirtualAdvice row. This concerns internal division advice, not tape reads.
For example, REM with a nonzero destination has advice, while AdviceLD does not.
See jolt/crates/jolt-program/src/expand/division/rem.rs (`expand_rem`) at 5def437f. -/
def ExpansionHasAdvice (bytecode : Array JoltInstructionRow)
    (first : Fin bytecode.size) : Prop :=
  ∃ offset < expansionRowCount bytecode first,
    ∃ row ∈ bytecode[first.val + offset]?, row.instruction.adviceValue? ≠ none

/-- A register is live after `done` rows if it is persistent, or if the source
is unfinished and one of its already executed rows wrote that register.
The block's ordered-row certificate in `ExpansionState` connects these bytecode
writes to executed rows. For example, temporary 40 is live after REM's advice
row but is no longer required to agree after all nine rows finish. -/
def ExpansionLive (bytecode : Array JoltInstructionRow)
    (first : Fin bytecode.size) (done : Nat) (register : Fin 128) : Prop :=
  ¬ IsInstructionTemporary register ∨
    (done < expansionRowCount bytecode first ∧
      ∃ offset < done, ∃ row ∈ bytecode[first.val + offset]?,
        ∃ destination ∈ row.instruction.destination?,
          TraceWitness.destinationRegisterAddress destination = register)

/-- `extended` retains every row of `run`, including its recorded advice and
pre/post states, after identifying their bytecode arrays.
For example, appending nine REM rows preserves the entire earlier prefix.
The step lemmas separately specify the number of appended rows; initialization
of both runs already identifies their initial states with the same instance. -/
def RunExtends {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs}
    (run extended : UntrustedAnswerRun joltInstance privateInputs) : Prop :=
  ∃ same : extended.bytecode = run.bytecode,
    (same ▸ extended.rows : Array (TraceRow run.bytecode)).extract 0 run.rows.size = run.rows

/-- Agreement after executing the first `done` rows of the source starting at
`first` in the context bytecode. `represents`, `real`, `noEarlierStop` and
`terminationWord` have the boundary invariant's meanings.
`starts`, `done_le`, `retained`, `ordered` and `priorBoundary` locate these rows
at the end of the run, following an empty prefix or a completed source.
`registers` compares the final state with the next witness column on `ExpansionLive`.
While unfinished, `next` provides a real next cycle, its consecutive selected
slot and the entry/linkage clause of `NextStep`; `notStopped` excludes a final stall.
Honest advice is deliberately separate: after REM's first row a run carrying
witness quotient 5 can satisfy this state, although the honest quotient is 0.
See jolt/crates/jolt-program/src/expand/division/rem.rs (`expand_rem`) and
jolt/tracer/src/instruction/mod.rs (`trace_inline_sequence_with_advice`) at 5def437f. -/
structure ExpansionState {F : Type} [Field F] {params : WitnessParams}
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (witness : WitnessType F params)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (run : UntrustedAnswerRun joltInstance privateInputs)
    (first : Fin context.bytecode.size) (done : Nat) : Prop where
  represents : RepresentsPrefix witness run.toTrace
  real : ∀ t : Fin params.traceLength,
    t.val < run.rows.size → witness.InstructionFlags .IsNoop t = 0
  noEarlierStop : ∀ (i : Nat) (current next : TraceRow run.bytecode),
    run.rows[i]? = some current → run.rows[i + 1]? = some next →
    ¬ current.StableStall
  terminationWord : ∀ bound : run.rows.size < params.traceLength,
    (¬ ∃ i : Fin run.rows.size, run.StoresTerminationAt i) →
    ∀ address : Fin params.ramSize,
      address.val = (run.initialState.jolt_device.memory_layout.termination.toNat -
        JoltConstraints.ramLowestAddress run.initialState.jolt_device.memory_layout) / 8 →
      witness.RamVal address ⟨run.rows.size, bound⟩ = 0
  starts : context.bytecode[first].starts_source = true
  done_le : done ≤ expansionRowCount context.bytecode first
  retained : done ≤ run.rows.size
  ordered : ∀ offset < done,
    ∃ row ∈ run.rows[run.rows.size - done + offset]?,
      row.rowIndex.val = first.val + offset
  priorBoundary : ∀ last ∈ (run.rows.extract 0 (run.rows.size - done)).back?,
    run.bytecode[last.rowIndex].virtual_sequence_remaining.getD 0 = 0
  registers : ∀ bound : run.rows.size < params.traceLength,
    RegisterAgreementOn (ExpansionLive context.bytecode first done)
      witness ⟨run.rows.size, bound⟩ (TraceWitness.finalTraceState run.toTrace)
  next : done < expansionRowCount context.bytecode first →
    ∃ bound : run.rows.size < params.traceLength,
      witness.InstructionFlags .IsNoop ⟨run.rows.size, bound⟩ = 0 ∧
      ∃ (next : Fin run.bytecode.size) (pre : SailJoltState)
        (slot : Fin (2 ^ params.logBytecodeK)),
        next.val = first.val + done ∧
        JoltConstraints.bytecodeRa witness slot ⟨run.rows.size, bound⟩ = 1 ∧
        slot.val = first.val + done + 1 ∧
        (match run.rows.back? with
        | none =>
          run.bytecode[next].address = joltInstance.program.entry_address ∧
          run.bytecode[next].starts_source ∧
          pre = advance_pc joltInstance.program.entry_address
            (source_is_compressed run.bytecode next) run.initialState
        | some last =>
          if run.bytecode[last.rowIndex].virtual_sequence_remaining.getD 0 ≠ 0 then
            next.val = last.rowIndex.val + 1 ∧ pre = last.postState
          else
            ∃ address, last.postState.sail.regs.get? Register.nextPC = some address ∧
              ¬ last.StableStall ∧
              run.bytecode[next].address = address ∧
              run.bytecode[next].starts_source ∧
              pre = advance_pc address (source_is_compressed run.bytecode next) last.postState)
  notStopped : done < expansionRowCount context.bytecode first →
    ∀ last ∈ run.rows.back?, ¬ last.StableStall

/-- Open the source selected by a boundary's real next cycle without adding a
row. `done = 0` leaves all instruction temporaries dead and preserves the run.
For example, before a two-row SLL, the selected first row is VirtualPow2 and
the next clause prepares that row's pre-state using the source compression flag. -/
theorem expansion_start {F : Type} [Field F] {params : WitnessParams}
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (witness : WitnessType F params)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (run : UntrustedAnswerRun joltInstance privateInputs)
    (boundary : BoundaryState witness context run)
    (bound : run.rows.size < params.traceLength)
    (real : witness.InstructionFlags .IsNoop ⟨run.rows.size, bound⟩ = 0)
    (notStopped : ∀ last ∈ run.rows.back?, ¬ last.StableStall) :
    ∃ first : Fin context.bytecode.size, ExpansionState witness context run first 0 := by
  sorry

/-- Append one row of an unfinished source with no VirtualAdvice, preserving
the expansion invariant and honest advice throughout the extended run.
For example, SLL's first row writes temporary 40, which becomes live for its
second row; no hypothesis equates that temporary before its first write. -/
theorem row_step {F : Type} [Field F] (joltField : JoltField F)
    (joltInstance : JoltInstance SourceInstruction)
    (assumptions : joltInstance.SoundnessAssumptions)
    (restrictions : joltInstance.TemporaryRestrictions)
    {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (equations : JoltConstraints.ConstraintEquations context.bytecode context.initialRam
      context.io context.entry witness)
    (run : UntrustedAnswerRun joltInstance privateInputs)
    (first : Fin context.bytecode.size) (done : Nat)
    (state : ExpansionState witness context run first done)
    (unfinished : done < expansionRowCount context.bytecode first)
    (honestAdvice : ∀ n : Fin run.rows.size, run.rows[n].someTracerAdvice? =
      honestTracerAdviceAtStepN joltInstance.program run.rows n)
    (noAdvice : ¬ ExpansionHasAdvice context.bytecode first) :
    ∃ run' : UntrustedAnswerRun joltInstance privateInputs,
      RunExtends run run' ∧ run'.rows.size = run.rows.size + 1 ∧
      ExpansionState witness context run' first (done + 1) ∧
      (∀ n : Fin run'.rows.size, run'.rows[n].someTracerAdvice? =
        honestTracerAdviceAtStepN joltInstance.program run'.rows n) := by
  sorry

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
  sorry

/-- Close a completed source expansion with honest advice, restoring the boundary
invariant including readiness for the next source when execution continues.
The assumptions retain `pcNoWrap` for the field/word PC comparison.
For example, a completed ADDI at address 0x1000 selects a successor at 0x1004
when uncompressed and when the next witness cycle is real. -/
theorem expansion_finish {F : Type} [Field F] (joltField : JoltField F)
    (joltInstance : JoltInstance SourceInstruction)
    (assumptions : joltInstance.SoundnessAssumptions)
    {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (equations : JoltConstraints.ConstraintEquations context.bytecode context.initialRam
      context.io context.entry witness)
    (run : UntrustedAnswerRun joltInstance privateInputs)
    (first : Fin context.bytecode.size)
    (state : ExpansionState witness context run first (expansionRowCount context.bytecode first))
    (honestAdvice : ∀ n : Fin run.rows.size, run.rows[n].someTracerAdvice? =
      honestTracerAdviceAtStepN joltInstance.program run.rows n) :
    BoundaryState witness context run := by
  sorry

/-- From a boundary with a real next witness cycle and no final stable stall,
execute a whole source instruction to obtain a larger run satisfying the same
boundary invariant. The conclusion requires progress, without specifying the
array extension used to construct that run.
For example, a REM step retains all nine expanded rows with honest quotient
advice, even when the witness's quotient differs in instruction temporaries. -/
theorem boundary_step {F : Type} [Field F] (joltField : JoltField F)
    (joltInstance : JoltInstance SourceInstruction)
    (assumptions : joltInstance.SoundnessAssumptions)
    (restrictions : joltInstance.TemporaryRestrictions)
    {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (equations : JoltConstraints.ConstraintEquations context.bytecode context.initialRam
      context.io context.entry witness)
    (run : UntrustedAnswerRun joltInstance privateInputs)
    (boundary : BoundaryState witness context run)
    (bound : run.rows.size < params.traceLength)
    (real : witness.InstructionFlags .IsNoop ⟨run.rows.size, bound⟩ = 0)
    (notStopped : ∀ last ∈ run.rows.back?, ¬ last.StableStall) :
    ∃ run' : UntrustedAnswerRun joltInstance privateInputs,
      run.rows.size < run'.rows.size ∧ BoundaryState witness context run' := by
  classical
  obtain ⟨first, initial⟩ := expansion_start witness context run boundary bound real notStopped
  let count := expansionRowCount context.bytecode first
  have complete : ∃ run' : UntrustedAnswerRun joltInstance privateInputs,
      run'.rows.size = run.rows.size + count ∧
      ExpansionState witness context run' first count ∧
      (∀ n : Fin run'.rows.size, run'.rows[n].someTracerAdvice? =
        honestTracerAdviceAtStepN joltInstance.program run'.rows n) := by
    by_cases hasAdvice : ExpansionHasAdvice context.bytecode first
    · obtain ⟨run', _, size, state, advice⟩ := division_block joltField witness context
        equations run first initial boundary.honestAdvice hasAdvice
      exact ⟨run', size, state, advice⟩
    have finish : ∀ remaining done (current : UntrustedAnswerRun joltInstance privateInputs),
        count - done = remaining → ExpansionState witness context current first done →
        (∀ n : Fin current.rows.size, current.rows[n].someTracerAdvice? =
          honestTracerAdviceAtStepN joltInstance.program current.rows n) →
        ∃ result : UntrustedAnswerRun joltInstance privateInputs,
          result.rows.size = current.rows.size + (count - done) ∧
          ExpansionState witness context result first count ∧
          (∀ n : Fin result.rows.size, result.rows[n].someTracerAdvice? =
            honestTracerAdviceAtStepN joltInstance.program result.rows n) := by
      intro remaining
      induction remaining with
      | zero =>
        intro done current left state advice
        have done_le : done ≤ count := state.done_le
        have doneEq : done = count := by omega
        subst done
        exact ⟨current, by omega, state, advice⟩
      | succ remaining ih =>
        intro done current left state advice
        have unfinished : done < count := by omega
        obtain ⟨next, _, size, state', advice'⟩ := row_step joltField joltInstance
          assumptions restrictions privateInputs witness context equations current first
          done state unfinished advice hasAdvice
        obtain ⟨result, total, completed, honest⟩ := ih (done + 1) next
          (by omega) state' advice'
        exact ⟨result, by omega, completed, honest⟩
    simpa only [Nat.sub_zero] using finish count 0 run rfl initial boundary.honestAdvice
  obtain ⟨run', size, state, advice⟩ := complete
  have positive : 0 < count := Nat.zero_lt_succ _
  exact ⟨run', by omega, expansion_finish joltField joltInstance assumptions
    privateInputs witness context equations run' first state advice⟩

/-- Reconstruct witness rows through the first stable stall, or through padding
or the last cycle when no stall occurs. Every retained row is real, no retained
row stops before the last, and its observations and internal advice agree. -/
theorem soundness_execution_prefix_agreement {F : Type} [Field F]
    (joltField : JoltField F)
    (joltInstance : JoltInstance SourceInstruction)
    (assumptions : joltInstance.SoundnessAssumptions)
    (restrictions : joltInstance.TemporaryRestrictions)
    {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (equations : JoltConstraints.ConstraintEquations context.bytecode context.initialRam
      context.io context.entry witness) :
    ∃ run : JoltConstraints.Soundness.UntrustedAnswerRun joltInstance privateInputs,
      run.bytecode = context.bytecode ∧
      RepresentsPrefix witness run.toTrace ∧
      (∀ t : Fin params.traceLength,
        t.val < run.rows.size → witness.InstructionFlags .IsNoop t = 0) ∧
      (∀ (i : Nat) (current next : TraceRow run.bytecode),
        run.rows[i]? = some current → run.rows[i + 1]? = some next →
        ¬ current.StableStall) ∧
      (run.rows.size = params.traceLength ∨
        ∃ bound : run.rows.size < params.traceLength,
          witness.InstructionFlags .IsNoop ⟨run.rows.size, bound⟩ = 1 ∨
          ∃ last ∈ run.rows.back?, last.StableStall) ∧
      (∀ n : Fin run.rows.size,
        run.rows[n].someTracerAdvice? =
          honestTracerAdviceAtStepN joltInstance.program run.rows n) := by
  classical
  obtain ⟨run, empty, boundary⟩ := boundaryState_empty joltField witness context equations
  clear empty
  generalize remainingEq : params.traceLength - run.rows.size = remaining
  induction remaining using Nat.strong_induction_on generalizing run with
  | h remaining ih =>
    have rowsBound := boundary.represents.rowsBound
    by_cases cut : run.rows.size = params.traceLength ∨
        ∃ bound : run.rows.size < params.traceLength,
          witness.InstructionFlags .IsNoop ⟨run.rows.size, bound⟩ = 1 ∨
          ∃ last ∈ run.rows.back?, last.StableStall
    · exact ⟨run, Option.some.inj (run.expands.symm.trans context.expands),
        boundary.represents, boundary.real, boundary.noEarlierStop, cut,
        boundary.honestAdvice⟩
    have notFull : run.rows.size ≠ params.traceLength := fun full => cut (Or.inl full)
    have bound : run.rows.size < params.traceLength := by omega
    have notPadding : witness.InstructionFlags .IsNoop ⟨run.rows.size, bound⟩ ≠ 1 :=
      fun padding => cut (Or.inr ⟨bound, Or.inl padding⟩)
    have real : witness.InstructionFlags .IsNoop ⟨run.rows.size, bound⟩ = 0 := by
      obtain ⟨slot, selected, _⟩ := bytecodeRa_unique
        (two_pow_127_lt_char joltField) context equations ⟨run.rows.size, bound⟩
      have flag := instructionFlag_of_selected_bytecode
        (two_pow_127_lt_char joltField) context equations .IsNoop
        ⟨run.rows.size, bound⟩ slot selected
      unfold JoltConstraints.bytecodeInstructionFlag at flag
      split at flag
      · simpa only [JoltMetadata.instructionFlag, Bool.false_eq_true, ↓reduceIte] using flag
      · exact False.elim (notPadding (by simpa only [↓reduceIte] using flag))
    have notStopped : ∀ last ∈ run.rows.back?, ¬ last.StableStall := by
      intro last atEnd stalled
      exact cut (Or.inr ⟨bound, Or.inr ⟨last, atEnd, stalled⟩⟩)
    obtain ⟨run', grows, boundary'⟩ := boundary_step joltField joltInstance
      assumptions restrictions privateInputs witness context equations run boundary
      bound real notStopped
    have nextBound := boundary'.represents.rowsBound
    exact ih (params.traceLength - run'.rows.size) (by omega) run' boundary' rfl

end JoltInstance
