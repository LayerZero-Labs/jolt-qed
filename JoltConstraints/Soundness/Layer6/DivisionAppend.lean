import JoltConstraints.Soundness.Layer6.DivisionDefs
import JoltConstraints.Soundness.Layer7.TerminationStore

/-! Reconstruction of an honest division expansion's trace rows. -/

set_option autoImplicit false

namespace JoltInstance

open JoltConstraints.Soundness
open Sail PreSail LeanRV64D.Functions JoltISA

private theorem division_source_advice_single (kind : DivisionKind)
    (rd rs1 rs2 : regidx) (placeholder : BitVec 64) (pre : SailJoltState) :
    (kind.source rd rs1 rs2 placeholder).honestTracerAdvice pre =
      [kind.honestAdvice rd rs1 rs2 pre] := by
  cases kind <;> rfl

private theorem division_block_later_not_start
    (image : Rv64ProgramImage SourceInstruction)
    (bytecode : Array JoltInstructionRow)
    (expanded : expand_program image = some bytecode)
    (first : Fin bytecode.size) (starts : bytecode[first].starts_source = true)
    (offset : Nat) (positive : 0 < offset)
    (inside : offset < expansionRowCount bytecode first)
    (row : JoltInstructionRow) (atRow : bytecode[first.val + offset]? = some row) :
    row.starts_source = false := by
  have endBound := (expand_program_layout image bytecode expanded).endInBounds first
  have prevBound : first.val + (offset - 1) < bytecode.size := by
    unfold expansionRowCount at inside
    omega
  have currentBound : first.val + offset < bytecode.size := by
    unfold expansionRowCount at inside
    omega
  let previous : Fin bytecode.size := ⟨first.val + (offset - 1), prevBound⟩
  let current : Fin bytecode.size := ⟨first.val + offset, currentBound⟩
  have remaining := expansion_row_remaining image bytecode expanded first starts
    (offset - 1) (by omega) bytecode[previous]
    (by simp only [previous, Array.getElem?_eq_getElem prevBound, Fin.getElem_fin])
  have continues : bytecode[previous].continues = true := by
    simpa only [JoltInstructionRow.continues, bne_iff_ne] using remaining
  have layout := (expand_program_layout image bytecode expanded).next previous current
    (by simp only [previous, current]; omega) continues
  rw [Array.getElem?_eq_getElem currentBound] at atRow
  have rowIs : row = bytecode[current] := by
    exact (Option.some.inj atRow).symm
  rw [rowIs]
  unfold JoltInstructionRow.starts_source
  simp only [layout.2.1, layout.2.2.1, Option.isNone_some, Bool.false_or]

private theorem expansion_start_of_segment {bytecode : Array JoltInstructionRow}
    (rows : Array (TraceRow bytecode)) (base offset : Nat)
    (starts : stepNOfTraceIsStartOfNewExpansion rows base = true)
    (later : ∀ k, 0 < k → k ≤ offset →
      stepNOfTraceIsStartOfNewExpansion rows (base + k) = false) :
    startOfExpansionContainingStepN rows (base + offset) = base := by
  induction offset with
  | zero =>
      by_cases empty : base = 0
      · subst base
        rfl
      · obtain ⟨previous, rfl⟩ := Nat.exists_eq_succ_of_ne_zero empty
        simp [startOfExpansionContainingStepN, starts]
  | succ offset ih =>
      have noStart := later (offset + 1) (by omega) (by omega)
      rw [Nat.add_succ, startOfExpansionContainingStepN]
      rw [show base + offset + 1 = base + (offset + 1) by omega, noStart]
      exact ih (fun k positive inside => later k positive (by omega))

/-- A replay of `count` consecutive division rows after `run`.
`ordered` identifies each bytecode row, `firstPre` records the prepared starting
state, and `adviceAtOffset` records the one patched advice word.
For example, a nine-row REM replay with quotient zero starts at the original
prefix's end and records zero on its VirtualAdvice row. -/
structure DivisionReplayRows
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (run replay : UntrustedAnswerRun joltInstance privateInputs)
    {bytecode : Array JoltInstructionRow} (first : Fin bytecode.size)
    (count : Nat) (pre honestPost : SailJoltState) (advice : BitVec 64) : Prop where
  extendsRun : RunExtends run replay
  size : replay.rows.size = run.rows.size + count
  ordered : ∀ offset < count, ∃ row ∈ replay.rows[run.rows.size + offset]?,
    row.rowIndex.val = first.val + offset
  firstPre : ∀ row ∈ replay.rows[run.rows.size]?, row.preState = pre
  finalPost : TraceWitness.finalTraceState replay.toTrace = honestPost
  adviceAtOffset : ∀ offset < count, ∀ row ∈ replay.rows[run.rows.size + offset]?,
    row.someTracerAdvice? =
      if replay.bytecode[row.rowIndex].instruction.adviceValue?.isSome then some advice else none

private theorem division_replay_start_flag
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (run replay : UntrustedAnswerRun joltInstance privateInputs)
    {bytecode : Array JoltInstructionRow} (first : Fin bytecode.size)
    (expanded : expand_program joltInstance.program = some bytecode)
    (starts : bytecode[first].starts_source = true)
    (count : Nat) (pre post : SailJoltState) (advice : BitVec 64)
    (replayed : DivisionReplayRows run replay first count pre post advice)
    (full : count = expansionRowCount bytecode first)
    (offset : Nat) (inside : offset < count) :
    stepNOfTraceIsStartOfNewExpansion replay.rows (run.rows.size + offset) =
      (offset == 0) := by
  obtain ⟨row, rowAt, index⟩ := replayed.ordered offset inside
  have bytecodeEq : replay.bytecode = bytecode :=
    Option.some.inj (replay.expands.symm.trans expanded)
  let first' : Fin replay.bytecode.size := ⟨first.val, by rw [bytecodeEq]; exact first.isLt⟩
  have firstRow : replay.bytecode[first'] = bytecode[first] := by
    have h := congrArg (fun b : Array JoltInstructionRow => b[first.val]?) bytecodeEq
    change replay.bytecode[first'.val]? = bytecode[first.val]? at h
    simp only [Array.getElem?_eq_getElem first'.isLt,
      Array.getElem?_eq_getElem first.isLt] at h
    exact Option.some.inj h
  have firstStarts : replay.bytecode[first'].starts_source = true := by
    rw [firstRow]
    exact starts
  by_cases zero : offset = 0
  · subst offset
    change replay.rows[run.rows.size + 0]? = some row at rowAt
    have rowIndex : row.rowIndex = first' := Fin.ext (by simpa only [Nat.add_zero, first'] using index)
    simp only [Nat.add_zero] at rowAt
    change (replay.rows[run.rows.size]?.map
      fun row => replay.bytecode[row.rowIndex].starts_source).getD false = true
    rw [rowAt]
    simpa only [Option.map_some, Option.getD_some, rowIndex] using firstStarts
  · have positive : 0 < offset := by omega
    have inside' : offset < expansionRowCount replay.bytecode first' := by
      have eqCount : expansionRowCount replay.bytecode first' =
          expansionRowCount bytecode first := by
        unfold expansionRowCount
        rw [firstRow]
      rw [eqCount, ← full]
      exact inside
    have atBytecode : replay.bytecode[first'.val + offset]? =
        some replay.bytecode[row.rowIndex] := by
      rw [show first'.val + offset = row.rowIndex.val by simpa only [first'] using index.symm]
      simp
    have notStart := division_block_later_not_start joltInstance.program replay.bytecode
      replay.expands first' firstStarts offset positive inside' _ atBytecode
    change replay.rows[run.rows.size + offset]? = some row at rowAt
    change (replay.rows[run.rows.size + offset]?.map
      fun row => replay.bytecode[row.rowIndex].starts_source).getD false = (offset == 0)
    rw [rowAt]
    have beqFalse : (offset == 0) = false := by
      cases offset with
      | zero => contradiction
      | succ _ => rfl
    simpa only [Option.map_some, Option.getD_some, beqFalse] using notStart

private theorem division_replay_start_at
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (run replay : UntrustedAnswerRun joltInstance privateInputs)
    {bytecode : Array JoltInstructionRow} (first : Fin bytecode.size)
    (expanded : expand_program joltInstance.program = some bytecode)
    (starts : bytecode[first].starts_source = true)
    (count : Nat) (pre post : SailJoltState) (advice : BitVec 64)
    (replayed : DivisionReplayRows run replay first count pre post advice)
    (full : count = expansionRowCount bytecode first)
    (offset : Nat) (inside : offset < count) :
    startOfExpansionContainingStepN replay.rows (run.rows.size + offset) =
      run.rows.size := by
  have firstInside : 0 < count := by omega
  have firstFlag : stepNOfTraceIsStartOfNewExpansion replay.rows run.rows.size = true := by
    simpa only [Nat.add_zero, beq_self_eq_true] using
      division_replay_start_flag run replay first expanded starts count pre post advice
        replayed full 0 firstInside
  apply expansion_start_of_segment replay.rows run.rows.size offset firstFlag
  intro k positive before
  have kInside : k < count := by omega
  have flag := division_replay_start_flag run replay first expanded starts count pre post
    advice replayed full k kInside
  have nonzero : k ≠ 0 := by omega
  have falseFlag : (k == 0) = false := by
    cases k with
    | zero => contradiction
    | succ _ => rfl
  simpa only [falseFlag] using flag

private theorem division_replay_instruction_at
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (run replay : UntrustedAnswerRun joltInstance privateInputs)
    {bytecode : Array JoltInstructionRow} (first : Fin bytecode.size)
    (expanded : expand_program joltInstance.program = some bytecode)
    (count : (expansionInstructions bytecode first).length = expansionRowCount bytecode first)
    (pre post : SailJoltState) (advice : BitVec 64)
    (replayed : DivisionReplayRows run replay first (expansionRowCount bytecode first)
      pre post advice)
    (offset : Nat) (inside : offset < expansionRowCount bytecode first)
    (row : TraceRow replay.bytecode)
    (rowAt : row ∈ replay.rows[run.rows.size + offset]?) :
    (expansionInstructions bytecode first)[offset]'(by omega) =
      replay.bytecode[row.rowIndex].instruction := by
  obtain ⟨other, otherAt, index⟩ := replayed.ordered offset inside
  have rowEq : row = other := by
    change replay.rows[run.rows.size + offset]? = some row at rowAt
    change replay.rows[run.rows.size + offset]? = some other at otherAt
    exact Option.some.inj (rowAt.symm.trans otherAt)
  subst other
  have bytecodeEq : replay.bytecode = bytecode :=
    Option.some.inj (replay.expands.symm.trans expanded)
  have bound : first.val + offset < bytecode.size := by
    rw [← index, ← bytecodeEq]
    exact row.rowIndex.isLt
  let i : Fin bytecode.size := ⟨first.val + offset, bound⟩
  have atContext : bytecode[first.val + offset]? = some bytecode[i] := by simp [i]
  have instrAt := expansionInstructions_at bytecode first offset inside count _ atContext
  have rowEq : bytecode[i] = replay.bytecode[row.rowIndex] := by
    have h := congrArg (fun b : Array JoltInstructionRow => b[first.val + offset]?) bytecodeEq
    change replay.bytecode[first.val + offset]? = bytecode[first.val + offset]? at h
    have replayBound : first.val + offset < replay.bytecode.size := by
      rw [← index]
      exact row.rowIndex.isLt
    simp only [Array.getElem?_eq_getElem replayBound,
      Array.getElem?_eq_getElem bound] at h
    have finEq : (⟨first.val + offset, replayBound⟩ : Fin replay.bytecode.size) =
        row.rowIndex := Fin.ext index.symm
    have h' := (Option.some.inj h).symm
    change bytecode[i] = replay.bytecode[(⟨first.val + offset, replayBound⟩ :
      Fin replay.bytecode.size)] at h'
    exact h'.trans (congrArg (fun j : Fin replay.bytecode.size => replay.bytecode[j]) finEq)
  simpa only [rowEq] using instrAt

private theorem division_replay_advice_flag
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (run replay : UntrustedAnswerRun joltInstance privateInputs)
    {bytecode : Array JoltInstructionRow} (first : Fin bytecode.size)
    (expanded : expand_program joltInstance.program = some bytecode)
    (count : (expansionInstructions bytecode first).length = expansionRowCount bytecode first)
    (pre post : SailJoltState) (advice : BitVec 64)
    (replayed : DivisionReplayRows run replay first (expansionRowCount bytecode first)
      pre post advice)
    (offset : Nat) (inside : offset < expansionRowCount bytecode first) :
    stepNOfTraceIsAdvice replay.rows (run.rows.size + offset) =
      ((expansionInstructions bytecode first)[offset]'(by omega)).adviceValue?.isSome := by
  obtain ⟨row, rowAt, _⟩ := replayed.ordered offset inside
  have instrEq := division_replay_instruction_at run replay first expanded count pre post
    advice replayed offset inside row rowAt
  change replay.rows[run.rows.size + offset]? = some row at rowAt
  unfold stepNOfTraceIsAdvice
  rw [rowAt]
  simpa only [Option.bind_some, Option.isSome, instrEq]

private theorem division_replay_advice_before_zero
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (run replay : UntrustedAnswerRun joltInstance privateInputs)
    {bytecode : Array JoltInstructionRow} (first : Fin bytecode.size)
    (expanded : expand_program joltInstance.program = some bytecode)
    (starts : bytecode[first].starts_source = true)
    (count : (expansionInstructions bytecode first).length = expansionRowCount bytecode first)
    {program : BitVec 64 → Program}
    (shape : ArithmeticAdviceSequence (expansionInstructions bytecode first) program)
    (pre post : SailJoltState) (advice : BitVec 64)
    (replayed : DivisionReplayRows run replay first (expansionRowCount bytecode first)
      pre post advice)
    (offset : Nat) (inside : offset < expansionRowCount bytecode first)
    (adviceAt : stepNOfTraceIsAdvice replay.rows (run.rows.size + offset) = true) :
    adviceStepsBeforeStepN replay.rows (run.rows.size + offset) = 0 := by
  obtain ⟨adviceIndex, adviceBound, _, unique⟩ :=
    single_advice_index (expansionInstructions bytecode first) shape.singleAdvice
  have currentFlag := division_replay_advice_flag run replay first expanded count pre post
    advice replayed offset inside
  have currentIndex : offset = adviceIndex := unique offset (by rw [count]; exact inside)
    (by rw [← currentFlag]; exact adviceAt)
  have startAt := division_replay_start_at run replay first expanded starts
    (expansionRowCount bytecode first) pre post advice replayed rfl offset inside
  unfold adviceStepsBeforeStepN
  rw [startAt]
  have empty : (List.range' run.rows.size offset).filter
      (stepNOfTraceIsAdvice replay.rows) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro n inRange
    obtain ⟨k, before, rfl⟩ := List.mem_range'.mp inRange
    have kInside : k < expansionRowCount bytecode first := by omega
    have earlierFlag := division_replay_advice_flag run replay first expanded count pre post
      advice replayed k kInside
    cases flag : stepNOfTraceIsAdvice replay.rows (run.rows.size + k) with
    | false => simpa only [one_mul, flag, Bool.false_eq_true, not_false_eq_true]
    | true =>
        have kAdvice : ((expansionInstructions bytecode first)[k]'(by omega)).adviceValue?.isSome = true := by
          rw [← earlierFlag]
          exact flag
        have kIndex := unique k (by rw [count]; exact kInside) kAdvice
        omega
  simpa only [Nat.add_sub_cancel_left, empty, List.length_nil]

private theorem division_replay_first_source
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (run replay : UntrustedAnswerRun joltInstance privateInputs)
    {bytecode : Array JoltInstructionRow} (first : Fin bytecode.size)
    (expanded : expand_program joltInstance.program = some bytecode)
    (source : SourceInstruction)
    (sourceAt : joltInstance.program.instructionAt bytecode[first].address = some source)
    (count : Nat) (positive : 0 < count) (pre post : SailJoltState)
    (advice : BitVec 64)
    (replayed : DivisionReplayRows run replay first count pre post advice) :
    ∃ row ∈ replay.rows[run.rows.size]?, row.preState = pre ∧
      joltInstance.program.instructionAt replay.bytecode[row.rowIndex].address =
        some source := by
  obtain ⟨row, atRow, index⟩ := replayed.ordered 0 positive
  have bytecodeEq : replay.bytecode = bytecode :=
    Option.some.inj (replay.expands.symm.trans expanded)
  let first' : Fin replay.bytecode.size := ⟨first.val, by rw [bytecodeEq]; exact first.isLt⟩
  have rowIndex : row.rowIndex = first' :=
    Fin.ext (by simpa only [Nat.add_zero, first'] using index)
  have firstBytecode : replay.bytecode[first'] = bytecode[first] := by
    have h := congrArg (fun b : Array JoltInstructionRow => b[first.val]?) bytecodeEq
    change replay.bytecode[first'.val]? = bytecode[first.val]? at h
    simp only [Array.getElem?_eq_getElem first'.isLt,
      Array.getElem?_eq_getElem first.isLt] at h
    exact Option.some.inj h
  refine ⟨row, by simpa only [Nat.add_zero] using atRow, replayed.firstPre row atRow, ?_⟩
  simpa only [rowIndex, firstBytecode] using sourceAt

/-- Appending rows preserves honest advice on the retained prefix.
For example, replaying a REM block after a JAL leaves the JAL's earlier advice
observation unchanged. -/
theorem RunExtends.honestAdvice_before
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (run replay : UntrustedAnswerRun joltInstance privateInputs)
    (extendsRun : RunExtends run replay)
    (honest : ∀ n : Fin run.rows.size, run.rows[n].someTracerAdvice? =
      honestTracerAdviceAtStepN joltInstance.program run.rows n)
    (n : Fin replay.rows.size) (before : n.val < run.rows.size) :
    replay.rows[n].someTracerAdvice? =
      honestTracerAdviceAtStepN joltInstance.program replay.rows n := by
  obtain ⟨bytecodeEq, rowsEq⟩ := extendsRun
  rcases run with ⟨⟨runBytecode, runRows, _⟩, _⟩
  rcases replay with ⟨⟨replayBytecode, replayRows, _⟩, _⟩
  dsimp only at bytecodeEq rowsEq honest n before ⊢
  subst bytecodeEq
  dsimp only at rowsEq honest before ⊢
  have sizes := congrArg Array.size rowsEq
  simp only [Array.size_extract, Nat.sub_zero] at sizes
  have within : runRows.size ≤ replayRows.size := by omega
  have rowEq : replayRows[n].someTracerAdvice? =
      (runRows[n.val]'before).someTracerAdvice? := by
    have h := congrArg (fun rows : Array (TraceRow replayBytecode) => rows[n.val]?) rowsEq
    simp only [Array.getElem?_extract, Nat.min_eq_left within, Nat.zero_add, Nat.sub_zero,
      if_pos before, Array.getElem?_eq_getElem n.isLt,
      Array.getElem?_eq_getElem before] at h
    exact congrArg TraceRow.someTracerAdvice? (Option.some.inj h)
  rw [rowEq]
  have adviceEq := honestTracerAdviceAtStepN_extract joltInstance.program
    replayRows runRows.size n.val within before
  rw [rowsEq] at adviceEq
  exact (honest ⟨n.val, before⟩).trans adviceEq

/-- Split an honest division program run and append each execution to the
original prefix, preserving its exact rows and recording the patched advice.
For example, the nine REM instructions become nine consecutive trace rows. -/
theorem division_replay_rows
    {F : Type} [Field F] {joltInstance : JoltInstance SourceInstruction}
    {params : WitnessParams} {privateInputs : JoltPrivateInputs}
    (witness : WitnessType F params)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (run : UntrustedAnswerRun joltInstance privateInputs)
    (first : Fin context.bytecode.size)
    (state : ExpansionState witness context run first 0)
    (kind : DivisionKind) (rd rs1 rs2 : regidx)
    (count : (expansionInstructions context.bytecode first).length =
      expansionRowCount context.bytecode first)
    (shape : ArithmeticAdviceSequence (expansionInstructions context.bytecode first)
      (kind.program rd rs1 rs2))
    (pre honestPost : SailJoltState)
    (entry : ∃ next : Fin run.bytecode.size, next.val = first.val ∧ run.NextStep next pre)
    (honestRun : Program.Run
      (kind.program rd rs1 rs2 (kind.honestAdvice rd rs1 rs2 pre)) pre honestPost) :
    ∃ replay : UntrustedAnswerRun joltInstance privateInputs,
      DivisionReplayRows run replay first (expansionRowCount context.bytecode first)
        pre honestPost (kind.honestAdvice rd rs1 rs2 pre) := by
  sorry

/-- Transfer a completed witness division block's observation, RAM, register,
and stopping invariants to its honest replay, using their equal final states
outside instruction temporaries.
For example, REM quotient five and quotient zero still agree on architectural
registers and RAM after the last row. -/
theorem division_replay_complete
    {F : Type} [Field F] {joltInstance : JoltInstance SourceInstruction}
    {params : WitnessParams} {privateInputs : JoltPrivateInputs}
    (witness : WitnessType F params)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (run candidate replay : UntrustedAnswerRun joltInstance privateInputs)
    (first : Fin context.bytecode.size)
    (state : ExpansionState witness context run first 0)
    (kind : DivisionKind) (rd rs1 rs2 : regidx)
    (count : (expansionInstructions context.bytecode first).length =
      expansionRowCount context.bytecode first)
    (shape : ArithmeticAdviceSequence (expansionInstructions context.bytecode first)
      (kind.program rd rs1 rs2))
    (pre honestPost : SailJoltState)
    (entry : ∃ next : Fin run.bytecode.size, next.val = first.val ∧ run.NextStep next pre)
    (candidateExtends : RunExtends run candidate)
    (candidateSize : candidate.rows.size = run.rows.size + expansionRowCount context.bytecode first)
    (complete : ExpansionState witness context candidate first
      (expansionRowCount context.bytecode first))
    (same : DivisionFinalAgreement (TraceWitness.finalTraceState candidate.toTrace) honestPost)
    (replayed : DivisionReplayRows run replay first (expansionRowCount context.bytecode first)
      pre honestPost (kind.honestAdvice rd rs1 rs2 pre)) :
    ExpansionState witness context replay first
      (expansionRowCount context.bytecode first) := by
  sorry

/-- On the appended block, the honest tracer recomputes the single advice word
from the source instruction and the prepared state at the block's first row.
For example, a REM by zero records quotient magnitude zero on its advice row. -/
theorem division_replay_honest_new
    {F : Type} [Field F] {joltInstance : JoltInstance SourceInstruction}
    {params : WitnessParams} {privateInputs : JoltPrivateInputs}
    (witness : WitnessType F params)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (run replay : UntrustedAnswerRun joltInstance privateInputs)
    (first : Fin context.bytecode.size)
    (starts : context.bytecode[first].starts_source = true)
    (kind : DivisionKind) (rd rs1 rs2 : regidx) (placeholder : BitVec 64)
    (source : joltInstance.program.instructionAt context.bytecode[first].address =
      some (kind.source rd rs1 rs2 placeholder))
    (count : (expansionInstructions context.bytecode first).length =
      expansionRowCount context.bytecode first)
    (shape : ArithmeticAdviceSequence (expansionInstructions context.bytecode first)
      (kind.program rd rs1 rs2))
    (pre honestPost : SailJoltState)
    (replayed : DivisionReplayRows run replay first (expansionRowCount context.bytecode first)
      pre honestPost (kind.honestAdvice rd rs1 rs2 pre))
    (n : Fin replay.rows.size) (new : run.rows.size ≤ n.val) :
    replay.rows[n].someTracerAdvice? =
      honestTracerAdviceAtStepN joltInstance.program replay.rows n := by
  let offset := n.val - run.rows.size
  have position : n.val = run.rows.size + offset := by simp only [offset]; omega
  have inside : offset < expansionRowCount context.bytecode first := by
    have bound : n.val < run.rows.size + expansionRowCount context.bytecode first := by
      simpa only [replayed.size] using n.isLt
    omega
  obtain ⟨row, rowAt, index⟩ := replayed.ordered offset inside
  have nRow : replay.rows[n.val]? = some row := by simpa only [position] using rowAt
  have rowEq : replay.rows[n] = row := by
    rw [Array.getElem?_eq_getElem n.isLt] at nRow
    exact Option.some.inj nRow
  have startAt := division_replay_start_at run replay first context.expands starts
    (expansionRowCount context.bytecode first) pre honestPost (kind.honestAdvice rd rs1 rs2 pre)
    replayed rfl offset inside
  obtain ⟨firstRow, firstAt', firstPre, sourceAt⟩ :=
    division_replay_first_source run replay first context.expands
      (kind.source rd rs1 rs2 placeholder) source
      (expansionRowCount context.bytecode first) (by omega) pre honestPost
      (kind.honestAdvice rd rs1 rs2 pre) replayed
  change replay.rows[run.rows.size]? = some firstRow at firstAt'
  have adviceAt := replayed.adviceAtOffset offset inside row rowAt
  cases adviceOption : replay.bytecode[row.rowIndex].instruction.adviceValue? with
  | none =>
      rw [rowEq]
      have absent : row.someTracerAdvice? = none := by
        simpa only [adviceOption, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
          using adviceAt
      rw [absent]
      unfold honestTracerAdviceAtStepN
      rw [nRow]
      change replay.bytecode[row.rowIndex.val].instruction.adviceValue? = none at adviceOption
      simp [adviceOption]
  | some value =>
      have adviceFlag : stepNOfTraceIsAdvice replay.rows (run.rows.size + offset) = true := by
        change (replay.rows[run.rows.size + offset]?.bind
          fun row => replay.bytecode[row.rowIndex].instruction.adviceValue?).isSome = true
        change replay.rows[run.rows.size + offset]? = some row at rowAt
        simp only [rowAt, Option.bind_some, adviceOption, Option.isSome_some]
      have adviceBefore := division_replay_advice_before_zero run replay first
        context.expands starts count shape pre honestPost (kind.honestAdvice rd rs1 rs2 pre)
        replayed offset inside adviceFlag
      have present : row.someTracerAdvice? = some (kind.honestAdvice rd rs1 rs2 pre) := by
        simpa only [adviceOption, Option.isSome_some, ↓reduceIte] using adviceAt
      rw [rowEq, present]
      have startAtN : startOfExpansionContainingStepN replay.rows n.val = run.rows.size := by
        rw [position]
        exact startAt
      have adviceBeforeN : adviceStepsBeforeStepN replay.rows n.val = 0 := by
        rw [position]
        exact adviceBefore
      unfold honestTracerAdviceAtStepN
      rw [nRow]
      change replay.bytecode[row.rowIndex.val].instruction.adviceValue? = some value at adviceOption
      change joltInstance.program.instructionAt
        replay.bytecode[firstRow.rowIndex.val].address =
        some (kind.source rd rs1 rs2 placeholder) at sourceAt
      simp [adviceOption, startAtN, firstAt', sourceAt, firstPre, adviceBeforeN,
        division_source_advice_single]

end JoltInstance
