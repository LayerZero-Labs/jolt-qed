import JoltConstraints.Soundness.Layer6.DivisionDefs
import JoltConstraints.Soundness.Layer7.TerminationStore

/-! Reconstruction of an honest division expansion's trace rows. -/

set_option autoImplicit false

namespace JoltInstance

open JoltConstraints.Soundness
open Sail PreSail LeanRV64D.Functions JoltISA

private theorem runtimeAdviceFor_patch (instruction : Instr) (q : BitVec 64) :
    instruction.withRuntimeAdvice (runtimeAdviceFor instruction q) =
      patchAdviceWord q instruction := by
  apply patchAdviceWord_runtime
  intro value present
  unfold runtimeAdviceFor at present
  unfold Instr.RuntimeAdvice at present
  split at present
  · simp only [Instr.withRuntimeAdvice, Instr.adviceValue?] at present
    exact (Option.some.inj present).symm
  · simp_all [Instr.withRuntimeAdvice, Instr.adviceValue?]

private theorem runtimeAdviceFor_observation (instruction : Instr) (q : BitVec 64) :
    (instruction.withRuntimeAdvice (runtimeAdviceFor instruction q)).adviceValue? =
      if instruction.adviceValue?.isSome then some q else none := by
  have sameFlag := runtime_advice_isSome instruction (runtimeAdviceFor instruction q)
  rw [runtimeAdviceFor_patch]
  unfold patchAdviceWord
  split <;> simp_all [Instr.adviceValue?]

private def divisionReplayStep
    {bytecode : Array JoltInstructionRow} (next : Fin bytecode.size)
    (pre post : SailJoltState) (q : BitVec 64) : TraceRow bytecode :=
  { rowIndex := next, runtimeAdvice := runtimeAdviceFor bytecode[next].instruction q,
    preState := pre, postState := post }

private theorem divisionReplayStep_exec
    {bytecode : Array JoltInstructionRow} (next : Fin bytecode.size)
    (pre post : SailJoltState) (q : BitVec 64)
    (arithmetic : DivisionArithmeticRow bytecode[next].instruction)
    (executes : execInstr (patchAdviceWord q bytecode[next].instruction) pre =
      .ok RETIRE_SUCCESS post) :
    execWithTapeAnswer
      (bytecode[next].instruction.withRuntimeAdvice
        (divisionReplayStep next pre post q).runtimeAdvice) 0 pre =
      .ok RETIRE_SUCCESS post := by
  have arithmeticPatched : DivisionArithmeticRow
      (patchAdviceWord q bytecode[next].instruction) := by
    unfold patchAdviceWord
    split
    · exact True.intro
    · exact arithmetic
  change execWithTapeAnswer
    (bytecode[next].instruction.withRuntimeAdvice
      (runtimeAdviceFor bytecode[next].instruction q)) 0 pre = .ok RETIRE_SUCCESS post
  rw [runtimeAdviceFor_patch, arithmetic_exec_eq _ arithmeticPatched]
  exact executes

private theorem division_replay_append_one
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (run : UntrustedAnswerRun joltInstance privateInputs)
    (next : Fin run.bytecode.size) (pre post : SailJoltState) (q : BitVec 64)
    (entry : RawRowEntry run next pre)
    (arithmetic : DivisionArithmeticRow run.bytecode[next].instruction)
    (executes : execInstr (patchAdviceWord q run.bytecode[next].instruction) pre =
      .ok RETIRE_SUCCESS post) :
    ∃ extended : UntrustedAnswerRun joltInstance privateInputs,
      RunExtends run extended ∧ extended.rows.size = run.rows.size + 1 ∧
      TraceWitness.finalTraceState extended.toTrace = post ∧
      ∃ step ∈ extended.rows[run.rows.size]?,
        step.rowIndex.val = next.val ∧ step.preState = pre ∧ step.postState = post ∧
        step.someTracerAdvice? =
          if run.bytecode[next].instruction.adviceValue?.isSome then some q else none := by
  let step := divisionReplayStep next pre post q
  have relaxed : execWithTapeAnswer
      (run.bytecode[step.rowIndex].instruction.withRuntimeAdvice step.runtimeAdvice) 0 pre =
      .ok RETIRE_SUCCESS post := by
    exact divisionReplayStep_exec next pre post q arithmetic executes
  let extended := appendUntrustedRow run step 0 relaxed
    (rawEntry_starts entry) (rawEntry_linked entry)
  refine ⟨extended, ⟨rfl, by simp [extended, appendUntrustedRow]⟩,
    by simp [extended, appendUntrustedRow], ?_, step, ?_, rfl, rfl, rfl, ?_⟩
  · simpa only [extended, appendUntrustedRow, finalTraceState_push] using
      (show step.postState = post by rfl)
  · change (run.rows.push step)[run.rows.size]? = some step
    exact Array.getElem?_push_size
  · exact runtimeAdviceFor_observation _ q

private theorem division_replay_interior_entry
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (run : UntrustedAnswerRun joltInstance privateInputs)
    (first : Fin run.bytecode.size) (starts : run.bytecode[first].starts_source = true)
    (offset : Nat) (positive : 0 < offset)
    (inside : offset < expansionRowCount run.bytecode first)
    (previous : TraceRow run.bytecode) (atBack : run.rows.back? = some previous)
    (previousIndex : previous.rowIndex.val = first.val + offset - 1)
    (next : Fin run.bytecode.size) (nextIndex : next.val = first.val + offset)
    (pre : SailJoltState) (preEq : pre = previous.postState) :
    RawRowEntry run next pre := by
  have atPrevious : run.bytecode[first.val + (offset - 1)]? =
      some run.bytecode[previous.rowIndex] := by
    rw [show first.val + (offset - 1) = previous.rowIndex.val by omega]
    simp
  have remaining := expansion_row_remaining joltInstance.program run.bytecode
    run.expands first starts (offset - 1) (by omega) _ atPrevious
  unfold RawRowEntry
  rw [atBack]
  simp only [if_pos remaining]
  exact ⟨by omega, preEq⟩

private theorem division_next_step_raw_entry
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (run : UntrustedAnswerRun joltInstance privateInputs)
    (next : Fin run.bytecode.size) (pre : SailJoltState)
    (entry : run.NextStep next pre) : RawRowEntry run next pre := by
  unfold RawRowEntry
  have ready := entry.ready
  cases lastAt : run.rows.back? with
  | none => simpa only [lastAt] using ready
  | some last =>
      simp only [lastAt] at ready ⊢
      by_cases remaining : run.bytecode[last.rowIndex].virtual_sequence_remaining.getD 0 ≠ 0
      · simpa only [if_pos remaining] using ready
      · simp only [if_neg remaining] at ready ⊢
        exact ready

private theorem division_replay_first_row
    {joltInstance : JoltInstance SourceInstruction}
    {params : WitnessParams} {privateInputs : JoltPrivateInputs}
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (run : UntrustedAnswerRun joltInstance privateInputs)
    (first : Fin context.bytecode.size)
    (kind : DivisionKind) (rd rs1 rs2 : regidx)
    (count : (expansionInstructions context.bytecode first).length =
      expansionRowCount context.bytecode first)
    (shape : ArithmeticAdviceSequence (expansionInstructions context.bytecode first)
      (kind.program rd rs1 rs2))
    (pre post : SailJoltState)
    (entry : ∃ next : Fin run.bytecode.size, next.val = first.val ∧ run.NextStep next pre)
    (honestRun : Program.Run
      (kind.program rd rs1 rs2 (kind.honestAdvice rd rs1 rs2 pre)) pre post) :
    ∃ (middle : SailJoltState) (firstRun : UntrustedAnswerRun joltInstance privateInputs),
      RunExtends run firstRun ∧ firstRun.rows.size = run.rows.size + 1 ∧
      TraceWitness.finalTraceState firstRun.toTrace = middle ∧
      Program.Run (Program.seq (((expansionInstructions context.bytecode first).drop 1).map
        (patchAdviceWord (kind.honestAdvice rd rs1 rs2 pre)))) middle post ∧
      ∃ step ∈ firstRun.rows[run.rows.size]?,
        step.rowIndex.val = first.val ∧ step.preState = pre ∧ step.postState = middle ∧
        step.someTracerAdvice? = if context.bytecode[first].instruction.adviceValue?.isSome
          then some (kind.honestAdvice rd rs1 rs2 pre) else none := by
  let q := kind.honestAdvice rd rs1 rs2 pre
  let instructions := expansionInstructions context.bytecode first
  have positive : 0 < instructions.length := by
    change 0 < (expansionInstructions context.bytecode first).length
    rw [count]
    unfold expansionRowCount
    omega
  have listEq : instructions = instructions[0] :: instructions.drop 1 := by
    simpa only [List.drop_zero] using List.drop_eq_getElem_cons (l := instructions) (i := 0) positive
  have runList : Program.Run (Program.seq (instructions.map (patchAdviceWord q))) pre post := by
    simpa only [instructions, q, shape.program_eq] using honestRun
  rw [listEq, List.map_cons] at runList
  obtain ⟨middle, head, tail⟩ := execProgram_instr_run_retire_inv
    (patchAdviceWord q instructions[0])
    (Program.seq ((instructions.drop 1).map (patchAdviceWord q))) pre post runList
  obtain ⟨next, nextIndex, ready⟩ := entry
  have bytecodeEq : run.bytecode = context.bytecode :=
    Option.some.inj (run.expands.symm.trans context.expands)
  have atBytecode : context.bytecode[first.val]? = some run.bytecode[next] := by
    rw [← nextIndex]
    have h := congrArg (fun b : Array JoltInstructionRow => b[next.val]?) bytecodeEq
    change run.bytecode[next.val]? = context.bytecode[next.val]? at h
    simp only [Array.getElem?_eq_getElem next.isLt] at h
    exact h.symm
  have instrEq := expansionInstructions_at context.bytecode first 0
    (by unfold expansionRowCount; omega)
    count _ (by simpa only [Nat.add_zero] using atBytecode)
  have firstRowEq : context.bytecode[first] = run.bytecode[next] := by
    rw [Array.getElem?_eq_getElem first.isLt] at atBytecode
    exact Option.some.inj atBytecode
  have arithmetic : DivisionArithmeticRow run.bytecode[next].instruction := by
    rw [← instrEq]
    exact shape.arithmetic _ (List.getElem_mem _)
  have headRun : execInstr (patchAdviceWord q run.bytecode[next].instruction) pre =
      .ok RETIRE_SUCCESS middle := by
    dsimp only [instructions] at head
    rw [instrEq] at head
    exact head
  obtain ⟨firstRun, extendsRun, size, finalPost, step, stepAt, index, firstPre,
    firstPost, advice⟩ :=
    division_replay_append_one run next pre middle q
      (division_next_step_raw_entry run next pre ready) arithmetic headRun
  refine ⟨middle, firstRun, extendsRun, size, finalPost, ?_, step, stepAt, ?_,
    firstPre, firstPost, ?_⟩
  · simpa only [instructions, q] using tail
  · exact index.trans nextIndex
  · simpa only [q, firstRowEq] using advice

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

private theorem DivisionReplayRows.push
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (base current : UntrustedAnswerRun joltInstance privateInputs)
    {bytecode : Array JoltInstructionRow} (first : Fin bytecode.size)
    (done : Nat) (positive : 0 < done) (pre middle post : SailJoltState)
    (q : BitVec 64) (replayed : DivisionReplayRows base current first done pre middle q)
    (step : TraceRow current.bytecode) (answer : BitVec 64)
    (executes : execWithTapeAnswer
      (current.bytecode[step.rowIndex].instruction.withRuntimeAdvice step.runtimeAdvice)
      answer step.preState = .ok RETIRE_SUCCESS step.postState)
    (starts : current.rows.size = 0 →
      current.bytecode[step.rowIndex].address = joltInstance.program.entry_address ∧
      current.bytecode[step.rowIndex].starts_source ∧
      step.preState = advance_pc joltInstance.program.entry_address
        (source_is_compressed current.bytecode step.rowIndex) current.initialState)
    (linked : ∀ last ∈ current.rows.back?,
      if current.bytecode[last.rowIndex].virtual_sequence_remaining.getD 0 ≠ 0 then
        step.rowIndex.val = last.rowIndex.val + 1 ∧ step.preState = last.postState
      else ∃ address, last.postState.sail.regs.get? Register.nextPC = some address ∧
        current.bytecode[step.rowIndex].address = address ∧
        current.bytecode[step.rowIndex].starts_source ∧
        step.preState = advance_pc address
          (source_is_compressed current.bytecode step.rowIndex) last.postState)
    (index : step.rowIndex.val = first.val + done)
    (postEq : step.postState = post)
    (adviceEq : step.someTracerAdvice? =
      if current.bytecode[step.rowIndex].instruction.adviceValue?.isSome then some q else none) :
    DivisionReplayRows base (appendUntrustedRow current step answer executes starts linked)
      first (done + 1) pre post q := by
  let extended := appendUntrustedRow current step answer executes starts linked
  have extendedSize : extended.rows.size = current.rows.size + 1 := by
    simp only [extended, appendUntrustedRow, Array.size_push]
  have before (offset : Nat) (old : offset < done) :
      base.rows.size + offset < current.rows.size := by
    rw [replayed.size]
    omega
  refine ⟨replayed.extendsRun.trans ⟨rfl, by simp [extended, appendUntrustedRow]⟩,
    by rw [extendedSize, replayed.size]; omega, ?_, ?_, ?_, ?_⟩
  · intro offset inside
    by_cases old : offset < done
    · obtain ⟨row, atRow, idx⟩ := replayed.ordered offset old
      refine ⟨row, ?_, idx⟩
      change row ∈ (current.rows.push step)[base.rows.size + offset]?
      simpa only [Array.getElem?_push_lt (before offset old),
        Array.getElem?_eq_getElem (before offset old)] using atRow
    · have same : offset = done := by omega
      subst offset
      refine ⟨step, ?_, index⟩
      change (current.rows.push step)[base.rows.size + done]? = some step
      rw [← replayed.size]
      exact Array.getElem?_push_size
  · intro row atRow
    have firstBefore : base.rows.size < current.rows.size := by rw [replayed.size]; omega
    have oldAt : row ∈ current.rows[base.rows.size]? := by
      change row ∈ (current.rows.push step)[base.rows.size]? at atRow
      simpa only [Array.getElem?_push_lt firstBefore,
        Array.getElem?_eq_getElem firstBefore] using atRow
    exact replayed.firstPre row oldAt
  · simpa only [extended, appendUntrustedRow, finalTraceState_push, postEq]
  · intro offset inside row atRow
    by_cases old : offset < done
    · have oldAt : row ∈ current.rows[base.rows.size + offset]? := by
        change row ∈ (current.rows.push step)[base.rows.size + offset]? at atRow
        simpa only [Array.getElem?_push_lt (before offset old),
          Array.getElem?_eq_getElem (before offset old)] using atRow
      exact replayed.adviceAtOffset offset old row oldAt
    · have same : offset = done := by omega
      subst offset
      have rowIs : row = step := by
        change (current.rows.push step)[base.rows.size + done]? = some row at atRow
        have atStep : (current.rows.push step)[base.rows.size + done]? = some step := by
          rw [← replayed.size]
          exact Array.getElem?_push_size
        exact Option.some.inj (atRow.symm.trans atStep)
      subst row
      exact adviceEq

private theorem division_replay_next_entry
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (base current : UntrustedAnswerRun joltInstance privateInputs)
    {bytecode : Array JoltInstructionRow} (first : Fin bytecode.size)
    (expanded : expand_program joltInstance.program = some bytecode)
    (starts : bytecode[first].starts_source = true)
    (done : Nat) (positive : 0 < done)
    (inside : done < expansionRowCount bytecode first)
    (pre middle : SailJoltState) (q : BitVec 64)
    (replayed : DivisionReplayRows base current first done pre middle q) :
    ∃ next : Fin current.bytecode.size,
      next.val = first.val + done ∧ RawRowEntry current next middle := by
  have bytecodeEq : current.bytecode = bytecode :=
    Option.some.inj (current.expands.symm.trans expanded)
  have bound : first.val + done < current.bytecode.size := by
    have endBound := (expand_program_layout joltInstance.program bytecode expanded).endInBounds first
    rw [bytecodeEq]
    unfold expansionRowCount at inside
    omega
  let next : Fin current.bytecode.size := ⟨first.val + done, bound⟩
  let first' : Fin current.bytecode.size := ⟨first.val, by omega⟩
  have firstRow : current.bytecode[first'] = bytecode[first] := by
    have h := congrArg (fun b : Array JoltInstructionRow => b[first.val]?) bytecodeEq
    change current.bytecode[first.val]? = bytecode[first.val]? at h
    have left : current.bytecode[first.val]? = some current.bytecode[first'] :=
      Array.getElem?_eq_getElem first'.isLt
    rw [left, Array.getElem?_eq_getElem first.isLt] at h
    exact Option.some.inj h
  have currentStarts : current.bytecode[first'].starts_source = true := by
    rw [firstRow]
    exact starts
  obtain ⟨previous, atPrevious, previousIndex⟩ := replayed.ordered (done - 1) (by omega)
  have atBack : current.rows.back? = some previous := by
    rw [Array.back?_eq_getElem?]
    have equal : current.rows.size - 1 = base.rows.size + (done - 1) := by
      rw [replayed.size]
      omega
    rw [equal]
    exact atPrevious
  have postEq : middle = previous.postState := by
    rw [← replayed.finalPost, finalTraceState_back]
    simp only [UntrustedAnswerRun.toTrace, atBack, Option.map_some, Option.getD_some]
  refine ⟨next, rfl, ?_⟩
  have inside' : done < expansionRowCount current.bytecode first' := by
    unfold expansionRowCount at inside ⊢
    rw [firstRow]
    exact inside
  exact division_replay_interior_entry current first' currentStarts done positive
    inside' previous atBack (by change previous.rowIndex.val = first.val + done - 1; omega)
    next rfl middle postEq

private theorem division_replay_first_state
    {joltInstance : JoltInstance SourceInstruction}
    {params : WitnessParams} {privateInputs : JoltPrivateInputs}
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (run : UntrustedAnswerRun joltInstance privateInputs)
    (first : Fin context.bytecode.size)
    (kind : DivisionKind) (rd rs1 rs2 : regidx)
    (count : (expansionInstructions context.bytecode first).length =
      expansionRowCount context.bytecode first)
    (shape : ArithmeticAdviceSequence (expansionInstructions context.bytecode first)
      (kind.program rd rs1 rs2))
    (pre post : SailJoltState)
    (entry : ∃ next : Fin run.bytecode.size, next.val = first.val ∧ run.NextStep next pre)
    (honestRun : Program.Run
      (kind.program rd rs1 rs2 (kind.honestAdvice rd rs1 rs2 pre)) pre post) :
    ∃ (middle : SailJoltState) (firstRun : UntrustedAnswerRun joltInstance privateInputs),
      DivisionReplayRows run firstRun first 1 pre middle
        (kind.honestAdvice rd rs1 rs2 pre) ∧
      Program.Run (Program.seq (((expansionInstructions context.bytecode first).drop 1).map
        (patchAdviceWord (kind.honestAdvice rd rs1 rs2 pre)))) middle post := by
  obtain ⟨middle, firstRun, extendsRun, size, finalPost, tail, step, stepAt,
    index, firstPre, firstPost, advice⟩ :=
    division_replay_first_row context run first kind rd rs1 rs2 count shape
      pre post entry honestRun
  have bytecodeEq : firstRun.bytecode = context.bytecode :=
    Option.some.inj (firstRun.expands.symm.trans context.expands)
  refine ⟨middle, firstRun, ?_, tail⟩
  refine ⟨extendsRun, size, ?_, ?_, finalPost, ?_⟩
  · intro offset inside
    have zero : offset = 0 := by omega
    subst offset
    exact ⟨step, by simpa only [Nat.add_zero] using stepAt,
      by simpa only [Nat.add_zero] using index⟩
  · intro row atRow
    have rowIs : row = step := by
      change firstRun.rows[run.rows.size]? = some row at atRow
      change firstRun.rows[run.rows.size]? = some step at stepAt
      exact Option.some.inj (atRow.symm.trans stepAt)
    subst row
    exact firstPre
  · intro offset inside row atRow
    have zero : offset = 0 := by omega
    subst offset
    have rowIs : row = step := by
      change firstRun.rows[run.rows.size]? = some row at atRow
      change firstRun.rows[run.rows.size]? = some step at stepAt
      exact Option.some.inj (atRow.symm.trans stepAt)
    subst row
    have first' : step.rowIndex.val = first.val := index
    have instructionEq : firstRun.bytecode[step.rowIndex].instruction =
        context.bytecode[first].instruction := by
      have h := congrArg (fun b : Array JoltInstructionRow => b[first.val]?) bytecodeEq
      change firstRun.bytecode[first.val]? = context.bytecode[first.val]? at h
      have bound : first.val < firstRun.bytecode.size := by rw [bytecodeEq]; exact first.isLt
      have left : firstRun.bytecode[first.val]? =
          some firstRun.bytecode[(⟨first.val, bound⟩ : Fin firstRun.bytecode.size)] :=
        Array.getElem?_eq_getElem bound
      rw [left,
        Array.getElem?_eq_getElem first.isLt] at h
      have finEq : step.rowIndex = (⟨first.val, bound⟩ : Fin firstRun.bytecode.size) :=
        Fin.ext first'
      simpa only [finEq] using congrArg JoltInstructionRow.instruction (Option.some.inj h)
    simpa only [instructionEq] using advice

private theorem division_replay_suffix
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (base current : UntrustedAnswerRun joltInstance privateInputs)
    {bytecode : Array JoltInstructionRow} (first : Fin bytecode.size)
    (expanded : expand_program joltInstance.program = some bytecode)
    (starts : bytecode[first].starts_source = true)
    (count : (expansionInstructions bytecode first).length =
      expansionRowCount bytecode first)
    (arithmetic : ∀ row ∈ expansionInstructions bytecode first, DivisionArithmeticRow row)
    (q : BitVec 64) (pre middle post : SailJoltState)
    (done : Nat) (positive : 0 < done)
    (within : done ≤ expansionRowCount bytecode first)
    (replayed : DivisionReplayRows base current first done pre middle q)
    (tailRun : Program.Run (Program.seq (((expansionInstructions bytecode first).drop done).map
      (patchAdviceWord q))) middle post) :
    ∃ finalRun : UntrustedAnswerRun joltInstance privateInputs,
      DivisionReplayRows base finalRun first (expansionRowCount bytecode first)
        pre post q := by
  generalize left : expansionRowCount bytecode first - done = remaining
  induction remaining generalizing done current middle with
  | zero =>
    have full : done = expansionRowCount bytecode first := by omega
    have empty : (expansionInstructions bytecode first).drop done = [] := by
      apply List.drop_eq_nil_of_le
      rw [count]
      omega
    rw [empty] at tailRun
    have same : middle = post := by
      simp [Program.seq, Program.Run, execProgram] at tailRun
      cases tailRun
      rfl
    subst done
    subst post
    exact ⟨current, replayed⟩
  | succ remaining ih =>
    have inside : done < expansionRowCount bytecode first := by omega
    have headBound : done < (expansionInstructions bytecode first).length := by
      rw [count]
      exact inside
    rw [List.drop_eq_getElem_cons headBound, List.map_cons] at tailRun
    obtain ⟨nextPost, headRun, restRun⟩ := execProgram_instr_run_retire_inv
      (patchAdviceWord q (expansionInstructions bytecode first)[done])
      (Program.seq (((expansionInstructions bytecode first).drop (done + 1)).map
        (patchAdviceWord q))) middle post tailRun
    obtain ⟨next, nextIndex, entry⟩ := division_replay_next_entry base current first
      expanded starts done positive inside pre middle q replayed
    have bytecodeEq : current.bytecode = bytecode :=
      Option.some.inj (current.expands.symm.trans expanded)
    have atBytecode : bytecode[first.val + done]? = some current.bytecode[next] := by
      rw [← nextIndex]
      have h := congrArg (fun b : Array JoltInstructionRow => b[next.val]?) bytecodeEq
      change current.bytecode[next.val]? = bytecode[next.val]? at h
      rw [Array.getElem?_eq_getElem next.isLt] at h
      exact h.symm
    have instrAt := expansionInstructions_at bytecode first done inside count _ atBytecode
    have rowArithmetic : DivisionArithmeticRow current.bytecode[next].instruction := by
      rw [← instrAt]
      exact arithmetic _ (List.getElem_mem _)
    have executes : execInstr (patchAdviceWord q current.bytecode[next].instruction)
        middle = .ok RETIRE_SUCCESS nextPost := by
      rw [instrAt] at headRun
      exact headRun
    let step := divisionReplayStep next middle nextPost q
    have relaxed := divisionReplayStep_exec next middle nextPost q rowArithmetic executes
    let extended := appendUntrustedRow current step 0 relaxed
      (rawEntry_starts entry) (rawEntry_linked entry)
    have nextReplayed : DivisionReplayRows base extended first (done + 1)
        pre nextPost q := by
      apply DivisionReplayRows.push base current first done positive pre middle nextPost q
        replayed step 0 relaxed (rawEntry_starts entry) (rawEntry_linked entry)
      · exact nextIndex
      · rfl
      · exact runtimeAdviceFor_observation _ q
    exact ih extended nextPost (done + 1) (by omega) (by omega) nextReplayed
      restRun (by omega)

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
  obtain ⟨middle, firstRun, replayed, tailRun⟩ :=
    division_replay_first_state context run first kind rd rs1 rs2 count shape
      pre honestPost entry honestRun
  exact division_replay_suffix run firstRun first context.expands state.starts count
    shape.arithmetic (kind.honestAdvice rd rs1 rs2 pre) pre middle honestPost 1
    (by omega) (by unfold expansionRowCount; omega) replayed tailRun

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
