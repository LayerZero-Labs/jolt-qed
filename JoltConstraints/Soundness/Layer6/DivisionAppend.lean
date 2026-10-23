import JoltConstraints.Soundness.Layer6.DivisionPrograms
import JoltConstraints.Completeness.Helpers.RegistersReadProofHelpers
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

private theorem division_expansion_instruction_at
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (trace : UntrustedAnswerRun joltInstance privateInputs)
    {bytecode : Array JoltInstructionRow} (first : Fin bytecode.size)
    (expanded : expand_program joltInstance.program = some bytecode)
    (count : (expansionInstructions bytecode first).length = expansionRowCount bytecode first)
    (offset : Nat) (inside : offset < expansionRowCount bytecode first)
    (row : TraceRow trace.bytecode) (index : row.rowIndex.val = first.val + offset) :
    (expansionInstructions bytecode first)[offset]'(by omega) =
      trace.bytecode[row.rowIndex].instruction := by
  have bytecodeEq : trace.bytecode = bytecode :=
    Option.some.inj (trace.expands.symm.trans expanded)
  have bound : first.val + offset < bytecode.size := by
    rw [← index, ← bytecodeEq]
    exact row.rowIndex.isLt
  let i : Fin bytecode.size := ⟨first.val + offset, bound⟩
  have atContext : bytecode[first.val + offset]? = some bytecode[i] := by simp [i]
  have instrAt := expansionInstructions_at bytecode first offset inside count _ atContext
  have rowEq : bytecode[i] = trace.bytecode[row.rowIndex] := by
    have h := congrArg (fun b : Array JoltInstructionRow => b[first.val + offset]?) bytecodeEq
    change trace.bytecode[first.val + offset]? = bytecode[first.val + offset]? at h
    have traceBound : first.val + offset < trace.bytecode.size := by
      rw [← index]
      exact row.rowIndex.isLt
    simp only [Array.getElem?_eq_getElem traceBound,
      Array.getElem?_eq_getElem bound] at h
    have finEq : (⟨first.val + offset, traceBound⟩ : Fin trace.bytecode.size) =
        row.rowIndex := Fin.ext index.symm
    have h' := (Option.some.inj h).symm
    change bytecode[i] = trace.bytecode[(⟨first.val + offset, traceBound⟩ :
      Fin trace.bytecode.size)] at h'
    exact h'.trans (congrArg (fun j : Fin trace.bytecode.size => trace.bytecode[j]) finEq)
  simpa only [rowEq] using instrAt

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
  exact division_expansion_instruction_at replay first expanded count offset inside row index

private theorem division_runtime_patch (instruction : Instr)
    (runtime : instruction.RuntimeAdvice) :
    instruction.withRuntimeAdvice runtime =
      patchAdviceWord ((instruction.withRuntimeAdvice runtime).adviceValue?.getD 0)
        instruction := by
  apply patchAdviceWord_runtime
  intro value present
  simp_all [Option.mem_def]

private theorem divisionArithmeticRow_patch (instruction : Instr) (word : BitVec 64)
    (arithmetic : DivisionArithmeticRow instruction) :
    DivisionArithmeticRow (patchAdviceWord word instruction) := by
  unfold patchAdviceWord
  split
  · exact True.intro
  · exact arithmetic

private theorem division_trace_row_frame
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (run : UntrustedAnswerRun joltInstance privateInputs)
    (kind : DivisionKind) (rd rs1 rs2 : regidx)
    (rows : List Instr)
    (shape : ArithmeticAdviceSequence rows (kind.program rd rs1 rs2))
    (step : Fin run.rows.size) (offset : Nat) (inside : offset < rows.length)
    (atInstruction : rows[offset] =
      run.bytecode[run.rows[step].rowIndex].instruction) :
    DivisionFrame run.rows[step].preState run.rows[step].postState ∧
      (offset + 1 < rows.length →
        run.rows[step].postState.sail = run.rows[step].preState.sail) := by
  let instr := run.bytecode[run.rows[step].rowIndex].instruction
  let runtime := run.rows[step].runtimeAdvice
  let q := (instr.withRuntimeAdvice runtime).adviceValue?.getD 0
  have programEq := shape.program_eq q
  have lengthEq : (kind.program rd rs1 rs2 q).instrs.length = rows.length := by
    rw [programEq, divisionProgram_instrs_seq, List.length_map]
  have programInstr : (kind.program rd rs1 rs2 q).instrs[offset]'(by omega) =
      instr.withRuntimeAdvice runtime := by
    simp only [programEq, divisionProgram_instrs_seq, List.getElem_map, atInstruction]
    exact (division_runtime_patch instr runtime).symm
  have rawArithmetic : DivisionArithmeticRow instr := by
    change DivisionArithmeticRow run.bytecode[run.rows[step].rowIndex].instruction
    rw [← atInstruction]
    exact shape.arithmetic _ (List.getElem_mem inside)
  have runtimeArithmetic : DivisionArithmeticRow (instr.withRuntimeAdvice runtime) := by
    rw [division_runtime_patch]
    exact divisionArithmeticRow_patch instr q rawArithmetic
  have executes := run.executes step
  change execWithTapeAnswer (instr.withRuntimeAdvice runtime)
    (run.answers step) run.rows[step].preState =
      .ok RETIRE_SUCCESS run.rows[step].postState at executes
  rw [arithmetic_exec_eq _ runtimeArithmetic] at executes
  have frame := division_program_row_frame kind rd rs1 rs2 q offset (by omega)
    run.rows[step].preState run.rows[step].postState (by rw [programInstr]; exact executes)
  exact ⟨frame.1, fun proper => frame.2 (by omega)⟩

private theorem division_block_row_frame
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (trace : UntrustedAnswerRun joltInstance privateInputs)
    {bytecode : Array JoltInstructionRow} (first : Fin bytecode.size)
    (expanded : expand_program joltInstance.program = some bytecode)
    (count : (expansionInstructions bytecode first).length = expansionRowCount bytecode first)
    (kind : DivisionKind) (rd rs1 rs2 : regidx)
    (shape : ArithmeticAdviceSequence (expansionInstructions bytecode first)
      (kind.program rd rs1 rs2))
    (step : Fin trace.rows.size) (offset : Nat)
    (inside : offset < expansionRowCount bytecode first)
    (index : trace.rows[step].rowIndex.val = first.val + offset) :
    DivisionFrame trace.rows[step].preState trace.rows[step].postState ∧
      (offset + 1 < expansionRowCount bytecode first →
        trace.rows[step].postState.sail = trace.rows[step].preState.sail) := by
  have instruction := division_expansion_instruction_at trace first expanded count offset
    inside trace.rows[step] index
  have frame := division_trace_row_frame trace kind rd rs1 rs2
    (expansionInstructions bytecode first) shape step offset (by omega) instruction
  exact ⟨frame.1, fun proper => frame.2 (by omega)⟩

private theorem division_block_arithmetic
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (trace : UntrustedAnswerRun joltInstance privateInputs)
    {bytecode : Array JoltInstructionRow} (first : Fin bytecode.size)
    (expanded : expand_program joltInstance.program = some bytecode)
    (count : (expansionInstructions bytecode first).length = expansionRowCount bytecode first)
    (kind : DivisionKind) (rd rs1 rs2 : regidx)
    (shape : ArithmeticAdviceSequence (expansionInstructions bytecode first)
      (kind.program rd rs1 rs2))
    (step : Fin trace.rows.size) (offset : Nat)
    (inside : offset < expansionRowCount bytecode first)
    (index : trace.rows[step].rowIndex.val = first.val + offset) :
    DivisionArithmeticRow trace.bytecode[trace.rows[step].rowIndex].instruction := by
  have instruction := division_expansion_instruction_at trace first expanded count offset
    inside trace.rows[step] index
  rw [← instruction]
  exact shape.arithmetic _ (List.getElem_mem (by omega))

private theorem DivisionArithmeticRow.ram_none (instruction : Instr)
    (pre : SailJoltState) (arithmetic : DivisionArithmeticRow instruction) :
    TraceWitness.ramAccessAddress instruction pre = none := by
  unfold TraceWitness.ramAccessAddress
  split <;> simp_all [DivisionArithmeticRow]

private theorem DivisionArithmeticRow.ramAddress_zero
    {F : Type} [Field F] (params : WitnessParams) (trace : Trace)
    (t : Fin params.traceLength) (inside : t.val < trace.rows.size)
    (arithmetic : DivisionArithmeticRow
      trace.bytecode[(trace.rows[t.val]'inside).rowIndex].instruction) :
    TraceWitness.RamAddress (F := F) params trace t = 0 := by
  unfold TraceWitness.RamAddress
  simp only [dif_pos inside]
  have noRam := DivisionArithmeticRow.ram_none
    trace.bytecode[(trace.rows[t.val]'inside).rowIndex].instruction
    (trace.rows[t.val]'inside).preState arithmetic
  change (match TraceWitness.ramAccessAddress
    trace.bytecode[(trace.rows[t.val]'inside).rowIndex].instruction
    (trace.rows[t.val]'inside).preState with
    | some address => (address.toNat : F)
    | none => 0) = 0
  rw [noRam]

private theorem DivisionArithmeticRow.notStoresTerminationAt
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (trace : UntrustedAnswerRun joltInstance privateInputs)
    (step : Fin trace.rows.size)
    (arithmetic : DivisionArithmeticRow
      trace.bytecode[trace.rows[step].rowIndex].instruction) :
    ¬ trace.StoresTerminationAt step := by
  intro stored
  unfold UntrustedAnswerRun.StoresTerminationAt at stored
  split at stored
  · simp_all [DivisionArithmeticRow]
  · exact stored

private theorem division_replay_finalRamWord
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (candidate replay : UntrustedAnswerRun joltInstance privateInputs)
    (honestPost : SailJoltState)
    (same : DivisionFinalAgreement (TraceWitness.finalTraceState candidate.toTrace) honestPost)
    (finalPost : TraceWitness.finalTraceState replay.toTrace = honestPost)
    (address : Nat) :
    TraceWitness.finalRamWord candidate.toTrace address =
      TraceWitness.finalRamWord replay.toTrace address := by
  have initialEq : candidate.initialState = replay.initialState :=
    Option.some.inj (candidate.initialized.symm.trans replay.initialized)
  have sailEq : (TraceWitness.finalTraceState replay.toTrace).sail =
      (TraceWitness.finalTraceState candidate.toTrace).sail := by
    rw [finalPost]
    exact same.sail
  have deviceEq : (TraceWitness.finalTraceState replay.toTrace).jolt_device =
      (TraceWitness.finalTraceState candidate.toTrace).jolt_device := by
    rw [finalPost]
    exact same.device
  simp only [TraceWitness.finalRamWord, ← initialEq, sailEq, deviceEq]

private theorem division_segment_pre_frame
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (trace : UntrustedAnswerRun joltInstance privateInputs)
    (base first count : Nat) (pre : SailJoltState)
    (ordered : ∀ offset < count,
      ∃ row ∈ trace.rows[base + offset]?, row.rowIndex.val = first + offset)
    (firstPre : ∀ row ∈ trace.rows[base]?, row.preState = pre)
    (rowFrame : ∀ offset < count, ∀ row ∈ trace.rows[base + offset]?,
      DivisionFrame row.preState row.postState ∧
        (offset + 1 < count → row.postState.sail = row.preState.sail))
    (remaining : ∀ offset, offset + 1 < count →
      ∀ row ∈ trace.rows[base + offset]?,
        trace.bytecode[row.rowIndex].virtual_sequence_remaining.getD 0 ≠ 0)
    (offset : Nat) (inside : offset < count) :
    ∃ row ∈ trace.rows[base + offset]?,
      DivisionFrame pre row.preState ∧ row.preState.sail = pre.sail := by
  induction offset with
  | zero =>
    obtain ⟨row, atRow, _⟩ := ordered 0 inside
    refine ⟨row, by simpa only [Nat.add_zero] using atRow, ?_⟩
    have starts := firstPre row (by simpa only [Nat.add_zero] using atRow)
    rw [starts]
    exact ⟨divisionFrame_refl pre, rfl⟩
  | succ previous ih =>
    have priorInside : previous < count := by omega
    obtain ⟨prior, priorAt, priorFrame, priorSail⟩ := ih priorInside
    obtain ⟨row, rowAt, rowIndex⟩ := ordered (previous + 1) inside
    have priorFrameStep := (rowFrame previous priorInside prior priorAt).1
    have priorSailStep := (rowFrame previous priorInside prior priorAt).2 (by omega)
    have linked := trace.linked (base + previous) prior row priorAt
      (by simpa only [Nat.add_assoc] using rowAt)
    rw [if_pos (remaining previous (by omega) prior priorAt)] at linked
    have preEq : row.preState = prior.postState := linked.2
    refine ⟨row, by simpa only [Nat.add_assoc] using rowAt, ?_, ?_⟩
    · rw [preEq]
      exact divisionFrame_trans pre prior.preState prior.postState priorFrame priorFrameStep
    · rw [preEq, priorSailStep, priorSail]

private theorem division_ordered_interior_remaining
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (trace : UntrustedAnswerRun joltInstance privateInputs)
    {bytecode : Array JoltInstructionRow} (first : Fin bytecode.size)
    (expanded : expand_program joltInstance.program = some bytecode)
    (starts : bytecode[first].starts_source = true)
    (base : Nat)
    (ordered : ∀ offset < expansionRowCount bytecode first,
      ∃ row ∈ trace.rows[base + offset]?, row.rowIndex.val = first.val + offset)
    (k : Nat) (proper : k + 1 < expansionRowCount bytecode first)
    (row : TraceRow trace.bytecode) (atRow : row ∈ trace.rows[base + k]?) :
    trace.bytecode[row.rowIndex].virtual_sequence_remaining.getD 0 ≠ 0 := by
  obtain ⟨other, otherAt, index⟩ := ordered k (by omega)
  have same : row = other := Option.some.inj (atRow.symm.trans otherAt)
  subst other
  have bytecodeEq : trace.bytecode = bytecode :=
    Option.some.inj (trace.expands.symm.trans expanded)
  have atContext : bytecode[first.val + k]? =
      some trace.bytecode[row.rowIndex] := by
    have sameAt := congrArg (fun b : Array JoltInstructionRow => b[first.val + k]?) bytecodeEq
    have atTrace : trace.bytecode[first.val + k]? =
        some trace.bytecode[row.rowIndex] := by
      simpa only [← index] using (Array.getElem?_eq_getElem row.rowIndex.isLt)
    exact sameAt.symm.trans atTrace
  exact expansion_row_remaining joltInstance.program bytecode expanded first starts k
    proper _ atContext

private theorem division_block_pre_frame
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (trace : UntrustedAnswerRun joltInstance privateInputs)
    {bytecode : Array JoltInstructionRow} (first : Fin bytecode.size)
    (expanded : expand_program joltInstance.program = some bytecode)
    (starts : bytecode[first].starts_source = true)
    (count : (expansionInstructions bytecode first).length = expansionRowCount bytecode first)
    (kind : DivisionKind) (rd rs1 rs2 : regidx)
    (shape : ArithmeticAdviceSequence (expansionInstructions bytecode first)
      (kind.program rd rs1 rs2))
    (base : Nat) (pre : SailJoltState)
    (ordered : ∀ offset < expansionRowCount bytecode first,
      ∃ row ∈ trace.rows[base + offset]?, row.rowIndex.val = first.val + offset)
    (firstPre : ∀ row ∈ trace.rows[base]?, row.preState = pre)
    (offset : Nat) (inside : offset < expansionRowCount bytecode first) :
    ∃ row ∈ trace.rows[base + offset]?,
      DivisionFrame pre row.preState ∧ row.preState.sail = pre.sail := by
  have rowFrame (k : Nat) (inBlock : k < expansionRowCount bytecode first)
      (row : TraceRow trace.bytecode) (atRow : row ∈ trace.rows[base + k]?) :
      DivisionFrame row.preState row.postState ∧
        (k + 1 < expansionRowCount bytecode first →
          row.postState.sail = row.preState.sail) := by
    obtain ⟨other, otherAt, index⟩ := ordered k inBlock
    have same : row = other := Option.some.inj (atRow.symm.trans otherAt)
    subst other
    have bound : base + k < trace.rows.size := (Array.getElem?_eq_some_iff.mp atRow).1
    let step : Fin trace.rows.size := ⟨base + k, bound⟩
    have rowEq : trace.rows[step] = row := (Array.getElem?_eq_some_iff.mp atRow).2
    have frame := division_block_row_frame trace first expanded count kind rd rs1 rs2
      shape step k inBlock (by rw [rowEq]; exact index)
    simpa only [rowEq] using frame
  have remaining (k : Nat) (proper : k + 1 < expansionRowCount bytecode first)
      (row : TraceRow trace.bytecode) (atRow : row ∈ trace.rows[base + k]?) :
      trace.bytecode[row.rowIndex].virtual_sequence_remaining.getD 0 ≠ 0 :=
    division_ordered_interior_remaining trace first expanded starts base ordered
      k proper row atRow
  exact division_segment_pre_frame trace base first.val
    (expansionRowCount bytecode first) pre ordered firstPre rowFrame remaining offset inside

private theorem division_transport_size {a b : Array JoltInstructionRow}
    (same : b = a) (rows : Array (TraceRow b)) :
    (same ▸ rows : Array (TraceRow a)).size = rows.size := by
  cases same
  rfl

private theorem division_transport_post_at? {a b : Array JoltInstructionRow}
    (same : b = a) (rows : Array (TraceRow b)) (i : Nat) :
    ((same ▸ rows : Array (TraceRow a))[i]?).map TraceRow.postState =
      (rows[i]?).map TraceRow.postState := by
  cases same
  rfl

private theorem division_transport_index_at? {a b : Array JoltInstructionRow}
    (same : b = a) (rows : Array (TraceRow b)) (i : Nat) :
    ((same ▸ rows : Array (TraceRow a))[i]?).map (fun row => row.rowIndex.val) =
      (rows[i]?).map (fun row => row.rowIndex.val) := by
  cases same
  rfl

private theorem RunExtends.prefix_get?
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (run extended : UntrustedAnswerRun joltInstance privateInputs)
    (extendsRun : RunExtends run extended) (i : Nat) (inside : i < run.rows.size) :
    ∃ same : extended.bytecode = run.bytecode,
      (same ▸ extended.rows : Array (TraceRow run.bytecode))[i]? = run.rows[i]? := by
  obtain ⟨same, retained⟩ := extendsRun
  refine ⟨same, ?_⟩
  have sizeEq := division_transport_size same extended.rows
  have bound : run.rows.size ≤ extended.rows.size := by
    have sizes := congrArg Array.size retained
    simp only [Array.size_extract, Nat.sub_zero, sizeEq] at sizes
    omega
  have atPrefix := congrArg (fun rows : Array (TraceRow run.bytecode) => rows[i]?) retained
  simpa only [Array.getElem?_extract, sizeEq, Nat.min_eq_left bound, Nat.zero_add,
    Nat.sub_zero, if_pos inside] using atPrefix

private theorem RunExtends.prefix_post
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (run extended : UntrustedAnswerRun joltInstance privateInputs)
    (extendsRun : RunExtends run extended) (i : Nat) (inside : i < run.rows.size)
    (extendedInside : i < extended.rows.size) :
    extended.rows[i].postState = run.rows[i].postState := by
  obtain ⟨same, atPrefix⟩ := RunExtends.prefix_get? run extended extendsRun i inside
  have mapped := congrArg (Option.map TraceRow.postState) atPrefix
  rw [division_transport_post_at? same extended.rows i] at mapped
  simpa only [Array.getElem?_eq_getElem extendedInside,
    Array.getElem?_eq_getElem inside, Option.map_some, Option.some.injEq] using mapped

private theorem RunExtends.prefix_index
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (run extended : UntrustedAnswerRun joltInstance privateInputs)
    (extendsRun : RunExtends run extended) (i : Nat) (inside : i < run.rows.size)
    (extendedInside : i < extended.rows.size) :
    extended.rows[i].rowIndex.val = run.rows[i].rowIndex.val := by
  obtain ⟨same, atPrefix⟩ := RunExtends.prefix_get? run extended extendsRun i inside
  have mapped := congrArg (Option.map fun row : TraceRow run.bytecode => row.rowIndex.val) atPrefix
  rw [division_transport_index_at? same extended.rows i] at mapped
  simpa only [Array.getElem?_eq_getElem extendedInside,
    Array.getElem?_eq_getElem inside, Option.map_some, Option.some.injEq] using mapped

private theorem RunExtends.prefix_row_heq
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (run candidate replay : UntrustedAnswerRun joltInstance privateInputs)
    (candidateExtends : RunExtends run candidate)
    (replayExtends : RunExtends run replay)
    (i : Nat) (inside : i < run.rows.size)
    (candidateInside : i < candidate.rows.size) (replayInside : i < replay.rows.size) :
    HEq candidate.rows[i] replay.rows[i] := by
  obtain ⟨candidateEq, candidateAt⟩ :=
    RunExtends.prefix_get? run candidate candidateExtends i inside
  obtain ⟨replayEq, replayAt⟩ :=
    RunExtends.prefix_get? run replay replayExtends i inside
  rcases run with ⟨⟨runBytecode, runRows, _⟩, _⟩
  rcases candidate with ⟨⟨candidateBytecode, candidateRows, _⟩, _⟩
  rcases replay with ⟨⟨replayBytecode, replayRows, _⟩, _⟩
  dsimp only at candidateEq candidateAt replayEq replayAt candidateInside replayInside ⊢
  subst candidateEq
  subst replayEq
  have h := candidateAt.trans replayAt.symm
  have rowEq : candidateRows[i] = replayRows[i] := by
    simpa only [Array.getElem?_eq_getElem candidateInside,
      Array.getElem?_eq_getElem replayInside, Option.some.injEq] using h
  rw [rowEq]

private theorem RunExtends.priorBoundary
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (run replay : UntrustedAnswerRun joltInstance privateInputs)
    (extendsRun : RunExtends run replay)
    (prior : ∀ last ∈ run.rows.back?,
      run.bytecode[last.rowIndex].virtual_sequence_remaining.getD 0 = 0)
    (last : TraceRow replay.bytecode)
    (atBack : last ∈ (replay.rows.extract 0 run.rows.size).back?) :
    replay.bytecode[last.rowIndex].virtual_sequence_remaining.getD 0 = 0 := by
  obtain ⟨bytecodeEq, rowsEq⟩ := extendsRun
  rcases run with ⟨⟨runBytecode, runRows, _⟩, _⟩
  rcases replay with ⟨⟨replayBytecode, replayRows, _⟩, _⟩
  dsimp only at bytecodeEq rowsEq prior atBack ⊢
  subst bytecodeEq
  dsimp only at rowsEq prior atBack ⊢
  rw [rowsEq] at atBack
  exact prior last atBack

private theorem division_replay_index_eq
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (run candidate replay : UntrustedAnswerRun joltInstance privateInputs)
    (first count : Nat)
    (candidateExtends : RunExtends run candidate)
    (replayExtends : RunExtends run replay)
    (candidateSize : candidate.rows.size = run.rows.size + count)
    (replaySize : replay.rows.size = run.rows.size + count)
    (candidateOrdered : ∀ offset < count,
      ∃ row ∈ candidate.rows[run.rows.size + offset]?,
        row.rowIndex.val = first + offset)
    (replayOrdered : ∀ offset < count,
      ∃ row ∈ replay.rows[run.rows.size + offset]?,
        row.rowIndex.val = first + offset)
    (i : Nat) (candidateInside : i < candidate.rows.size)
    (replayInside : i < replay.rows.size) :
    candidate.rows[i].rowIndex.val = replay.rows[i].rowIndex.val := by
  by_cases old : i < run.rows.size
  · calc
      candidate.rows[i].rowIndex.val = run.rows[i].rowIndex.val :=
        RunExtends.prefix_index run candidate candidateExtends i old candidateInside
      _ = replay.rows[i].rowIndex.val :=
        (RunExtends.prefix_index run replay replayExtends i old replayInside).symm
  · let offset := i - run.rows.size
    have inside : offset < count := by dsimp [offset]; omega
    obtain ⟨candidateRow, candidateAt, candidateIndex⟩ := candidateOrdered offset inside
    obtain ⟨replayRow, replayAt, replayIndex⟩ := replayOrdered offset inside
    have position : run.rows.size + offset = i := by dsimp [offset]; omega
    have candidateAtI : candidate.rows[i]? = some candidateRow := by
      simpa only [position] using candidateAt
    have replayAtI : replay.rows[i]? = some replayRow := by
      simpa only [position] using replayAt
    have candidateRowEq : candidate.rows[i] = candidateRow :=
      Option.some.inj ((Array.getElem?_eq_getElem candidateInside).symm.trans candidateAtI)
    have replayRowEq : replay.rows[i] = replayRow :=
      Option.some.inj ((Array.getElem?_eq_getElem replayInside).symm.trans replayAtI)
    rw [candidateRowEq, replayRowEq]
    omega

private theorem RunExtends.prefix_observations
    {F : Type} [Field F] {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} (params : WitnessParams)
    (run candidate replay : UntrustedAnswerRun joltInstance privateInputs)
    (candidateExtends : RunExtends run candidate)
    (replayExtends : RunExtends run replay)
    (t : Fin params.traceLength) (old : t.val < run.rows.size)
    (candidateInside : t.val < candidate.rows.size)
    (replayInside : t.val < replay.rows.size) :
    TraceWitness.PC (F := F) params candidate.toTrace t =
        TraceWitness.PC (F := F) params replay.toTrace t ∧
      TraceWitness.Rs1Value (F := F) params candidate.toTrace t =
        TraceWitness.Rs1Value (F := F) params replay.toTrace t ∧
      TraceWitness.Rs2Value (F := F) params candidate.toTrace t =
        TraceWitness.Rs2Value (F := F) params replay.toTrace t ∧
      TraceWitness.RamAddress (F := F) params candidate.toTrace t =
        TraceWitness.RamAddress (F := F) params replay.toTrace t ∧
      (candidate.rows[t.val].StableStall ↔ replay.rows[t.val].StableStall) ∧
      (candidate.StoresTerminationAt ⟨t.val, candidateInside⟩ ↔
        replay.StoresTerminationAt ⟨t.val, replayInside⟩) := by
  have rowEq := RunExtends.prefix_row_heq run candidate replay candidateExtends
    replayExtends t.val old candidateInside replayInside
  obtain ⟨candidateEq, _⟩ := candidateExtends
  obtain ⟨replayEq, _⟩ := replayExtends
  rcases run with ⟨⟨runBytecode, runRows, _⟩, _⟩
  rcases candidate with ⟨⟨candidateBytecode, candidateRows, _⟩, _⟩
  rcases replay with ⟨⟨replayBytecode, replayRows, _⟩, _⟩
  dsimp only at candidateEq replayEq rowEq candidateInside replayInside ⊢
  subst candidateEq
  subst replayEq
  have sameRow : candidateRows[t.val] = replayRows[t.val] := eq_of_heq rowEq
  have sameAt :
      candidateRows[(⟨t.val, candidateInside⟩ : Fin candidateRows.size)] =
        replayRows[(⟨t.val, replayInside⟩ : Fin replayRows.size)] := by
    change candidateRows[t.val] = replayRows[t.val]
    exact sameRow
  constructor
  · simp only [TraceWitness.PC, TraceWitness.bytecodePc,
      dif_pos candidateInside, dif_pos replayInside, sameRow]
  constructor
  · simp only [TraceWitness.Rs1Value, dif_pos candidateInside,
      dif_pos replayInside, sameRow]
  constructor
  · simp only [TraceWitness.Rs2Value, dif_pos candidateInside,
      dif_pos replayInside, sameRow]
  constructor
  · simp only [TraceWitness.RamAddress, dif_pos candidateInside,
      dif_pos replayInside, sameRow]
  constructor
  · simp only [TraceRow.StableStall, sameRow]
  · simp only [UntrustedAnswerRun.StoresTerminationAt, sameAt]

private theorem division_source_is_compressed_eq
    {a b : Array JoltInstructionRow} (same : a = b)
    (i : Fin a.size) (j : Fin b.size) (index : i.val = j.val) :
    source_is_compressed a i = source_is_compressed b j := by
  cases same
  have : i = j := Fin.ext index
  subst j
  rfl

private theorem division_bytecode_at_eq
    {a b : Array JoltInstructionRow} (same : a = b)
    (i : Fin a.size) (j : Fin b.size) (index : i.val = j.val) :
    a[i] = b[j] := by
  cases same
  have : i = j := Fin.ext index
  subst j
  rfl

private theorem division_candidate_first_pre
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (run candidate : UntrustedAnswerRun joltInstance privateInputs)
    (first : Nat) (pre : SailJoltState)
    (entry : ∃ next : Fin run.bytecode.size, next.val = first ∧ run.NextStep next pre)
    (extendsRun : RunExtends run candidate)
    (firstRow : ∃ row ∈ candidate.rows[run.rows.size]?, row.rowIndex.val = first)
    (row : TraceRow candidate.bytecode) (atRow : row ∈ candidate.rows[run.rows.size]?) :
    row.preState = pre := by
  obtain ⟨next, nextIndex, nextStep⟩ := entry
  obtain ⟨chosen, chosenAt, chosenIndex⟩ := firstRow
  have rowEq : row = chosen := Option.some.inj (atRow.symm.trans chosenAt)
  subst chosen
  have sameBytecode : candidate.bytecode = run.bytecode := extendsRun.choose
  have indexEq : row.rowIndex.val = next.val := by omega
  have compressedEq := division_source_is_compressed_eq sameBytecode
    row.rowIndex next indexEq
  by_cases empty : run.rows.size = 0
  · have runBack : run.rows.back? = none := by
      have rowsEmpty : run.rows = #[] := Array.size_eq_zero_iff.mp empty
      simp [rowsEmpty]
    have ready := nextStep.ready
    simp only [runBack] at ready
    have atZero : row ∈ candidate.rows[0]? := by simpa only [empty] using atRow
    have starts := candidate.starts row atZero
    have initialEq : candidate.initialState = run.initialState :=
      Option.some.inj (candidate.initialized.symm.trans run.initialized)
    calc
      row.preState = advance_pc joltInstance.program.entry_address
          (source_is_compressed candidate.bytecode row.rowIndex) candidate.initialState := starts.2.2
      _ = advance_pc joltInstance.program.entry_address
          (source_is_compressed run.bytecode next) run.initialState := by rw [compressedEq, initialEq]
      _ = pre := ready.2.2.symm
  · have positive : 0 < run.rows.size := by omega
    let i := run.rows.size - 1
    have oldInside : i < run.rows.size := by dsimp [i]; omega
    have candidateBound : run.rows.size < candidate.rows.size :=
      (Array.getElem?_eq_some_iff.mp atRow).1
    have candidateInside : i < candidate.rows.size := by dsimp [i]; omega
    let prior : TraceRow candidate.bytecode := candidate.rows[i]'candidateInside
    let last : TraceRow run.bytecode := run.rows[i]'oldInside
    have priorAt : candidate.rows[i]? = some prior := Array.getElem?_eq_getElem candidateInside
    have lastAt : run.rows.back? = some last := by
      rw [Array.back?_eq_getElem?]
      change run.rows[run.rows.size - 1]? = some run.rows[run.rows.size - 1]
      exact Array.getElem?_eq_getElem (by omega)
    have rowAtNext : candidate.rows[i + 1]? = some row := by
      simpa only [show i + 1 = run.rows.size by dsimp [i]; omega] using atRow
    have postEq : prior.postState = last.postState :=
      RunExtends.prefix_post run candidate extendsRun i oldInside candidateInside
    have priorIndex : prior.rowIndex.val = last.rowIndex.val :=
      RunExtends.prefix_index run candidate extendsRun i oldInside candidateInside
    have bytecodeAt := division_bytecode_at_eq sameBytecode prior.rowIndex last.rowIndex priorIndex
    have linked := candidate.linked i prior row priorAt rowAtNext
    have ready := nextStep.ready
    simp only [lastAt] at ready
    by_cases remaining : run.bytecode[last.rowIndex].virtual_sequence_remaining.getD 0 ≠ 0
    · have candidateRemaining :
          candidate.bytecode[prior.rowIndex].virtual_sequence_remaining.getD 0 ≠ 0 := by
        rw [bytecodeAt]
        exact remaining
      rw [if_pos candidateRemaining] at linked
      rw [if_pos remaining] at ready
      calc
        row.preState = prior.postState := linked.2
        _ = last.postState := postEq
        _ = pre := ready.2.symm
    · have candidateRemaining :
          ¬ candidate.bytecode[prior.rowIndex].virtual_sequence_remaining.getD 0 ≠ 0 := by
        rw [bytecodeAt]
        exact remaining
      rw [if_neg candidateRemaining] at linked
      rw [if_neg remaining] at ready
      obtain ⟨candidateAddress, candidatePC, _, _, candidatePre⟩ := linked
      obtain ⟨runAddress, runPC, _, _, _, runPre⟩ := ready
      have addressEq : candidateAddress = runAddress := by
        rw [postEq] at candidatePC
        exact Option.some.inj (candidatePC.symm.trans runPC)
      calc
        row.preState = advance_pc candidateAddress
            (source_is_compressed candidate.bytecode row.rowIndex) prior.postState := candidatePre
        _ = advance_pc runAddress (source_is_compressed run.bytecode next) last.postState := by
          rw [addressEq, compressedEq, postEq]
        _ = pre := runPre.symm

private theorem division_replay_pre_frames
    {F : Type} [Field F] {joltInstance : JoltInstance SourceInstruction}
    {params : WitnessParams} {privateInputs : JoltPrivateInputs}
    (witness : WitnessType F params)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (run candidate replay : UntrustedAnswerRun joltInstance privateInputs)
    (first : Fin context.bytecode.size)
    (starts : context.bytecode[first].starts_source = true)
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
    (replayed : DivisionReplayRows run replay first (expansionRowCount context.bytecode first)
      pre honestPost (kind.honestAdvice rd rs1 rs2 pre))
    (offset : Nat) (inside : offset < expansionRowCount context.bytecode first) :
    (∃ row ∈ candidate.rows[run.rows.size + offset]?,
      DivisionFrame pre row.preState ∧ row.preState.sail = pre.sail) ∧
    (∃ row ∈ replay.rows[run.rows.size + offset]?,
      DivisionFrame pre row.preState ∧ row.preState.sail = pre.sail) := by
  have candidateOrdered (k : Nat) (bound : k < expansionRowCount context.bytecode first) :
      ∃ row ∈ candidate.rows[run.rows.size + k]?, row.rowIndex.val = first.val + k := by
    have ordered := complete.ordered k bound
    simpa only [candidateSize, Nat.add_sub_cancel_right] using ordered
  have positive : 0 < expansionRowCount context.bytecode first := by
    unfold expansionRowCount
    omega
  have candidateFirst (row : TraceRow candidate.bytecode)
      (atRow : row ∈ candidate.rows[run.rows.size]?) : row.preState = pre := by
    exact division_candidate_first_pre run candidate first.val pre entry candidateExtends
      (by simpa only [Nat.add_zero] using candidateOrdered 0 positive) row atRow
  have replayFirst (row : TraceRow replay.bytecode)
      (atRow : row ∈ replay.rows[run.rows.size]?) : row.preState = pre :=
    replayed.firstPre row atRow
  constructor
  · exact division_block_pre_frame candidate first context.expands starts count kind rd rs1 rs2
      shape run.rows.size pre candidateOrdered candidateFirst offset inside
  · exact division_block_pre_frame replay first context.expands starts count kind rd rs1 rs2
      shape run.rows.size pre replayed.ordered replayFirst offset inside

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

private theorem divisionFrame_sourceValue (source : Src) (pre state : SailJoltState)
    (frame : DivisionFrame pre state) (sail : state.sail = pre.sail)
    (persistent : ¬ IsInstructionTemporary (TraceWitness.sourceRegisterAddress source)) :
    sourceValue source state = sourceValue source pre := by
  cases source with
  | xreg register => simp only [sourceValue, sail]
  | vreg register =>
      change ¬ IsInstructionTemporary register.toFin at persistent
      exact frame.2.2.2 register persistent

private theorem divisionFrame_selectedOperandValue {F : Type} [Field F]
    (operand : Instr → Option Src) (selector : Instr → Option (Fin 128))
    (selectorEq : ∀ instruction,
      selector instruction = (operand instruction).map TraceWitness.sourceRegisterAddress)
    (candidateInstruction replayInstruction : Instr)
    (instructionEq : candidateInstruction = replayInstruction)
    (pre candidatePre replayPre : SailJoltState)
    (candidateFrame : DivisionFrame pre candidatePre)
    (candidateSail : candidatePre.sail = pre.sail)
    (replayFrame : DivisionFrame pre replayPre)
    (replaySail : replayPre.sail = pre.sail)
    (persistent : ∀ register ∈ selector replayInstruction,
      ¬ IsInstructionTemporary register) :
    (match operand candidateInstruction with
      | some source => ((sourceValue source candidatePre).toNat : F)
      | none => 0) =
    (match operand replayInstruction with
      | some source => ((sourceValue source replayPre).toNat : F)
      | none => 0) := by
  subst candidateInstruction
  cases h : operand replayInstruction with
  | none => simp only [h]
  | some source =>
      have keep : ¬ IsInstructionTemporary (TraceWitness.sourceRegisterAddress source) := by
        apply persistent (TraceWitness.sourceRegisterAddress source)
        rw [selectorEq, h]
        simp
      simp only [h]
      rw [divisionFrame_sourceValue source pre candidatePre candidateFrame candidateSail keep,
        divisionFrame_sourceValue source pre replayPre replayFrame replaySail keep]

private theorem division_replay_new_selected_value {F : Type} [Field F]
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (run candidate replay : UntrustedAnswerRun joltInstance privateInputs)
    (count offset : Nat) (inside : offset < count) (pre : SailJoltState)
    (candidateSize : candidate.rows.size = run.rows.size + count)
    (replaySize : replay.rows.size = run.rows.size + count)
    (frames : ∀ k < count,
      (∃ row ∈ candidate.rows[run.rows.size + k]?,
        DivisionFrame pre row.preState ∧ row.preState.sail = pre.sail) ∧
      (∃ row ∈ replay.rows[run.rows.size + k]?,
        DivisionFrame pre row.preState ∧ row.preState.sail = pre.sail))
    (operand : Instr → Option Src) (selector : Instr → Option (Fin 128))
    (selectorEq : ∀ instruction,
      selector instruction = (operand instruction).map TraceWitness.sourceRegisterAddress)
    (instructionEq :
      candidate.bytecode[(candidate.rows[run.rows.size + offset]'(by omega)).rowIndex].instruction =
        replay.bytecode[(replay.rows[run.rows.size + offset]'(by omega)).rowIndex].instruction)
    (persistent : ∀ register ∈
      selector replay.bytecode[(replay.rows[run.rows.size + offset]'(by omega)).rowIndex].instruction,
      ¬ IsInstructionTemporary register) :
    (match operand candidate.bytecode[
        (candidate.rows[run.rows.size + offset]'(by omega)).rowIndex].instruction with
      | some source =>
          ((sourceValue source (candidate.rows[run.rows.size + offset]'(by omega)).preState).toNat : F)
      | none => 0) =
    (match operand replay.bytecode[
        (replay.rows[run.rows.size + offset]'(by omega)).rowIndex].instruction with
      | some source =>
          ((sourceValue source (replay.rows[run.rows.size + offset]'(by omega)).preState).toNat : F)
      | none => 0) := by
  obtain ⟨⟨candidateRow, candidateAt, candidateFrame, candidateSail⟩,
    ⟨replayRow, replayAt, replayFrame, replaySail⟩⟩ := frames offset inside
  have candidateBound : run.rows.size + offset < candidate.rows.size := by omega
  have replayBound : run.rows.size + offset < replay.rows.size := by omega
  have candidateRowEq : candidate.rows[run.rows.size + offset] = candidateRow :=
    Option.some.inj ((Array.getElem?_eq_getElem candidateBound).symm.trans candidateAt)
  have replayRowEq : replay.rows[run.rows.size + offset] = replayRow :=
    Option.some.inj ((Array.getElem?_eq_getElem replayBound).symm.trans replayAt)
  rw [← candidateRowEq] at candidateFrame candidateSail
  rw [← replayRowEq] at replayFrame replaySail
  exact divisionFrame_selectedOperandValue (F := F) operand selector selectorEq
    _ _ instructionEq pre _ _ candidateFrame candidateSail replayFrame replaySail persistent

private theorem division_replay_selected_value {F : Type} [Field F]
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (params : WitnessParams)
    (run candidate replay : UntrustedAnswerRun joltInstance privateInputs)
    (count : Nat) (pre : SailJoltState)
    (candidateSize : candidate.rows.size = run.rows.size + count)
    (replaySize : replay.rows.size = run.rows.size + count)
    (frames : ∀ k < count,
      (∃ row ∈ candidate.rows[run.rows.size + k]?,
        DivisionFrame pre row.preState ∧ row.preState.sail = pre.sail) ∧
      (∃ row ∈ replay.rows[run.rows.size + k]?,
        DivisionFrame pre row.preState ∧ row.preState.sail = pre.sail))
    (operand : Instr → Option Src) (selector : Instr → Option (Fin 128))
    (selectorEq : ∀ instruction,
      selector instruction = (operand instruction).map TraceWitness.sourceRegisterAddress)
    (observe : Trace → Fin params.traceLength → F)
    (projection : ∀ (trace : Trace) (t : Fin params.traceLength)
      (inside : t.val < trace.rows.size),
      observe trace t =
        match operand trace.bytecode[(trace.rows[t.val]'inside).rowIndex].instruction with
        | some source => ((sourceValue source (trace.rows[t.val]'inside).preState).toNat : F)
        | none => 0)
    (instructionEq : ∀ (t : Nat) (ci : t < candidate.rows.size)
      (ri : t < replay.rows.size),
      candidate.bytecode[candidate.rows[t].rowIndex].instruction =
        replay.bytecode[replay.rows[t].rowIndex].instruction)
    (oldEq : ∀ (t : Fin params.traceLength) (old : t.val < run.rows.size)
      (ci : t.val < candidate.rows.size) (ri : t.val < replay.rows.size),
      observe candidate.toTrace t = observe replay.toTrace t)
    (t : Fin params.traceLength)
    (candidateInside : t.val < candidate.rows.size)
    (replayInside : t.val < replay.rows.size)
    (persistent : ∀ register ∈
      selector replay.bytecode[replay.rows[t.val].rowIndex].instruction,
      ¬ IsInstructionTemporary register) :
    observe candidate.toTrace t = observe replay.toTrace t := by
  by_cases old : t.val < run.rows.size
  · exact oldEq t old candidateInside replayInside
  · let offset := t.val - run.rows.size
    have offsetInside : offset < count := by
      dsimp [offset]
      rw [replaySize] at replayInside
      omega
    have position : run.rows.size + offset = t.val := by dsimp [offset]; omega
    have selectedEq := division_replay_new_selected_value (F := F)
      run candidate replay count offset offsetInside pre candidateSize replaySize frames
      operand selector selectorEq
      (by simpa only [position] using instructionEq t.val candidateInside replayInside)
      (by simpa only [position] using persistent)
    rw [projection candidate.toTrace t candidateInside,
      projection replay.toTrace t replayInside]
    simpa only [position] using selectedEq

/-- The remaining observation, stopping, and register transfer after both runs'
block pre-states have the prefix frame and their final RAM images agree.
For example, REM with different internal quotients has the same persistent
operands and final RAM word at every address. -/
private theorem division_replay_complete_transfer
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
    (candidateExtends : RunExtends run candidate)
    (candidateSize : candidate.rows.size = run.rows.size + expansionRowCount context.bytecode first)
    (complete : ExpansionState witness context candidate first
      (expansionRowCount context.bytecode first))
    (same : DivisionFinalAgreement (TraceWitness.finalTraceState candidate.toTrace) honestPost)
    (replayed : DivisionReplayRows run replay first (expansionRowCount context.bytecode first)
      pre honestPost (kind.honestAdvice rd rs1 rs2 pre))
    (preFrames : ∀ offset < expansionRowCount context.bytecode first,
      (∃ row ∈ candidate.rows[run.rows.size + offset]?,
        DivisionFrame pre row.preState ∧ row.preState.sail = pre.sail) ∧
      (∃ row ∈ replay.rows[run.rows.size + offset]?,
        DivisionFrame pre row.preState ∧ row.preState.sail = pre.sail))
    (finalRam : ∀ address : Nat,
      TraceWitness.finalRamWord candidate.toTrace address =
        TraceWitness.finalRamWord replay.toTrace address) :
    ExpansionState witness context replay first
      (expansionRowCount context.bytecode first) := by
  have candidateOrdered : ∀ offset < expansionRowCount context.bytecode first,
      ∃ row ∈ candidate.rows[run.rows.size + offset]?,
        row.rowIndex.val = first.val + offset := by
    intro offset inside
    have base : candidate.rows.size - expansionRowCount context.bytecode first =
        run.rows.size := by rw [candidateSize]; omega
    simpa only [base] using complete.ordered offset inside
  have equalSize : candidate.rows.size = replay.rows.size := by
    rw [candidateSize, replayed.size]
  have rowIndexEq (t : Nat) (candidateInside : t < candidate.rows.size)
      (replayInside : t < replay.rows.size) :
      candidate.rows[t].rowIndex.val = replay.rows[t].rowIndex.val :=
    division_replay_index_eq run candidate replay first.val
      (expansionRowCount context.bytecode first) candidateExtends replayed.extendsRun
      candidateSize replayed.size candidateOrdered replayed.ordered
      t candidateInside replayInside
  have instructionEq (t : Nat) (candidateInside : t < candidate.rows.size)
      (replayInside : t < replay.rows.size) :
      candidate.bytecode[candidate.rows[t].rowIndex].instruction =
        replay.bytecode[replay.rows[t].rowIndex].instruction := by
    exact congrArg JoltInstructionRow.instruction
      (division_bytecode_at_eq
        (candidateExtends.choose.trans replayed.extendsRun.choose.symm)
        candidate.rows[t].rowIndex replay.rows[t].rowIndex
        (rowIndexEq t candidateInside replayInside))
  refine {
    represents := by
      have initialEq : candidate.initialState = replay.initialState :=
        Option.some.inj (candidate.initialized.symm.trans replay.initialized)
      refine {
        toRepresentsRows := {
          rowsBound := by rw [← equalSize]; exact complete.represents.rowsBound
          pc := by
            intro t inside
            have candidateInside : t.val < candidate.rows.size := by
              rw [equalSize]
              exact inside
            have indexEq := rowIndexEq t.val candidateInside inside
            have value := complete.represents.pc t candidateInside
            rw [value]
            unfold TraceWitness.PC TraceWitness.bytecodePc
            simp only [dif_pos candidateInside, dif_pos inside, indexEq]
          rs1 := by
            intro t inside persistent
            have candidateInside : t.val < candidate.rows.size := by
              rw [equalSize]
              exact inside
            have candidatePersistent : ∀ register ∈
                JoltConstraints.bytecodeRs1Register
                  candidate.bytecode[candidate.rows[t.val].rowIndex].instruction,
                ¬ IsInstructionTemporary register := by
              rw [instructionEq t.val candidateInside inside]
              exact persistent
            have candidateValue := complete.represents.rs1 t candidateInside candidatePersistent
            rw [candidateValue]
            exact division_replay_selected_value params run candidate replay
              (expansionRowCount context.bytecode first) pre candidateSize replayed.size
              preFrames JoltConstraints.rs1Operand? JoltConstraints.bytecodeRs1Register
              JoltConstraints.bytecodeRs1Register_eq_rs1Operand
              (TraceWitness.Rs1Value (F := F) params)
              (JoltConstraints.rs1Value_real (F := F) params)
              instructionEq
              (fun t old ci ri => (RunExtends.prefix_observations (F := F) params
                run candidate replay candidateExtends replayed.extendsRun t old ci ri).2.1)
              t candidateInside inside persistent
          rs2 := by
            intro t inside persistent
            have candidateInside : t.val < candidate.rows.size := by
              rw [equalSize]
              exact inside
            have candidatePersistent : ∀ register ∈
                JoltConstraints.bytecodeRs2Register
                  candidate.bytecode[candidate.rows[t.val].rowIndex].instruction,
                ¬ IsInstructionTemporary register := by
              rw [instructionEq t.val candidateInside inside]
              exact persistent
            have candidateValue := complete.represents.rs2 t candidateInside candidatePersistent
            rw [candidateValue]
            exact division_replay_selected_value params run candidate replay
              (expansionRowCount context.bytecode first) pre candidateSize replayed.size
              preFrames JoltConstraints.rs2Operand? JoltConstraints.bytecodeRs2Register
              JoltConstraints.bytecodeRs2Register_eq_rs2Operand
              (TraceWitness.Rs2Value (F := F) params)
              (JoltConstraints.rs2Value_real (F := F) params)
              instructionEq
              (fun t old ci ri => (RunExtends.prefix_observations (F := F) params
                run candidate replay candidateExtends replayed.extendsRun t old ci ri).2.2.1)
              t candidateInside inside persistent
          ramAddress := by
            intro t inside
            have candidateInside : t.val < candidate.rows.size := by
              rw [equalSize]
              exact inside
            have candidateValue := complete.represents.ramAddress t candidateInside
            rw [candidateValue]
            by_cases old : t.val < run.rows.size
            · exact (RunExtends.prefix_observations (F := F) params run candidate replay
                candidateExtends replayed.extendsRun t old candidateInside inside).2.2.2.1
            · let offset := t.val - run.rows.size
              have offsetInside : offset < expansionRowCount context.bytecode first := by
                dsimp [offset]
                rw [replayed.size] at inside
                omega
              have position : run.rows.size + offset = t.val := by dsimp [offset]; omega
              obtain ⟨row, rowAt, rowIndex⟩ := replayed.ordered offset offsetInside
              have rowAtT : replay.rows[t.val]? = some row := by
                simpa only [position] using rowAt
              have rowEq : replay.rows[t.val] = row :=
                Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans rowAtT)
              have replayArithmetic : DivisionArithmeticRow
                  replay.bytecode[replay.rows[t.val].rowIndex].instruction := by
                have index : replay.rows[(⟨t.val, inside⟩ : Fin replay.rows.size)].rowIndex.val =
                    first.val + offset := by
                  change replay.rows[t.val].rowIndex.val = first.val + offset
                  rw [rowEq]
                  exact rowIndex
                exact division_block_arithmetic replay first context.expands count
                  kind rd rs1 rs2 shape ⟨t.val, inside⟩ offset offsetInside
                  index
              have candidateArithmetic : DivisionArithmeticRow
                  candidate.bytecode[candidate.rows[t.val].rowIndex].instruction := by
                rw [instructionEq t.val candidateInside inside]
                exact replayArithmetic
              rw [DivisionArithmeticRow.ramAddress_zero (F := F) params candidate.toTrace
                t candidateInside candidateArithmetic,
                DivisionArithmeticRow.ramAddress_zero (F := F) params replay.toTrace
                  t inside replayArithmetic]
        }
        cutRam := by
          constructor
          · intro bound address outside
            have candidateBound : candidate.rows.size < params.traceLength := by
              rw [equalSize]
              exact bound
            have candidateOutside : address.val ≠
                (candidate.initialState.jolt_device.memory_layout.termination.toNat -
                  JoltConstraints.ramLowestAddress candidate.initialState.jolt_device.memory_layout) / 8 := by
              rw [initialEq]
              exact outside
            have value := complete.represents.cutRam.1 candidateBound address candidateOutside
            have indexEq :
                (⟨candidate.rows.size, candidateBound⟩ : Fin params.traceLength) =
                  ⟨replay.rows.size, bound⟩ := Fin.ext equalSize
            rw [indexEq] at value
            exact value.trans (by rw [finalRam])
          · intro full address outside
            have candidateFull : candidate.rows.size = params.traceLength := by
              rw [equalSize]
              exact full
            have candidateOutside : address.val ≠
                (candidate.initialState.jolt_device.memory_layout.termination.toNat -
                  JoltConstraints.ramLowestAddress candidate.initialState.jolt_device.memory_layout) / 8 := by
              rw [initialEq]
              exact outside
            have value := complete.represents.cutRam.2 candidateFull address candidateOutside
            exact value.trans (by rw [finalRam])
      }
    real := by
      intro t inside
      exact complete.real t (by rw [candidateSize, ← replayed.size]; exact inside)
    noEarlierStop := by
      intro i current next currentAt nextAt
      have replayInside : i < replay.rows.size :=
        (Array.getElem?_eq_some_iff.mp currentAt).1
      have replayNextInside : i + 1 < replay.rows.size :=
        (Array.getElem?_eq_some_iff.mp nextAt).1
      by_cases old : i < run.rows.size
      · have candidateInside : i < candidate.rows.size := by
          rw [equalSize]
          exact replayInside
        have candidateNextInside : i + 1 < candidate.rows.size := by
          rw [equalSize]
          exact replayNextInside
        have candidateNo := complete.noEarlierStop i
          candidate.rows[i] candidate.rows[i + 1]
          (Array.getElem?_eq_getElem candidateInside)
          (Array.getElem?_eq_getElem candidateNextInside)
        have indexBound : i < params.traceLength := by
          have bound := complete.represents.rowsBound
          omega
        let t : Fin params.traceLength := ⟨i, indexBound⟩
        have stableEq := (RunExtends.prefix_observations (F := F) params run
          candidate replay candidateExtends replayed.extendsRun t old
          candidateInside replayInside).2.2.2.2.1
        have currentEq : current = replay.rows[i] :=
          (Array.getElem?_eq_some_iff.mp currentAt).2.symm
        intro stable
        rw [currentEq] at stable
        exact candidateNo (stableEq.mpr stable)
      · let offset := i - run.rows.size
        have proper : offset + 1 < expansionRowCount context.bytecode first := by
          dsimp [offset]
          rw [replayed.size] at replayNextInside
          omega
        have position : run.rows.size + offset = i := by dsimp [offset]; omega
        have atBlock : current ∈ replay.rows[run.rows.size + offset]? := by
          simpa only [position] using currentAt
        have remaining := division_ordered_interior_remaining replay first
          context.expands state.starts run.rows.size replayed.ordered
          offset proper current atBlock
        intro stable
        exact remaining stable.1
    terminationWord := by
      intro bound noReplayStore address atTermination
      have candidateBound : candidate.rows.size < params.traceLength := by
        rw [equalSize]
        exact bound
      have noCandidateStore : ¬ ∃ i : Fin candidate.rows.size,
          candidate.StoresTerminationAt i := by
        rintro ⟨i, stored⟩
        have replayInside : i.val < replay.rows.size := by
          rw [← equalSize]
          exact i.isLt
        by_cases old : i.val < run.rows.size
        · have tBound : i.val < params.traceLength := by
            have rowsBound := complete.represents.rowsBound
            omega
          let t : Fin params.traceLength := ⟨i.val, tBound⟩
          have storeEq := (RunExtends.prefix_observations (F := F) params
            run candidate replay candidateExtends replayed.extendsRun t old
            i.isLt replayInside).2.2.2.2.2
          have replayStore : replay.StoresTerminationAt ⟨i.val, replayInside⟩ :=
            storeEq.mp stored
          exact noReplayStore ⟨⟨i.val, replayInside⟩, replayStore⟩
        · let offset := i.val - run.rows.size
          have offsetInside : offset < expansionRowCount context.bytecode first := by
            dsimp [offset]
            omega
          have position : run.rows.size + offset = i.val := by dsimp [offset]; omega
          obtain ⟨row, rowAt, rowIndex⟩ := candidateOrdered offset offsetInside
          have rowAtI : candidate.rows[i.val]? = some row := by
            simpa only [position] using rowAt
          have rowEq : candidate.rows[i] = row :=
            Option.some.inj ((Array.getElem?_eq_getElem i.isLt).symm.trans rowAtI)
          have arithmetic := division_block_arithmetic candidate first context.expands
            count kind rd rs1 rs2 shape i offset offsetInside
            (by rw [rowEq]; exact rowIndex)
          exact (DivisionArithmeticRow.notStoresTerminationAt candidate i arithmetic) stored
      have initialEq : candidate.initialState = replay.initialState :=
        Option.some.inj (candidate.initialized.symm.trans replay.initialized)
      have candidateAtTermination : address.val =
          (candidate.initialState.jolt_device.memory_layout.termination.toNat -
            JoltConstraints.ramLowestAddress candidate.initialState.jolt_device.memory_layout) / 8 := by
        rw [initialEq]
        exact atTermination
      have value := complete.terminationWord candidateBound noCandidateStore
        address candidateAtTermination
      have indexEq :
          (⟨candidate.rows.size, candidateBound⟩ : Fin params.traceLength) =
            ⟨replay.rows.size, bound⟩ := Fin.ext equalSize
      rw [indexEq] at value
      exact value
    starts := state.starts
    done_le := Nat.le_refl _
    retained := by rw [replayed.size]; omega
    ordered := by
      intro offset inside
      have base : replay.rows.size - expansionRowCount context.bytecode first =
          run.rows.size := by rw [replayed.size]; omega
      simpa only [base] using replayed.ordered offset inside
    priorBoundary := by
      intro last atBack
      have base : replay.rows.size - expansionRowCount context.bytecode first =
          run.rows.size := by rw [replayed.size]; omega
      rw [base] at atBack
      have prior : ∀ row ∈ run.rows.back?,
          run.bytecode[row.rowIndex].virtual_sequence_remaining.getD 0 = 0 := by
        intro row atRow
        apply state.priorBoundary row
        simpa only [Nat.sub_zero,
          Array.extract_eq_self_of_le (Nat.le_refl run.rows.size)] using atRow
      exact RunExtends.priorBoundary run replay replayed.extendsRun prior last atBack
    registers := by
      intro bound
      have equalSize : candidate.rows.size = replay.rows.size := by
        rw [candidateSize, replayed.size]
      have candidateBound : candidate.rows.size < params.traceLength := by
        rw [equalSize]
        exact bound
      have agreed := complete.registers candidateBound
      have finalFrame : DivisionFrame
          (TraceWitness.finalTraceState candidate.toTrace) honestPost :=
        ⟨same.device, same.tape, same.host, same.virtualRegisters⟩
      refine ⟨?_, ?_⟩
      · rw [replayed.finalPost, same.sail]
        exact agreed.present
      · intro register live
        have persistent : ¬ IsInstructionTemporary register := by
          rcases live with keep | ⟨unfinished, _⟩
          · exact keep
          · omega
        have candidateLive : ExpansionLive context.bytecode first
            (expansionRowCount context.bytecode first) register := Or.inl persistent
        have value := agreed.values register candidateLive
        have sameColumn :
            (⟨candidate.rows.size, candidateBound⟩ : Fin params.traceLength) =
              ⟨replay.rows.size, bound⟩ := Fin.ext equalSize
        rw [sameColumn] at value
        have decoded : TraceWitness.sourceRegisterAddress
            (JoltRegisterEncoding.source (BitVec.ofFin register)) = register := by
          simpa using JoltConstraints.Soundness.source_encode_decode (BitVec.ofFin register)
        have keepSource : ¬ IsInstructionTemporary
            (TraceWitness.sourceRegisterAddress
              (JoltRegisterEncoding.source (BitVec.ofFin register))) := by
          rw [decoded]
          exact persistent
        have sourceEq := divisionFrame_sourceValue
          (JoltRegisterEncoding.source (BitVec.ofFin register))
          (TraceWitness.finalTraceState candidate.toTrace) honestPost
          finalFrame same.sail keepSource
        rw [replayed.finalPost]
        exact value.trans (congrArg (fun word : BitVec 64 => (word.toNat : F)) sourceEq.symm)
    next := by intro impossible; omega
    notStopped := by intro impossible; omega
  }

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
  exact division_replay_complete_transfer witness context run candidate replay first state
    kind rd rs1 rs2 count shape pre honestPost candidateExtends candidateSize complete
    same replayed
    (fun offset inside => division_replay_pre_frames witness context run candidate replay
      first state.starts kind rd rs1 rs2 count shape pre honestPost entry candidateExtends
      candidateSize complete replayed offset inside)
    (division_replay_finalRamWord candidate replay honestPost same replayed.finalPost)

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
