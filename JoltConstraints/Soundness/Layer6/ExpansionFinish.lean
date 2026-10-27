import JoltConstraints.Soundness.Layer6.PrefixState
import JoltConstraints.Soundness.Layer6.TerminalNextPC

/-! Staged transition from a completed source expansion to the next boundary. -/

set_option autoImplicit false

namespace JoltInstance

open JoltConstraints.Soundness

/-- Following an expanded row's countdown reaches a row with no rows remaining.
For example, the first of three rows has count two and its endpoint has count zero. -/
private theorem expanded_endpoint_terminal (bytecode : Array JoltInstructionRow)
    (layout : BytecodeLayout bytecode) (count : Nat) :
    ∀ (first : Fin bytecode.size)
      (_countEq : (bytecode[first].virtual_sequence_remaining.getD 0).toNat = count)
      (endBound : first.val + count < bytecode.size),
      (bytecode[(⟨first.val + count, endBound⟩ : Fin bytecode.size)].virtual_sequence_remaining.getD 0) = 0 := by
  have zeroNat : (0 : BitVec 16).toNat = 0 := rfl
  have oneNat : (1 : BitVec 16).toNat = 1 := rfl
  induction count with
  | zero =>
    intro first countEq endBound
    have zeroCount : bytecode[first].virtual_sequence_remaining.getD 0 = 0 := by
      apply BitVec.eq_of_toNat_eq
      simpa only [zeroNat] using countEq
    simpa only [Nat.add_zero, Fin.getElem_fin] using zeroCount
  | succ count ih =>
    intro first countEq endBound
    have positive : bytecode[first].virtual_sequence_remaining.getD 0 ≠ 0 := by
      intro zero
      simp only [zero, zeroNat] at countEq
      omega
    let next : Fin bytecode.size := ⟨first.val + 1, by
      have := layout.endInBounds first
      omega⟩
    have nextIs := (layout.next first next rfl
      (by simpa [JoltInstructionRow.continues] using positive)).2.1
    have nextCount : (bytecode[next].virtual_sequence_remaining.getD 0).toNat = count := by
      rw [nextIs, Option.getD_some]
      have atLeastOne : (1 : BitVec 16) ≤
          bytecode[first].virtual_sequence_remaining.getD 0 := by
        rw [BitVec.le_def, oneNat]
        omega
      rw [BitVec.toNat_sub_of_le atLeastOne]
      rw [oneNat]
      omega
    have nextEndBound : next.val + count < bytecode.size := by
      dsimp [next]
      omega
    have endpoint := ih next nextCount nextEndBound
    have sameIndex : first.val + (count + 1) = next.val + count := by
      dsimp [next]
      omega
    simpa only [sameIndex, Fin.getElem_fin] using endpoint

/-- A real cycle after a terminal run row selects the first bytecode row at
Sail's post-state next PC.
For example, after a terminal ADDI at `0x80000000`, the next real cycle selects
a source-start row at `0x80000004`.
See jolt/crates/jolt-witness/src/witnesses/pc.rs (`NextUnexpandedPc::extract`)
at 5def437f. -/
private theorem boundary_successor {F : Type} [Field F] (joltField : JoltField F)
    (joltInstance : JoltInstance SourceInstruction)
    (noWrap : joltInstance.program.NextPCNoWrap)
    {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (equations : JoltConstraints.ConstraintEquations context.bytecode context.initialRam
      context.io context.entry witness)
    (run : UntrustedAnswerRun joltInstance privateInputs)
    (bytecodeEq : run.bytecode = context.bytecode)
    (represented : RepresentsRows witness run.toTrace)
    (last : TraceRow run.bytecode) (atEnd : last ∈ run.rows.back?)
    (terminal : run.bytecode[last.rowIndex].virtual_sequence_remaining.getD 0 = 0)
    (cycle : Fin params.traceLength) (atCycle : cycle.val + 1 = run.rows.size)
    (nextBound : run.rows.size < params.traceLength)
    (nextReal : witness.InstructionFlags .IsNoop ⟨run.rows.size, nextBound⟩ = 0)
    (address : BitVec 64)
    (postNext : last.postState.sail.regs.get? Register.nextPC = some address) :
    ∃ (next : Fin run.bytecode.size) (slot : Fin (2 ^ params.logBytecodeK)),
      JoltConstraints.bytecodeRa witness slot ⟨run.rows.size, nextBound⟩ = 1 ∧
      slot.val = next.val + 1 ∧ run.bytecode[next].address = address ∧
      run.bytecode[next].starts_source = true := by
  have nextRealNe : witness.InstructionFlags .IsNoop ⟨run.rows.size, nextBound⟩ ≠ 1 := by
    rw [nextReal]
    exact zero_ne_one
  have target := terminal_next_unexpanded_pc joltField joltInstance noWrap
    privateInputs witness context equations run bytecodeEq represented last atEnd
    terminal cycle atCycle nextBound nextRealNe address postNext
  have nextCycleBound : cycle.val + 1 < params.traceLength := by omega
  have nextCycleEq : (⟨cycle.val + 1, nextCycleBound⟩ : Fin params.traceLength) =
      ⟨run.rows.size, nextBound⟩ := Fin.ext atCycle
  rcases next_cycle_of_target joltField joltInstance privateInputs witness
    context equations cycle nextCycleBound address target with padding |
      ⟨slot, row, selectedNext, nextRowAt, rowAddress⟩
  · exact False.elim (nextRealNe (by simpa only [nextCycleEq] using padding))
  have selectedAt : JoltConstraints.bytecodeRa witness slot
      ⟨run.rows.size, nextBound⟩ = 1 := by
    simpa only [nextCycleEq] using selectedNext
  have nextRowAtRun : JoltConstraints.bytecodeRow run.bytecode slot.val = some row := by
    simpa only [bytecodeEq] using nextRowAt
  obtain ⟨_, _, next, slotIs, rowIs⟩ := stall_cycle_selected_row
    joltInstance privateInputs context run.bytecode bytecodeEq slot row nextRowAtRun
  obtain ⟨before, lastSlot, beforeIs, _, selectedLast, lastRowRun, _⟩ :=
    selected_last_represented_row joltField joltInstance privateInputs witness
      context equations run bytecodeEq represented last atEnd nextBound
  have beforeEq : before = cycle := Fin.ext (by omega)
  have selectedLastAt : JoltConstraints.bytecodeRa witness lastSlot cycle = 1 := by
    simpa only [beforeEq] using selectedLast
  have lastRowAt : JoltConstraints.bytecodeRow context.bytecode lastSlot.val =
      some run.bytecode[last.rowIndex] := by
    simpa only [← bytecodeEq] using lastRowRun
  have starts : row.starts_source = true := by
    by_cases sourceStart : row.starts_source = true
    · exact sourceStart
    have interior : row.starts_source = false := Bool.eq_false_iff.mpr sourceStart
    have remaining := selected_interior_current_remaining
      (two_pow_127_lt_char joltField) context equations cycle nextCycleBound
      lastSlot slot selectedLastAt selectedNext lastRowAt nextRowAt interior
    exact False.elim (remaining terminal)
  refine ⟨next, slot, selectedAt, slotIs, ?_, ?_⟩
  · simpa only [← rowIs] using rowAddress
  · simpa only [← rowIs] using starts

/-- All retained rows of a completed source block end at its terminal bytecode row.
For example, the ninth REM expansion row has countdown zero. -/
private theorem expansion_at_boundary {F : Type} [Field F]
    (joltInstance : JoltInstance SourceInstruction)
    {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (run : UntrustedAnswerRun joltInstance privateInputs)
    (first : Fin context.bytecode.size)
    (state : ExpansionState witness context run first (expansionRowCount context.bytecode first)) :
    ∀ last ∈ run.rows.back?,
      run.bytecode[last.rowIndex].virtual_sequence_remaining.getD 0 = 0 := by
  have bytecodeEq : run.bytecode = context.bytecode :=
    Option.some.inj (run.expands.symm.trans context.expands)
  let count := expansionRowCount context.bytecode first
  have countPositive : 0 < count := by simp [count, expansionRowCount]
  have rowsPositive : 0 < run.rows.size := by have := state.retained; omega
  have endpointBound : first.val + count - 1 < context.bytecode.size := by
    have layout := expand_program_layout joltInstance.program context.bytecode context.expands
    have := layout.endInBounds first
    dsimp [count, expansionRowCount]
    omega
  have endpointZero :
      (context.bytecode[(⟨first.val + count - 1, endpointBound⟩ : Fin context.bytecode.size)].virtual_sequence_remaining.getD 0) = 0 := by
    have layout := expand_program_layout joltInstance.program context.bytecode context.expands
    have terminal := expanded_endpoint_terminal context.bytecode layout
      (context.bytecode[first].virtual_sequence_remaining.getD 0).toNat first rfl
      (layout.endInBounds first)
    have indexEq : first.val + count - 1 =
        first.val + (context.bytecode[first].virtual_sequence_remaining.getD 0).toNat := by
      simp [count, expansionRowCount]
    simpa only [indexEq, Fin.getElem_fin] using terminal
  have lastEndpoint : ∀ last ∈ run.rows.back?,
      last.rowIndex.val = first.val + count - 1 := by
    intro last atEnd
    have back : run.rows.back? = some last := by simpa using atEnd
    have offsetBound : count - 1 < count := by omega
    obtain ⟨row, atRow, index⟩ := state.ordered (count - 1) offsetBound
    have atLast : run.rows[run.rows.size - 1]? = some last := by
      simpa only [Array.back?_eq_getElem?] using back
    have atRowLast : run.rows[run.rows.size - 1]? = some row := by
      have offsetIs : run.rows.size - count + (count - 1) = run.rows.size - 1 := by
        have := state.retained
        omega
      simpa only [show expansionRowCount context.bytecode first = count from rfl,
        offsetIs, Option.mem_def] using atRow
    have rowEq : row = last := Option.some.inj (atRowLast.symm.trans atLast)
    subst row
    omega
  have atBoundaryFact : ∀ last ∈ run.rows.back?,
      run.bytecode[last.rowIndex].virtual_sequence_remaining.getD 0 = 0 := by
    intro last atEnd
    have index := lastEndpoint last atEnd
    have rowEq : run.bytecode[last.rowIndex] =
        context.bytecode[(⟨first.val + count - 1, endpointBound⟩ :
          Fin context.bytecode.size)] := by
      have same : (⟨last.rowIndex.val, last.rowIndex.isLt⟩ : Fin run.bytecode.size) =
          ⟨first.val + count - 1, by simpa only [← bytecodeEq] using endpointBound⟩ :=
        Fin.ext index
      simpa only [bytecodeEq, Fin.getElem_fin] using congrArg
        (fun i : Fin run.bytecode.size => run.bytecode[i]) same
    rw [rowEq]
    exact endpointZero
  exact atBoundaryFact

/-- At the completed block's boundary, a real next cycle selects a prepared
source-start row. For example, a completed ADDI prepares its next address. -/
private theorem expansion_ready {F : Type} [Field F] (joltField : JoltField F)
    (joltInstance : JoltInstance SourceInstruction)
    (noWrap : joltInstance.program.NextPCNoWrap)
    {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (equations : JoltConstraints.ConstraintEquations context.bytecode context.initialRam
      context.io context.entry witness)
    (run : UntrustedAnswerRun joltInstance privateInputs)
    (first : Fin context.bytecode.size)
    (state : ExpansionState witness context run first (expansionRowCount context.bytecode first))
    (honestAdvice : ∀ n : Fin run.rows.size, run.rows[n].someTracerAdvice? =
      honestTracerAdviceAtStepN joltInstance.program run.rows n)
    (atBoundary : ∀ last ∈ run.rows.back?,
      run.bytecode[last.rowIndex].virtual_sequence_remaining.getD 0 = 0) :
    ∀ bound : run.rows.size < params.traceLength,
      witness.InstructionFlags .IsNoop ⟨run.rows.size, bound⟩ = 0 →
      (∀ last ∈ run.rows.back?, ¬ last.StableStall) →
      ∃ (next : Fin run.bytecode.size) (pre : SailJoltState)
        (slot : Fin (2 ^ params.logBytecodeK)),
        JoltConstraints.bytecodeRa witness slot ⟨run.rows.size, bound⟩ = 1 ∧
        slot.val = next.val + 1 ∧ run.NextStep next pre := by
  have bytecodeEq : run.bytecode = context.bytecode :=
    Option.some.inj (run.expands.symm.trans context.expands)
  have rowsPositive : 0 < run.rows.size := by
    have := state.retained
    simp [expansionRowCount] at this
    omega
  intro bound real notStopped
  have back : ∃ last, run.rows.back? = some last := by
    cases back : run.rows.back? with
    | none =>
      have empty := Array.back?_eq_none_iff.mp back
      simp [empty] at rowsPositive
    | some last => exact ⟨last, rfl⟩
  obtain ⟨last, atEnd⟩ := back
  have terminal : run.bytecode[last.rowIndex].virtual_sequence_remaining.getD 0 = 0 :=
    atBoundary last (by simp [atEnd])
  have endState : TraceWitness.finalTraceState run.toTrace = last.postState := by
    unfold TraceWitness.finalTraceState
    simp only [dif_pos rowsPositive]
    have atLast : run.rows[run.rows.size - 1]? = some last := by
      simpa only [Array.back?_eq_getElem?] using atEnd
    exact congrArg TraceRow.postState (Array.getElem?_eq_some_iff.mp atLast).2
  have present : AllRegistersPresent last.postState.sail := by
    rw [← endState]
    exact (state.registers bound).present
  obtain ⟨address, postNext⟩ :
      ∃ address, last.postState.sail.regs.get? Register.nextPC = some address := by
    exact Option.isSome_iff_exists.mp (present Register.nextPC)
  let cycle : Fin params.traceLength := ⟨run.rows.size - 1, by omega⟩
  have atCycle : cycle.val + 1 = run.rows.size := by dsimp [cycle]; omega
  obtain ⟨next, slot, selected, slotIs, nextAddress, starts⟩ :=
    boundary_successor joltField joltInstance noWrap privateInputs
      witness context equations run bytecodeEq state.represents.toRepresentsRows
      last (by simp [atEnd]) terminal cycle atCycle bound real address postNext
  refine ⟨next, advance_pc address (source_is_compressed run.bytecode next)
    last.postState, slot, selected, slotIs, ?_⟩
  refine ⟨honestAdvice, state.noEarlierStop, ?_⟩
  rw [atEnd]
  simp only [terminal, ne_eq, not_true_eq_false, ↓reduceIte]
  exact ⟨address, postNext, notStopped last (by simp [atEnd]),
    nextAddress, starts, rfl⟩

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
  have atBoundary := expansion_at_boundary joltInstance privateInputs witness context
    run first state
  refine {
    represents := state.represents
    real := state.real
    noEarlierStop := state.noEarlierStop
    honestAdvice := honestAdvice
    atBoundary := atBoundary
    registers := ?_
    terminationWord := state.terminationWord
    ready := expansion_ready joltField joltInstance assumptions.pcNoWrap privateInputs
      witness context equations run first state honestAdvice atBoundary
  }
  intro bound
  exact (state.registers bound).mono (fun register live => Or.inl live)

end JoltInstance
