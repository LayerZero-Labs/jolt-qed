import JoltConstraints.theorems.Soundness.Layer6.SelectedRows
import JoltConstraints.theorems.Soundness.Layer6.BytecodePC
import JoltConstraints.theorems.Soundness.Layer3.Access
import JoltConstraints.theorems.Soundness.Layer3.History
import JoltConstraints.theorems.Soundness.Layer5.Halt
import JoltConstraints.theorems.Soundness.Layer1.HaltEndRule
import JoltConstraints.theorems.Soundness.Layer5.TapeTrace

open LeanRV64D
set_option autoImplicit false

namespace JoltInstance
open JoltConstraints JoltConstraints.Soundness

/-- A represented executed halt has exactly the publicly claimed halt kind.
For example, a panic row cannot represent a success statement.
This uses the halt lane and selected-row metadata, without flag-word restrictions. -/
theorem RepresentsRows.halt_kind
    {F : Type} [Field F] (joltField : JoltField F)
    {inst : JoltInstance SourceInstruction} {inputs : JoltPrivateInputs} {params : WitnessParams}
    {witness : WitnessType F params} (context : ConstraintContext inst inputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
    (trace : Trace) (bytecodeEq : trace.bytecode = context.bytecode)
    (represented : RepresentsRows witness trace)
    (cycle : Fin params.traceLength) (inside : cycle.val < trace.rows.size)
    (halted : trace.rows[cycle.val].Halts) :
    trace.bytecode[trace.rows[cycle.val].rowIndex].instruction.haltKind? =
      some (if context.io.panic then .panic else .success) := by
  let slot : Fin (2 ^ params.logBytecodeK) := ⟨trace.rows[cycle.val].rowIndex.val + 1, by
    have fits := context.bytecodeDomain.rowsFit
    have rowBound := trace.rows[cycle.val].rowIndex.isLt
    have sizeEq := congrArg Array.size bytecodeEq
    omega⟩
  have selected : bytecodeRa witness slot cycle = 1 :=
    RepresentsRows.selected_row joltField inst inputs witness context equations trace bytecodeEq
      represented cycle inside
  have atRow : bytecodeRow context.bytecode slot.val =
      some trace.bytecode[trace.rows[cycle.val].rowIndex] := by
    rw [← bytecodeEq]
    simp only [slot, bytecodeRow]
    simpa only [Fin.getElem_fin] using
      (Array.getElem?_eq_getElem trace.rows[cycle.val].rowIndex.isLt)
  have next := selected_halt_forces_next_padding (two_pow_127_lt_char joltField)
    context equations cycle slot selected _ atRow halted
  exact selected_halt_of_next_padding (two_pow_127_lt_char joltField)
    context equations cycle slot selected _ atRow next

/-- The final device panic flag of a represented completed run equals its public claim.
For example, a one-row panic trace sets the claim without a memory flag word. -/
theorem represented_final_panic
    {F : Type} [Field F] (joltField : JoltField F)
    {inst : JoltInstance SourceInstruction} {inputs : JoltPrivateInputs} {params : WitnessParams}
    {witness : WitnessType F params} (context : ConstraintContext inst inputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
    (trace : UntrustedAnswerTrace inst inputs) (bytecodeEq : trace.bytecode = context.bytecode)
    (represented : RepresentsRows witness trace.toUntrustedAnswerRun.toTrace) :
    (TraceWitness.finalTraceState trace).jolt_device.panic = context.io.panic := by
  let index : Fin trace.rows.size := ⟨trace.rows.size - 1, by have := trace.nonempty; omega⟩
  let cycle : Fin params.traceLength := ⟨index.val, by
    have := represented.rowsBound
    exact Nat.lt_of_lt_of_le index.isLt this⟩
  have atLast : trace.rows.back? = some trace.rows[index] := by
    rw [Array.back?_eq_getElem?, Array.getElem?_eq_getElem index.isLt]
    rfl
  have kindIs : trace.bytecode[trace.rows[index].rowIndex].instruction.haltKind? =
      some (if context.io.panic then .panic else .success) := by
    simpa only [cycle, Fin.getElem_fin] using
      represented.halt_kind joltField context equations trace bytecodeEq
        cycle index.isLt (trace.stops _ atLast)
  obtain ⟨dst, shape⟩ := halt_instruction_of_kind _ _ kindIs
  have executed := trace.executes index
  simp only [Fin.getElem_fin] at shape executed
  rw [execWithTapeAnswer_halt_eq _ dst _ shape (trace.answers index)
    trace.rows[index.val].runtimeAdvice] at executed
  obtain ⟨link, address, middle, _, _, _, postEq⟩ := execHalt_shape _ dst _ _ executed
  have panicEq := congrArg (fun state : SailJoltState => state.jolt_device.panic) postEq
  have finalEq : TraceWitness.finalTraceState trace = trace.rows[index].postState := by
    simp only [TraceWitness.finalTraceState, dite_eq_left trace.nonempty,
      index, Fin.getElem_fin]
  rw [finalEq]
  simp only [Fin.getElem_fin]
  rw [panicEq]
  cases context.io.panic <;> rfl

/-- A represented real prefix cut at padding, a halt or the domain boundary
ends at an explicit halt and agrees with every final shared-memory word.
For example, a one-row panic prefix followed by padding needs no synthetic status word.
Jolt at `ff6fc6568`: `rv64_trace_constraints` (halt lane) and `Cpu::halt`. -/
theorem soundness_stopping {F : Type} [Field F] (joltField : JoltField F)
    (inst : JoltInstance SourceInstruction)
    {params : WitnessParams} (inputs : JoltPrivateInputs)
    (witness : WitnessType F params) (context : ConstraintContext inst inputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
    (run : UntrustedAnswerRun inst inputs) (bytecodeEq : run.bytecode = context.bytecode)
    (represented : RepresentsPrefix witness run.toTrace)
    (cut : run.rows.size = params.traceLength ∨
      ∃ bound : run.rows.size < params.traceLength,
        witness.InstructionFlags .IsNoop ⟨run.rows.size, bound⟩ = 1 ∨
        ∃ last ∈ run.rows.back?, last.Halts) :
    (∀ last ∈ run.rows.back?, last.Halts) ∧ 0 < run.rows.size ∧
      (∀ address : Fin params.ramSize,
        witness.RamValFinal address = ((TraceWitness.finalRamWord run.toTrace address.val).toNat : F)) := by
  have char := two_pow_127_lt_char joltField
  have nonempty : 0 < run.rows.size := by
    by_contra empty
    have sizeZero : run.rows.size = 0 := by omega
    rcases cut with full | ⟨bound, padding | ⟨last, atLast, _⟩⟩
    · have positive : 0 < params.traceLength := Nat.two_pow_pos _
      omega
    · obtain ⟨row, atEntry⟩ := JoltConstraints.Soundness.ConstraintContext.entry_row context
      have real := instructionFlag_of_selected_bytecode char context equations .IsNoop
        ⟨0, Nat.two_pow_pos _⟩ context.entry equations.bytecodeRaAtEntryEqOne
      have zero : witness.InstructionFlags .IsNoop ⟨0, Nat.two_pow_pos _⟩ = (0 : F) := by
        simpa only [bytecodeInstructionFlag, atEntry, JoltMetadata.instructionFlag,
          Bool.false_eq_true, ↓reduceIte] using real
      have firstPadding : witness.InstructionFlags .IsNoop ⟨0, Nat.two_pow_pos _⟩ = (1 : F) := by
        simpa only [sizeZero] using padding
      exact zero_ne_one (zero.symm.trans firstPadding)
    · have noLast : run.rows.back? = none := by
        rw [Array.back?_eq_getElem?]
        exact Array.getElem?_eq_none (by omega)
      rw [noLast] at atLast
      cases atLast
  have lastBound : run.rows.size - 1 < run.rows.size := by omega
  have domainBound : run.rows.size - 1 < params.traceLength := by
    have bound := represented.rowsBound
    omega
  let cycle : Fin params.traceLength := ⟨run.rows.size - 1, domainBound⟩
  let last := run.rows[run.rows.size - 1]
  have back : run.rows.back? = some last := by
    rw [Array.back?_eq_getElem?, Array.getElem?_eq_getElem lastBound]
  have cycleNext : cycle.val + 1 = run.rows.size := by dsimp only [cycle]; omega
  let slot : Fin (2 ^ params.logBytecodeK) := ⟨last.rowIndex.val + 1, by
    have fits := context.bytecodeDomain.rowsFit
    have rowBound := last.rowIndex.isLt
    have sizeEq := congrArg Array.size bytecodeEq
    omega⟩
  have selected : bytecodeRa witness slot cycle = 1 :=
    RepresentsRows.selected_row joltField inst inputs witness context equations run.toTrace bytecodeEq
      represented.toRepresentsRows cycle lastBound
  have atRow : bytecodeRow context.bytecode slot.val = some run.bytecode[last.rowIndex] := by
    rw [← bytecodeEq]
    simp only [slot, bytecodeRow]
    simpa only [Fin.getElem_fin] using (Array.getElem?_eq_getElem last.rowIndex.isLt)
  have nextPadding : witness.NextIsNoop cycle = 1 := by
    rcases cut with full | ⟨bound, padding | ⟨other, atOther, halted⟩⟩
    · rw [equations.nextIsNoopEqShift cycle, dite_eq_right (by omega)]
    · rw [equations.nextIsNoopEqShift cycle]
      have nextBound : cycle.val + 1 < params.traceLength := by omega
      rw [dite_eq_left nextBound]
      have same : (⟨cycle.val + 1, nextBound⟩ : Fin params.traceLength) = ⟨run.rows.size, bound⟩ :=
        Fin.ext cycleNext
      rw [same]
      exact padding
    · have same : other = last := Option.some.inj (atOther.symm.trans back)
      subst other
      exact selected_halt_forces_next_padding char context equations cycle slot selected _ atRow halted
  have kind := selected_halt_of_next_padding char context equations cycle slot selected _ atRow nextPadding
  have stops : ∀ other ∈ run.rows.back?, other.Halts := by
    intro other atOther
    have same : other = last := Option.some.inj (atOther.symm.trans back)
    subst other
    simp only [TraceRow.Halts, kind, Option.isSome_some]
  refine ⟨stops, nonempty, ?_⟩
  intro address
  by_cases below : run.rows.size < params.traceLength
  · have nextBound : cycle.val + 1 < params.traceLength := by omega
    have atCut : witness.InstructionFlags .IsNoop ⟨run.rows.size, below⟩ = 1 := by
      rw [equations.nextIsNoopEqShift cycle, dite_eq_left nextBound] at nextPadding
      have same : (⟨cycle.val + 1, nextBound⟩ : Fin params.traceLength) = ⟨run.rows.size, below⟩ :=
        Fin.ext cycleNext
      rwa [same] at nextPadding
    have suffixZero (t : Fin params.traceLength) (later : run.rows.size ≤ t.val) :
        witness.RamRa address t * witness.RamInc t = 0 := by
      have padding := padding_from char context equations ⟨run.rows.size, below⟩ t atCut later
      exact (ram_zero_effects char context equations t
        (ramAddress_zero_of_padding char context equations t padding)).2.2 address
    exact (ramVal_eq_final_of_suffix_zero equations.ramValEqInitialPlusPrefixRamInc
      equations.ramValFinalEqInitialPlusRamInc address ⟨run.rows.size, below⟩ suffixZero).symm.trans
        (represented.cutRam.1 below address)
  · have full : run.rows.size = params.traceLength := by
      have bound := represented.rowsBound
      omega
    exact represented.cutRam.2 full address

end JoltInstance
