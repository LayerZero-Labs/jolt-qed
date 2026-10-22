import JoltConstraints.Soundness.Layer6.PrefixState
import JoltConstraints.Soundness.Layer6.BytecodePC
import JoltConstraints.Soundness.Layer7.StallSuffix
import JoltConstraints.Soundness.Layer7.LastJump
import JoltConstraints.Soundness.Layer5.Advice
import JoltConstraints.Soundness.Layer5.AddImmediate
import JoltConstraints.Soundness.Layer5.Arithmetic
import JoltConstraints.Soundness.Layer5.Xor
import JoltConstraints.Soundness.Layer5.VirtualBinary
import JoltConstraints.Soundness.Layer5.UnaryWord
import JoltConstraints.Soundness.Layer5.AssertionsBinary
import JoltConstraints.Soundness.Layer5.AssertionMulOverflow
import JoltConstraints.Soundness.Layer5.AssertLessThanEqual
import JoltConstraints.Soundness.Layer3.Access
import JoltConstraints.Soundness.Layer3.Updates

/-! Append a non-memory, non-host, non-jump row without requiring honest advice. -/

set_option autoImplicit false

namespace JoltInstance

open JoltConstraints JoltConstraints.Soundness
open Sail PreSail LeanRV64D.Functions JoltISA

/-- The twelve row kinds used by the eight division expansions.
This excludes memory accesses, tape loads, branches, jumps and HostIO.
For example, REM's VirtualAdvice, VirtualNegateIf, multiplication, subtraction
and assertion rows all satisfy this predicate. -/
def DivisionArithmeticRow : Instr → Prop
  | .VirtualAdvice .. | .VirtualNegateIf .. | .XOR .. | .MUL .. | .SUB .. | .ADDI ..
  | .VirtualSignExtendWord .. | .VirtualZeroExtendWord ..
  | .VirtualAssertValidDiv0 .. | .VirtualAssertMulUNoOverflow ..
  | .VirtualAssertLTE .. | .VirtualAssertValidUnsignedRemainder .. => True
  | _ => False

/-- The row kinds handled without a memory/host-call restriction or a jump rule.
For example, VirtualAdvice and an unsigned division guard are plain rows;
LD, SD, VirtualHostIO, JAL and JALR are excluded. -/
def PlainRow (instruction : Instr) : Prop :=
  match instruction with
  | .LD .. | .SD .. | .VirtualHostIO | .JAL .. | .JALR .. => False
  | _ => True

/-- Every division arithmetic row is plain; for example, REM's MUL needs no
memory-access or host-call restriction. -/
theorem DivisionArithmeticRow.plain {instruction : Instr}
    (arithmetic : DivisionArithmeticRow instruction) : PlainRow instruction := by
  unfold PlainRow
  split <;> first | exact True.intro | exact arithmetic

/-- A run retains its own rows; for example, an empty block extends its input prefix. -/
theorem RunExtends.refl {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (run : UntrustedAnswerRun joltInstance privateInputs) : RunExtends run run := by
  exact ⟨rfl, by simp⟩

/-- Retaining two consecutive prefixes retains the original prefix.
For example, appending REM's advice row and then its guard keeps all earlier rows. -/
theorem RunExtends.trans {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    {first middle last : UntrustedAnswerRun joltInstance privateInputs}
    (left : RunExtends first middle) (right : RunExtends middle last) :
    RunExtends first last := by
  obtain ⟨a, left⟩ := left
  obtain ⟨b, right⟩ := right
  rcases first with ⟨⟨_, firstRows, _⟩, _⟩
  rcases middle with ⟨⟨_, middleRows, _⟩, _⟩
  rcases last with ⟨⟨_, lastRows, _⟩, _⟩
  dsimp only at a b left right ⊢
  subst a b
  refine ⟨rfl, ?_⟩
  dsimp only at left right ⊢
  have bound := congrArg Array.size left
  simp only [Array.size_extract, Nat.sub_zero] at bound
  have le : firstRows.size ≤ middleRows.size := by omega
  have composed := congrArg (fun rows => rows.extract 0 firstRows.size) right
  simpa only [Array.extract_extract, Nat.zero_add, Nat.min_eq_left le] using
    composed.trans left

private theorem rows_block_property
    (property : List JoltInstructionRow → Prop)
    (chunks : List (List JoltInstructionRow))
    (each : ∀ rows ∈ chunks, (∃ address compressed, ExpandedRows address compressed rows) ∧ property rows)
    (i : Nat) (bound : i < chunks.flatten.length)
    (starts : chunks.flatten[i].starts_source = true) :
    property ((chunks.flatten.drop i).take
      ((chunks.flatten[i].virtual_sequence_remaining.getD 0).toNat + 1)) := by
  induction chunks generalizing i with
  | nil => simp at bound
  | cons rows rest ih =>
    obtain ⟨⟨address, compressed, valid⟩, good⟩ := each rows (by simp)
    have tail := fun r h => each r (List.mem_cons_of_mem rows h)
    simp only [List.flatten_cons, List.length_append] at bound starts ⊢
    by_cases inside : i < rows.length
    · rw [List.getElem_append_left inside, valid.starts i inside] at starts
      have zero : i = 0 := by simpa using starts
      subst i
      rw [List.getElem_append_left inside, valid.countdown 0 inside]
      simpa only [Nat.sub_zero, show rows.length - 1 + 1 = rows.length by omega,
        List.drop_zero, List.take_left] using good
    · have outside : rows.length ≤ i := by omega
      rw [List.getElem_append_right outside] at starts ⊢
      rw [List.drop_append, List.drop_eq_nil_of_le outside, List.nil_append]
      exact ih tail (i - rows.length) (by omega) starts

private theorem expand_program_block
    (image : Rv64ProgramImage SourceInstruction) (bytecode : Array JoltInstructionRow)
    (expanded : expand_program image = some bytecode)
    (first : Fin bytecode.size) (starts : bytecode[first].starts_source = true) :
    ∃ source : SourceInstructionRow SourceInstruction,
      expand_instruction source = some ((bytecode.toList.drop first.val).take
        (JoltInstance.expansionRowCount bytecode first)) := by
  unfold expand_program at expanded
  cases mapped : image.instructions.toList.mapM expand_instruction with
  | none => simp only [mapped, Option.map_none] at expanded; cases expanded
  | some chunks =>
    simp only [mapped, Option.map_some, Option.some.injEq] at expanded
    subst bytecode
    have steps := option_mapM_results expand_instruction _ chunks mapped
    have each : ∀ rows ∈ chunks,
        (∃ address compressed, ExpandedRows address compressed rows) ∧
          ∃ source : SourceInstructionRow SourceInstruction, expand_instruction source = some rows := by
      intro rows member
      obtain ⟨index, bound, atIndex⟩ := List.mem_iff_getElem.mp member
      have step := steps.2 index (by omega) bound
      rw [atIndex] at step
      exact ⟨⟨_, _, expand_instruction_expandedRows _ _ step⟩, ⟨_, step⟩⟩
    simpa only [List.toList_toArray, JoltInstance.expansionRowCount,
      Fin.getElem_fin, List.getElem_toArray] using
      rows_block_property _ chunks each first.val
        (by simpa only [List.size_toArray] using first.isLt)
        (by simpa only [Fin.getElem_fin, List.getElem_toArray] using starts)

open ExpansionTempLiveness
private theorem firstAccessIsWrite_read_before
    (register : JoltISA.VReg) (rows : List Instr)
    (valid : firstAccessIsWrite register rows = true)
    (index : Nat) (bound : index < rows.length)
    (read : reads register rows[index] = true) :
    ∃ (before : Nat) (earlier : before < index), writes register rows[before] = true := by
  induction rows generalizing index with
  | nil => simp at bound
  | cons row rest ih =>
    cases index with
    | zero =>
      have noRead := firstAccessIsWrite_head_no_read register row rest valid
      simp only [List.getElem_cons_zero] at read
      rw [noRead] at read
      cases read
    | succ index =>
      by_cases written : writes register row = true
      · exact ⟨0, Nat.zero_lt_succ _, written⟩
      · have pending := firstAccessIsWrite_tail register row rest valid
          (Bool.eq_false_iff.mpr written)
        obtain ⟨before, earlier, write⟩ := ih pending index (by simpa using bound) read
        exact ⟨before + 1, by omega, write⟩

open ExpansionTempLiveness
/-- Every source operand of an unfinished expansion is live.
A temporary source has an earlier write in the same source expansion;
persistent sources are live by definition.
For example, REM's MUL can read the quotient temporary initialized by its
preceding advice row, even if that temporary was dead at the boundary. -/
theorem expansion_sources_live
    (image : Rv64ProgramImage SourceInstruction) (bytecode : Array JoltInstructionRow)
    (expanded : expand_program image = some bytecode)
    (first : Fin bytecode.size) (starts : bytecode[first].starts_source = true)
    (done : Nat) (unfinished : done < expansionRowCount bytecode first)
    (row : JoltInstructionRow) (atRow : bytecode[first.val + done]? = some row)
    (source : Src) (read : source ∈ readSources row.instruction) :
    ExpansionLive bytecode first done (TraceWitness.sourceRegisterAddress source) := by
  by_cases persistent : ¬ IsInstructionTemporary (TraceWitness.sourceRegisterAddress source)
  · exact Or.inl persistent
  obtain ⟨index, address⟩ := instructionTemporary_index _ (not_not.mp persistent)
  let temp := BitVec.ofNat 7 (40 + index.val)
  have registerEq : TraceWitness.sourceRegisterAddress source = temp.toFin := by
    apply Fin.ext
    change (TraceWitness.sourceRegisterAddress source).val = (40 + index.val) % 128
    have bound := index.isLt
    omega
  have sourceEq := temporary_source source index registerEq
  let rows := (bytecode.toList.drop first.val).take (expansionRowCount bytecode first)
  obtain ⟨emitter, expands⟩ := expand_program_block image bytecode expanded first starts
  have temps := ExpansionFacts.expand_instruction_property
    (fun instructions => tempsReadAfterWrite instructions = true)
    ExpansionFacts.nativeRowOk_tempsReadAfterWrite
    ExpansionFacts.sequenceOk_tempsReadAfterWrite emitter rows expands
  have valid : firstAccessIsWrite temp (rows.map (·.instruction)) = true :=
    List.all_eq_true.mp temps index.val (List.mem_range.mpr index.isLt)
  have endBound := (expand_program_layout image bytecode expanded).endInBounds first
  have length : rows.length = expansionRowCount bytecode first := by
    simp only [rows, List.length_take, List.length_drop, Array.length_toList]
    unfold expansionRowCount at endBound ⊢
    omega
  have atOffset (offset : Nat) (inRange : offset < rows.length) :
      bytecode[first.val + offset]? = some rows[offset] := by
    have inside : first.val + offset < bytecode.size := by
      rw [length] at inRange
      unfold expansionRowCount at inRange
      omega
    simp only [Array.getElem?_eq_getElem inside, rows, List.getElem_take,
      List.getElem_drop, Array.getElem_toList]
  have current : rows[done]'(by omega) = row :=
    Option.some.inj ((atOffset done (by omega)).symm.trans atRow)
  have reading : reads temp ((rows.map (·.instruction))[done]'(by simp [length]; exact unfinished)) = true := by
    simp only [List.getElem_map, current]
    apply List.any_eq_true.mpr
    exact ⟨source, read, by rw [sourceEq]; simp [temp]⟩
  obtain ⟨offset, earlier, written⟩ := firstAccessIsWrite_read_before
    temp (rows.map (·.instruction)) valid done (by simp [length]; exact unfinished) reading
  simp only [List.getElem_map, writes] at written
  split at written
  · rename_i destination selected
    have destinationEq : destination = temp := by simpa using written
    refine Or.inr ⟨unfinished, offset, earlier, rows[offset], atOffset offset (by omega),
      .vreg destination, selected, ?_⟩
    simpa only [TraceWitness.destinationRegisterAddress, destinationEq] using registerEq.symm
  · cases written

private theorem expansion_row_countdown
    (image : Rv64ProgramImage SourceInstruction) (bytecode : Array JoltInstructionRow)
    (expanded : expand_program image = some bytecode)
    (first : Fin bytecode.size) (starts : bytecode[first].starts_source = true)
    (offset : Nat) (inside : offset < expansionRowCount bytecode first)
    (row : JoltInstructionRow) (atRow : bytecode[first.val + offset]? = some row) :
    (row.virtual_sequence_remaining.getD 0).toNat + offset + 1 =
      expansionRowCount bytecode first := by
  let rows := (bytecode.toList.drop first.val).take (expansionRowCount bytecode first)
  obtain ⟨source, expandedRows⟩ := expand_program_block image bytecode expanded first starts
  have endBound := (expand_program_layout image bytecode expanded).endInBounds first
  have length : rows.length = expansionRowCount bytecode first := by
    simp only [rows, List.length_take, List.length_drop, Array.length_toList]
    unfold expansionRowCount at endBound ⊢
    omega
  have inRows : offset < rows.length := by omega
  have atOffset : rows[offset] = row := by
    have bound : first.val + offset < bytecode.size := by
      unfold expansionRowCount at inside
      omega
    simpa only [Array.getElem?_eq_getElem bound, Option.some.injEq, rows,
      List.getElem_take, List.getElem_drop, Array.getElem_toList] using atRow
  have countdown := expand_instruction_countdown source rows expandedRows offset inRows
  rw [atOffset] at countdown
  omega

/-- A row before the end of a stamped expansion has a nonzero countdown.
For example, the first row of a nine-row REM block has eight rows remaining.
The proof uses Jolt's sequence stamp from
`jolt/crates/jolt-program/src/expand/metadata.rs` (`stamp_sequence_metadata`)
at 5def437f. -/
theorem expansion_row_remaining
    (image : Rv64ProgramImage SourceInstruction) (bytecode : Array JoltInstructionRow)
    (expanded : expand_program image = some bytecode)
    (first : Fin bytecode.size) (starts : bytecode[first].starts_source = true)
    (offset : Nat) (interior : offset + 1 < expansionRowCount bytecode first)
    (row : JoltInstructionRow) (atRow : bytecode[first.val + offset]? = some row) :
    row.virtual_sequence_remaining.getD 0 ≠ 0 := by
  intro zero
  have countdown := expansion_row_countdown image bytecode expanded first starts offset (by omega) row atRow
  rw [zero] at countdown
  change 0 + offset + 1 = expansionRowCount bytecode first at countdown
  omega

private theorem expansion_order_push (bytecode : Array JoltInstructionRow)
    (rows : Array (TraceRow bytecode)) (first done : Nat)
    (retained : done ≤ rows.size)
    (ordered : ∀ offset < done, ∃ row ∈ rows[rows.size - done + offset]?, row.rowIndex.val = first + offset)
    (step : TraceRow bytecode) (indexIs : step.rowIndex.val = first + done) :
    (∀ offset < done + 1, ∃ row ∈ (rows.push step)[(rows.push step).size - (done + 1) + offset]?,
      row.rowIndex.val = first + offset) ∧
    (rows.push step).extract 0 ((rows.push step).size - (done + 1)) = rows.extract 0 (rows.size - done) := by
  constructor
  · intro offset before
    rw [Array.size_push, show rows.size + 1 - (done + 1) = rows.size - done by omega]
    by_cases old : offset < done
    · obtain ⟨row, atIndex, index⟩ := ordered offset old
      refine ⟨row, ?_, index⟩
      rw [Array.getElem?_push, if_neg (by omega)]
      exact atIndex
    · have same : offset = done := by omega
      subst offset
      rw [show rows.size - done + done = rows.size by omega]
      exact ⟨step, Array.getElem?_push_size, indexIs⟩
  · rw [Array.size_push, show rows.size + 1 - (done + 1) = rows.size - done by omega,
      Array.extract_push_of_le (Nat.sub_le _ _)]

private theorem expansionLive_after
    (bytecode : Array JoltInstructionRow) (first : Fin bytecode.size) (done : Nat)
    (row : JoltInstructionRow) (atRow : bytecode[first.val + done]? = some row)
    (register : Fin 128) (live : ExpansionLive bytecode first (done + 1) register) :
    ExpansionLive bytecode first done register ∨
      ∃ destination ∈ row.instruction.destination?,
        register = TraceWitness.destinationRegisterAddress destination := by
  rcases live with persistent | ⟨unfinished, offset, earlier, before, atBefore,
    destination, written, address⟩
  · exact Or.inl (Or.inl persistent)
  by_cases previous : offset < done
  · exact Or.inl (Or.inr ⟨by omega, offset, previous, before, atBefore,
      destination, written, address⟩)
  · have equal : offset = done := by omega
    subst offset
    have same : before = row := Option.some.inj (atBefore.symm.trans atRow)
    subst before
    exact Or.inr ⟨destination, written, address.symm⟩

private theorem adjacent_push {α : Type} (rows : Array α) (step : α)
    (relation : α → α → Prop)
    (old : ∀ index current next, rows[index]? = some current →
      rows[index + 1]? = some next → relation current next)
    (last : ∀ current ∈ rows.back?, relation current step) :
    ∀ index current next, (rows.push step)[index]? = some current →
      (rows.push step)[index + 1]? = some next → relation current next := by
  intro index current next atCurrent atNext
  have nextBound := Array.getElem?_eq_some_iff.mp atNext
  have oldCurrent : index < rows.size := by
    have h := nextBound.1
    simp only [Array.size_push] at h
    omega
  have currentOld : rows[index]? = some current := by
    simpa only [Array.getElem?_push_lt oldCurrent, Array.getElem?_eq_getElem oldCurrent] using atCurrent
  by_cases oldNext : index + 1 < rows.size
  · exact old index current next currentOld
      (by simpa only [Array.getElem?_push_lt oldNext, Array.getElem?_eq_getElem oldNext] using atNext)
  · have equal : index + 1 = rows.size := by
      have h := nextBound.1
      simp only [Array.size_push] at h
      omega
    have same : step = next := by
      simpa only [equal, Array.getElem?_push_size, Option.some.injEq] using atNext
    subst next
    apply last current
    rw [Array.back?_eq_getElem?]
    simpa only [show rows.size - 1 = index by omega] using currentOld

/-- Append a certified execution using an arbitrary tape answer.
The entry and linkage hypotheses connect the new row to the retained prefix.
For example, REM's VirtualAdvice row can record witness quotient 5 without
requiring it to equal the honest quotient. -/
noncomputable def appendUntrustedRow
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (run : UntrustedAnswerRun joltInstance privateInputs)
    (step : TraceRow run.bytecode) (answer : BitVec 64)
    (executes : execWithTapeAnswer
      (run.bytecode[step.rowIndex].instruction.withRuntimeAdvice step.runtimeAdvice)
      answer step.preState = .ok RETIRE_SUCCESS step.postState)
    (starts : run.rows.size = 0 →
      run.bytecode[step.rowIndex].address = joltInstance.program.entry_address ∧
      run.bytecode[step.rowIndex].starts_source ∧
      step.preState = advance_pc joltInstance.program.entry_address
        (source_is_compressed run.bytecode step.rowIndex) run.initialState)
    (linked : ∀ last ∈ run.rows.back?,
      if run.bytecode[last.rowIndex].virtual_sequence_remaining.getD 0 ≠ 0 then
        step.rowIndex.val = last.rowIndex.val + 1 ∧ step.preState = last.postState
      else
        ∃ address, last.postState.sail.regs.get? Register.nextPC = some address ∧
          run.bytecode[step.rowIndex].address = address ∧
          run.bytecode[step.rowIndex].starts_source ∧
          step.preState = advance_pc address
            (source_is_compressed run.bytecode step.rowIndex) last.postState) :
    UntrustedAnswerRun joltInstance privateInputs where
  toTrace := { run.toTrace with rows := run.rows.push step }
  answers index := if before : index.val < run.rows.size then
    run.answers ⟨index.val, before⟩ else answer
  expands := run.expands
  initialized := run.initialized
  executes index := by
    by_cases before : index.val < run.rows.size
    · simp only [dif_pos before]
      have same : (run.rows.push step)[index.val] = run.rows[index.val] := Array.getElem_push_lt before
      change (fun row : TraceRow run.bytecode =>
        execWithTapeAnswer (run.bytecode[row.rowIndex].instruction.withRuntimeAdvice row.runtimeAdvice)
          (run.answers ⟨index.val, before⟩) row.preState = .ok RETIRE_SUCCESS row.postState)
        (run.rows.push step)[index.val]
      rw [same]
      exact run.executes ⟨index.val, before⟩
    · have equal : index.val = run.rows.size := by have h := index.isLt; simp at h; omega
      simp only [dif_neg before]
      have same : (run.rows.push step)[index.val] = step := by simp only [equal, Array.getElem_push_eq]
      change (fun row : TraceRow run.bytecode =>
        execWithTapeAnswer (run.bytecode[row.rowIndex].instruction.withRuntimeAdvice row.runtimeAdvice)
          answer row.preState = .ok RETIRE_SUCCESS row.postState)
        (run.rows.push step)[index.val]
      rw [same]
      exact executes
  starts first atFirst := by
    change (run.rows.push step)[0]? = some first at atFirst
    by_cases empty : run.rows.size = 0
    · have equal : step = first := by simpa only [Array.getElem?_push, empty, ↓reduceIte, Option.some.injEq] using atFirst
      subst first
      exact starts empty
    · rw [Array.getElem?_push, if_neg (Ne.symm empty)] at atFirst
      exact run.starts first atFirst
  linked := adjacent_push run.rows step _ run.linked linked

private theorem trace_push_observations {F : Type} [Field F] {params : WitnessParams}
    (trace : Trace) (step : TraceRow trace.bytecode) (t : Fin params.traceLength)
    (old : t.val < trace.rows.size) :
    TraceWitness.PC (F := F) params { trace with rows := trace.rows.push step } t =
        TraceWitness.PC params trace t ∧
    TraceWitness.Rs1Value (F := F) params { trace with rows := trace.rows.push step } t =
        TraceWitness.Rs1Value params trace t ∧
    TraceWitness.Rs2Value (F := F) params { trace with rows := trace.rows.push step } t =
        TraceWitness.Rs2Value params trace t ∧
    TraceWitness.RamAddress (F := F) params { trace with rows := trace.rows.push step } t =
        TraceWitness.RamAddress params trace t := by
  have larger : t.val < (trace.rows.push step).size := by simp only [Array.size_push]; omega
  simp only [TraceWitness.PC, TraceWitness.bytecodePc, TraceWitness.Rs1Value,
    TraceWitness.Rs2Value, TraceWitness.RamAddress, dif_pos old, dif_pos larger,
    Array.getElem_push_lt old, and_self]

private theorem representsRows_push {F : Type} [Field F] {params : WitnessParams}
    (witness : WitnessType F params) (trace : Trace) (step : TraceRow trace.bytecode)
    (old : RepresentsRows witness trace) (bound : trace.rows.size < params.traceLength)
    (pc : witness.PC ⟨trace.rows.size, bound⟩ =
      TraceWitness.PC params {trace with rows := trace.rows.push step} ⟨trace.rows.size, bound⟩)
    (rs1 : witness.Rs1Value ⟨trace.rows.size, bound⟩ =
      TraceWitness.Rs1Value params {trace with rows := trace.rows.push step} ⟨trace.rows.size, bound⟩)
    (rs2 : witness.Rs2Value ⟨trace.rows.size, bound⟩ =
      TraceWitness.Rs2Value params {trace with rows := trace.rows.push step} ⟨trace.rows.size, bound⟩)
    (ram : witness.RamAddress ⟨trace.rows.size, bound⟩ =
      TraceWitness.RamAddress params {trace with rows := trace.rows.push step} ⟨trace.rows.size, bound⟩) :
    RepresentsRows witness {trace with rows := trace.rows.push step} := by
  have casesAt (t : Fin params.traceLength) (inside : t.val < (trace.rows.push step).size) :
      t.val < trace.rows.size ∨ t = ⟨trace.rows.size, bound⟩ := by
    simp only [Array.size_push] at inside
    by_cases before : t.val < trace.rows.size
    · exact Or.inl before
    · exact Or.inr (Fin.ext (show t.val = trace.rows.size by omega))
  refine ⟨by simp only [Array.size_push]; omega, ?_, ?_, ?_, ?_⟩
  · intro t inside
    rcases casesAt t inside with before | rfl
    · exact (old.pc t before).trans (trace_push_observations trace step t before).1.symm
    · exact pc
  · intro t inside persistent
    rcases casesAt t inside with before | rfl
    · have kept := trace_push_observations (F := F) trace step t before
      exact (old.rs1 t before (by simpa only [Array.getElem_push_lt before] using persistent)).trans kept.2.1.symm
    · exact rs1
  · intro t inside persistent
    rcases casesAt t inside with before | rfl
    · have kept := trace_push_observations (F := F) trace step t before
      exact (old.rs2 t before (by simpa only [Array.getElem_push_lt before] using persistent)).trans kept.2.2.1.symm
    · exact rs2
  · intro t inside
    rcases casesAt t inside with before | rfl
    · exact (old.ramAddress t before).trans (trace_push_observations trace step t before).2.2.2.symm
    · exact ram

/-- Appending a row makes its post-state the final trace state.
For example, a REM advice row leaves the final trace state with its quotient write. -/
theorem finalTraceState_push (trace : Trace) (step : TraceRow trace.bytecode) :
    TraceWitness.finalTraceState {trace with rows := trace.rows.push step} = step.postState := by
  simp only [TraceWitness.finalTraceState, Array.size_push, Nat.zero_lt_succ,
    ↓reduceDIte, Nat.add_sub_cancel, Array.getElem_push_eq]

private theorem finalTraceState_back (trace : Trace) :
    TraceWitness.finalTraceState trace =
      (trace.rows.back?.map (·.postState)).getD trace.initialState := by
  unfold TraceWitness.finalTraceState
  split
  · rename_i positive
    rw [Array.back?_eq_getElem?, Array.getElem?_eq_getElem (by omega)]
    rfl
  · rename_i empty
    have zero : trace.rows.size = 0 := by omega
    have rows : trace.rows = #[] := Array.size_eq_zero_iff.mp zero
    simp only [rows, Array.back?_empty, Option.map_none, Option.getD_none]

private theorem representsPrefix_push {F : Type} [Field F] {params : WitnessParams}
    (joltField : JoltField F) (witness : WitnessType F params)
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (context : ConstraintContext joltInstance privateInputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
    (trace : Trace) (step : TraceRow trace.bytecode)
    (old : RepresentsPrefix witness trace) (bound : trace.rows.size < params.traceLength)
    (rows : RepresentsRows witness {trace with rows := trace.rows.push step})
    (zero : witness.RamAddress ⟨trace.rows.size, bound⟩ = 0)
    (memory : step.postState.sail.mem = (TraceWitness.finalTraceState trace).sail.mem)
    (device : step.postState.jolt_device = (TraceWitness.finalTraceState trace).jolt_device) :
    RepresentsPrefix witness {trace with rows := trace.rows.push step} := by
  have same (address : Nat) :
      TraceWitness.finalRamWord {trace with rows := trace.rows.push step} address =
        TraceWitness.finalRamWord trace address := by
    simp only [TraceWitness.finalRamWord, finalTraceState_push, memory, device]
  refine {rows with cutRam := ⟨?_, ?_⟩}
  · intro next address outside
    rw [same]
    simpa only [Array.size_push] using
      (ramVal_succ_of_address_zero (two_pow_127_lt_char joltField)
        context equations address ⟨trace.rows.size, bound⟩
        (by simpa only [Array.size_push] using next) zero).trans
        (old.cutRam.1 bound address outside)
  · intro last address outside
    rw [same]
    simpa only [Array.size_push] using
      (ramValFinal_of_address_zero (two_pow_127_lt_char joltField)
        context equations address ⟨trace.rows.size, bound⟩
        (by simpa only [Array.size_push] using last) zero).trans
        (old.cutRam.1 bound address outside)

private theorem interior_progress {F : Type} [Field F] {params : WitnessParams}
    (joltField : JoltField F) (witness : WitnessType F params)
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (context : ConstraintContext joltInstance privateInputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
    (run : UntrustedAnswerRun joltInstance privateInputs)
    (bytecodeEq : run.bytecode = context.bytecode)
    (step : TraceRow run.bytecode) (cycle : Fin params.traceLength)
    (slot : Fin (2 ^ params.logBytecodeK))
    (slotIndex : slot.val = step.rowIndex.val + 1)
    (selected : bytecodeRa witness slot cycle = 1)
    (rowIs : bytecodeRow context.bytecode slot.val = some run.bytecode[step.rowIndex])
    (remaining : run.bytecode[step.rowIndex].virtual_sequence_remaining.getD 0 ≠ 0) :
    ∃ (bound : cycle.val + 1 < params.traceLength)
      (next : Fin run.bytecode.size) (nextSlot : Fin (2 ^ params.logBytecodeK)),
      next.val = step.rowIndex.val + 1 ∧
      nextSlot.val = next.val + 1 ∧
      bytecodeRa witness nextSlot ⟨cycle.val + 1, bound⟩ = 1 ∧
      witness.InstructionFlags .IsNoop ⟨cycle.val + 1, bound⟩ = 0 := by
  have increment := nonterminal_virtual_row_pc_plus_one joltField joltInstance privateInputs
    witness context equations cycle slot selected _ rowIs remaining
  have bound : cycle.val + 1 < params.traceLength := by
    by_contra full
    exact nonterminal_at_last_cycle_impossible joltField joltInstance privateInputs witness
      context equations run bytecodeEq step cycle (by omega) slot slotIndex selected increment
  obtain ⟨nextSlot, nextSelected, consecutive⟩ := selected_next_of_remaining
    (two_pow_127_lt_char joltField) context equations cycle bound slot selected rowIs remaining
  have endBound := (expand_program_layout joltInstance.program run.bytecode run.expands).endInBounds step.rowIndex
  have positive : 0 < (run.bytecode[step.rowIndex].virtual_sequence_remaining.getD 0).toNat := by
    have nonzero := BitVec.toNat_ne_iff_ne.mpr remaining
    change (run.bytecode[step.rowIndex].virtual_sequence_remaining.getD 0).toNat ≠ 0 at nonzero
    omega
  let next : Fin run.bytecode.size := ⟨step.rowIndex.val + 1, by omega⟩
  have nextSlotIs : nextSlot.val = next.val + 1 := by dsimp [next]; omega
  have nextRowIs : bytecodeRow context.bytecode nextSlot.val = some run.bytecode[next] := by
    rw [← bytecodeEq, nextSlotIs]
    simp only [bytecodeRow, Array.getElem?_eq_getElem next.isLt, Fin.getElem_fin]
  refine ⟨bound, next, nextSlot, rfl, nextSlotIs, nextSelected, ?_⟩
  simpa only [bytecodeInstructionFlag, nextRowIs, JoltMetadata.instructionFlag,
    Bool.false_eq_true, ↓reduceIte] using
    instructionFlag_of_selected_bytecode (two_pow_127_lt_char joltField) context equations
      .IsNoop ⟨cycle.val + 1, bound⟩ nextSlot nextSelected

/-- The old live set plus the current destination, if any.
For example, REM's advice row adds temporary 40. -/
private def rowLive (live : Fin 128 → Prop) (instruction : Instr) (register : Fin 128) : Prop :=
  live register ∨ ∃ destination ∈ instruction.destination?,
    register = TraceWitness.destinationRegisterAddress destination

/-- Local arithmetic execution, with witness advice, live-register agreement,
and unchanged RAM and device; for example, a MUL writes only its destination. -/
private structure ArithmeticExecution {F : Type} [Field F] {params : WitnessParams}
    (witness : WitnessType F params) (t : Fin params.traceLength) (live : Fin 128 → Prop)
    (instruction : Instr) (pre post : SailJoltState) (advice : instruction.RuntimeAdvice) : Prop where
  executes : execWithTapeAnswer (instruction.withRuntimeAdvice advice) 0 pre = .ok RETIRE_SUCCESS post
  encoded : ∀ value ∈ (instruction.withRuntimeAdvice advice).adviceValue?,
    witness.RdWriteValue t = (value.toNat : F)
  registers : ∀ next : t.val + 1 < params.traceLength,
    RegisterAgreementOn (rowLive live instruction) witness ⟨t.val + 1, next⟩ post
  memory : post.sail.mem = pre.sail.mem
  device : post.jolt_device = pre.jolt_device

private theorem arithmeticExecution_write {F : Type} [Field F] {params : WitnessParams}
    {witness : WitnessType F params} {t : Fin params.traceLength} {live : Fin 128 → Prop}
    {instruction : Instr} {pre : SailJoltState} (advice : instruction.RuntimeAdvice)
    (destination : Dst) (destinationIs : instruction.destination? = some destination)
    (value : BitVec 64)
    (encoded : ∀ v ∈ (instruction.withRuntimeAdvice advice).adviceValue?, witness.RdWriteValue t = (v.toNat : F))
    (executes : execWithTapeAnswer (instruction.withRuntimeAdvice advice) 0 pre =
      .ok RETIRE_SUCCESS (afterWriteDst destination value pre))
    (registers : ∀ next : t.val + 1 < params.traceLength,
      RegisterAgreementOn (fun register => live register ∨
        register = TraceWitness.destinationRegisterAddress destination)
        witness ⟨t.val + 1, next⟩ (afterWriteDst destination value pre)) :
    ArithmeticExecution witness t live instruction pre (afterWriteDst destination value pre) advice := by
  refine ⟨executes, encoded, ?_, ?_, ?_⟩
  · intro next
    apply (registers next).mono
    intro register member
    rcases member with old | ⟨dst, written, same⟩
    · exact Or.inl old
    · simp only [destinationIs, Option.mem_some_iff] at written
      subst dst
      exact Or.inr same
  · cases destination <;> rfl
  · cases destination <;> rfl

private theorem arithmeticExecution_assert {F : Type} [Field F] {params : WitnessParams}
    {witness : WitnessType F params} {t : Fin params.traceLength} {live : Fin 128 → Prop}
    {instruction : Instr} {pre : SailJoltState} (advice : instruction.RuntimeAdvice)
    (destinationIs : instruction.destination? = none)
    (noAdvice : instruction.adviceValue? = none)
    (executes : execWithTapeAnswer (instruction.withRuntimeAdvice advice) 0 pre = .ok RETIRE_SUCCESS pre)
    (registers : ∀ next : t.val + 1 < params.traceLength,
      RegisterAgreementOn live witness ⟨t.val + 1, next⟩ pre) :
    ArithmeticExecution witness t live instruction pre pre advice := by
  refine ⟨executes, ?_, ?_, rfl, rfl⟩
  · rw [withRuntimeAdvice_eq_of_noAdvice _ advice noAdvice, noAdvice]
    simp
  · intro next
    apply (registers next).mono
    intro register member
    rcases member with old | ⟨dst, written, _⟩
    · exact old
    · rw [destinationIs] at written
      cases written

/-- A well-typed placeholder for ignored runtime advice.
For example, MUL uses the unit value; VirtualAdvice has word placeholder zero. -/
private def zeroRuntimeAdvice (instruction : Instr) : instruction.RuntimeAdvice := by
  unfold Instr.RuntimeAdvice
  split
  · exact 0
  · exact ()

private theorem arithmetic_execution {F : Type} [Field F] {params : WitnessParams}
    (joltField : JoltField F) {witness : WitnessType F params} {live : Fin 128 → Prop}
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (context : ConstraintContext joltInstance privateInputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
    {t : Fin params.traceLength} {slot : Fin (2 ^ params.logBytecodeK)}
    (selected : bytecodeRa witness slot t = 1)
    {row : JoltInstructionRow} (rowIs : bytecodeRow context.bytecode slot.val = some row)
    (arithmetic : DivisionArithmeticRow row.instruction)
    {pre : SailJoltState} (agrees : RegisterAgreementOn live witness t pre)
    (sourcesLive : ∀ source ∈ ExpansionTempLiveness.readSources row.instruction,
      live (TraceWitness.sourceRegisterAddress source)) :
    ∃ (post : SailJoltState) (advice : row.instruction.RuntimeAdvice),
      ArithmeticExecution witness t live row.instruction pre post advice := by
  let advice := zeroRuntimeAdvice row.instruction
  have nonAdviceWrite {destination : Dst} {value : BitVec 64}
      (destinationIs : row.instruction.destination? = some destination)
      (noAdvice : row.instruction.adviceValue? = none)
      (result : witness.RdWriteValue t = (value.toNat : F) ∧
        execWithTapeAnswer (row.instruction.withRuntimeAdvice advice) 0 pre =
          .ok RETIRE_SUCCESS (afterWriteDst destination value pre) ∧
        ∀ next : t.val + 1 < params.traceLength,
          RegisterAgreementOn (fun r => live r ∨ r = TraceWitness.destinationRegisterAddress destination)
            witness ⟨t.val + 1, next⟩ (afterWriteDst destination value pre)) :
      ∃ (post : SailJoltState) (advice : row.instruction.RuntimeAdvice),
        ArithmeticExecution witness t live row.instruction pre post advice := by
    refine ⟨afterWriteDst destination value pre, advice,
      arithmeticExecution_write advice destination destinationIs value ?_ result.2.1 result.2.2⟩
    rw [withRuntimeAdvice_eq_of_noAdvice _ advice noAdvice, noAdvice]
    simp
  unfold DivisionArithmeticRow at arithmetic
  split at arithmetic
  · rename_i destination placeholder imm instructionIs
    obtain ⟨value, chosen, patched, encoded, executes, registers⟩ :=
      advice_step joltField context equations selected rowIs instructionIs agrees 0
    refine ⟨_, chosen, arithmeticExecution_write chosen destination
      (by rw [instructionIs]; rfl) value ?_ executes registers⟩
    intro v present
    rw [patched] at present
    have same : value = v := by simpa only [Instr.adviceValue?, Option.mem_some_iff] using present
    simpa only [← same] using encoded
  · rename_i destination lhs rhs instructionIs
    exact nonAdviceWrite (by rw [instructionIs]; rfl) (by rw [instructionIs]; rfl)
      (virtualBinary_step joltField context equations selected rowIs .negateIf instructionIs agrees
        (sourcesLive lhs (by rw [instructionIs]; simp [ExpansionTempLiveness.readSources]))
        (sourcesLive rhs (by rw [instructionIs]; simp [ExpansionTempLiveness.readSources])) 0 advice)
  · rename_i destination lhs rhs instructionIs
    exact nonAdviceWrite (by rw [instructionIs]; rfl) (by rw [instructionIs]; rfl)
      (xor_step joltField context equations selected rowIs instructionIs agrees
        (sourcesLive lhs (by rw [instructionIs]; simp [ExpansionTempLiveness.readSources]))
        (sourcesLive rhs (by rw [instructionIs]; simp [ExpansionTempLiveness.readSources])) 0 advice)
  · rename_i destination lhs rhs instructionIs
    exact nonAdviceWrite (by rw [instructionIs]; rfl) (by rw [instructionIs]; rfl)
      (arithmetic_step joltField context equations selected rowIs .mul instructionIs agrees
        (sourcesLive lhs (by rw [instructionIs]; simp [ExpansionTempLiveness.readSources]))
        (sourcesLive rhs (by rw [instructionIs]; simp [ExpansionTempLiveness.readSources])) 0 advice)
  · rename_i destination lhs rhs instructionIs
    exact nonAdviceWrite (by rw [instructionIs]; rfl) (by rw [instructionIs]; rfl)
      (arithmetic_step joltField context equations selected rowIs .sub instructionIs agrees
        (sourcesLive lhs (by rw [instructionIs]; simp [ExpansionTempLiveness.readSources]))
        (sourcesLive rhs (by rw [instructionIs]; simp [ExpansionTempLiveness.readSources])) 0 advice)
  · rename_i destination source imm instructionIs
    exact nonAdviceWrite (by rw [instructionIs]; rfl) (by rw [instructionIs]; rfl)
      (addi_step joltField context equations selected rowIs instructionIs agrees
        (sourcesLive source (by rw [instructionIs]; simp [ExpansionTempLiveness.readSources])) 0 advice)
  · rename_i destination source imm instructionIs
    exact nonAdviceWrite (by rw [instructionIs]; rfl) (by rw [instructionIs]; rfl)
      (unaryWord_step joltField context equations selected rowIs .signExtend instructionIs agrees
        (sourcesLive source (by rw [instructionIs]; simp [ExpansionTempLiveness.readSources])) 0 advice)
  · rename_i destination source imm instructionIs
    exact nonAdviceWrite (by rw [instructionIs]; rfl) (by rw [instructionIs]; rfl)
      (unaryWord_step joltField context equations selected rowIs .zeroExtend instructionIs agrees
        (sourcesLive source (by rw [instructionIs]; simp [ExpansionTempLiveness.readSources])) 0 advice)
  · rename_i lhs rhs imm instructionIs
    have result := binaryAssertion_step joltField context equations selected rowIs .div0 instructionIs agrees
      (sourcesLive lhs (by rw [instructionIs]; simp [ExpansionTempLiveness.readSources]))
      (sourcesLive rhs (by rw [instructionIs]; simp [ExpansionTempLiveness.readSources])) 0 advice
    exact ⟨pre, advice, arithmeticExecution_assert advice (by rw [instructionIs]; rfl)
      (by rw [instructionIs]; rfl) result.2.1 result.2.2⟩
  · rename_i lhs rhs imm instructionIs
    have result := mulAssertion_step joltField context equations selected rowIs instructionIs agrees
      (sourcesLive lhs (by rw [instructionIs]; simp [ExpansionTempLiveness.readSources]))
      (sourcesLive rhs (by rw [instructionIs]; simp [ExpansionTempLiveness.readSources])) 0 advice
    exact ⟨pre, advice, arithmeticExecution_assert advice (by rw [instructionIs]; rfl)
      (by rw [instructionIs]; rfl) result.2.1 result.2.2⟩
  · rename_i lhs rhs imm instructionIs
    have result := assertLTE_step joltField context equations selected rowIs instructionIs agrees
      (sourcesLive lhs (by rw [instructionIs]; simp [ExpansionTempLiveness.readSources]))
      (sourcesLive rhs (by rw [instructionIs]; simp [ExpansionTempLiveness.readSources])) 0 advice
    exact ⟨pre, advice, arithmeticExecution_assert advice (by rw [instructionIs]; rfl)
      (by rw [instructionIs]; rfl) result.2.1 result.2.2⟩
  · rename_i lhs rhs imm instructionIs
    have result := binaryAssertion_step joltField context equations selected rowIs .remainder instructionIs agrees
      (sourcesLive lhs (by rw [instructionIs]; simp [ExpansionTempLiveness.readSources]))
      (sourcesLive rhs (by rw [instructionIs]; simp [ExpansionTempLiveness.readSources])) 0 advice
    exact ⟨pre, advice, arithmeticExecution_assert advice (by rw [instructionIs]; rfl)
      (by rw [instructionIs]; rfl) result.2.1 result.2.2⟩
  · contradiction

private theorem plain_no_memory (instruction : Instr) (plain : PlainRow instruction)
    (pre : SailJoltState) :
    JoltMetadata.opcodeFlag instruction .Load = false ∧
    JoltMetadata.opcodeFlag instruction .Store = false ∧
    TraceWitness.ramAccessAddress instruction pre = none := by
  refine ⟨?_, ?_, ?_⟩
  · apply Bool.eq_false_iff.mpr
    intro flag
    obtain ⟨fault, destination, base, imm, same⟩ := JoltMetadata.opcodeFlag_load_requiresLD instruction flag
    rw [same] at plain
    exact plain
  · apply Bool.eq_false_iff.mpr
    intro flag
    obtain ⟨base, value, imm, same⟩ := JoltMetadata.opcodeFlag_store_requiresSD instruction flag
    rw [same] at plain
    exact plain
  · unfold TraceWitness.ramAccessAddress
    split <;> first | rfl | exact False.elim plain

private theorem plain_row_ram {F : Type} [Field F] {params : WitnessParams}
    (joltField : JoltField F) (witness : WitnessType F params)
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (context : ConstraintContext joltInstance privateInputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
    (trace : Trace) (step : TraceRow trace.bytecode) (bound : trace.rows.size < params.traceLength)
    (slot : Fin (2 ^ params.logBytecodeK))
    (selected : bytecodeRa witness slot ⟨trace.rows.size, bound⟩ = 1)
    (rowIs : bytecodeRow context.bytecode slot.val = some trace.bytecode[step.rowIndex])
    (plain : PlainRow trace.bytecode[step.rowIndex].instruction) :
    witness.RamAddress ⟨trace.rows.size, bound⟩ = 0 ∧
    TraceWitness.RamAddress (F := F) params {trace with rows := trace.rows.push step}
      ⟨trace.rows.size, bound⟩ = 0 := by
  obtain ⟨noLoad, noStore, noAccess⟩ := plain_no_memory _ plain step.preState
  have load : witness.OpFlags .Load ⟨trace.rows.size, bound⟩ = 0 := by
    simpa only [bytecodeCircuitFlag, rowIs, JoltMetadata.circuitFlag, noLoad,
      Bool.false_eq_true, ↓reduceIte] using
      opFlag_of_selected_bytecode (two_pow_127_lt_char joltField) context equations
        .Load ⟨trace.rows.size, bound⟩ slot selected
  have store : witness.OpFlags .Store ⟨trace.rows.size, bound⟩ = 0 := by
    simpa only [bytecodeCircuitFlag, rowIs, JoltMetadata.circuitFlag, noStore,
      Bool.false_eq_true, ↓reduceIte] using
      opFlag_of_selected_bytecode (two_pow_127_lt_char joltField) context equations
        .Store ⟨trace.rows.size, bound⟩ slot selected
  refine ⟨ramAddress_zero_of_not_load_store equations.ramAddrEqZeroIfNotLoadStore _ load store, ?_⟩
  simp only [Fin.getElem_fin] at noAccess
  simp only [TraceWitness.RamAddress, Array.size_push, Nat.lt_add_one,
    ↓reduceDIte, Array.getElem_push_eq, noAccess]

private theorem arithmetic_row_observations {F : Type} [Field F] {params : WitnessParams}
    (joltField : JoltField F) (witness : WitnessType F params) {live : Fin 128 → Prop}
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (context : ConstraintContext joltInstance privateInputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
    (trace : Trace) (step : TraceRow trace.bytecode) (bound : trace.rows.size < params.traceLength)
    (slot : Fin (2 ^ params.logBytecodeK))
    (selected : bytecodeRa witness slot ⟨trace.rows.size, bound⟩ = 1)
    (rowIs : bytecodeRow context.bytecode slot.val = some trace.bytecode[step.rowIndex])
    (arithmetic : DivisionArithmeticRow trace.bytecode[step.rowIndex].instruction)
    (agrees : RegisterAgreementOn live witness ⟨trace.rows.size, bound⟩ step.preState)
    (sourcesLive : ∀ source ∈ ExpansionTempLiveness.readSources trace.bytecode[step.rowIndex].instruction,
      live (TraceWitness.sourceRegisterAddress source)) :
    witness.Rs1Value ⟨trace.rows.size, bound⟩ =
        TraceWitness.Rs1Value params {trace with rows := trace.rows.push step} ⟨trace.rows.size, bound⟩ ∧
    witness.Rs2Value ⟨trace.rows.size, bound⟩ =
        TraceWitness.Rs2Value params {trace with rows := trace.rows.push step} ⟨trace.rows.size, bound⟩ := by
  have canonical := (bytecodeRow_rowOk context rowIs).canonical
  rw [rs1Value_of_selected_bytecode (two_pow_127_lt_char joltField) context equations
      ⟨trace.rows.size, bound⟩ slot selected,
    rs2Value_of_selected_bytecode (two_pow_127_lt_char joltField) context equations
      ⟨trace.rows.size, bound⟩ slot selected]
  simp only [rowIs, Option.bind_some, TraceWitness.Rs1Value, TraceWitness.Rs2Value,
    Array.size_push, Nat.lt_add_one, ↓reduceDIte, Array.getElem_push_eq, Fin.getElem_fin]
  simp only [Fin.getElem_fin] at arithmetic canonical sourcesLive
  unfold DivisionArithmeticRow at arithmetic
  split at arithmetic
  all_goals first
    | exact False.elim arithmetic
    | (rename_i instructionIs
       simp only [instructionIs, JoltRegisterEncoding.instructionIsCanonical,
         Bool.and_eq_true] at canonical
       simp only [instructionIs, bytecodeRs1Register, bytecodeRs2Register]
       constructor <;> first
         | exact True.intro
         | rfl
         | exact (agrees.read _ (by tauto)
             (sourcesLive _ (by simp [instructionIs, ExpansionTempLiveness.readSources]))).2)

/-- The entry and linkage part of `NextStep`, without honest-advice or
no-earlier-stop requirements on the retained prefix.
For example, the guard after REM's witness quotient 5 is ready even when the
honest quotient is 0. -/
def RawRowEntry {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (run : UntrustedAnswerRun joltInstance privateInputs)
    (next : Fin run.bytecode.size) (pre : SailJoltState) : Prop :=
  match run.rows.back? with
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
        ¬ last.StableStall ∧ run.bytecode[next].address = address ∧
        run.bytecode[next].starts_source ∧
        pre = advance_pc address (source_is_compressed run.bytecode next) last.postState

private theorem rawEntry_starts
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    {run : UntrustedAnswerRun joltInstance privateInputs} {next : Fin run.bytecode.size}
    {pre : SailJoltState} (entry : RawRowEntry run next pre) (empty : run.rows.size = 0) :
    run.bytecode[next].address = joltInstance.program.entry_address ∧
      run.bytecode[next].starts_source ∧
      pre = advance_pc joltInstance.program.entry_address
        (source_is_compressed run.bytecode next) run.initialState := by
  have lastIs : run.rows.back? = none :=
    Array.back?_eq_none_iff.mpr (Array.size_eq_zero_iff.mp empty)
  simpa only [RawRowEntry, lastIs] using entry

private theorem rawEntry_linked
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    {run : UntrustedAnswerRun joltInstance privateInputs} {next : Fin run.bytecode.size}
    {pre : SailJoltState} (entry : RawRowEntry run next pre) :
    ∀ last ∈ run.rows.back?,
      if run.bytecode[last.rowIndex].virtual_sequence_remaining.getD 0 ≠ 0 then
        next.val = last.rowIndex.val + 1 ∧ pre = last.postState
      else ∃ address, last.postState.sail.regs.get? Register.nextPC = some address ∧
        run.bytecode[next].address = address ∧ run.bytecode[next].starts_source ∧
        pre = advance_pc address (source_is_compressed run.bytecode next) last.postState := by
  intro last atEnd
  change run.rows.back? = some last at atEnd
  simp only [RawRowEntry, atEnd] at entry
  by_cases remaining : run.bytecode[last.rowIndex].virtual_sequence_remaining.getD 0 ≠ 0
  · simpa only [if_pos remaining] using entry
  · simp only [if_neg remaining] at entry ⊢
    obtain ⟨address, pc, _, addressIs, starts, preIs⟩ := entry
    exact ⟨address, pc, addressIs, starts, preIs⟩

private theorem rawEntry_prepared {F : Type} [Field F] {params : WitnessParams}
    {witness : WitnessType F params} {t : Fin params.traceLength} {live : Fin 128 → Prop}
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    {run : UntrustedAnswerRun joltInstance privateInputs} {next : Fin run.bytecode.size}
    {pre : SailJoltState} (entry : RawRowEntry run next pre)
    (agrees : RegisterAgreementOn live witness t (TraceWitness.finalTraceState run.toTrace)) :
    RegisterAgreementOn live witness t pre ∧
      pre.sail.mem = (TraceWitness.finalTraceState run.toTrace).sail.mem ∧
      pre.jolt_device = (TraceWitness.finalTraceState run.toTrace).jolt_device := by
  unfold RawRowEntry at entry
  rw [finalTraceState_back] at agrees ⊢
  cases lastIs : run.rows.back? with
  | none =>
    simp only [lastIs, Option.map_none, Option.getD_none] at entry agrees ⊢
    rw [entry.2.2]
    exact ⟨agrees.advance_pc _ _, rfl, rfl⟩
  | some last =>
    simp only [lastIs, Option.map_some, Option.getD_some] at entry agrees ⊢
    split at entry
    · rw [entry.2]
      exact ⟨agrees, rfl, rfl⟩
    · obtain ⟨address, _, _, _, _, same⟩ := entry
      rw [same]
      exact ⟨agrees.advance_pc _ _, rfl, rfl⟩

private theorem append_expansion_row {F : Type} [Field F] {params : WitnessParams}
    (joltField : JoltField F) (witness : WitnessType F params)
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (context : ConstraintContext joltInstance privateInputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
    (run : UntrustedAnswerRun joltInstance privateInputs)
    (first : Fin context.bytecode.size) (done : Nat)
    (state : ExpansionState witness context run first done)
    (unfinished : done < expansionRowCount context.bytecode first)
    (bound : run.rows.size < params.traceLength)
    (step : TraceRow run.bytecode) (answer : BitVec 64)
    (indexIs : step.rowIndex.val = first.val + done)
    (executes : execWithTapeAnswer
      (run.bytecode[step.rowIndex].instruction.withRuntimeAdvice step.runtimeAdvice)
      answer step.preState = .ok RETIRE_SUCCESS step.postState)
    (entry : RawRowEntry run step.rowIndex step.preState)
    (observations : RepresentsPrefix witness {run.toTrace with rows := run.rows.push step})
    (zero : witness.RamAddress ⟨run.rows.size, bound⟩ = 0)
    (registers : ∀ next : run.rows.size + 1 < params.traceLength,
      RegisterAgreementOn (ExpansionLive context.bytecode first (done + 1))
        witness ⟨run.rows.size + 1, next⟩ step.postState) :
    ∃ candidate : UntrustedAnswerRun joltInstance privateInputs,
      candidate.toTrace = {run.toTrace with rows := run.rows.push step} ∧
      (∀ index : Fin candidate.rows.size,
        index.val = run.rows.size → candidate.answers index = answer) ∧
      RunExtends run candidate ∧ candidate.rows.size = run.rows.size + 1 ∧
      ExpansionState witness context candidate first (done + 1) := by
  let candidate := appendUntrustedRow run step answer executes
    (rawEntry_starts entry) (rawEntry_linked entry)
  have bytecodeEq : run.bytecode = context.bytecode :=
    Option.some.inj (run.expands.symm.trans context.expands)
  obtain ⟨_, real, next, pre, slot, nextIs, selected, slotIs, ready⟩ := state.next unfinished
  have rowIs : bytecodeRow context.bytecode slot.val = some run.bytecode[step.rowIndex] := by
    rw [← bytecodeEq, show slot.val = step.rowIndex.val + 1 by omega]
    simp only [bytecodeRow, Array.getElem?_eq_getElem step.rowIndex.isLt, Fin.getElem_fin]
  have atRow : context.bytecode[first.val + done]? = some run.bytecode[step.rowIndex] := by
    rw [← indexIs, ← bytecodeEq]
    simp only [Array.getElem?_eq_getElem step.rowIndex.isLt, Fin.getElem_fin]
  have remaining (more : done + 1 < expansionRowCount context.bytecode first) :=
    expansion_row_remaining joltInstance.program context.bytecode context.expands first state.starts done more _ atRow
  have order := expansion_order_push run.bytecode run.rows first.val done state.retained state.ordered step indexIs
  refine ⟨candidate, rfl, ?_, ?_, ?_, ?_⟩
  · intro index atEnd
    change (if old : index.val < run.rows.size then run.answers ⟨index.val, old⟩ else answer) = answer
    rw [dif_neg (by omega)]
  · exact ⟨rfl, by simp [candidate, appendUntrustedRow]⟩
  · exact Array.size_push step
  · refine {
      represents := observations
      real := ?_
      noEarlierStop := adjacent_push run.rows step (fun current _ => ¬ current.StableStall)
        state.noEarlierStop (state.notStopped unfinished)
      terminationWord := ?_
      starts := state.starts
      done_le := by omega
      retained := by have old := state.retained; change done + 1 ≤ (run.rows.push step).size; simp; omega
      ordered := order.1
      priorBoundary := ?_
      registers := ?_
      next := ?_
      notStopped := ?_ }
    · intro t inside
      change t.val < (run.rows.push step).size at inside
      simp only [Array.size_push] at inside
      by_cases old : t.val < run.rows.size
      · exact state.real t old
      · have same : t = ⟨run.rows.size, bound⟩ := Fin.ext (show t.val = run.rows.size by omega)
        subst t
        exact real
    · intro next noStore address atTermination
      have noEarlierStore : ¬ ∃ i : Fin run.rows.size, run.StoresTerminationAt i := by
        rintro ⟨i, store⟩
        apply noStore
        refine ⟨⟨i.val, by change i.val < (run.rows.push step).size; simpa only [Array.size_push] using Nat.lt_succ_of_lt i.isLt⟩, ?_⟩
        change (fun row : TraceRow run.bytecode =>
          match (run.bytecode[row.rowIndex.val]'row.rowIndex.isLt).instruction with
          | .SD base _ imm => TouchesTermination row.preState.jolt_device
              (sourceValue base row.preState + imm)
          | _ => False) (run.rows.push step)[i.val]
        rw [Array.getElem_push_lt i.isLt]
        exact store
      have nextBound : run.rows.size + 1 < params.traceLength := by
        simpa only [candidate, appendUntrustedRow, Array.size_push] using next
      have unchanged := ramVal_succ_of_address_zero (two_pow_127_lt_char joltField)
        context equations address ⟨run.rows.size, bound⟩ nextBound zero
      simpa only [candidate, appendUntrustedRow, Array.size_push] using
        unchanged.trans (state.terminationWord bound noEarlierStore address atTermination)
    · intro last atEnd
      change last ∈ ((run.rows.push step).extract 0 ((run.rows.push step).size - (done + 1))).back? at atEnd
      rw [order.2] at atEnd
      exact state.priorBoundary last atEnd
    · intro next
      change RegisterAgreementOn _ witness ⟨(run.rows.push step).size, next⟩
        (TraceWitness.finalTraceState {run.toTrace with rows := run.rows.push step})
      rw [finalTraceState_push]
      simpa only [Array.size_push] using registers (by simpa only [candidate, appendUntrustedRow, Array.size_push] using next)
    · intro more
      obtain ⟨nextBound, nextIndex, nextSlot, nextIs, nextSlotIs, chosen, realNext⟩ :=
        interior_progress joltField witness context equations run bytecodeEq step
          ⟨run.rows.size, bound⟩ slot (by omega) selected rowIs (remaining more)
      refine ⟨by simpa only [candidate, appendUntrustedRow, Array.size_push] using nextBound,
        ?_, nextIndex, step.postState, nextSlot, ?_, ?_, ?_, ?_⟩
      · simpa only [candidate, appendUntrustedRow, Array.size_push] using realNext
      · omega
      · simpa only [candidate, appendUntrustedRow, Array.size_push] using chosen
      · omega
      · dsimp only [candidate, appendUntrustedRow]
        simp only [Array.back?_push]
        split
        · exact ⟨nextIs, True.intro⟩
        · rename_i last
          exact False.elim (last (remaining more))
    · intro more last atEnd stalled
      change (run.rows.push step).back? = some last at atEnd
      rw [Array.back?_push] at atEnd
      have same : step = last := Option.some.inj atEnd
      subst last
      exact remaining more stalled.1

/-- Inside an unfinished expansion, the next prepared state is the preceding
row's post-state, with no source-boundary PC preparation in between.
For example, REM's MUL starts in the state left by its preceding assertion. -/
theorem ExpansionState.interior_pre {F : Type} [Field F] {params : WitnessParams}
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    {witness : WitnessType F params} {context : ConstraintContext joltInstance privateInputs params}
    {run : UntrustedAnswerRun joltInstance privateInputs} {first : Fin context.bytecode.size}
    {done : Nat} (state : ExpansionState witness context run first done)
    (positive : 0 < done) (unfinished : done < expansionRowCount context.bytecode first)
    (next : Fin run.bytecode.size) (pre : SailJoltState) (entry : RawRowEntry run next pre) :
    pre = TraceWitness.finalTraceState run.toTrace := by
  have retained := state.retained
  obtain ⟨last, atLast, indexIs⟩ := state.ordered (done - 1) (by omega)
  have back : run.rows.back? = some last := by
    rw [Array.back?_eq_getElem?]
    simpa only [show run.rows.size - done + (done - 1) = run.rows.size - 1 by omega] using atLast
  have bytecodeEq : run.bytecode = context.bytecode :=
    Option.some.inj (run.expands.symm.trans context.expands)
  have atRow : context.bytecode[first.val + (done - 1)]? = some run.bytecode[last.rowIndex] := by
    rw [← indexIs, ← bytecodeEq]
    simp only [Array.getElem?_eq_getElem last.rowIndex.isLt, Fin.getElem_fin]
  have remaining := expansion_row_remaining joltInstance.program context.bytecode context.expands
    first state.starts (done - 1) (by omega) _ atRow
  simp only [RawRowEntry, back] at entry
  have same : pre = last.postState := by
    split at entry
    · exact entry.2
    · rename_i terminal
      exact False.elim (terminal remaining)
  rw [same, finalTraceState_back]
  simp only [back, Option.map_some, Option.getD_some]

/-- One appended row, including its successful execution and the new expansion invariant.
The entry certificate omits advice honesty; runtime advice and tape answers are
constrained to the witness's written value when the row uses them.
For example, REM's first row can initialize its dead quotient temporary with 5. -/
def PlainRowExtension {F : Type} [Field F] {params : WitnessParams}
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (witness : WitnessType F params) (context : ConstraintContext joltInstance privateInputs params)
    (run : UntrustedAnswerRun joltInstance privateInputs) (first : Fin context.bytecode.size)
    (done : Nat) (bound : run.rows.size < params.traceLength) : Prop :=
  ∃ (step : TraceRow run.bytecode) (answer : BitVec 64)
    (candidate : UntrustedAnswerRun joltInstance privateInputs),
    step.rowIndex.val = first.val + done ∧
    RawRowEntry run step.rowIndex step.preState ∧ AllRegistersPresent step.preState.sail ∧
    candidate.toTrace = {run.toTrace with rows := run.rows.push step} ∧
    execWithTapeAnswer
      (run.bytecode[step.rowIndex].instruction.withRuntimeAdvice step.runtimeAdvice)
      answer step.preState = .ok RETIRE_SUCCESS step.postState ∧
    (∀ value ∈ step.someTracerAdvice?,
      witness.RdWriteValue ⟨run.rows.size, bound⟩ = (value.toNat : F)) ∧
    (∀ destination width,
      run.bytecode[step.rowIndex].instruction = .VirtualAdviceLoad destination width →
      witness.RdWriteValue ⟨run.rows.size, bound⟩ = (answer.toNat : F)) ∧
    (∀ index : Fin candidate.rows.size,
      index.val = run.rows.size → candidate.answers index = answer) ∧
    RunExtends run candidate ∧ candidate.rows.size = run.rows.size + 1 ∧
    ExpansionState witness context candidate first (done + 1)

/-- The twelve division arithmetic kinds satisfy the plain-row extension contract
using their live-register step rules, without the remaining-kinds gap.
For example, a REM guard executes with its initialized quotient temporary. -/
theorem arithmetic_plain_row_step {F : Type} [Field F] (joltField : JoltField F)
    {joltInstance : JoltInstance SourceInstruction} {params : WitnessParams}
    {privateInputs : JoltPrivateInputs} (witness : WitnessType F params)
    (context : ConstraintContext joltInstance privateInputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
    (run : UntrustedAnswerRun joltInstance privateInputs)
    (first : Fin context.bytecode.size) (done : Nat)
    (state : ExpansionState witness context run first done)
    (unfinished : done < expansionRowCount context.bytecode first)
    (bound : run.rows.size < params.traceLength)
    (arithmetic : ∀ row ∈ context.bytecode[first.val + done]?, DivisionArithmeticRow row.instruction) :
    PlainRowExtension witness context run first done bound := by
  have bytecodeEq : run.bytecode = context.bytecode :=
    Option.some.inj (run.expands.symm.trans context.expands)
  obtain ⟨_, real, next, pre, slot, indexIs, selected, slotIs, ready⟩ := state.next unfinished
  have atRow : context.bytecode[first.val + done]? = some run.bytecode[next] := by
    rw [← indexIs, ← bytecodeEq]
    simp only [Array.getElem?_eq_getElem next.isLt, Fin.getElem_fin]
  have rowIs : bytecodeRow context.bytecode slot.val = some run.bytecode[next] := by
    rw [show slot.val = next.val + 1 by omega, bytecodeRow]
    simpa only [indexIs] using atRow
  have kind := arithmetic _ atRow
  have live (source : Src) (member : source ∈ ExpansionTempLiveness.readSources run.bytecode[next].instruction) :=
    expansion_sources_live joltInstance.program context.bytecode context.expands first state.starts
      done unfinished _ atRow source member
  have prepared := rawEntry_prepared (show RawRowEntry run next pre from ready) (state.registers bound)
  obtain ⟨post, advice, execution⟩ := arithmetic_execution joltField context equations
    selected rowIs kind prepared.1 live
  let step : TraceRow run.bytecode := ⟨next, advice, pre, post⟩
  obtain ⟨rs1, rs2⟩ := arithmetic_row_observations joltField witness context equations
    run.toTrace step bound slot selected rowIs kind prepared.1 live
  obtain ⟨zero, ramZero⟩ := plain_row_ram joltField witness context equations run.toTrace step
    bound slot selected rowIs kind.plain
  have pc : witness.PC ⟨run.rows.size, bound⟩ =
      TraceWitness.PC params {run.toTrace with rows := run.rows.push step} ⟨run.rows.size, bound⟩ := by
    rw [pc_of_selected_bytecode (two_pow_127_lt_char joltField) context equations
      ⟨run.rows.size, bound⟩ slot selected]
    simp only [TraceWitness.PC, TraceWitness.bytecodePc, Array.size_push, Nat.lt_add_one,
      ↓reduceDIte, Array.getElem_push_eq]
    congr 1
    exact slotIs.trans (congrArg (· + 1) indexIs.symm)
  have represented := representsRows_push witness run.toTrace step state.represents.toRepresentsRows
    bound pc rs1 rs2 (zero.trans ramZero.symm)
  have prefixAgreement := representsPrefix_push joltField witness context equations run.toTrace step
    state.represents bound represented zero (execution.memory.trans prepared.2.1)
      (execution.device.trans prepared.2.2)
  have registers (nextCycle : run.rows.size + 1 < params.traceLength) :
      RegisterAgreementOn (ExpansionLive context.bytecode first (done + 1))
        witness ⟨run.rows.size + 1, nextCycle⟩ step.postState := by
    apply (execution.registers nextCycle).mono
    exact expansionLive_after context.bytecode first done _ atRow
  obtain ⟨candidate, traceEq, answers, extendsRun, size, after⟩ :=
    append_expansion_row joltField witness context equations run first done state unfinished
      bound step 0 indexIs execution.executes ready prefixAgreement zero registers
  refine ⟨step, 0, candidate, indexIs, ready, prepared.1.present, traceEq,
    execution.executes, execution.encoded, ?_, answers, extendsRun, size, after⟩
  intro destination width same
  have impossible := kind
  change run.bytecode[next].instruction = .VirtualAdviceLoad destination width at same
  rw [same] at impossible
  exact False.elim impossible

/-- The plain row kinds outside the twelve division arithmetic kinds.
Their remaining work is to port their Layer 5 rules and supply the same append
invariant; for example, a native AND row belongs to this remaining group. -/
theorem plain_row_step_other {F : Type} [Field F] (joltField : JoltField F)
    {joltInstance : JoltInstance SourceInstruction} {params : WitnessParams}
    {privateInputs : JoltPrivateInputs} (witness : WitnessType F params)
    (context : ConstraintContext joltInstance privateInputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
    (run : UntrustedAnswerRun joltInstance privateInputs)
    (first : Fin context.bytecode.size) (done : Nat)
    (state : ExpansionState witness context run first done)
    (unfinished : done < expansionRowCount context.bytecode first)
    (bound : run.rows.size < params.traceLength)
    (plain : ∀ row ∈ context.bytecode[first.val + done]?, PlainRow row.instruction)
    (other : ∀ row ∈ context.bytecode[first.val + done]?, ¬ DivisionArithmeticRow row.instruction) :
    PlainRowExtension witness context run first done bound := by
  sorry

/-- Append one selected plain row of an unfinished expansion.
For example, REM's advice and guard rows extend a witness-advice run without
assuming honest internal advice or agreement on uninitialized temporaries. -/
theorem plain_row_step {F : Type} [Field F] (joltField : JoltField F)
    {joltInstance : JoltInstance SourceInstruction} {params : WitnessParams}
    {privateInputs : JoltPrivateInputs} (witness : WitnessType F params)
    (context : ConstraintContext joltInstance privateInputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
    (run : UntrustedAnswerRun joltInstance privateInputs)
    (first : Fin context.bytecode.size) (done : Nat)
    (state : ExpansionState witness context run first done)
    (unfinished : done < expansionRowCount context.bytecode first)
    (bound : run.rows.size < params.traceLength)
    (plain : ∀ row ∈ context.bytecode[first.val + done]?, PlainRow row.instruction) :
    PlainRowExtension witness context run first done bound := by
  classical
  by_cases arithmetic : ∀ row ∈ context.bytecode[first.val + done]?, DivisionArithmeticRow row.instruction
  · exact arithmetic_plain_row_step joltField witness context equations run first done state unfinished bound arithmetic
  · apply plain_row_step_other joltField witness context equations run first done state unfinished bound plain
    push_neg at arithmetic
    obtain ⟨row, atRow, other⟩ := arithmetic
    intro same atSame
    have eq : row = same := Option.some.inj (atRow.symm.trans atSame)
    subst same
    exact other

end JoltInstance
