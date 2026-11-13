import JoltConstraints.WholeRun.Basic
import JoltConstraints.program_facts
import JoltConstraints.execution_facts

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail
  LeanRV64D LeanRV64D.Functions

set_option autoImplicit false

noncomputable section

namespace WholeRun

private theorem source_at (image : Rv64ProgramImage SourceInstruction)
    (bytecode : Array JoltInstructionRow) (expanded : expand_program image = some bytecode)
    (accepted : pc_map_ok bytecode = true)
    (source : SourceInstructionRow SourceInstruction) (member : source ∈ image.instructions.toList) :
    rowAt image source.address = some source := by
  have distinct := pc_map_ok_distinct_addresses image bytecode expanded accepted
  obtain ⟨index, inside, atSource⟩ := List.mem_iff_getElem.mp member
  have found : image.instructions.toList.find? (·.address == source.address) = some source := by
    apply List.find?_eq_some_iff_getElem.mpr
    refine ⟨by simp, index, inside, atSource, ?_⟩
    intro other earlier
    simp only [Bool.not_eq_true', beq_eq_false_iff_ne]
    intro same
    have equal := List.inj_on_of_nodup_map distinct (List.getElem_mem (by omega)) member same
    have indices := (List.Nodup.getElem_inj_iff (List.Nodup.of_map _ distinct)).mp
      (equal.trans atSource.symm)
    omega
  simpa only [rowAt, ← Array.find?_toList] using found

private theorem source_segment (image : Rv64ProgramImage SourceInstruction)
    (bytecode : Array JoltInstructionRow) (expanded : expand_program image = some bytecode)
    (accepted : pc_map_ok bytecode = true) (first : Fin bytecode.size)
    (starts : bytecode[first].starts_source = true) :
    ∃ source rows before after,
      rowAt image source.address = some source ∧
      expand_instruction source = some rows ∧
      bytecode.toList = before ++ rows ++ after ∧ first.val = before.length := by
  obtain ⟨source, member, rows, emits, inRows⟩ := expand_program_source_of_row image
    bytecode expanded bytecode[first] (by simp)
  obtain ⟨offset, inside, atRow⟩ := List.mem_iff_getElem.mp inRows
  have zero : offset = 0 := by
    have start := expand_instruction_starts_source source rows emits offset inside
    rw [atRow, starts] at start
    simpa using start.symm
  subst offset
  obtain ⟨chunks, mapped, materialized⟩ := Option.map_eq_some_iff.mp expanded
  obtain ⟨index, bound, atSource⟩ := List.mem_iff_getElem.mp member
  obtain ⟨lengths, steps⟩ := option_mapM_results expand_instruction _ chunks mapped
  have inChunks : index < chunks.length := by omega
  have atRows : chunks[index] = rows := by
    have step := steps index bound inChunks
    rw [atSource, emits] at step
    exact (Option.some.inj step).symm
  let before := (chunks.take index).flatten
  let after := (chunks.drop (index + 1)).flatten
  have splitRows : bytecode.toList = before ++ rows ++ after := by
    rw [← materialized, List.toList_toArray]
    conv_lhs => rw [← List.take_append_drop index chunks, List.drop_eq_getElem_cons inChunks]
    simp only [List.flatten_append, List.flatten_cons, atRows, List.append_assoc, before, after]
  have inBytecode : before.length < bytecode.size := by
    have sizes := congrArg List.length splitRows
    simp only [Array.length_toList, List.length_append] at sizes
    omega
  have atStart : bytecode[before.length] = bytecode[first] := by
    have h : bytecode.toList[before.length]? = some rows[0] := by
      rw [splitRows, List.append_assoc, List.getElem?_append_right (Nat.le_refl _)]
      simp only [Nat.sub_self, List.getElem?_append_left inside, List.getElem?_eq_getElem inside]
    simpa only [Array.getElem?_toList, Array.getElem?_eq_getElem inBytecode,
      Option.some.injEq, atRow] using h
  have firstIndex := expand_program_unique image bytecode expanded accepted
    before.length first.val inBytecode first.isLt
    (congrArg JoltInstructionRow.address atStart)
    (congrArg (fun row => row.virtual_sequence_remaining.getD 0) atStart)
  exact ⟨source, rows, before, after, source_at image bytecode expanded accepted source member,
    emits, splitRows, firstIndex.symm⟩

private theorem segment_row {bytecode : Array JoltInstructionRow}
    {rows before after : List JoltInstructionRow}
    (splitRows : bytecode.toList = before ++ rows ++ after)
    (k : Nat) (inside : k < rows.length) :
    bytecode[before.length + k]? = some rows[k] := by
  rw [← Array.getElem?_toList, splitRows, List.append_assoc,
    List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
    List.getElem?_append_left inside, List.getElem?_eq_getElem inside]

private theorem segment_get {bytecode : Array JoltInstructionRow}
    {rows before after : List JoltInstructionRow}
    (splitRows : bytecode.toList = before ++ rows ++ after)
    (k : Nat) (inside : k < rows.length) (i : Fin bytecode.size)
    (position : i.val = before.length + k) : bytecode[i] = rows[k] := by
  have h := segment_row splitRows k inside
  rw [← position, Array.getElem?_eq_getElem i.isLt] at h
  exact Option.some.inj h

private theorem segment_compressed {bytecode : Array JoltInstructionRow}
    {source : SourceInstructionRow SourceInstruction} {rows before after : List JoltInstructionRow}
    (emits : expand_instruction source = some rows)
    (splitRows : bytecode.toList = before ++ rows ++ after)
    (first : Fin bytecode.size) (position : first.val = before.length) :
    source_is_compressed bytecode first = source.is_compressed := by
  have nonempty := expand_instruction_nonempty source rows emits
  have positive : 0 < rows.length := List.length_pos_iff.mpr nonempty
  have atFirst := segment_get splitRows 0 positive first (by omega)
  have count := expand_instruction_countdown source rows emits 0 positive
  have lastInside : rows.length - 1 < rows.length := by omega
  have atLast := segment_row splitRows (rows.length - 1) lastInside
  unfold source_is_compressed
  rw [atFirst, count]
  simp only [Nat.sub_zero]
  rw [position, atLast, Option.map_some, Option.getD_some,
    expand_instruction_compressed source rows emits _ lastInside]
  simp

private theorem trace_segment {joltInstance : JoltInstance SourceInstruction}
    {inputs : JoltPrivateInputs} (trace : HonestTrace joltInstance inputs)
    (n : Nat) (hn : n < trace.rows.size)
    {source : SourceInstructionRow SourceInstruction} {rows before after : List JoltInstructionRow}
    (emits : expand_instruction source = some rows)
    (splitRows : trace.bytecode.toList = before ++ rows ++ after)
    (position : (trace.rows[n]'hn).rowIndex.val = before.length) :
    ∀ k, k < rows.length → ∃ hk : n + k < trace.rows.size,
      (trace.rows[n + k]'hk).rowIndex.val = before.length + k := by
  intro k
  induction k with
  | zero =>
    intro inside
    exact ⟨by omega, by simpa using position⟩
  | succ k ih =>
    intro inside
    obtain ⟨hk, atK⟩ := ih (by omega)
    have byteAt := segment_get splitRows k (by omega) (trace.rows[n + k]'hk).rowIndex atK
    have remaining : trace.bytecode[(trace.rows[n + k]'hk).rowIndex].virtual_sequence_remaining.getD 0 ≠ 0 := by
      intro zero
      have count := expand_instruction_countdown source rows emits k (by omega)
      rw [← byteAt, zero] at count
      have : (0 : BitVec 16).toNat = 0 := rfl
      omega
    have nextBound : n + k + 1 < trace.rows.size := by
      by_contra noNext
      have lastIndex : trace.rows.size - 1 = n + k := by omega
      have lastAt : trace.rows.back? = some (trace.rows[n + k]'hk) := by
        rw [Array.back?_eq_getElem?, lastIndex, Array.getElem?_eq_getElem hk]
      exact remaining (trace.stops _ lastAt).1
    have linked := trace.linked (n + k) _ _ (Array.getElem?_eq_getElem hk)
      (Array.getElem?_eq_getElem nextBound)
    rw [ite_eq_left remaining] at linked
    exact ⟨by omega, by simpa only [Nat.add_succ] using (by omega :
      (trace.rows[n + k + 1]'nextBound).rowIndex.val = before.length + (k + 1))⟩

/-- Patch the next available advice value into one instruction, for example the
quotient into a VirtualAdvice row of DIV. -/
private def patchHead (values : List (BitVec 64)) : JoltISA.Instr → JoltISA.Instr
  | .VirtualAdvice dst placeholder imm => .VirtualAdvice dst (values.headD placeholder) imm
  | instruction => instruction

private theorem patchAdvice_cons (values : List (BitVec 64))
    (instruction : JoltISA.Instr) (rest : List JoltISA.Instr) :
    patchAdvice values (instruction :: rest) = patchHead values instruction ::
      patchAdvice (if instruction.adviceValue?.isSome then values.tail else values) rest := by
  cases instruction <;> rfl

private theorem patchAdvice_length (values : List (BitVec 64)) (instructions : List JoltISA.Instr) :
    (patchAdvice values instructions).length = instructions.length := by
  induction instructions generalizing values with
  | nil => rfl
  | cons instruction rest ih => rw [patchAdvice_cons]; simp only [List.length_cons, ih]

private theorem patchAdvice_get (values : List (BitVec 64)) (instructions : List JoltISA.Instr)
    (k : Nat) (inside : k < instructions.length) :
    (patchAdvice values instructions)[k]'(by rw [patchAdvice_length]; exact inside) =
      patchHead (values.drop ((instructions.take k).filter (·.adviceValue?.isSome)).length)
        instructions[k] := by
  induction instructions generalizing values k with
  | nil => simp at inside
  | cons instruction rest ih =>
    cases k with
    | zero => simp only [patchAdvice_cons, List.getElem_cons_zero, List.take_zero,
        List.filter_nil, List.length_nil, List.drop_zero]
    | succ k =>
      simp only [patchAdvice_cons, List.getElem_cons_succ, List.take_succ_cons]
      rw [ih _ k (by simp only [List.length_cons] at inside; omega)]
      cases flag : instruction.adviceValue?.isSome <;>
        simp [flag, ← List.drop_one, List.drop_drop, Nat.add_comm]

private theorem patchHead_runtime (values : List (BitVec 64))
    (instruction : JoltISA.Instr) (runtime : instruction.RuntimeAdvice)
    (agrees : (instruction.withRuntimeAdvice runtime).adviceValue? =
      instruction.adviceValue?.map (fun placeholder => values.headD placeholder)) :
    instruction.withRuntimeAdvice runtime = patchHead values instruction := by
  cases instruction <;> simp only [JoltISA.Instr.withRuntimeAdvice, JoltISA.Instr.adviceValue?,
    Option.map_some, patchHead] at agrees ⊢
  exact congrArg (fun v => JoltISA.Instr.VirtualAdvice _ v _) (Option.some.inj agrees)

private theorem segment_start {bytecode : Array JoltInstructionRow}
    (traceRows : Array (TraceRow bytecode)) (base offset : Nat)
    (starts : stepNOfTraceIsStartOfNewExpansion traceRows base = true)
    (later : ∀ k, 0 < k → k ≤ offset →
      stepNOfTraceIsStartOfNewExpansion traceRows (base + k) = false) :
    startOfExpansionContainingStepN traceRows (base + offset) = base := by
  induction offset with
  | zero =>
    cases base with
    | zero => rfl
    | succ base => simp only [startOfExpansionContainingStepN, starts, ite_true]
  | succ offset ih =>
    have noStart := later (offset + 1) (by omega) (by omega)
    rw [Nat.add_succ, startOfExpansionContainingStepN]
    rw [show base + offset + 1 = base + (offset + 1) by omega, noStart]
    exact ih (fun k positive inside => later k positive (by omega))

private theorem segment_advice_count {bytecode : Array JoltInstructionRow}
    (traceRows : Array (TraceRow bytecode)) (base : Nat) (rows : List JoltInstructionRow)
    (inside : base + rows.length ≤ traceRows.size)
    (ordered : ∀ k (hk : k < rows.length),
      bytecode[(traceRows[base + k]'(by omega)).rowIndex] = rows[k])
    (offset : Nat) (bound : offset ≤ rows.length)
    (start : startOfExpansionContainingStepN traceRows (base + offset) = base) :
    adviceStepsBeforeStepN traceRows (base + offset) =
      (((rows.map (·.instruction)).take offset).filter (·.adviceValue?.isSome)).length := by
  unfold adviceStepsBeforeStepN
  simp only [start, Nat.add_sub_cancel_left]
  clear start
  induction offset with
  | zero => rfl
  | succ offset ih =>
    have hk : offset < rows.length := by omega
    have atOffset : stepNOfTraceIsAdvice traceRows (base + offset) =
        rows[offset].instruction.adviceValue?.isSome := by
      simp only [stepNOfTraceIsAdvice, Array.getElem?_eq_getElem (show base + offset < traceRows.size by omega),
        Option.bind_some, ordered offset hk]
    rw [List.range'_concat, List.take_succ_eq_append_getElem (by simpa using hk),
      List.filter_append, List.filter_append, List.length_append, List.length_append,
      List.getElem_map, Nat.one_mul, ih (by omega)]
    simp only [List.filter_cons, List.filter_nil, atOffset]
    split <;> simp_all only [List.length_singleton, List.length_nil]

/-- Every step of a block's segment belongs to the expansion that starts at the
segment's first step. For example, if a nine-row expansion starts at step 10, then
step 14 belongs to the expansion that starts at step 10. -/
private theorem segment_starts {joltInstance : JoltInstance SourceInstruction}
    {inputs : JoltPrivateInputs} (trace : HonestTrace joltInstance inputs)
    (base : Nat) (source : SourceInstructionRow SourceInstruction) (rows : List JoltInstructionRow)
    (emits : expand_instruction source = some rows)
    (inside : base + rows.length ≤ trace.rows.size)
    (ordered : ∀ k (hk : k < rows.length),
      trace.bytecode[(trace.rows[base + k]'(by omega)).rowIndex] = rows[k]) :
    ∀ k, k < rows.length → startOfExpansionContainingStepN trace.rows (base + k) = base := by
  have positive : 0 < rows.length := List.length_pos_iff.mpr
    (expand_instruction_nonempty source rows emits)
  have markers : ∀ k (hk : k < rows.length),
      stepNOfTraceIsStartOfNewExpansion trace.rows (base + k) = (k == 0) := by
    intro k hk
    simp only [stepNOfTraceIsStartOfNewExpansion,
      Array.getElem?_eq_getElem (show base + k < trace.rows.size by omega),
      Option.map_some, Option.getD_some, ordered k hk,
      expand_instruction_starts_source source rows emits k hk]
  intro k hk
  apply segment_start
  · simpa only [Nat.add_zero, beq_self_eq_true] using markers 0 positive
  · intro j hj hjk
    rw [markers j (by omega)]
    exact beq_eq_false_iff_ne.mpr (by omega)

/-- Inside a registered inline's expansion, a step is an inline advice step exactly
when it runs a VirtualAdvice row. For example, the VirtualAdvice steps of a
SECP256K1_MULQ call are its inline advice steps. -/
private theorem inline_flag_in_segment {bytecode : Array JoltInstructionRow}
    (program : Rv64ProgramImage SourceInstruction) (traceRows : Array (TraceRow bytecode))
    (base n : Nat) (bound : base < traceRows.size)
    (start : startOfExpansionContainingStepN traceRows n = base)
    (key : JoltISA.Inlines.InlineKey) (rs1 rs2 rs3 : regidx)
    (inline : program.instructionAt bytecode[(traceRows[base]'bound).rowIndex].address =
      some (.inline key rs1 rs2 rs3)) :
    stepNOfTraceIsInlineAdvice program traceRows n = stepNOfTraceIsAdvice traceRows n := by
  simp only [stepNOfTraceIsInlineAdvice, start, Array.getElem?_eq_getElem bound,
    Option.bind_some, inline, Bool.and_true]

/-- The inline advice steps before a step inside an inline's expansion are those
before the expansion, plus the VirtualAdvice steps of the expansion before that
step. For example, the third VirtualAdvice step of the second SECP256K1_MULQ call,
after a first call with 4 of them, has 6 inline advice steps before it. -/
private theorem segment_inline_count {bytecode : Array JoltInstructionRow}
    (program : Rv64ProgramImage SourceInstruction) (traceRows : Array (TraceRow bytecode))
    (base : Nat) (bound : base < traceRows.size)
    (key : JoltISA.Inlines.InlineKey) (rs1 rs2 rs3 : regidx)
    (inline : program.instructionAt bytecode[(traceRows[base]'bound).rowIndex].address =
      some (.inline key rs1 rs2 rs3)) (k : Nat)
    (start : ∀ j, j < k → startOfExpansionContainingStepN traceRows (base + j) = base) :
    inlineAdviceStepsBeforeStepN program traceRows (base + k) =
      inlineAdviceStepsBeforeStepN program traceRows base +
        ((List.range' base k).filter (stepNOfTraceIsAdvice traceRows)).length := by
  induction k with
  | zero => simp
  | succ k ih =>
    have flag := inline_flag_in_segment program traceRows base (base + k) bound
      (start k (by omega)) key rs1 rs2 rs3 inline
    unfold inlineAdviceStepsBeforeStepN at ih ⊢
    rw [show base + (k + 1) = (base + k) + 1 by omega, List.range_succ, List.filter_append,
      List.length_append, ih (fun j hj => start j (by omega)), List.range'_concat,
      List.filter_append, List.length_append, Nat.one_mul]
    simp only [List.filter_cons, List.filter_nil, flag]
    split <;> simp only [List.length_singleton, List.length_nil] <;> omega

/-- If each step of a block's segment records the advice that `values` gives it,
the patched rows are the rows the trace runs. For example, a DIV block whose
VirtualAdvice step records the quotient runs `patchAdvice [quotient] rows`. -/
private theorem segment_patched {joltInstance : JoltInstance SourceInstruction}
    {inputs : JoltPrivateInputs} (trace : HonestTrace joltInstance inputs)
    (base : Nat) (rows : List JoltInstructionRow)
    (inside : base + rows.length ≤ trace.rows.size)
    (ordered : ∀ k (hk : k < rows.length),
      trace.bytecode[(trace.rows[base + k]'(by omega)).rowIndex] = rows[k])
    (values : List (BitVec 64))
    (agrees : ∀ k (hk : k < rows.length),
      (trace.bytecode[(trace.rows[base + k]'(by omega)).rowIndex].instruction.withRuntimeAdvice
        (trace.rows[base + k]'(by omega)).runtimeAdvice).adviceValue? =
      trace.bytecode[(trace.rows[base + k]'(by omega)).rowIndex].instruction.adviceValue?.map
        (fun placeholder => (values.drop
          (((rows.map (·.instruction)).take k).filter (·.adviceValue?.isSome)).length).headD
            placeholder)) :
    ∀ k (hk : k < rows.length),
      (patchAdvice values (rows.map (·.instruction)))[k]'
            (by rw [patchAdvice_length, List.length_map]; exact hk) =
      trace.bytecode[(trace.rows[base + k]'(by omega)).rowIndex].instruction.withRuntimeAdvice
        (trace.rows[base + k]'(by omega)).runtimeAdvice := by
  intro k hk
  have patched := patchHead_runtime
    (values.drop (((rows.map (·.instruction)).take k).filter (·.adviceValue?.isSome)).length)
    _ (trace.rows[base + k]'(by omega)).runtimeAdvice (agrees k hk)
  have byteEq := congrArg JoltInstructionRow.instruction (ordered k hk)
  rw [patchAdvice_get]
  have mapEq := List.getElem_map (fun row : JoltInstructionRow => row.instruction)
    (l := rows) (i := k) (h := by simpa only [List.length_map] using hk)
  exact (congrArg (patchHead _) mapEq).trans
    (patched.trans (congrArg (patchHead _) byteEq)).symm

/-- A block that is not a registered inline records, at each VirtualAdvice step,
the honest tracer's value for that step, from the state the block starts in.
For example, a DIV block records its quotient. -/
private theorem segment_agrees_plain {joltInstance : JoltInstance SourceInstruction}
    {inputs : JoltPrivateInputs} (trace : HonestTrace joltInstance inputs)
    (base : Nat) (firstBound : base < trace.rows.size)
    (source : SourceInstructionRow SourceInstruction) (rows : List JoltInstructionRow)
    (emits : expand_instruction source = some rows)
    (atSource : rowAt joltInstance.program source.address = some source)
    (inside : base + rows.length ≤ trace.rows.size)
    (ordered : ∀ k (hk : k < rows.length),
      trace.bytecode[(trace.rows[base + k]'(by omega)).rowIndex] = rows[k])
    (plain : ∀ key rs1 rs2 rs3, source.instruction ≠ .inline key rs1 rs2 rs3) :
    ∀ k (hk : k < rows.length),
      (trace.bytecode[(trace.rows[base + k]'(by omega)).rowIndex].instruction.withRuntimeAdvice
        (trace.rows[base + k]'(by omega)).runtimeAdvice).adviceValue? =
      trace.bytecode[(trace.rows[base + k]'(by omega)).rowIndex].instruction.adviceValue?.map
        (fun placeholder => ((source.instruction.honestTracerAdvice
          (trace.rows[base]'firstBound).preState).drop
          (((rows.map (·.instruction)).take k).filter (·.adviceValue?.isSome)).length).headD
            placeholder) := by
  have positive : 0 < rows.length := List.length_pos_iff.mpr
    (expand_instruction_nonempty source rows emits)
  have firstAddress : trace.bytecode[(trace.rows[base]'firstBound).rowIndex].address = source.address := by
    have eq := congrArg JoltInstructionRow.address (ordered 0 positive)
    simpa only [Nat.add_zero, expand_instruction_address source rows emits _
      (List.getElem_mem positive)] using eq
  have instructionAt : joltInstance.program.instructionAt source.address = some source.instruction := by
    simpa only [Rv64ProgramImage.instructionAt, rowAt, Option.map_some] using
      congrArg (Option.map (·.instruction)) atSource
  intro k hk
  have start := segment_starts trace base source rows emits inside ordered k hk
  have counter := segment_advice_count trace.rows base rows inside ordered k (by omega) start
  have honest := trace.advice_from_honest_tracer ⟨base + k, by omega⟩
  change (trace.bytecode[(trace.rows[base + k]'(by omega)).rowIndex].instruction.withRuntimeAdvice
    (trace.rows[base + k]'(by omega)).runtimeAdvice).adviceValue? = _ at honest
  cases flag : trace.bytecode[(trace.rows[base + k]'(by omega)).rowIndex].instruction.adviceValue? with
  | none =>
    simpa only [honestTracerAdviceAtStepN,
      Array.getElem?_eq_getElem (show base + k < trace.rows.size by omega), bind, Option.bind,
      flag, Option.map_none] using honest
  | some placeholder =>
    simp only [honestTracerAdviceAtStepN,
      Array.getElem?_eq_getElem (show base + k < trace.rows.size by omega), bind, Option.bind,
      pure, flag, start, Array.getElem?_eq_getElem firstBound, firstAddress, instructionAt,
      counter] at honest
    simpa only [Option.map_some, List.headD_eq_head?_getD, List.head?_drop] using honest

/-- The advice words a registered inline's block takes: the call's VirtualAdvice
steps take the inline advice words in order, from the first one no earlier inline
call used. A word missing from `inline_advice` reads as 0, as in
`honestTracerAdviceAtStepN`. There is one word per row of the expansion, which is at
least one per VirtualAdvice row. For example, a SECP256K1_MULQ call after a first
SECP256K1_MULQ call, which has 4 VirtualAdvice rows, takes words 4, 5, and so on. -/
def inlineCallAdvice (program : Rv64ProgramImage SourceInstruction)
    (inputs : JoltPrivateInputs) {bytecode : Array JoltInstructionRow}
    (traceRows : Array (TraceRow bytecode)) (base length : Nat) : List (BitVec 64) :=
  (List.range length).map fun j =>
    inputs.inline_advice[inlineAdviceStepsBeforeStepN program traceRows base + j]?.getD 0

/-- A registered inline's block records, at each VirtualAdvice step, the next word of
the private input `inline_advice` (`inlineCallAdvice`). For example, the first
VirtualAdvice step of the first SECP256K1_MULQ call records word 0. -/
private theorem segment_agrees_inline {joltInstance : JoltInstance SourceInstruction}
    {inputs : JoltPrivateInputs} (trace : HonestTrace joltInstance inputs)
    (base : Nat) (firstBound : base < trace.rows.size)
    (source : SourceInstructionRow SourceInstruction) (rows : List JoltInstructionRow)
    (emits : expand_instruction source = some rows)
    (atSource : rowAt joltInstance.program source.address = some source)
    (inside : base + rows.length ≤ trace.rows.size)
    (ordered : ∀ k (hk : k < rows.length),
      trace.bytecode[(trace.rows[base + k]'(by omega)).rowIndex] = rows[k])
    (key : JoltISA.Inlines.InlineKey) (rs1 rs2 rs3 : regidx)
    (inline : source.instruction = .inline key rs1 rs2 rs3) :
    ∀ k (hk : k < rows.length),
      (trace.bytecode[(trace.rows[base + k]'(by omega)).rowIndex].instruction.withRuntimeAdvice
        (trace.rows[base + k]'(by omega)).runtimeAdvice).adviceValue? =
      trace.bytecode[(trace.rows[base + k]'(by omega)).rowIndex].instruction.adviceValue?.map
        (fun placeholder => ((inlineCallAdvice joltInstance.program inputs trace.rows base
          rows.length).drop
          (((rows.map (·.instruction)).take k).filter (·.adviceValue?.isSome)).length).headD
            placeholder) := by
  have positive : 0 < rows.length := List.length_pos_iff.mpr
    (expand_instruction_nonempty source rows emits)
  have firstAddress : trace.bytecode[(trace.rows[base]'firstBound).rowIndex].address = source.address := by
    have eq := congrArg JoltInstructionRow.address (ordered 0 positive)
    simpa only [Nat.add_zero, expand_instruction_address source rows emits _
      (List.getElem_mem positive)] using eq
  have instructionAt : joltInstance.program.instructionAt source.address = some source.instruction := by
    simpa only [Rv64ProgramImage.instructionAt, rowAt, Option.map_some] using
      congrArg (Option.map (·.instruction)) atSource
  have inlineAt : joltInstance.program.instructionAt
      trace.bytecode[(trace.rows[base]'firstBound).rowIndex].address =
        some (.inline key rs1 rs2 rs3) := by
    rw [firstAddress, instructionAt, inline]
  intro k hk
  have start := segment_starts trace base source rows emits inside ordered k hk
  have counter := segment_advice_count trace.rows base rows inside ordered k (by omega) start
  have inlineCount := segment_inline_count joltInstance.program trace.rows base firstBound
    key rs1 rs2 rs3 inlineAt k
    (fun j hj => segment_starts trace base source rows emits inside ordered j (by omega))
  have priorAdvice : adviceStepsBeforeStepN trace.rows (base + k) =
      ((List.range' base k).filter (stepNOfTraceIsAdvice trace.rows)).length := by
    unfold adviceStepsBeforeStepN
    simp only [start, Nat.add_sub_cancel_left]
  rw [← priorAdvice, counter] at inlineCount
  have short : (((rows.map (·.instruction)).take k).filter (·.adviceValue?.isSome)).length <
      rows.length :=
    Nat.lt_of_le_of_lt ((List.length_filter_le _ _).trans (by simp)) hk
  have honest := trace.advice_from_honest_tracer ⟨base + k, by omega⟩
  change (trace.bytecode[(trace.rows[base + k]'(by omega)).rowIndex].instruction.withRuntimeAdvice
    (trace.rows[base + k]'(by omega)).runtimeAdvice).adviceValue? = _ at honest
  cases flag : trace.bytecode[(trace.rows[base + k]'(by omega)).rowIndex].instruction.adviceValue? with
  | none =>
    simpa only [honestTracerAdviceAtStepN,
      Array.getElem?_eq_getElem (show base + k < trace.rows.size by omega), bind, Option.bind,
      flag, Option.map_none] using honest
  | some placeholder =>
    simp only [honestTracerAdviceAtStepN,
      Array.getElem?_eq_getElem (show base + k < trace.rows.size by omega), bind, Option.bind,
      pure, flag, start, Array.getElem?_eq_getElem firstBound, firstAddress, instructionAt,
      inline, inlineCount] at honest
    simpa only [Option.map_some, List.headD_eq_head?_getD, List.head?_drop, inlineCallAdvice,
      List.getElem?_map, List.getElem?_range short, Option.map_some, Option.getD_some]
      using honest

private theorem exec_seq (instructions : List JoltISA.Instr) (states : Nat → SailJoltState)
    (runs : ∀ k (hk : k < instructions.length),
      JoltISA.execInstr instructions[k] (states k) = .ok RETIRE_SUCCESS (states (k + 1))) :
    JoltISA.execProgram (JoltISA.Program.seq instructions) (states 0) =
      .ok RETIRE_SUCCESS (states instructions.length) := by
  induction instructions generalizing states with
  | nil => rfl
  | cons instruction rest ih =>
    have first := runs 0 (by simp)
    have tail := ih (fun k => states (k + 1)) (by
      intro k hk
      have step := runs (k + 1) (by simp only [List.length_cons]; omega)
      change JoltISA.execInstr rest[k] (states (k + 1)) =
        .ok RETIRE_SUCCESS (states ((k + 1) + 1)) at step
      exact step)
    exact (JoltISA.execProgram_instr_run_retire instruction (JoltISA.Program.seq rest)
      (states 0) (states 1) first).trans tail

private theorem segment_exec {joltInstance : JoltInstance SourceInstruction}
    {inputs : JoltPrivateInputs} (trace : HonestTrace joltInstance inputs)
    (base : Nat) (firstBound : base < trace.rows.size)
    (source : SourceInstructionRow SourceInstruction) (rows : List JoltInstructionRow)
    (emits : expand_instruction source = some rows)
    (inside : base + rows.length ≤ trace.rows.size)
    (ordered : ∀ k (hk : k < rows.length),
      trace.bytecode[(trace.rows[base + k]'(by omega)).rowIndex] = rows[k])
    (lastBound : base + rows.length - 1 < trace.rows.size) (values : List (BitVec 64))
    (patched : ∀ k (hk : k < rows.length),
      (patchAdvice values (rows.map (·.instruction)))[k]'
            (by rw [patchAdvice_length, List.length_map]; exact hk) =
      trace.bytecode[(trace.rows[base + k]'(by omega)).rowIndex].instruction.withRuntimeAdvice
        (trace.rows[base + k]'(by omega)).runtimeAdvice) :
    JoltISA.execProgram (JoltISA.Program.seq
      (patchAdvice values (rows.map (·.instruction)))) (trace.rows[base]'firstBound).preState =
      .ok RETIRE_SUCCESS (trace.rows[base + rows.length - 1]'lastBound).postState := by
  have positive : 0 < rows.length := List.length_pos_iff.mpr
    (expand_instruction_nonempty source rows emits)
  let instructions := patchAdvice values (rows.map (·.instruction))
  have sizes : instructions.length = rows.length := by
    simp only [instructions, patchAdvice_length, List.length_map]
  let states (k : Nat) : SailJoltState := if h : k < rows.length then
    (trace.rows[base + k]'(by omega)).preState
    else (trace.rows[base + rows.length - 1]'lastBound).postState
  have runs : ∀ k (hk : k < instructions.length),
      JoltISA.execInstr instructions[k] (states k) = .ok RETIRE_SUCCESS (states (k + 1)) := by
    intro k hk
    have kr : k < rows.length := by omega
    have currentBound : base + k < trace.rows.size := by omega
    have instructionEq := patched k kr
    change instructions[k] = _ at instructionEq
    have stateAt : states k = (trace.rows[base + k]'currentBound).preState := by
      simp only [states, dite_eq_left kr]
    have stateNext : states (k + 1) = (trace.rows[base + k]'currentBound).postState := by
      by_cases more : k + 1 < rows.length
      · have nextBound : base + k + 1 < trace.rows.size := by omega
        have remaining : trace.bytecode[(trace.rows[base + k]'currentBound).rowIndex].virtual_sequence_remaining.getD 0 ≠ 0 := by
          intro zero
          have count := expand_instruction_countdown source rows emits k kr
          rw [← ordered k kr, zero] at count
          have : (0 : BitVec 16).toNat = 0 := rfl
          omega
        have linked := trace.linked (base + k) _ _ (Array.getElem?_eq_getElem currentBound)
          (Array.getElem?_eq_getElem nextBound)
        rw [ite_eq_left remaining] at linked
        simpa only [states, dite_eq_left more, Nat.add_succ] using linked.2
      · have lastIndex : base + k = base + rows.length - 1 := by omega
        simp only [states, dite_eq_right more]
        simp only [lastIndex]
    rw [instructionEq, stateAt, stateNext]
    exact trace.executes _ (Array.getElem_mem currentBound)
  have executed := exec_seq instructions states runs
  simpa only [sizes, states, dite_eq_left positive, Nat.add_zero,
    dite_eq_right (Nat.lt_irrefl rows.length)] using executed

/-- A complete block at trace step `base`, with `stop` the first excluded step.
For example, a nine-row expansion at step 10 has `stop = 19`. -/
private structure TracedBlock (trace : Trace) (program : Rv64ProgramImage SourceInstruction)
    (base : Nat) (pre : SailJoltState) where
  block : Block
  stop : Nat
  advances : base < stop
  within : stop ≤ trace.rows.size
  pre_eq : block.pre = pre
  runs : block.Runs program
  first : block.FirstRowAt trace base
  post_eq : block.post = (trace.rows[stop - 1]'(by omega)).postState
  finishes : trace.bytecode[(trace.rows[stop - 1]'(by omega)).rowIndex].virtual_sequence_remaining.getD 0 = 0
  address : trace.bytecode[(trace.rows[stop - 1]'(by omega)).rowIndex].address = block.row.address

/-- **An inline call in an honest trace.** If a source expansion starts at step `base` and
its source row is a registered inline, then that row's expansion rows, patched in order with
the call's inline advice words (`inlineCallAdvice`), run from the state before step `base`
to the state after the call's last step.
For example, a SECP256K1_MULQ call that starts at step 100 runs its 186 rows, with its four
VirtualAdvice rows taking the next four words of `inline_advice`, from the state before step
100 to the state after step 285. -/
theorem HonestTrace.inline_call_exec {joltInstance : JoltInstance SourceInstruction}
    {inputs : JoltPrivateInputs} (trace : HonestTrace joltInstance inputs)
    (base : Nat) (hbase : base < trace.rows.size)
    (starts : trace.bytecode[(trace.rows[base]'hbase).rowIndex].starts_source = true) :
    ∃ source rows, rowAt joltInstance.program source.address = some source ∧
      expand_instruction source = some rows ∧
      trace.bytecode[(trace.rows[base]'hbase).rowIndex].address = source.address ∧
      ∃ lastBound : base + rows.length - 1 < trace.rows.size,
        ∀ key rs1 rs2 rs3, source.instruction = .inline key rs1 rs2 rs3 →
          JoltISA.execProgram (JoltISA.Program.seq
            (patchAdvice (inlineCallAdvice joltInstance.program inputs trace.rows base rows.length)
              (rows.map (·.instruction)))) (trace.rows[base]'hbase).preState =
            .ok RETIRE_SUCCESS (trace.rows[base + rows.length - 1]'lastBound).postState := by
  have accepted := accepted_pc_map_ok joltInstance trace.bytecode trace.expands trace.accepted
  obtain ⟨source, rows, before, after, atSource, emits, splitRows, position⟩ :=
    source_segment joltInstance.program trace.bytecode trace.expands accepted
      (trace.rows[base]'hbase).rowIndex starts
  have positive : 0 < rows.length := List.length_pos_iff.mpr
    (expand_instruction_nonempty source rows emits)
  have orderedIndices := trace_segment trace base hbase emits splitRows position
  have inside : base + rows.length ≤ trace.rows.size := by
    obtain ⟨bound, _⟩ := orderedIndices (rows.length - 1) (by omega)
    omega
  have ordered : ∀ k (hk : k < rows.length),
      trace.bytecode[(trace.rows[base + k]'(by omega)).rowIndex] = rows[k] := by
    intro k hk
    obtain ⟨bound, atK⟩ := orderedIndices k hk
    exact segment_get splitRows k hk _ atK
  have firstAddress : trace.bytecode[(trace.rows[base]'hbase).rowIndex].address = source.address := by
    have eq := congrArg JoltInstructionRow.address (ordered 0 positive)
    simpa only [Nat.add_zero, expand_instruction_address source rows emits _
      (List.getElem_mem positive)] using eq
  have lastBound : base + rows.length - 1 < trace.rows.size := by omega
  refine ⟨source, rows, atSource, emits, firstAddress, lastBound, ?_⟩
  intro key rs1 rs2 rs3 isInline
  let values := inlineCallAdvice joltInstance.program inputs trace.rows base rows.length
  exact segment_exec trace base hbase source rows emits inside ordered lastBound
    values (segment_patched trace base rows inside ordered values
      (segment_agrees_inline trace base hbase source rows emits atSource inside ordered
        key rs1 rs2 rs3 isInline))

private theorem block_at {joltInstance : JoltInstance SourceInstruction}
    {inputs : JoltPrivateInputs} (trace : HonestTrace joltInstance inputs)
    (base : Nat) (hbase : base < trace.rows.size) (pre : SailJoltState)
    (starts : trace.bytecode[(trace.rows[base]'hbase).rowIndex].starts_source = true)
    (continues : pre.sail.regs.get? Register.nextPC =
      some trace.bytecode[(trace.rows[base]'hbase).rowIndex].address)
    (prepared : (trace.rows[base]'hbase).preState =
      advance_pc trace.bytecode[(trace.rows[base]'hbase).rowIndex].address
        (source_is_compressed trace.bytecode (trace.rows[base]'hbase).rowIndex) pre) :
    Nonempty (TracedBlock trace joltInstance.program base pre) := by
  have accepted := accepted_pc_map_ok joltInstance trace.bytecode trace.expands trace.accepted
  obtain ⟨source, rows, before, after, atSource, emits, splitRows, position⟩ :=
    source_segment joltInstance.program trace.bytecode trace.expands accepted
      (trace.rows[base]'hbase).rowIndex starts
  have positive : 0 < rows.length := List.length_pos_iff.mpr
    (expand_instruction_nonempty source rows emits)
  have orderedIndices := trace_segment trace base hbase emits splitRows position
  have inside : base + rows.length ≤ trace.rows.size := by
    obtain ⟨bound, _⟩ := orderedIndices (rows.length - 1) (by omega)
    omega
  have ordered : ∀ k (hk : k < rows.length),
      trace.bytecode[(trace.rows[base + k]'(by omega)).rowIndex] = rows[k] := by
    intro k hk
    obtain ⟨bound, atK⟩ := orderedIndices k hk
    exact segment_get splitRows k hk _ atK
  have firstAddress : trace.bytecode[(trace.rows[base]'hbase).rowIndex].address = source.address := by
    have eq := congrArg JoltInstructionRow.address (ordered 0 positive)
    simpa only [Nat.add_zero, expand_instruction_address source rows emits _
      (List.getElem_mem positive)] using eq
  have compressed := segment_compressed emits splitRows (trace.rows[base]'hbase).rowIndex position
  have lastBound : base + rows.length - 1 < trace.rows.size := by omega
  let block : Block := ⟨source, pre, (trace.rows[base + rows.length - 1]'lastBound).postState⟩
  have startEq : block.start = (trace.rows[base]'hbase).preState := by
    rw [prepared, firstAddress, compressed]
    rfl
  have runs : block.Runs joltInstance.program := by
    refine ⟨atSource, ?_, ?_⟩
    · simpa only [block, firstAddress] using continues
    · by_cases inline : ∃ key rs1 rs2 rs3, source.instruction = .inline key rs1 rs2 rs3
      · obtain ⟨key, rs1, rs2, rs3, isInline⟩ := inline
        let values := inlineCallAdvice joltInstance.program inputs trace.rows base rows.length
        refine ⟨values, patchAdvice values (rows.map (·.instruction)),
          Or.inl ⟨key, rs1, rs2, rs3, isInline⟩, ?_, ?_⟩
        · simp only [block, emits, Option.map_some]
        · rw [startEq]
          exact segment_exec trace base hbase source rows emits inside ordered lastBound
            values (segment_patched trace base rows inside ordered values
              (segment_agrees_inline trace base hbase source rows emits atSource inside ordered
                key rs1 rs2 rs3 isInline))
      · have plain : ∀ key rs1 rs2 rs3, source.instruction ≠ .inline key rs1 rs2 rs3 :=
          fun key rs1 rs2 rs3 isInline => inline ⟨key, rs1, rs2, rs3, isInline⟩
        let values := source.instruction.honestTracerAdvice (trace.rows[base]'hbase).preState
        refine ⟨values, patchAdvice values (rows.map (·.instruction)), Or.inr ?_, ?_, ?_⟩
        · simp only [values, block, startEq]
        · simp only [block, emits, Option.map_some]
        · rw [startEq]
          exact segment_exec trace base hbase source rows emits inside ordered lastBound
            values (segment_patched trace base rows inside ordered values
              (segment_agrees_plain trace base hbase source rows emits atSource inside ordered
                plain))
  have lastInside : rows.length - 1 < rows.length := by omega
  have lastIndex : base + (rows.length - 1) = base + rows.length - 1 := by omega
  refine ⟨⟨block, base + rows.length, by omega, inside, rfl, runs, ?_, rfl, ?_, ?_⟩⟩
  · refine ⟨hbase, startEq, rows, emits, ?_⟩
    simpa only [List.head?_eq_getElem?, List.getElem?_eq_getElem positive, Nat.add_zero]
      using congrArg some (ordered 0 positive).symm
  · have count := expand_instruction_countdown source rows emits (rows.length - 1) lastInside
    have byteEq := ordered (rows.length - 1) lastInside
    simp only [lastIndex] at byteEq
    rw [byteEq]
    apply BitVec.eq_of_toNat_eq
    change (rows[rows.length - 1].virtual_sequence_remaining.getD 0).toNat = 0
    simpa only [Nat.sub_self] using count
  · have address := expand_instruction_address source rows emits rows[rows.length - 1]
      (List.getElem_mem lastInside)
    have byteEq := ordered (rows.length - 1) lastInside
    simp only [lastIndex] at byteEq
    simpa only [byteEq, block] using address

private theorem blocks_suffix {joltInstance : JoltInstance SourceInstruction}
    {inputs : JoltPrivateInputs} (trace : HonestTrace joltInstance inputs)
    (base : Nat) (hbase : base < trace.rows.size) (pre : SailJoltState)
    (starts : trace.bytecode[(trace.rows[base]'hbase).rowIndex].starts_source = true)
    (continues : pre.sail.regs.get? Register.nextPC =
      some trace.bytecode[(trace.rows[base]'hbase).rowIndex].address)
    (prepared : (trace.rows[base]'hbase).preState =
      advance_pc trace.bytecode[(trace.rows[base]'hbase).rowIndex].address
        (source_is_compressed trace.bytecode (trace.rows[base]'hbase).rowIndex) pre) :
    ∃ bs : List Block,
      bs ≠ [] ∧
      (∀ b ∈ bs, b.Runs joltInstance.program) ∧
      bs.head?.map (·.pre) = some pre ∧
      bs.IsChain (fun b c => b.post = c.pre) ∧
      bs.getLast?.map (·.post) = trace.rows.back?.map (·.postState) ∧
      (∀ b ∈ bs.getLast?, b.post.sail.regs.get? Register.nextPC = some b.row.address) ∧
      ∀ b ∈ bs, ∃ k, b.FirstRowAt trace.toTrace k := by
  obtain ⟨segment⟩ := block_at trace base hbase pre starts continues prepared
  have lastBound : segment.stop - 1 < trace.rows.size := by
    have := segment.advances
    have := segment.within
    omega
  by_cases finished : segment.stop = trace.rows.size
  · have lastAt : trace.rows.back? = some (trace.rows[segment.stop - 1]'lastBound) := by
      simp only [Array.back?_eq_getElem?, ← finished, Array.getElem?_eq_getElem lastBound]
    have stalled := (trace.stops _ lastAt).2.1
    rw [segment.address, ← segment.post_eq] at stalled
    refine ⟨[segment.block], by simp, ?_, ?_, by simp, ?_, ?_, ?_⟩
    · intro b hb
      simpa only [List.mem_singleton.mp hb] using segment.runs
    · simp only [List.head?_cons, Option.map_some, segment.pre_eq]
    · simp only [List.getLast?_singleton, Option.map_some, lastAt, segment.post_eq]
    · intro b hb
      have eq : b = segment.block := by simpa only [List.getLast?_singleton, Option.mem_def,
        Option.some.injEq] using hb.symm
      exact eq ▸ stalled
    · intro b hb
      exact ⟨base, List.mem_singleton.mp hb ▸ segment.first⟩
  · have nextBound : segment.stop < trace.rows.size := by
      have := segment.within
      omega
    have nextIndex : segment.stop - 1 + 1 = segment.stop := by
      have := segment.advances
      omega
    have linked := trace.linked (segment.stop - 1) _ _
      (Array.getElem?_eq_getElem lastBound)
      (by simpa only [nextIndex] using Array.getElem?_eq_getElem nextBound)
    simp only [segment.finishes, ne_self_iff_false, ite_false] at linked
    obtain ⟨address, nextPC, nextAddress, nextStarts, nextPrepared⟩ := linked
    obtain ⟨bs, nonempty, runs, first, chain, last, stalls, traced⟩ :=
      blocks_suffix trace segment.stop nextBound segment.block.post nextStarts
        (by simpa only [segment.post_eq, nextAddress] using nextPC)
        (by simpa only [segment.post_eq, nextAddress] using nextPrepared)
    refine ⟨segment.block :: bs, by simp, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact segment.runs
      · exact runs b hb
    · simp only [List.head?_cons, Option.map_some, segment.pre_eq]
    · apply List.isChain_cons.mpr
      refine ⟨?_, chain⟩
      intro b hb
      rw [Option.mem_def] at hb
      rw [hb, Option.map_some, Option.some.injEq] at first
      exact first.symm
    · simpa only [List.getLast?_cons_of_ne_nil nonempty] using last
    · simpa only [List.getLast?_cons_of_ne_nil nonempty] using stalls
    · intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact ⟨base, segment.first⟩
      · exact traced b hb
termination_by trace.rows.size - base
decreasing_by
  have := segment.advances
  omega

private theorem initial_nextPC {joltInstance : JoltInstance SourceInstruction}
    {inputs : JoltPrivateInputs} (trace : HonestTrace joltInstance inputs) :
    trace.initialState.sail.regs.get? Register.nextPC = some joltInstance.program.entry_address := by
  have built := trace.initialized
  unfold JoltInstance.initial_state at built
  cases layout : joltInstance.memory_layout with
  | none => simp only [layout, bind, Option.bind] at built; cases built
  | some value =>
    simp only [layout, bind, Option.bind] at built
    split_ifs at built
    have stateEq := Option.some.inj built
    rw [← stateEq]
    exact init_state_register _ _ _ _ _ Register.nextPC

/-- Every honest trace is a nonempty chain of whole source-instruction blocks.
Each block runs its image row with the honest advice, the first starts at the
initial pre-state, and the last leaves the trace's final state with nextPC at its
own address.
For example, a trace consisting of one repeating self-jump gives one block.
Source boundaries follow Jolt's tracer, `Cpu::tick` in
`jolt/tracer/src/emulator/cpu.rs` at 5def437f.
The stable-stall rule follows `Cpu::tick` and `self_jump_repeats` in PR #2109
(merge commit 0249591a). -/
theorem HonestTrace.blocks {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs) :
    ∃ bs : List Block,
      bs ≠ [] ∧
      (∀ b ∈ bs, b.Runs joltInstance.program) ∧
      bs.head?.map (·.pre) = some trace.initialState ∧
      bs.IsChain (fun b c => b.post = c.pre) ∧
      bs.getLast?.map (·.post) = trace.rows.back?.map (·.postState) ∧
      (∀ b ∈ bs.getLast?, b.post.sail.regs.get? Register.nextPC = some b.row.address) ∧
      ∀ b ∈ bs, ∃ k, b.FirstRowAt trace.toTrace k := by
  obtain ⟨entry, starts, prepared⟩ := trace.starts (trace.rows[0]'trace.nonempty)
    (Array.getElem?_eq_getElem trace.nonempty)
  apply blocks_suffix trace 0 trace.nonempty trace.initialState starts
  · rw [entry]
    exact initial_nextPC trace
  · simpa only [entry] using prepared

end WholeRun
