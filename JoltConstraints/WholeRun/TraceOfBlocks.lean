import JoltConstraints.WholeRun.Blocks
import JoltConstraints.Soundness.Layer5.InlineAdvice
import JoltConstraints.witness_domain

/-!
# An honest trace from a chain of blocks

`HonestTrace.blocks` cuts an honest trace into one block per source instruction. This file
goes the other way: a chain of blocks that run (`Block.Runs`), starts from the instance's
initial state, ends at a block that stalls (`Block.Stalls`) and has no stalling block before
its last, gives an honest trace (`HonestTrace.ofBlocks`). The trace runs the blocks' rows in
order. Its inline advice words (`JoltPrivateInputs.inline_advice`) are the words the inline
blocks' VirtualAdvice rows record (`collectInlineAdvice`).

The construction appends one row at a time. `RunPrefix` collects the fields of
`HonestTrace` that a prefix of the run already meets; `RunPrefix.push` appends one row,
`RunPrefix.appendBlock` appends one block's rows, and `RunPrefix.appendBlocks` appends a
chain of blocks.

Example: an ADDI block followed by a stalling `jal x0, 0` block gives an honest trace of two
rows.
-/

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail
  LeanRV64D LeanRV64D.Functions
open JoltConstraints.Soundness

set_option autoImplicit false

noncomputable section

namespace WholeRun

/-! ## Rows of the image and of the bytecode -/

/-- The row `rowAt` finds is a row of the image, at the address searched for.
Example: `rowAt program 0x80000000` finds the image row at `0x80000000`. -/
theorem rowAt_mem {program : Rv64ProgramImage SourceInstruction} {address : BitVec 64}
    {source : SourceInstructionRow SourceInstruction} (h : rowAt program address = some source) :
    source ∈ program.instructions.toList ∧ source.address = address := by
  unfold rowAt at h
  rw [← Array.find?_toList] at h
  exact ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

/-- `instructionAt` reads the instruction of the row `rowAt` finds.
Example: at the address of an ADDI row, both find the ADDI. -/
theorem instructionAt_of_rowAt {program : Rv64ProgramImage SourceInstruction}
    {address : BitVec 64} {source : SourceInstructionRow SourceInstruction}
    (h : rowAt program address = some source) :
    program.instructionAt address = some source.instruction := by
  unfold Rv64ProgramImage.instructionAt
  unfold rowAt at h
  rw [h]
  rfl

/-- Every image row's expansion is a contiguous segment of the expanded bytecode.
Example: a DIV row's nine rows sit together in the bytecode. -/
theorem segment_of_member (image : Rv64ProgramImage SourceInstruction)
    (bytecode : Array JoltInstructionRow) (expanded : expand_program image = some bytecode)
    (source : SourceInstructionRow SourceInstruction) (member : source ∈ image.instructions.toList) :
    ∃ rows before after, expand_instruction source = some rows ∧
      bytecode.toList = before ++ rows ++ after := by
  obtain ⟨chunks, mapped, materialized⟩ := Option.map_eq_some_iff.mp expanded
  obtain ⟨index, bound, atSource⟩ := List.mem_iff_getElem.mp member
  obtain ⟨lengths, steps⟩ := option_mapM_results expand_instruction _ chunks mapped
  have inChunks : index < chunks.length := by omega
  have emits : expand_instruction source = some chunks[index] := by
    have step := steps index bound inChunks
    rwa [atSource] at step
  refine ⟨chunks[index], (chunks.take index).flatten, (chunks.drop (index + 1)).flatten, emits, ?_⟩
  rw [← materialized, List.toList_toArray]
  conv_lhs => rw [← List.take_append_drop index chunks, List.drop_eq_getElem_cons inChunks]
  simp only [List.flatten_append, List.flatten_cons, List.append_assoc]

/-! ## Runs of a sequence -/

/-- A sequence of rows that retires passes through one state per row.
Example: `[ADDI, ADDI]` that retires from `s` to `s'` passes through the state between the two
rows. -/
theorem exec_seq_states : ∀ (instructions : List JoltISA.Instr) (s s' : SailJoltState),
    JoltISA.execProgram (JoltISA.Program.seq instructions) s = .ok RETIRE_SUCCESS s' →
    ∃ states : Nat → SailJoltState, states 0 = s ∧ states instructions.length = s' ∧
      ∀ k (hk : k < instructions.length),
        JoltISA.execInstr instructions[k] (states k) = .ok RETIRE_SUCCESS (states (k + 1))
  | [], s, s', h => by
    have h' : (EStateM.Result.ok RETIRE_SUCCESS s : EStateM.Result _ _ _) =
        .ok RETIRE_SUCCESS s' := h
    cases h'
    exact ⟨fun _ => s, rfl, rfl, fun k hk => by simp at hk⟩
  | instruction :: rest, s, s', h => by
    obtain ⟨s₁, first, tail⟩ := JoltISA.execProgram_instr_run_retire_inv instruction
      (JoltISA.Program.seq rest) s s' h
    obtain ⟨states, h0, hlast, hsteps⟩ := exec_seq_states rest s₁ s' tail
    refine ⟨fun k => if k = 0 then s else states (k - 1), by simp, ?_, ?_⟩
    · simpa using hlast
    · intro k hk
      cases k with
      | zero =>
        have first' : JoltISA.execInstr instruction s = .ok RETIRE_SUCCESS s₁ := first
        simpa [h0] using first'
      | succ k =>
        simpa using hsteps k (by simp only [List.length_cons] at hk; omega)

/-! ## Runtime advice -/

/-- The runtime advice that turns `instruction` into `target`: `target`'s advice value for a
VirtualAdvice row, nothing for any other row.
Example: for `VirtualAdvice vr40 0 0` and target `VirtualAdvice vr40 7 0`, the advice is `7`. -/
def runtimeFor (instruction target : JoltISA.Instr) : instruction.RuntimeAdvice := by
  cases instruction with
  | VirtualAdvice _ placeholder _ => exact target.adviceValue?.getD placeholder
  | _ => exact ()

/-- `runtimeFor` recovers a patched row: the row with the runtime advice `runtimeFor` gives
is the patched row.
Example: `VirtualAdvice vr40 0 0` patched with `[7]` runs as `VirtualAdvice vr40 7 0`. -/
theorem withRuntimeAdvice_runtimeFor (values : List (BitVec 64)) (instruction : JoltISA.Instr) :
    instruction.withRuntimeAdvice (runtimeFor instruction (patchHead values instruction)) =
      patchHead values instruction := by
  cases instruction <;> rfl

/-! ## Run prefixes -/

/-- How row `next` follows row `current` in a run (`ValidRun.linked`): the next row of the same
source instruction from the same state, or the first row of the source instruction at `nextPC`,
from the state `advance_pc` prepares.
Example: the second row of a DIV follows the first from the state the first left. -/
def RowsLinked {bytecode : Array JoltInstructionRow} (current next : TraceRow bytecode) : Prop :=
  if bytecode[current.rowIndex].virtual_sequence_remaining.getD 0 ≠ 0 then
    next.rowIndex.val = current.rowIndex.val + 1 ∧
    next.preState = current.postState
  else
    ∃ address, current.postState.sail.regs.get? Register.nextPC = some address ∧
      bytecode[next.rowIndex].address = address ∧
      bytecode[next.rowIndex].starts_source ∧
      next.preState = advance_pc address (source_is_compressed bytecode next.rowIndex)
        current.postState

/-- The first row of a run (`ValidRun.starts`): the first row of the source instruction at the
entry address, from the initial state that `advance_pc` prepares.
Example: a run whose entry row is an ADDI starts with that ADDI. -/
def StartsRun (joltInstance : JoltInstance SourceInstruction) (init : SailJoltState)
    {bytecode : Array JoltInstructionRow} (first : TraceRow bytecode) : Prop :=
  bytecode[first.rowIndex].address = joltInstance.program.entry_address ∧
    bytecode[first.rowIndex].starts_source ∧
    first.preState = advance_pc joltInstance.program.entry_address
      (source_is_compressed bytecode first.rowIndex) init

/-- The fields of `HonestTrace` that a prefix of a run from `init` meets: every row retires, the
first row starts the run, each row follows the one before, the rows outside inline calls record
the honest tracer's advice, and no row but the last is a stable stall.
Example: the empty prefix meets every field. -/
structure RunPrefix (joltInstance : JoltInstance SourceInstruction) (init : SailJoltState)
    {bytecode : Array JoltInstructionRow} (rows : Array (TraceRow bytecode)) : Prop where
  executes : ∀ row ∈ rows,
    JoltISA.execInstr (bytecode[row.rowIndex].instruction.withRuntimeAdvice row.runtimeAdvice)
      row.preState = .ok (.Retire_Success ()) row.postState
  starts : ∀ first ∈ rows[0]?, StartsRun joltInstance init first
  linked : ∀ (i : Nat) (current next : TraceRow bytecode),
    rows[i]? = some current → rows[i + 1]? = some next → RowsLinked current next
  builtin : BuiltinAdviceHonest joltInstance.program rows
  runs_until_stop : ∀ (i : Nat) (current next : TraceRow bytecode),
    rows[i]? = some current → rows[i + 1]? = some next → ¬ current.StableStall

/-- The empty prefix.
Example: `RunPrefix joltInstance init #[]`. -/
theorem RunPrefix.empty (joltInstance : JoltInstance SourceInstruction) (init : SailJoltState)
    (bytecode : Array JoltInstructionRow) :
    RunPrefix joltInstance init (#[] : Array (TraceRow bytecode)) where
  executes := by simp
  starts := by simp
  linked := by simp
  builtin := fun n => n.elim0
  runs_until_stop := by simp

/-- **Appending one row.** A row that retires, follows the prefix's last row (or starts the run
when the prefix is empty), comes after a last row that is not a stable stall, and records its
built-in advice outside inline calls, extends the prefix.
Example: pushing an ADD after an ADDI. -/
theorem RunPrefix.push {joltInstance : JoltInstance SourceInstruction} {init : SailJoltState}
    {bytecode : Array JoltInstructionRow} {rows : Array (TraceRow bytecode)}
    (h : RunPrefix joltInstance init rows) (step : TraceRow bytecode)
    (executes : JoltISA.execInstr
      (bytecode[step.rowIndex].instruction.withRuntimeAdvice step.runtimeAdvice)
      step.preState = .ok (.Retire_Success ()) step.postState)
    (first : rows.size = 0 → StartsRun joltInstance init step)
    (link : ∀ last ∈ rows.back?, RowsLinked last step ∧ ¬ last.StableStall)
    (advice : stepNOfTraceIsInlineAdvice joltInstance.program (rows.push step) rows.size = false →
      step.someTracerAdvice? = builtinAdviceAtStepN joltInstance.program (rows.push step) rows.size) :
    RunPrefix joltInstance init (rows.push step) where
  executes := by
    intro row member
    rcases Array.mem_push.mp member with old | rfl
    · exact h.executes row old
    · exact executes
  starts := by
    intro row hrow
    rw [Array.getElem?_push] at hrow
    by_cases empty : 0 = rows.size
    · rw [ite_eq_left_of_eq_true _ _ (eq_true empty)] at hrow
      cases hrow
      exact first empty.symm
    · rw [ite_eq_right_of_eq_false _ _ (eq_false empty)] at hrow
      exact h.starts row hrow
  linked := by
    intro i current next hcur hnext
    rw [Array.getElem?_push] at hcur hnext
    by_cases atEnd : i + 1 = rows.size
    · rw [ite_eq_left_of_eq_true _ _ (eq_true atEnd)] at hnext
      cases hnext
      rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))] at hcur
      have hlast : rows.back? = some current := by
        rw [Array.back?_eq_getElem?, ← atEnd, Nat.add_sub_cancel]
        exact hcur
      exact (link current hlast).1
    · rw [ite_eq_right_of_eq_false _ _ (eq_false atEnd)] at hnext
      have inside : i + 1 < rows.size := by
        by_contra outside
        rw [Array.getElem?_eq_none (by omega)] at hnext
        cases hnext
      rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))] at hcur
      exact h.linked i current next hcur hnext
  builtin := BuiltinAdviceHonest.push joltInstance.program rows step h.builtin advice
  runs_until_stop := by
    intro i current next hcur hnext
    rw [Array.getElem?_push] at hcur hnext
    by_cases atEnd : i + 1 = rows.size
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))] at hcur
      have hlast : rows.back? = some current := by
        rw [Array.back?_eq_getElem?, ← atEnd, Nat.add_sub_cancel]
        exact hcur
      exact (link current hlast).2
    · rw [ite_eq_right_of_eq_false _ _ (eq_false atEnd)] at hnext
      have inside : i + 1 < rows.size := by
        by_contra outside
        rw [Array.getElem?_eq_none (by omega)] at hnext
        cases hnext
      rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))] at hcur
      exact h.runs_until_stop i current next hcur hnext

/-! ## Appending a block -/

/-- A block stalls: its rows leave `nextPC` at the block's own address, and the last row of its
expansion would jump there again if re-run (`JoltInstructionRow.selfJumpRepeats`). Jolt's
tracer stops after such a block.
Example: a `jal x0, 0` block stalls. -/
def Block.Stalls (b : Block) : Prop :=
  b.post.sail.regs.get? Register.nextPC = some b.row.address ∧
    ∀ rows, expand_instruction b.row = some rows →
      ∀ last ∈ rows.getLast?, last.selfJumpRepeats = true

/-- `headD` of a dropped list reads the list at the drop count.
Example: `([1, 2, 3].drop 1).headD 0 = 2`. -/
theorem headD_drop {α : Type} (l : List α) (n : Nat) (d : α) :
    (l.drop n).headD d = l[n]?.getD d := by
  simp [List.headD_eq_head?_getD, List.head?_drop]

/-- Patching a VirtualAdvice row puts the first value in it.
Example: `VirtualAdvice vr40 0 0` patched with `[7]` records `7`. -/
theorem adviceValue?_patchHead (values : List (BitVec 64)) (instruction : JoltISA.Instr)
    (placeholder : BitVec 64) (h : instruction.adviceValue? = some placeholder) :
    (patchHead values instruction).adviceValue? = some (values.headD placeholder) := by
  cases instruction
  case VirtualAdvice dst placeholder' imm =>
    simp only [JoltISA.Instr.adviceValue?, Option.some.injEq] at h
    subst h
    rfl
  all_goals exact absurd h (by intro h'; cases h')

/-- The rows of one block, appended to a run prefix one at a time: after `d` rows, the prefix
holds row `k < d` of the block's expansion at index `rows.size + k`, run from `states k` to
`states (k + 1)`.
Example: after two rows of a DIV block, the prefix ends with the DIV's first two rows. -/
private theorem RunPrefix.appendRows {joltInstance : JoltInstance SourceInstruction}
    {init : SailJoltState} {bytecode : Array JoltInstructionRow}
    {rows : Array (TraceRow bytecode)} (h : RunPrefix joltInstance init rows)
    {b : Block} (atRow : rowAt joltInstance.program b.row.address = some b.row)
    {segment before after : List JoltInstructionRow}
    (emits : expand_instruction b.row = some segment)
    (split : bytecode.toList = before ++ segment ++ after)
    (values : List (BitVec 64))
    (honest : (∃ key rs1 rs2 rs3, b.row.instruction = .inline key rs1 rs2 rs3) ∨
      values = b.row.instruction.honestTracerAdvice b.start)
    (states : Nat → SailJoltState) (state0 : states 0 = b.start)
    (steps : ∀ k (hk : k < segment.length),
      JoltISA.execInstr ((patchAdvice values (segment.map (·.instruction)))[k]'(by
        rw [patchAdvice_length, List.length_map]; exact hk)) (states k) =
        .ok RETIRE_SUCCESS (states (k + 1)))
    (firstRow : rows.size = 0 → b.row.address = joltInstance.program.entry_address ∧
      b.pre = init)
    (link0 : ∀ last ∈ rows.back?, last.postState = b.pre ∧
      b.pre.sail.regs.get? Register.nextPC = some b.row.address ∧
      bytecode[last.rowIndex].virtual_sequence_remaining.getD 0 = 0 ∧ ¬ last.StableStall) :
    ∀ d ≤ segment.length, ∃ rows' : Array (TraceRow bytecode),
      RunPrefix joltInstance init rows' ∧ rows'.size = rows.size + d ∧
      (∀ i < rows.size, rows'[i]? = rows[i]?) ∧
      ∀ k < d, ∃ r, rows'[rows.size + k]? = some r ∧ r.rowIndex.val = before.length + k ∧
        r.preState = states k ∧ r.postState = states (k + 1) := by
  have sizes : bytecode.size = before.length + segment.length + after.length := by
    have := congrArg List.length split
    simpa only [Array.length_toList, List.length_append] using this
  have positive : 0 < segment.length := List.length_pos_iff.mpr
    (expand_instruction_nonempty b.row segment emits)
  intro d
  induction d with
  | zero =>
    intro _
    exact ⟨rows, h, rfl, fun _ _ => rfl, fun k hk => absurd hk (Nat.not_lt_zero k)⟩
  | succ d ih =>
    intro hd
    obtain ⟨rows', h', size', keep', entries'⟩ := ih (by omega)
    have dlt : d < segment.length := by omega
    let idx : Fin bytecode.size := ⟨before.length + d, by omega⟩
    have atIdx : bytecode[idx] = segment[d] := segment_get split d dlt idx rfl
    let count := (((segment.map (·.instruction)).take d).filter (·.adviceValue?.isSome)).length
    let step : TraceRow bytecode :=
      { rowIndex := idx
        runtimeAdvice := runtimeFor bytecode[idx].instruction
          (patchHead (values.drop count) bytecode[idx].instruction)
        preState := states d
        postState := states (d + 1) }
    have patchedAt : (patchAdvice values (segment.map (·.instruction)))[d]'(by
        rw [patchAdvice_length, List.length_map]; exact dlt) =
        patchHead (values.drop count) bytecode[idx].instruction := by
      rw [patchAdvice_get values _ d (by simpa using dlt), atIdx]
      simp only [List.getElem_map, count]
    have runsStep : bytecode[step.rowIndex].instruction.withRuntimeAdvice step.runtimeAdvice =
        patchHead (values.drop count) bytecode[idx].instruction :=
      withRuntimeAdvice_runtimeFor _ _
    -- The pushed array, read inside the block.
    let pushed := rows'.push step
    have pushedAt : ∀ k ≤ d, ∃ r, pushed[rows.size + k]? = some r ∧
        r.rowIndex.val = before.length + k ∧ r.preState = states k := by
      intro k hk
      by_cases last : k = d
      · subst last
        refine ⟨step, ?_, rfl, rfl⟩
        rw [Array.getElem?_push, ite_eq_left_of_eq_true _ _ (eq_true (by omega))]
      · obtain ⟨r, hr, hidx, hpre, -⟩ := entries' k (by omega)
        refine ⟨r, ?_, hidx, hpre⟩
        rw [Array.getElem?_push, ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
        exact hr
    have bytecodeAt : ∀ k (hk : k < segment.length) (r : TraceRow bytecode),
        r.rowIndex.val = before.length + k → bytecode[r.rowIndex] = segment[k] :=
      fun k hk r hr => segment_get split k hk r.rowIndex hr
    have startHere : startOfExpansionContainingStepN pushed (rows.size + d) = rows.size := by
      apply segment_start
      · obtain ⟨r, hr, hidx, -⟩ := pushedAt 0 (Nat.zero_le _)
        simp only [Nat.add_zero] at hr
        simp only [stepNOfTraceIsStartOfNewExpansion, hr, Option.map_some, Option.getD_some,
          bytecodeAt 0 positive r (by simpa using hidx),
          expand_instruction_starts_source b.row segment emits 0 positive, beq_self_eq_true]
      · intro k kpos kle
        obtain ⟨r, hr, hidx, -⟩ := pushedAt k kle
        simp only [stepNOfTraceIsStartOfNewExpansion, hr, Option.map_some, Option.getD_some,
          bytecodeAt k (by omega) r hidx,
          expand_instruction_starts_source b.row segment emits k (by omega)]
        exact beq_eq_false_iff_ne.mpr (by omega)
    obtain ⟨row0, hrow0, hidx0, hpre0⟩ := pushedAt 0 (Nat.zero_le _)
    simp only [Nat.add_zero] at hrow0
    have firstAddress : bytecode[row0.rowIndex].address = b.row.address := by
      rw [bytecodeAt 0 positive row0 (by simpa using hidx0)]
      exact expand_instruction_address b.row segment emits _ (List.getElem_mem positive)
    have instructionHere : joltInstance.program.instructionAt bytecode[row0.rowIndex].address =
        some b.row.instruction := by
      rw [firstAddress]
      exact instructionAt_of_rowAt atRow
    have compressedAt : ∀ i : Fin bytecode.size, i.val = before.length →
        source_is_compressed bytecode i = b.row.is_compressed :=
      fun i hi => segment_compressed emits split i hi
    have stepRuns : JoltISA.execInstr
        (bytecode[step.rowIndex].instruction.withRuntimeAdvice step.runtimeAdvice)
        step.preState = .ok (.Retire_Success ()) step.postState := by
      rw [runsStep, ← patchedAt]
      exact steps d dlt
    have hpush := h'.push step stepRuns ?first ?link ?advice
    case first =>
      intro empty
      have hd0 : d = 0 := by omega
      have hr0 : rows.size = 0 := by omega
      obtain ⟨entry, preInit⟩ := firstRow hr0
      subst hd0
      have hstep0 : bytecode[step.rowIndex] = segment[0] := atIdx
      refine ⟨?_, ?_, ?_⟩
      · rw [hstep0, expand_instruction_address b.row segment emits _ (List.getElem_mem positive),
          entry]
      · rw [hstep0, expand_instruction_starts_source b.row segment emits 0 positive]
        rfl
      · show states 0 = _
        rw [state0, compressedAt step.rowIndex (by simp [step, idx]), ← entry, ← preInit]
        rfl
    case link =>
      intro last hlast
      by_cases hd0 : d = 0
      · subst hd0
        have hback : rows.back? = some last := by
          rw [Array.back?_eq_getElem?, size'] at hlast
          rw [Array.back?_eq_getElem?]
          by_cases hr : rows.size = 0
          · rw [hr] at hlast ⊢
            simp only [Nat.add_zero, Nat.zero_sub] at hlast ⊢
            rw [Array.getElem?_eq_none (by omega)] at hlast
            cases hlast
          · rw [← keep' _ (by omega)]
            simpa using hlast
        obtain ⟨postEq, continues, remaining, notStall⟩ := link0 last hback
        refine ⟨?_, notStall⟩
        unfold RowsLinked
        rw [ite_eq_right_of_eq_false _ _ (eq_false (by simpa using remaining))]
        have hstep0 : bytecode[step.rowIndex] = segment[0] := atIdx
        refine ⟨b.row.address, by rw [postEq]; exact continues, ?_, ?_, ?_⟩
        · rw [hstep0]
          exact expand_instruction_address b.row segment emits _ (List.getElem_mem positive)
        · rw [hstep0, expand_instruction_starts_source b.row segment emits 0 positive]
          rfl
        · show states 0 = _
          rw [state0, compressedAt step.rowIndex (by simp [step, idx]), postEq]
          rfl
      · obtain ⟨r, hr, hidx, -, hpost⟩ := entries' (d - 1) (by omega)
        have hback : rows'.back? = some r := by
          rw [Array.back?_eq_getElem?, size', ← hr]
          congr 1
          omega
        rw [hback] at hlast
        cases hlast
        have hdm : d - 1 < segment.length := by omega
        have remaining : bytecode[last.rowIndex].virtual_sequence_remaining.getD 0 ≠ 0 := by
          intro zero
          have count := expand_instruction_countdown b.row segment emits (d - 1) hdm
          rw [← bytecodeAt (d - 1) hdm last hidx, zero] at count
          have : (0 : BitVec 16).toNat = 0 := rfl
          omega
        refine ⟨?_, fun stall => remaining stall.1⟩
        unfold RowsLinked
        rw [ite_eq_left_of_eq_true _ _ (eq_true remaining)]
        refine ⟨?_, ?_⟩
        · show before.length + d = last.rowIndex.val + 1
          omega
        · show states d = last.postState
          rw [hpost]
          congr 1
          omega
    case advice =>
      intro notInline
      by_cases absent : bytecode[step.rowIndex].instruction.adviceValue? = none
      · have agrees := runtimeAdvice_agrees_of_noAdvice joltInstance.program (rows'.push step)
          ⟨rows'.size, by simp⟩ (by simpa only [Fin.getElem_fin, Array.getElem_push_eq] using absent)
        simpa only [Fin.getElem_fin, Array.getElem_push_eq] using agrees
      · obtain ⟨placeholder, hplace⟩ := Option.ne_none_iff_exists'.mp absent
        have startEq : startOfExpansionContainingStepN pushed rows'.size = rows.size := by
          rw [size']
          exact startHere
        rcases honest with ⟨key, rs1, rs2, rs3, inline⟩ | honestValues
        · exfalso
          have flag : stepNOfTraceIsInlineAdvice joltInstance.program pushed rows'.size = true := by
            simp only [stepNOfTraceIsInlineAdvice, stepNOfTraceIsAdvice, startEq, hrow0,
              Option.bind_some, instructionHere, inline, Bool.and_true]
            simp only [Fin.getElem_fin] at hplace
            simp [pushed, hplace]
          exact absurd flag (by simpa [pushed] using notInline)
        · have hstepAt : pushed[rows'.size]? = some step := by simp [pushed]
          have ordered : ∀ k (hk : k < (segment.take (d + 1)).length),
              bytecode[(pushed[rows.size + k]'(by
                simp only [List.length_take] at hk
                simp only [pushed, Array.size_push, size']
                omega)).rowIndex] = (segment.take (d + 1))[k] := by
            intro k hk
            simp only [List.length_take] at hk
            obtain ⟨r, hr, hidx, -⟩ := pushedAt k (by omega)
            obtain ⟨_, hget⟩ := Array.getElem?_eq_some_iff.mp hr
            subst hget
            rw [List.getElem_take]
            exact bytecodeAt k (by omega) _ hidx
          have hcount : adviceStepsBeforeStepN pushed rows'.size = count := by
            rw [size']
            have := segment_advice_count pushed rows.size (segment.take (d + 1))
              (by simp only [List.length_take, pushed, Array.size_push, size']; omega)
              ordered d (by simp only [List.length_take]; omega) startHere
            rw [this]
            simp only [count, List.map_take, List.take_take]
            congr 3
            omega
          have stepAdvice : step.someTracerAdvice? = some ((values.drop count).headD placeholder) := by
            unfold TraceRow.someTracerAdvice?
            rw [runsStep]
            simp only [Fin.getElem_fin] at hplace
            exact adviceValue?_patchHead _ _ _ hplace
          rw [stepAdvice, headD_drop]
          simp only [Fin.getElem_fin] at hplace
          have hstepAt' : (rows'.push step)[rows'.size]? = some step := hstepAt
          have startEq' : startOfExpansionContainingStepN (rows'.push step) rows'.size =
            rows.size := startEq
          have hrow0' : (rows'.push step)[rows.size]? = some row0 := hrow0
          have hcount' : adviceStepsBeforeStepN (rows'.push step) rows'.size = count := hcount
          simp only [builtinAdviceAtStepN, hstepAt', startEq', hrow0', bind, Option.bind_some,
            instructionHere, hpre0, state0, ← honestValues, hcount']
          rw [show bytecode[step.rowIndex].instruction.adviceValue? = some placeholder from hplace]
          rfl
    refine ⟨pushed, hpush, by simp only [pushed, Array.size_push, size']; omega, ?_, ?_⟩
    · intro i hi
      rw [Array.getElem?_push, ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
      exact keep' i hi
    · intro k hk
      by_cases last : k = d
      · subst last
        exact ⟨step, by rw [← size']; simp [pushed], rfl, rfl, rfl⟩
      · obtain ⟨r, hr, hidx, hpre, hpost⟩ := entries' k (by omega)
        refine ⟨r, ?_, hidx, hpre, hpost⟩
        rw [Array.getElem?_push, ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
        exact hr
/-- A Jolt row's RAM access lies in Jolt's memory map: the address `TraceRow.ram_address` records
is 0 (no access) or at least the layout's lowest address. Jolt's prover sizes its RAM table from
these addresses and rejects a trace with an address below the lowest one.
Example: an SD into the heap lies in the map; an LB in the gap below the advice regions does
not. -/
def AccessInMap (lowest : Nat) (instruction : JoltISA.Instr) (s : SailJoltState) : Prop :=
  ∀ address ∈ TraceWitness.ramAccessAddress instruction s,
    address.toNat = 0 ∨ lowest ≤ address.toNat

/-- Every RAM access of a block's rows lies in Jolt's memory map (`AccessInMap`), for every
advice the block may run with and every sequence of states its rows pass through.
Example: an LD block whose address is in the heap. -/
def Block.AccessesInMap (lowest : Nat) (b : Block) : Prop :=
  ∀ segment, expand_instruction b.row = some segment →
    ∀ (values : List (BitVec 64)) (states : Nat → SailJoltState),
      ((∃ key rs1 rs2 rs3, b.row.instruction = .inline key rs1 rs2 rs3) ∨
        values = b.row.instruction.honestTracerAdvice b.start) →
      states 0 = b.start →
      (∀ k (hk : k < segment.length),
        JoltISA.execInstr ((patchAdvice values (segment.map (·.instruction)))[k]'(by
          rw [patchAdvice_length, List.length_map]; exact hk)) (states k) =
          .ok RETIRE_SUCCESS (states (k + 1))) →
      ∀ k (hk : k < segment.length), AccessInMap lowest segment[k].instruction (states k)

/-- A trace row's recorded RAM address lies in Jolt's memory map.
Example: a row that is not a load or store records no address. -/
def RowInMap {bytecode : Array JoltInstructionRow} (lowest : Nat) (row : TraceRow bytecode) :
    Prop :=
  ∀ address ∈ row.ram_address, address = 0 ∨ lowest ≤ address

/-- **Appending a block.** A block that runs, continues from the prefix's last row (or starts the
run when the prefix is empty), after a last row that is not a stable stall, extends the prefix by
the rows of its expansion. The new last row ends at the block's last state, ends its source
instruction, and is a stable stall exactly when the block stalls.
Example: appending an ADDI block to the empty prefix gives the one-row prefix of the ADDI. -/
theorem RunPrefix.appendBlock {joltInstance : JoltInstance SourceInstruction}
    {init : SailJoltState} {bytecode : Array JoltInstructionRow}
    (expanded : expand_program joltInstance.program = some bytecode)
    {rows : Array (TraceRow bytecode)} (h : RunPrefix joltInstance init rows)
    {b : Block} (runs : b.Runs joltInstance.program)
    (firstRow : rows.size = 0 → b.row.address = joltInstance.program.entry_address ∧
      b.pre = init)
    (link0 : ∀ last ∈ rows.back?, last.postState = b.pre ∧
      bytecode[last.rowIndex].virtual_sequence_remaining.getD 0 = 0 ∧ ¬ last.StableStall) :
    ∃ (rows' : Array (TraceRow bytecode)) (segment : List JoltInstructionRow),
      RunPrefix joltInstance init rows' ∧ expand_instruction b.row = some segment ∧
      rows'.size = rows.size + segment.length ∧
      (∀ i < rows.size, rows'[i]? = rows[i]?) ∧
      (∀ (i : Nat) (r : TraceRow bytecode), rows.size ≤ i → rows'[i]? = some r →
        bytecode[r.rowIndex] ∈ segment ∧
        ∀ lowest, b.AccessesInMap lowest → RowInMap lowest r) ∧
      ∀ last ∈ rows'.back?, last.postState = b.post ∧
        bytecode[last.rowIndex].virtual_sequence_remaining.getD 0 = 0 ∧
        (last.StableStall ↔ b.Stalls) ∧ segment.getLast? = some bytecode[last.rowIndex] := by
  obtain ⟨member, -⟩ := rowAt_mem runs.at_row
  obtain ⟨segment, before, after, emits, split⟩ :=
    segment_of_member joltInstance.program bytecode expanded b.row member
  obtain ⟨values, instrs, honest, patched, executed⟩ := runs.executes
  rw [emits, Option.map_some] at patched
  cases patched
  obtain ⟨states, state0, stateLast, steps⟩ := exec_seq_states _ _ _ executed
  have lengthEq : (patchAdvice values (segment.map (·.instruction))).length = segment.length := by
    rw [patchAdvice_length, List.length_map]
  have steps' : ∀ k (hk : k < segment.length),
      JoltISA.execInstr ((patchAdvice values (segment.map (·.instruction)))[k]'(by
        rw [lengthEq]; exact hk)) (states k) = .ok RETIRE_SUCCESS (states (k + 1)) :=
    fun k hk => steps k (by rw [lengthEq]; exact hk)
  have positive : 0 < segment.length := List.length_pos_iff.mpr
    (expand_instruction_nonempty b.row segment emits)
  obtain ⟨rows', h', size', keep', entries'⟩ := RunPrefix.appendRows h runs.at_row emits split
    values honest states state0 steps' firstRow
    (fun last hlast => by
      obtain ⟨post, remaining, notStall⟩ := link0 last hlast
      exact ⟨post, runs.continues, remaining, notStall⟩)
    segment.length le_rfl
  have bytecodeAt : ∀ k (hk : k < segment.length) (r : TraceRow bytecode),
      r.rowIndex.val = before.length + k → bytecode[r.rowIndex] = segment[k] :=
    fun k hk r hr => segment_get split k hk r.rowIndex hr
  refine ⟨rows', segment, h', emits, size', keep', ?_, ?_⟩
  · intro i r lower hr
    obtain ⟨r', hr', hidx, hpre, -⟩ := entries' (i - rows.size) (by
      by_contra outside
      rw [Array.getElem?_eq_none (by omega)] at hr
      cases hr)
    rw [show rows.size + (i - rows.size) = i by omega, hr] at hr'
    cases hr'
    have inside : i - rows.size < segment.length := by
      by_contra outside
      rw [Array.getElem?_eq_none (by omega)] at hr
      cases hr
    refine ⟨?_, ?_⟩
    · rw [bytecodeAt _ inside r hidx]
      exact List.getElem_mem inside
    · intro lowest inMap address haddress
      rw [TraceRow.ram_address_eq, bytecodeAt _ inside r hidx, hpre] at haddress
      obtain ⟨word, hword, rfl⟩ := Option.mem_map.mp haddress
      exact inMap segment emits values states honest state0 steps' _ inside word hword
  · intro last hlast
    have lastIndex : rows'.size - 1 = rows.size + (segment.length - 1) := by omega
    obtain ⟨r, hr, hidx, -, hpost⟩ := entries' (segment.length - 1) (by omega)
    rw [Array.back?_eq_getElem?, lastIndex, hr] at hlast
    cases hlast
    have hlen : segment.length - 1 + 1 = segment.length := by omega
    have lastPost : last.postState = b.post := by
      rw [hpost, hlen]
      simpa only [lengthEq] using stateLast
    have atLast := bytecodeAt _ (by omega) last hidx
    have remaining : bytecode[last.rowIndex].virtual_sequence_remaining.getD 0 = 0 := by
      have count := expand_instruction_countdown b.row segment emits (segment.length - 1)
        (by omega)
      rw [← atLast] at count
      apply BitVec.eq_of_toNat_eq
      rw [count]
      simp
    have address : bytecode[last.rowIndex].address = b.row.address := by
      rw [atLast]
      exact expand_instruction_address b.row segment emits _ (List.getElem_mem _)
    have getLast : segment.getLast? = some bytecode[last.rowIndex] := by
      rw [atLast, List.getLast?_eq_getElem?]
      exact List.getElem?_eq_getElem _
    refine ⟨lastPost, remaining, ?_, getLast⟩
    unfold TraceRow.StableStall Block.Stalls
    rw [lastPost, address]
    constructor
    · rintro ⟨-, next, repeats⟩
      refine ⟨next, fun rows hrows lastRow hlastRow => ?_⟩
      rw [emits] at hrows
      cases hrows
      rw [getLast] at hlastRow
      cases hlastRow
      exact repeats
    · rintro ⟨next, repeats⟩
      exact ⟨remaining, next, repeats segment emits _ getLast⟩

/-- The number of rows a block's expansion has (0 if the row has no expansion).
Example: a DIV block has the nine rows of DIV's expansion. -/
def Block.rowCount (b : Block) : Nat :=
  ((expand_instruction b.row).map List.length).getD 0

/-- How block `b` continues a run prefix: it starts the run when the prefix is empty, and
otherwise starts from the state the prefix's last row left, which ends its source instruction
and is not a stable stall.
Example: every block continues the empty prefix whose first block starts at the entry from the
initial state. -/
def Continues (joltInstance : JoltInstance SourceInstruction) (init : SailJoltState)
    {bytecode : Array JoltInstructionRow} (rows : Array (TraceRow bytecode)) (b : Block) : Prop :=
  (rows.size = 0 → b.row.address = joltInstance.program.entry_address ∧ b.pre = init) ∧
    ∀ last ∈ rows.back?, last.postState = b.pre ∧
      bytecode[last.rowIndex].virtual_sequence_remaining.getD 0 = 0 ∧ ¬ last.StableStall

/-- **Appending a chain of blocks.** Blocks that run, follow each other, continue the prefix and
do not stall before the last extend the prefix by their rows. Every new row is a row of some
block's expansion, and the new last row ends at the last block's last state and is a stable stall
exactly when that block stalls.
Example: appending an ADDI block and a `jal x0, 0` block to the empty prefix gives two rows. -/
theorem RunPrefix.appendBlocks {joltInstance : JoltInstance SourceInstruction}
    {init : SailJoltState} {bytecode : Array JoltInstructionRow}
    (expanded : expand_program joltInstance.program = some bytecode) :
    ∀ (blocks : List Block) (rows : Array (TraceRow bytecode)),
      RunPrefix joltInstance init rows →
      (∀ b ∈ blocks, b.Runs joltInstance.program) →
      blocks.IsChain (fun b c => b.post = c.pre) →
      (∀ first ∈ blocks.head?, Continues joltInstance init rows first) →
      (∀ b ∈ blocks.dropLast, ¬ b.Stalls) →
      ∃ rows' : Array (TraceRow bytecode), RunPrefix joltInstance init rows' ∧
        rows'.size = rows.size + (blocks.map Block.rowCount).sum ∧
        (∀ i < rows.size, rows'[i]? = rows[i]?) ∧
        (∀ (i : Nat) (r : TraceRow bytecode), rows.size ≤ i → rows'[i]? = some r →
          ∃ b ∈ blocks, (∃ segment, expand_instruction b.row = some segment ∧
            bytecode[r.rowIndex] ∈ segment) ∧
            ∀ lowest, b.AccessesInMap lowest → RowInMap lowest r) ∧
        ∀ final ∈ blocks.getLast?, ∀ last ∈ rows'.back?, last.postState = final.post ∧
          bytecode[last.rowIndex].virtual_sequence_remaining.getD 0 = 0 ∧
          (last.StableStall ↔ final.Stalls) ∧
          ∀ segment, expand_instruction final.row = some segment →
            segment.getLast? = some bytecode[last.rowIndex]
  | [], rows, h, _, _, _, _ =>
    ⟨rows, h, by simp, fun _ _ => rfl, fun i r lower hr => absurd hr (by
      rw [Array.getElem?_eq_none lower]; simp), by simp⟩
  | b :: rest, rows, h, runs, chain, first, noStall => by
    obtain ⟨cont0, cont1⟩ := first b rfl
    obtain ⟨rows1, segment, h1, emits, size1, keep1, new1, last1⟩ :=
      h.appendBlock expanded (runs b (by simp)) cont0 cont1
    have count : b.rowCount = segment.length := by simp [Block.rowCount, emits]
    have positive : 0 < segment.length := List.length_pos_iff.mpr
      (expand_instruction_nonempty b.row segment emits)
    cases rest with
    | nil =>
      refine ⟨rows1, h1, by simp [size1, count], keep1, ?_, ?_⟩
      · intro i r lower hr
        obtain ⟨member, inMap⟩ := new1 i r lower hr
        exact ⟨b, by simp, ⟨segment, emits, member⟩, inMap⟩
      · intro final hfinal
        simp only [List.getLast?_singleton, Option.mem_def, Option.some.injEq] at hfinal
        subst hfinal
        intro last hlast
        obtain ⟨post, remaining, stall, getLast⟩ := last1 last hlast
        refine ⟨post, remaining, stall, fun segment' emits' => ?_⟩
        rw [emits] at emits'
        cases emits'
        exact getLast
    | cons c rest' =>
      obtain ⟨link, chain'⟩ := List.isChain_cons_cons.mp chain
      have bStill : ¬ b.Stalls := noStall b (by simp)
      obtain ⟨rows2, h2, size2, keep2, new2, last2⟩ := RunPrefix.appendBlocks expanded
        (c :: rest') rows1 h1 (fun d hd => runs d (List.mem_cons_of_mem _ hd)) chain'
        (by
          intro first' hfirst'
          simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hfirst'
          subst hfirst'
          refine ⟨fun empty => by omega, fun last hlast => ?_⟩
          obtain ⟨post, remaining, stall, -⟩ := last1 last hlast
          exact ⟨post.trans link, remaining, fun stable => bStill (stall.mp stable)⟩)
        (fun d hd => noStall d (by
          rw [List.dropLast_cons_of_ne_nil (by simp)]
          exact List.mem_cons_of_mem _ hd))
      refine ⟨rows2, h2, ?_, ?_, ?_, ?_⟩
      · rw [size2, size1]
        simp only [List.map_cons, List.sum_cons, count]
        omega
      · intro i hi
        rw [keep2 i (by omega)]
        exact keep1 i hi
      · intro i r lower hr
        by_cases early : i < rows1.size
        · rw [keep2 i early] at hr
          obtain ⟨member, inMap⟩ := new1 i r lower hr
          exact ⟨b, by simp, ⟨segment, emits, member⟩, inMap⟩
        · obtain ⟨d, hd, rest⟩ := new2 i r (by omega) hr
          exact ⟨d, List.mem_cons_of_mem _ hd, rest⟩
      · intro final hfinal
        rw [List.getLast?_cons_cons] at hfinal
        exact last2 final hfinal

/-! ## The honest trace -/

/-- **An honest trace from a chain of blocks.** Let a nonempty chain of blocks run, start at the
entry from the instance's initial state `init`, stall at its last block and not before. Then the
private inputs with the inline advice words the blocks record give an honest trace from `init`
whose rows are the blocks' rows: it has one row per row of the blocks' expansions, ends at the
last block's last state, and each of its rows is a row of some block's expansion.
Example: an ADDI block followed by a stalling `jal x0, 0` block gives a two-row honest trace. -/
theorem HonestTrace.ofBlocks {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} {init : SailJoltState}
    (initialized : joltInstance.initial_state privateInputs = some init)
    (accepted : joltInstance.bytecode.isSome) (valid : joltInstance.validate_inputs = true)
    {bytecode : Array JoltInstructionRow}
    (expanded : expand_program joltInstance.program = some bytecode)
    (blocks : List Block) (nonempty : blocks ≠ [])
    (runs : ∀ b ∈ blocks, b.Runs joltInstance.program)
    (chain : blocks.IsChain (fun b c => b.post = c.pre))
    (first : ∀ f ∈ blocks.head?, f.row.address = joltInstance.program.entry_address ∧
      f.pre = init)
    (stops : ∀ l ∈ blocks.getLast?, l.Stalls)
    (noStall : ∀ b ∈ blocks.dropLast, ¬ b.Stalls) :
    ∃ (words : Array (BitVec 64))
      (trace : HonestTrace joltInstance { privateInputs with inline_advice := words }),
      trace.initialState = init ∧
      trace.rows.size = (blocks.map Block.rowCount).sum ∧
      (∀ last ∈ trace.rows.back?, ∀ final ∈ blocks.getLast?, last.postState = final.post ∧
        ∀ segment, expand_instruction final.row = some segment →
          segment.getLast? = some trace.bytecode[last.rowIndex]) ∧
      ∀ r ∈ trace.rows, ∃ b ∈ blocks,
        (∃ segment, expand_instruction b.row = some segment ∧
          trace.bytecode[r.rowIndex] ∈ segment) ∧
        ∀ lowest, b.AccessesInMap lowest → RowInMap lowest r := by
  obtain ⟨rows, h, size, -, new, last⟩ := RunPrefix.appendBlocks expanded blocks #[]
    (RunPrefix.empty joltInstance init bytecode) runs chain
    (fun f hf => ⟨fun _ => first f hf, by simp⟩) noStall
  simp only [List.size_toArray, List.length_nil, Nat.zero_add] at size
  obtain ⟨final, hfinal⟩ : ∃ final, blocks.getLast? = some final :=
    ⟨_, List.getLast?_eq_some_getLast nonempty⟩
  have positive : 0 < rows.size := by
    obtain ⟨b, hb⟩ := List.exists_mem_of_ne_nil blocks nonempty
    obtain ⟨member, -⟩ := rowAt_mem (runs b hb).at_row
    obtain ⟨segment, -, -, emits, -⟩ :=
      segment_of_member joltInstance.program bytecode expanded b.row member
    have count : b.rowCount = segment.length := by simp [Block.rowCount, emits]
    have : b.rowCount ≤ (blocks.map Block.rowCount).sum :=
      List.le_sum_of_mem (List.mem_map_of_mem hb)
    have := List.length_pos_iff.mpr (expand_instruction_nonempty b.row segment emits)
    omega
  let trace : HonestTrace joltInstance
      { privateInputs with inline_advice := collectInlineAdvice joltInstance.program rows } :=
    { bytecode := bytecode
      rows := rows
      initialState := init
      expands := expanded
      executes := h.executes
      initialized := initialized
      starts := h.starts
      linked := h.linked
      accepted := accepted
      valid_inputs := valid
      advice_from_honest_tracer :=
        honest_of_builtin joltInstance.program privateInputs rows h.builtin
      stops := fun row hrow => ((last final hfinal row hrow).2.2.1).mpr (stops final hfinal)
      runs_until_stop := h.runs_until_stop
      nonempty := positive }
  refine ⟨collectInlineAdvice joltInstance.program rows, trace, rfl, size, ?_, ?_⟩
  · intro row hrow final' hfinal'
    obtain ⟨post, -, -, getLast⟩ := last final' hfinal' row hrow
    exact ⟨post, getLast⟩
  · intro r hr
    obtain ⟨i, hi⟩ := Array.mem_iff_getElem?.mp hr
    exact new i r (Nat.zero_le _) hi

end WholeRun
