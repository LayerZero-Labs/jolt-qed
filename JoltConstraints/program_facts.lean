/-
Facts about the Jolt program: what the rows built from an ELF always look like.
Each one is proved from how program_fresh.lean builds the rows.
-/
import JoltConstraints.program_fresh

set_option autoImplicit false

-- Every row an instruction expands to carries that instruction's address.
theorem expand_instruction_address (source : SourceInstructionRow SourceInstruction)
    (rows : List JoltInstructionRow) (expanded : expand_instruction source = some rows) :
    ∀ row ∈ rows, row.address = source.address := by
  intro row member
  unfold expand_instruction at expanded
  split at expanded
  · -- no expansion: nothing to check
    cases expanded
  · -- a native instruction: its single row has the instruction's address
    cases expanded
    simp only [List.mem_singleton] at member
    rw [member]
  · split at expanded
    · cases expanded
    · -- a sequence: stamping gives every row the instruction's address
      cases expanded
      simp only [stamp_sequence, List.mem_map] at member
      obtain ⟨_, _, rfl⟩ := member
      rfl

-- An instruction always expands to at least one row.
theorem expand_instruction_nonempty (source : SourceInstructionRow SourceInstruction)
    (rows : List JoltInstructionRow) (expanded : expand_instruction source = some rows) :
    rows ≠ [] := by
  unfold expand_instruction at expanded
  split at expanded
  · -- no expansion
    cases expanded
  · -- a native instruction: one row
    cases expanded
    exact List.cons_ne_nil _ _
  · split at expanded
    · cases expanded
    · -- a sequence: Rust rejects an empty one, and stamping keeps every instruction
      rename_i instructions _ sizeOk
      cases expanded
      simp only [stamp_sequence, ne_eq, List.map_eq_nil_iff, List.zipIdx_eq_nil_iff]
      simp only [Bool.or_eq_true, List.isEmpty_iff, decide_eq_true_eq, not_or] at sizeOk
      exact sizeOk.1

-- An instruction's rows count down to 0: row k of n has n - 1 - k rows after it
-- (a native row's `none` counts as 0).
theorem expand_instruction_countdown (source : SourceInstructionRow SourceInstruction)
    (rows : List JoltInstructionRow) (expanded : expand_instruction source = some rows)
    (k : Nat) (inRange : k < rows.length) :
    (rows[k].virtual_sequence_remaining.getD 0).toNat = rows.length - 1 - k := by
  unfold expand_instruction at expanded
  split at expanded
  · -- no expansion
    cases expanded
  · -- a native instruction: its single row has `none`, which counts as 0
    cases expanded
    simp only [List.length_singleton] at inRange
    have first : k = 0 := by omega
    subst first
    rfl
  · split at expanded
    · cases expanded
    · -- a sequence: stamping gives row k the count n - k - 1, and n is at most 64
      rename_i instructions _ sizeOk
      cases expanded
      simp only [Bool.or_eq_true, List.isEmpty_iff, decide_eq_true_eq, not_or, not_lt]
        at sizeOk
      simp only [stamp_sequence, List.getElem_map, List.getElem_zipIdx, List.length_map,
        List.length_zipIdx, Option.getD_some, BitVec.toNat_ofNat, Nat.zero_add]
      have small : instructions.length - k - 1 < 2 ^ 16 := by
        have bound : MAX_FINAL_ROWS_PER_SOURCE = 64 := rfl
        omega
      rw [Nat.mod_eq_of_lt small]
      omega

-- Only an instruction's first row is where it starts.
theorem expand_instruction_starts_source (source : SourceInstructionRow SourceInstruction)
    (rows : List JoltInstructionRow) (expanded : expand_instruction source = some rows)
    (k : Nat) (inRange : k < rows.length) :
    rows[k].starts_source = (k == 0) := by
  unfold expand_instruction at expanded
  split at expanded
  · -- no expansion
    cases expanded
  · -- a native instruction: its single row has `none`, so it starts the instruction
    cases expanded
    simp only [List.length_singleton] at inRange
    have first : k = 0 := by omega
    subst first
    rfl
  · split at expanded
    · cases expanded
    · -- a sequence: every row has a count, and only row 0 is marked first
      cases expanded
      simp only [JoltInstructionRow.starts_source, stamp_sequence, List.getElem_map,
        List.getElem_zipIdx, Nat.zero_add, Option.isNone_some, Bool.false_or]

-- Only an instruction's last row carries its compressed flag.
theorem expand_instruction_compressed (source : SourceInstructionRow SourceInstruction)
    (rows : List JoltInstructionRow) (expanded : expand_instruction source = some rows)
    (k : Nat) (inRange : k < rows.length) :
    rows[k].is_compressed = (k == rows.length - 1 && source.is_compressed) := by
  unfold expand_instruction at expanded
  split at expanded
  · -- no expansion
    cases expanded
  · -- a native instruction: its single row is also its last row
    cases expanded
    simp only [List.length_singleton] at inRange
    have first : k = 0 := by omega
    subst first
    rfl
  · split at expanded
    · cases expanded
    · -- a sequence: stamping sets the flag only on the last row
      cases expanded
      simp only [stamp_sequence, List.getElem_map, List.getElem_zipIdx, Nat.zero_add,
        List.length_map, List.length_zipIdx]

-- The rows one instruction expands to (one row if native, several if expanded):
-- at least one row, all at the instruction's address, counting down to 0, started
-- only by the first row, and carrying the compressed flag only on the last row.
structure ExpandedRows (address : BitVec 64) (is_compressed : Bool)
    (rows : List JoltInstructionRow) : Prop where
  nonempty : rows ≠ []
  same_address : ∀ row ∈ rows, row.address = address
  countdown : ∀ (k : Nat) (inRange : k < rows.length),
    (rows[k].virtual_sequence_remaining.getD 0).toNat = rows.length - 1 - k
  starts : ∀ (k : Nat) (inRange : k < rows.length), rows[k].starts_source = (k == 0)
  compressed : ∀ (k : Nat) (inRange : k < rows.length),
    rows[k].is_compressed = (k == rows.length - 1 && is_compressed)

-- Whatever expand_instruction returns are the instruction's expanded rows.
theorem expand_instruction_expandedRows (source : SourceInstructionRow SourceInstruction)
    (rows : List JoltInstructionRow) (expanded : expand_instruction source = some rows) :
    ExpandedRows source.address source.is_compressed rows where
  nonempty := expand_instruction_nonempty source rows expanded
  same_address := expand_instruction_address source rows expanded
  countdown := expand_instruction_countdown source rows expanded
  starts := expand_instruction_starts_source source rows expanded
  compressed := expand_instruction_compressed source rows expanded

-- In rows laid end to end, a row that is not its instruction's last row is followed
-- by that instruction's next row.
theorem rows_next (instructions : List (List JoltInstructionRow))
    (valid : ∀ rows ∈ instructions, ∃ address is_compressed,
      ExpandedRows address is_compressed rows)
    (i : Nat) (inRange : i + 1 < instructions.flatten.length)
    (notLast : instructions.flatten[i].virtual_sequence_remaining.getD 0 ≠ 0) :
    instructions.flatten[i + 1].address = instructions.flatten[i].address ∧
    (instructions.flatten[i + 1].virtual_sequence_remaining.getD 0).toNat =
      (instructions.flatten[i].virtual_sequence_remaining.getD 0).toNat - 1 ∧
    instructions.flatten[i + 1].starts_source = false ∧
    instructions.flatten[i].is_compressed = false := by
  induction instructions generalizing i with
  | nil =>
    simp only [List.flatten_nil, List.length_nil] at inRange
    omega
  | cons rows rest ih =>
    obtain ⟨address, is_compressed, expandedRows⟩ := valid rows List.mem_cons_self
    have validRest : ∀ rows ∈ rest, ∃ address is_compressed,
        ExpandedRows address is_compressed rows :=
      fun later member => valid later (List.mem_cons_of_mem _ member)
    simp only [List.flatten_cons, List.length_append] at inRange notLast ⊢
    by_cases inside : i + 1 < rows.length
    · -- both rows belong to this instruction: read the four facts off its rows
      rw [List.getElem_append_left (show i < rows.length by omega),
        List.getElem_append_left (show i + 1 < rows.length by omega)]
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [expandedRows.same_address _ (List.getElem_mem _),
          expandedRows.same_address _ (List.getElem_mem _)]
      · rw [expandedRows.countdown i (by omega), expandedRows.countdown (i + 1) inside]
        omega
      · rw [expandedRows.starts (i + 1) inside]
        rfl
      · rw [expandedRows.compressed i (by omega)]
        have notLastRow : (i == rows.length - 1) = false := by
          rw [beq_eq_false_iff_ne]
          omega
        rw [notLastRow, Bool.false_and]
    · by_cases lastRow : i < rows.length
      · -- row i is this instruction's last row, so its count is 0: impossible here
        rw [List.getElem_append_left lastRow] at notLast
        apply absurd _ notLast
        apply BitVec.eq_of_toNat_eq
        rw [expandedRows.countdown i lastRow]
        have zero : (0 : BitVec 16).toNat = 0 := rfl
        rw [zero]
        omega
      · -- both rows belong to a later instruction: use the same fact for the rest
        rw [List.getElem_append_right (show rows.length ≤ i by omega),
          List.getElem_append_right (show rows.length ≤ i + 1 by omega)]
        rw [List.getElem_append_right (show rows.length ≤ i by omega)] at notLast
        have index : i + 1 - rows.length = i - rows.length + 1 := by omega
        simp only [index]
        exact ih validRest (i - rows.length) (by omega) notLast

-- In rows laid end to end, the first row starts an instruction.
theorem rows_first_starts (instructions : List (List JoltInstructionRow))
    (valid : ∀ rows ∈ instructions, ∃ address is_compressed,
      ExpandedRows address is_compressed rows)
    (inRange : 0 < instructions.flatten.length) :
    instructions.flatten[0].starts_source = true := by
  cases instructions with
  | nil =>
    simp only [List.flatten_nil, List.length_nil] at inRange
    omega
  | cons rows rest =>
    -- the first instruction has at least one row, and its row 0 starts it
    obtain ⟨address, is_compressed, expandedRows⟩ := valid rows List.mem_cons_self
    have someRow : 0 < rows.length := List.length_pos_iff.mpr expandedRows.nonempty
    simp only [List.flatten_cons]
    rw [List.getElem_append_left someRow, expandedRows.starts 0 someRow]
    rfl

-- In rows laid end to end, the row after an instruction's last row starts the
-- next instruction.
theorem rows_after_last (instructions : List (List JoltInstructionRow))
    (valid : ∀ rows ∈ instructions, ∃ address is_compressed,
      ExpandedRows address is_compressed rows)
    (i : Nat) (inRange : i + 1 < instructions.flatten.length)
    (last : instructions.flatten[i].virtual_sequence_remaining.getD 0 = 0) :
    instructions.flatten[i + 1].starts_source = true := by
  induction instructions generalizing i with
  | nil =>
    simp only [List.flatten_nil, List.length_nil] at inRange
    omega
  | cons rows rest ih =>
    obtain ⟨address, is_compressed, expandedRows⟩ := valid rows List.mem_cons_self
    have validRest : ∀ rows ∈ rest, ∃ address is_compressed,
        ExpandedRows address is_compressed rows :=
      fun later member => valid later (List.mem_cons_of_mem _ member)
    simp only [List.flatten_cons, List.length_append] at inRange last ⊢
    by_cases inside : i + 1 < rows.length
    · -- row i is not this instruction's last row, so its count is not 0: impossible
      rw [List.getElem_append_left (show i < rows.length by omega)] at last
      have count := expandedRows.countdown i (by omega)
      rw [last] at count
      have zero : (0 : BitVec 16).toNat = 0 := rfl
      rw [zero] at count
      omega
    · by_cases lastRow : i < rows.length
      · -- row i is this instruction's last row: row i + 1 is the next instruction's first
        rw [List.getElem_append_right (show rows.length ≤ i + 1 by omega)]
        have index : i + 1 - rows.length = 0 := by omega
        simp only [index]
        exact rows_first_starts rest validRest (by omega)
      · -- both rows belong to a later instruction: use the same fact for the rest
        rw [List.getElem_append_right (show rows.length ≤ i + 1 by omega)]
        rw [List.getElem_append_right (show rows.length ≤ i by omega)] at last
        have index : i + 1 - rows.length = i - rows.length + 1 := by omega
        simp only [index]
        exact ih validRest (i - rows.length) (by omega) last

-- In rows laid end to end, counting a row's remaining rows forward stays inside
-- the rows.
theorem rows_end_in_bounds (instructions : List (List JoltInstructionRow))
    (valid : ∀ rows ∈ instructions, ∃ address is_compressed,
      ExpandedRows address is_compressed rows)
    (i : Nat) (inRange : i < instructions.flatten.length) :
    i + (instructions.flatten[i].virtual_sequence_remaining.getD 0).toNat <
      instructions.flatten.length := by
  induction instructions generalizing i with
  | nil =>
    simp only [List.flatten_nil, List.length_nil] at inRange
    omega
  | cons rows rest ih =>
    obtain ⟨address, is_compressed, expandedRows⟩ := valid rows List.mem_cons_self
    have validRest : ∀ rows ∈ rest, ∃ address is_compressed,
        ExpandedRows address is_compressed rows :=
      fun later member => valid later (List.mem_cons_of_mem _ member)
    simp only [List.flatten_cons, List.length_append] at inRange ⊢
    by_cases inside : i < rows.length
    · -- row i belongs to this instruction: its count reaches exactly its last row
      rw [List.getElem_append_left inside, expandedRows.countdown i inside]
      omega
    · -- row i belongs to a later instruction: use the same fact for the rest
      rw [List.getElem_append_right (show rows.length ≤ i by omega)]
      have later := ih validRest (i - rows.length) (by omega)
      omega

-- When an Option-valued map over a list succeeds, the results line up one to one
-- with the inputs.
theorem option_mapM_results {Input Output : Type} (step : Input → Option Output) :
    ∀ (inputs : List Input) (outputs : List Output), inputs.mapM step = some outputs →
      outputs.length = inputs.length ∧
      ∀ (index : Nat) (inInputs : index < inputs.length) (inOutputs : index < outputs.length),
        step inputs[index] = some outputs[index] := by
  intro inputs
  induction inputs with
  | nil =>
    intro outputs mapped
    simp only [List.mapM_nil, pure, Option.some.injEq] at mapped
    subst mapped
    refine ⟨rfl, ?_⟩
    intro index inInputs
    simp only [List.length_nil] at inInputs
    omega
  | cons head tail ih =>
    intro outputs mapped
    rw [List.mapM_cons] at mapped
    cases headResult : step head with
    | none =>
      simp only [headResult, bind, Option.bind] at mapped
      cases mapped
    | some headOutput =>
      cases tailResult : tail.mapM step with
      | none =>
        simp only [headResult, tailResult, bind, Option.bind] at mapped
        cases mapped
      | some tailOutputs =>
        simp only [headResult, tailResult, bind, Option.bind, pure,
          Option.some.injEq] at mapped
        subst mapped
        obtain ⟨tailLength, tailSteps⟩ := ih tailOutputs tailResult
        refine ⟨by simp only [List.length_cons, tailLength], ?_⟩
        intro index inInputs inOutputs
        cases index with
        | zero => exact headResult
        | succ before =>
          simp only [List.getElem_cons_succ]
          exact tailSteps before (by simp only [List.length_cons] at inInputs; omega)
            (by simp only [List.length_cons] at inOutputs; omega)

-- The program's bytecode is each source instruction's expanded rows, in order.
theorem expand_program_rows (image : Rv64ProgramImage SourceInstruction)
    (bytecode : Array JoltInstructionRow) (expanded : expand_program image = some bytecode) :
    ∃ instructions : List (List JoltInstructionRow),
      bytecode = instructions.flatten.toArray ∧
      instructions.length = image.instructions.size ∧
      ∀ (k : Nat) (inRange : k < image.instructions.size) (inRows : k < instructions.length),
        ExpandedRows image.instructions[k].address image.instructions[k].is_compressed
          instructions[k] := by
  unfold expand_program at expanded
  cases mapped : image.instructions.toList.mapM expand_instruction with
  | none =>
    rw [mapped] at expanded
    cases expanded
  | some instructions =>
    rw [mapped, Option.map_some, Option.some.injEq] at expanded
    obtain ⟨lengths, steps⟩ := option_mapM_results expand_instruction _ instructions mapped
    refine ⟨instructions, expanded.symm, ?_, ?_⟩
    · rw [lengths, Array.length_toList]
    · intro k inRange inRows
      have step := steps k (by rw [Array.length_toList]; exact inRange) inRows
      rw [Array.getElem_toList inRange] at step
      exact expand_instruction_expandedRows _ _ step

-- A run Rust's PC map accepts counts down to 0: row k of n has count n - 1 - k.
theorem valid_run_countdown (run : List JoltInstructionRow)
    (valid : valid_run run = true) (position : Nat) (inRange : position < run.length) :
    (run[position].virtual_sequence_remaining.getD 0).toNat = run.length - 1 - position := by
  unfold valid_run at valid
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at valid
  have atPosition := List.getElem_of_eq valid.1 (by rw [List.length_map]; exact inRange)
  simp only [List.getElem_map, List.getElem_reverse, List.getElem_range, List.length_map,
    List.length_range] at atPosition
  exact atPosition

-- In runs laid end to end, where each run counts down to 0 and neighbouring runs
-- differ in address, a row with count 0 is followed by a row at a different address.
theorem runs_zero_then_new_address (runs : List (List JoltInstructionRow))
    (countdown : ∀ run ∈ runs, ∀ (position : Nat) (inRange : position < run.length),
      (run[position].virtual_sequence_remaining.getD 0).toNat = run.length - 1 - position)
    (nonempty : [] ∉ runs)
    (boundaries : runs.IsChain fun first second =>
      ∃ firstNonempty secondNonempty,
        (fun a b : JoltInstructionRow => a.address == b.address)
          (first.getLast firstNonempty) (second.head secondNonempty) = false)
    (position : Nat) (inRange : position + 1 < runs.flatten.length)
    (zero : (runs.flatten[position].virtual_sequence_remaining.getD 0).toNat = 0) :
    runs.flatten[position + 1].address ≠ runs.flatten[position].address := by
  induction runs generalizing position with
  | nil =>
    simp only [List.flatten_nil, List.length_nil] at inRange
    omega
  | cons run rest ih =>
    have runCountdown := countdown run List.mem_cons_self
    have runNonempty : run ≠ [] := fun empty => nonempty (empty ▸ List.mem_cons_self)
    simp only [List.flatten_cons, List.length_append] at inRange zero ⊢
    by_cases inside : position + 1 < run.length
    · -- row `position` is not the run's last row, so its count is not 0: impossible
      rw [List.getElem_append_left (show position < run.length by omega),
        runCountdown position (by omega)] at zero
      omega
    · by_cases lastRow : position < run.length
      · -- row `position` ends the run, so the next row starts the next run
        cases rest with
        | nil =>
          simp only [List.flatten_nil, List.length_nil] at inRange
          omega
        | cons next later =>
          have nextNonempty : next ≠ [] :=
            fun empty => nonempty (empty ▸ List.mem_cons_of_mem _ List.mem_cons_self)
          obtain ⟨⟨lastNonempty, headNonempty, differ⟩, _⟩ :=
            List.isChain_cons_cons.mp boundaries
          rw [List.getElem_append_left lastRow,
            List.getElem_append_right (show run.length ≤ position + 1 by omega)]
          have index : position + 1 - run.length = 0 := by omega
          simp only [index, List.flatten_cons]
          rw [List.getElem_append_left (List.length_pos_iff.mpr nextNonempty)]
          rw [List.getLast_eq_getElem, List.head_eq_getElem] at differ
          have samePosition : position = run.length - 1 := by omega
          simp only [samePosition]
          intro equal
          rw [beq_eq_false_iff_ne] at differ
          exact differ equal.symm
      · -- both rows lie in later runs: use the same fact for the rest
        rw [List.getElem_append_right (show run.length ≤ position + 1 by omega),
          List.getElem_append_right (show run.length ≤ position by omega)]
        rw [List.getElem_append_right (show run.length ≤ position by omega)] at zero
        have index : position + 1 - run.length = position - run.length + 1 := by omega
        simp only [index]
        exact ih (fun later member => countdown later (List.mem_cons_of_mem _ member))
          (fun empty => nonempty (List.mem_cons_of_mem _ empty)) boundaries.tail
          (position - run.length) (by omega) zero

-- If every row with count 0 is followed by a row at a different address, then
-- neighbouring instructions differ in address.
theorem instructions_boundaries (instructions : List (List JoltInstructionRow))
    (valid : ∀ rows ∈ instructions, ∃ address is_compressed,
      ExpandedRows address is_compressed rows)
    (newAddress : ∀ (position : Nat) (inRange : position + 1 < instructions.flatten.length),
      (instructions.flatten[position].virtual_sequence_remaining.getD 0).toNat = 0 →
      instructions.flatten[position + 1].address ≠ instructions.flatten[position].address) :
    instructions.IsChain fun first second => ∃ firstNonempty secondNonempty,
      (fun a b : JoltInstructionRow => a.address == b.address)
        (first.getLast firstNonempty) (second.head secondNonempty) = false := by
  induction instructions with
  | nil => exact List.IsChain.nil
  | cons rows rest ih =>
    obtain ⟨address, is_compressed, expandedRows⟩ := valid rows List.mem_cons_self
    have rowsNonempty := expandedRows.nonempty
    have someRow : 0 < rows.length := List.length_pos_iff.mpr rowsNonempty
    -- the same fact, seen from the rest of the instructions
    have newAddressRest : ∀ (position : Nat) (inRange : position + 1 < rest.flatten.length),
        (rest.flatten[position].virtual_sequence_remaining.getD 0).toNat = 0 →
        rest.flatten[position + 1].address ≠ rest.flatten[position].address := by
      intro position inRange zero
      have shifted := newAddress (position + rows.length)
        (by simp only [List.flatten_cons, List.length_append]; omega)
      simp only [List.flatten_cons] at shifted
      rw [List.getElem_append_right (show rows.length ≤ position + rows.length + 1 by omega),
        List.getElem_append_right (show rows.length ≤ position + rows.length by omega)]
        at shifted
      have index : position + rows.length + 1 - rows.length = position + 1 := by omega
      have index' : position + rows.length - rows.length = position := by omega
      simp only [index, index'] at shifted
      exact shifted zero
    have restChain := ih (fun later member => valid later (List.mem_cons_of_mem _ member))
      newAddressRest
    cases rest with
    | nil => exact List.IsChain.singleton _
    | cons next later =>
      refine List.isChain_cons_cons.mpr ⟨?_, restChain⟩
      obtain ⟨_, _, nextRows⟩ := valid next (List.mem_cons_of_mem _ List.mem_cons_self)
      have nextNonempty := nextRows.nonempty
      refine ⟨rowsNonempty, nextNonempty, ?_⟩
      -- the instruction's last row has count 0, so the next instruction's first
      -- row is at a different address
      have nextSome := List.length_pos_iff.mpr nextNonempty
      have differ := newAddress (rows.length - 1)
        (by simp only [List.flatten_cons, List.length_append]; omega)
        (by
          simp only [List.flatten_cons]
          rw [List.getElem_append_left (show rows.length - 1 < rows.length by omega),
            expandedRows.countdown _ (by omega)]
          omega)
      simp only [List.flatten_cons] at differ
      rw [List.getElem_append_left (show rows.length - 1 < rows.length by omega),
        List.getElem_append_right (show rows.length ≤ rows.length - 1 + 1 by omega)] at differ
      have index : rows.length - 1 + 1 - rows.length = 0 := by omega
      simp only [index] at differ
      rw [List.getElem_append_left (List.length_pos_iff.mpr nextNonempty)] at differ
      rw [List.getLast_eq_getElem, List.head_eq_getElem, beq_eq_false_iff_ne]
      exact fun equal => differ equal.symm

-- One instruction's rows all share an address, so Rust's split keeps them together.
theorem same_address_chain (rows : List JoltInstructionRow) (address : BitVec 64)
    (same : ∀ row ∈ rows, row.address = address) :
    rows.IsChain fun a b : JoltInstructionRow => (a.address == b.address) = true := by
  induction rows with
  | nil => exact List.IsChain.nil
  | cons first rest ih =>
    have restChain := ih (fun row member => same row (List.mem_cons_of_mem _ member))
    cases rest with
    | nil => exact List.IsChain.singleton _
    | cons second later =>
      refine List.isChain_cons_cons.mpr ⟨?_, restChain⟩
      rw [same first List.mem_cons_self,
        same second (List.mem_cons_of_mem _ List.mem_cons_self), beq_self_eq_true]

-- The address each instruction's rows start at is that instruction's address.
theorem run_addresses (instructions : List (List JoltInstructionRow))
    (sources : List (SourceInstructionRow SourceInstruction))
    (lengths : instructions.length = sources.length)
    (each : ∀ (position : Nat) (inSources : position < sources.length)
      (inRows : position < instructions.length),
      ExpandedRows sources[position].address sources[position].is_compressed
        instructions[position]) :
    instructions.filterMap (fun run => run.head?.map (·.address)) =
      sources.map (·.address) := by
  induction instructions generalizing sources with
  | nil =>
    cases sources with
    | nil => rfl
    | cons _ _ =>
      simp only [List.length_nil, List.length_cons] at lengths
      omega
  | cons rows rest ih =>
    cases sources with
    | nil =>
      simp only [List.length_nil, List.length_cons] at lengths
      omega
    | cons source moreSources =>
      have firstRows := each 0 (by simp only [List.length_cons]; omega)
        (by simp only [List.length_cons]; omega)
      simp only [List.getElem_cons_zero] at firstRows
      cases rows with
      | nil => exact absurd rfl firstRows.nonempty
      | cons firstRow _ =>
        rw [List.filterMap_cons_some (b := source.address)
          (by simp only [List.head?_cons, Option.map_some,
            firstRows.same_address firstRow List.mem_cons_self])]
        rw [List.map_cons]
        congr 1
        exact ih moreSources (by simp only [List.length_cons] at lengths; omega)
          (fun position inSources inRows => by
            have shifted := each (position + 1) (by simp only [List.length_cons]; omega)
              (by simp only [List.length_cons]; omega)
            simp only [List.getElem_cons_succ] at shifted
            exact shifted)

-- If Rust's PC map accepts the program's rows, no two source instructions share
-- an address.
theorem pc_map_ok_distinct_addresses (image : Rv64ProgramImage SourceInstruction)
    (bytecode : Array JoltInstructionRow) (expanded : expand_program image = some bytecode)
    (accepted : pc_map_ok bytecode = true) :
    (image.instructions.toList.map (·.address)).Nodup := by
  obtain ⟨instructions, isFlatten, lengths, each⟩ := expand_program_rows image bytecode expanded
  have rowsList : bytecode.toList = instructions.flatten := by
    rw [isFlatten, List.toList_toArray]
  -- every instruction's rows are ExpandedRows
  have valid : ∀ rows ∈ instructions, ∃ address is_compressed,
      ExpandedRows address is_compressed rows := by
    intro rows member
    obtain ⟨position, inRows, atPosition⟩ := List.mem_iff_getElem.mp member
    exact ⟨_, _, atPosition ▸ each position (by omega) inRows⟩
  -- unpack Rust's checks: every run counts down to 0, and run addresses are distinct
  unfold pc_map_ok at accepted
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at accepted
  obtain ⟨⟨runsOk, distinct⟩, _⟩ := accepted
  rw [rowsList] at runsOk distinct
  -- step 1: in Rust's runs, a row with count 0 is followed by a different address
  have newAddress := runs_zero_then_new_address
    (instructions.flatten.splitBy fun a b => a.address == b.address)
    (fun run member => valid_run_countdown run (runsOk run member).2)
    (List.nil_notMem_splitBy _ _)
    (List.isChain_getLast_head_splitBy (fun a b : JoltInstructionRow => a.address == b.address)
      instructions.flatten)
  simp only [List.flatten_splitBy] at newAddress
  -- step 2: so neighbouring instructions differ in address, and
  -- step 3: Rust's runs are exactly the instructions' rows
  have runsAreInstructions :
      (instructions.flatten.splitBy fun a b => a.address == b.address) = instructions := by
    rw [List.splitBy_eq_iff]
    refine ⟨rfl, fun empty => ?_, fun rows member => ?_,
      instructions_boundaries instructions valid newAddress⟩
    · obtain ⟨_, _, emptyRows⟩ := valid [] empty
      exact emptyRows.nonempty rfl
    · obtain ⟨address, _, expandedRows⟩ := valid rows member
      exact same_address_chain rows address expandedRows.same_address
  rw [runsAreInstructions] at distinct
  -- the runs' addresses are the source instructions' addresses
  rw [run_addresses instructions image.instructions.toList
    (by rw [lengths, Array.length_toList])
    (fun position inSources inRows => by
      rw [Array.getElem_toList (by rw [Array.length_toList] at inSources; exact inSources)]
      exact each position (by rw [Array.length_toList] at inSources; exact inSources) inRows)]
    at distinct
  exact distinct

-- In rows laid end to end, a row of a later instruction has one of the later
-- instructions' addresses.
theorem later_row_address (rest : List (List JoltInstructionRow))
    (moreSources : List (SourceInstructionRow SourceInstruction))
    (each : ∀ (position : Nat) (inSources : position < moreSources.length)
      (inRows : position < rest.length),
      ExpandedRows moreSources[position].address moreSources[position].is_compressed
        rest[position])
    (lengths : rest.length = moreSources.length)
    (row : JoltInstructionRow) (member : row ∈ rest.flatten) :
    row.address ∈ moreSources.map (·.address) := by
  obtain ⟨rows, inRest, inRows⟩ := List.mem_flatten.mp member
  obtain ⟨position, inRange, atPosition⟩ := List.mem_iff_getElem.mp inRest
  have expandedRows := each position (by omega) inRange
  rw [atPosition] at expandedRows
  rw [expandedRows.same_address row inRows]
  exact List.mem_map_of_mem (List.getElem_mem _)

-- In rows laid end to end, where different instructions have different addresses,
-- no two rows share both an address and a countdown.
theorem rows_unique (instructions : List (List JoltInstructionRow))
    (sources : List (SourceInstructionRow SourceInstruction))
    (lengths : instructions.length = sources.length)
    (each : ∀ (position : Nat) (inSources : position < sources.length)
      (inRows : position < instructions.length),
      ExpandedRows sources[position].address sources[position].is_compressed
        instructions[position])
    (distinct : (sources.map (·.address)).Nodup)
    (first second : Nat) (inFirst : first < instructions.flatten.length)
    (inSecond : second < instructions.flatten.length)
    (sameAddress : instructions.flatten[first].address = instructions.flatten[second].address)
    (sameCount : instructions.flatten[first].virtual_sequence_remaining.getD 0 =
      instructions.flatten[second].virtual_sequence_remaining.getD 0) :
    first = second := by
  induction instructions generalizing sources first second with
  | nil =>
    simp only [List.flatten_nil, List.length_nil] at inFirst
    omega
  | cons rows rest ih =>
    cases sources with
    | nil =>
      simp only [List.length_nil, List.length_cons] at lengths
      omega
    | cons source moreSources =>
      have firstRows := each 0 (by simp only [List.length_cons]; omega)
        (by simp only [List.length_cons]; omega)
      simp only [List.getElem_cons_zero] at firstRows
      have eachRest : ∀ (position : Nat) (inSources : position < moreSources.length)
          (inRows : position < rest.length),
          ExpandedRows moreSources[position].address moreSources[position].is_compressed
            rest[position] := fun position inSources inRows => by
        have shifted := each (position + 1) (by simp only [List.length_cons]; omega)
          (by simp only [List.length_cons]; omega)
        simp only [List.getElem_cons_succ] at shifted
        exact shifted
      have lengthsRest : rest.length = moreSources.length := by
        simp only [List.length_cons] at lengths
        omega
      simp only [List.map_cons, List.nodup_cons] at distinct
      obtain ⟨notLater, distinctRest⟩ := distinct
      -- a row of a later instruction never has this instruction's address
      have laterAddress : ∀ position (inRange : position < rest.flatten.length),
          rest.flatten[position].address ≠ source.address := fun position inRange equal =>
        notLater (equal ▸ later_row_address rest moreSources eachRest lengthsRest _
          (List.getElem_mem inRange))
      simp only [List.flatten_cons, List.length_append] at inFirst inSecond sameAddress sameCount
      by_cases firstInside : first < rows.length
      · by_cases secondInside : second < rows.length
        · -- both rows belong to this instruction: equal countdowns mean the same row
          rw [List.getElem_append_left firstInside, List.getElem_append_left secondInside]
            at sameCount
          have counts := congrArg BitVec.toNat sameCount
          rw [firstRows.countdown first firstInside, firstRows.countdown second secondInside]
            at counts
          omega
        · -- the second row belongs to a later instruction: the addresses differ
          rw [List.getElem_append_left firstInside,
            List.getElem_append_right (show rows.length ≤ second by omega),
            firstRows.same_address _ (List.getElem_mem _)] at sameAddress
          exact absurd sameAddress.symm (laterAddress _ (by omega))
      · by_cases secondInside : second < rows.length
        · -- the first row belongs to a later instruction: the addresses differ
          rw [List.getElem_append_right (show rows.length ≤ first by omega),
            List.getElem_append_left secondInside,
            firstRows.same_address _ (List.getElem_mem _)] at sameAddress
          exact absurd sameAddress (laterAddress _ (by omega))
        · -- both rows belong to later instructions: use the same fact for the rest
          rw [List.getElem_append_right (show rows.length ≤ first by omega),
            List.getElem_append_right (show rows.length ≤ second by omega)]
            at sameAddress sameCount
          have shifted := ih moreSources lengthsRest eachRest distinctRest
            (first - rows.length) (second - rows.length) (by omega) (by omega)
            sameAddress sameCount
          omega

-- In an accepted program, no two rows share both an address and a countdown.
theorem expand_program_unique (image : Rv64ProgramImage SourceInstruction)
    (bytecode : Array JoltInstructionRow) (expanded : expand_program image = some bytecode)
    (accepted : pc_map_ok bytecode = true)
    (first second : Nat) (inFirst : first < bytecode.size) (inSecond : second < bytecode.size)
    (sameAddress : bytecode[first].address = bytecode[second].address)
    (sameCount : bytecode[first].virtual_sequence_remaining.getD 0 =
      bytecode[second].virtual_sequence_remaining.getD 0) :
    first = second := by
  have distinct := pc_map_ok_distinct_addresses image bytecode expanded accepted
  obtain ⟨instructions, isFlatten, lengths, each⟩ := expand_program_rows image bytecode expanded
  subst isFlatten
  simp only [List.getElem_toArray] at sameAddress sameCount
  simp only [List.size_toArray] at inFirst inSecond
  exact rows_unique instructions image.instructions.toList
    (by rw [lengths, Array.length_toList])
    (fun position inSources inRows => by
      rw [Array.getElem_toList (by rw [Array.length_toList] at inSources; exact inSources)]
      exact each position (by rw [Array.length_toList] at inSources; exact inSources) inRows)
    distinct first second inFirst inSecond sameAddress sameCount

-- If Rust accepts the instance's program, its expanded rows pass the PC map checks.
theorem accepted_pc_map_ok (joltInstance : JoltInstance SourceInstruction)
    (bytecode : Array JoltInstructionRow)
    (expanded : expand_program joltInstance.program = some bytecode)
    (accepted : joltInstance.bytecode.isSome = true) :
    pc_map_ok bytecode = true := by
  by_contra rejected
  -- preprocessing rejects rows that fail the PC map checks, so Rust rejects the program
  have noSlots : preprocess bytecode = none := by
    unfold preprocess
    rw [if_neg rejected]
  have rejectedProgram : joltInstance.bytecode = none := by
    unfold JoltInstance.bytecode
    rw [expanded]
    simp only [bind, Option.bind, noSlots]
  rw [rejectedProgram, Option.isSome_none] at accepted
  exact Bool.false_ne_true accepted

-- Rust's preprocessed bytecode: the NoOp at slot 0, row k at slot k + 1, NoOps after
-- the rows, and a power-of-two number of slots, at least 2.
theorem preprocess_slots (rows : Array JoltInstructionRow) (slots : Array BytecodeSlot)
    (preprocessed : preprocess rows = some slots) :
    slots[0]? = some .noop ∧
    (∀ (position : Nat) (inRows : position < rows.size),
      slots[position + 1]? = some (.row rows[position])) ∧
    (∀ (position : Nat), rows.size < position → position < slots.size →
      slots[position]? = some .noop) ∧
    slots.size = max 2 (2 ^ Nat.clog 2 (rows.size + 1)) := by
  unfold preprocess at preprocessed
  split at preprocessed
  · simp only [Option.some.injEq] at preprocessed
    subst preprocessed
    -- the NoOp and the rows come first, then the padding
    have baseSize : (#[BytecodeSlot.noop] ++ rows.map BytecodeSlot.row).size = rows.size + 1 := by
      simp only [Array.size_append, Array.size_map, List.size_toArray, List.length_singleton]
      omega
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- slot 0 is the NoOp
      rw [Array.getElem?_append_left (by rw [baseSize]; omega),
        Array.getElem?_append_left (by simp only [List.size_toArray, List.length_singleton]; omega)]
      rfl
    · -- row k sits at slot k + 1
      intro position inRows
      rw [Array.getElem?_append_left (by rw [baseSize]; omega),
        Array.getElem?_append_right (by simp only [List.size_toArray, List.length_singleton]; omega),
        Array.getElem?_map]
      simp only [List.size_toArray, List.length_singleton, Nat.add_sub_cancel,
        Array.getElem?_eq_getElem inRows, Option.map_some]
    · -- every slot after the rows is padding
      intro position after inSlots
      rw [Array.getElem?_append_right (by rw [baseSize]; omega), Array.getElem?_replicate]
      rw [if_pos (by
        simp only [Array.size_append, Array.size_replicate, baseSize] at inSlots
        rw [baseSize]
        omega)]
    · -- the slots fill exactly a power of two, at least 2
      simp only [Array.size_append, Array.size_replicate, baseSize]
      have fits := Nat.le_pow_clog (by decide : 1 < 2) (rows.size + 1)
      omega
  · cases preprocessed
