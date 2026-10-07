/-
How an accepted program's bytecode rows are laid out: where a source instruction's
rows end and how one row leads to the next. Proved from program_facts.lean; nothing
here is assumed.
-/
import JoltConstraints.program_facts
import JoltConstraints.honest_trace

set_option autoImplicit false

-- Every expanded program is its instructions' rows laid end to end, and each
-- instruction's rows are its expanded rows.
theorem expand_program_flatten (image : Rv64ProgramImage SourceInstruction)
    (bytecode : Array JoltInstructionRow) (expanded : expand_program image = some bytecode) :
    ∃ instructions : List (List JoltInstructionRow),
      bytecode = instructions.flatten.toArray ∧
      ∀ rows ∈ instructions, ∃ address is_compressed, ExpandedRows address is_compressed rows := by
  obtain ⟨instructions, isFlatten, _, each⟩ := expand_program_rows image bytecode expanded
  refine ⟨instructions, isFlatten, fun rows member => ?_⟩
  obtain ⟨position, inRows, atPosition⟩ := List.mem_iff_getElem.mp member
  exact ⟨_, _, atPosition ▸ each position (by omega) inRows⟩

-- The layout facts the completeness proofs use about bytecode rows.
structure BytecodeLayout (bytecode : Array JoltInstructionRow) : Prop where
  -- An instruction's rows stay inside the bytecode.
  endInBounds : ∀ i : Fin bytecode.size,
    i.val + (bytecode[i].virtual_sequence_remaining.getD 0).toNat < bytecode.size
  -- A row that continues is followed by the next row of the same instruction: same
  -- address, count one lower, not a first row; and only a last row is compressed.
  next : ∀ i j : Fin bytecode.size, j.val = i.val + 1 → bytecode[i].continues = true →
    bytecode[j].address = bytecode[i].address ∧
    bytecode[j].virtual_sequence_remaining =
      some (bytecode[i].virtual_sequence_remaining.getD 0 - 1) ∧
    bytecode[j].is_first_in_sequence = false ∧
    bytecode[i].is_compressed = false
  -- A row with no countdown is a native row, so it is not first in a sequence.
  ordinary : ∀ i : Fin bytecode.size,
    bytecode[i].virtual_sequence_remaining = none → bytecode[i].is_first_in_sequence = false

-- The rows Rust's expansion produces have this layout.
theorem expand_program_layout (image : Rv64ProgramImage SourceInstruction)
    (bytecode : Array JoltInstructionRow) (expanded : expand_program image = some bytecode) :
    BytecodeLayout bytecode := by
  obtain ⟨instructions, isFlatten, valid⟩ := expand_program_flatten image bytecode expanded
  subst isFlatten
  constructor
  · -- the rows of an instruction end inside the bytecode
    intro i
    have bound := rows_end_in_bounds instructions valid i.val (by simpa using i.isLt)
    simpa only [Fin.getElem_fin, List.getElem_toArray, List.size_toArray] using bound
  · -- a continuing row is followed by the next row of its instruction
    intro i j isNext continues
    have inRange : i.val + 1 < instructions.flatten.length := by
      have := j.isLt
      simp only [List.size_toArray] at this
      omega
    have notLast : instructions.flatten[i.val].virtual_sequence_remaining.getD 0 ≠ 0 := by
      simpa only [JoltInstructionRow.continues, Fin.getElem_fin, List.getElem_toArray,
        bne_iff_ne, ne_eq] using continues
    obtain ⟨sameAddress, countDown, notStart, notCompressed⟩ :=
      rows_next instructions valid i.val inRange notLast
    have jIs : (instructions.flatten.toArray)[j] = instructions.flatten[i.val + 1] := by
      simp only [Fin.getElem_fin, List.getElem_toArray, isNext]
    have iIs : (instructions.flatten.toArray)[i] = instructions.flatten[i.val] := by
      simp only [Fin.getElem_fin, List.getElem_toArray]
    rw [jIs, iIs]
    -- the next row is not a first row, so it has a count and is not first in sequence
    unfold JoltInstructionRow.starts_source at notStart
    simp only [Bool.or_eq_false_iff] at notStart
    obtain ⟨hasCount, notFirst⟩ := notStart
    obtain ⟨count, isCount⟩ :
        ∃ count, instructions.flatten[i.val + 1].virtual_sequence_remaining = some count := by
      cases hasValue : instructions.flatten[i.val + 1].virtual_sequence_remaining with
      | none =>
        rw [hasValue] at hasCount
        exact absurd hasCount (by decide)
      | some count => exact ⟨count, rfl⟩
    refine ⟨sameAddress, ?_, notFirst, notCompressed⟩
    -- its count is one lower
    rw [isCount]
    rw [isCount, Option.getD_some] at countDown
    have positive : (1 : BitVec 16) ≤ instructions.flatten[i.val].virtual_sequence_remaining.getD 0 := by
      rw [BitVec.le_def]
      have := BitVec.toNat_ne_iff_ne.mpr notLast
      have zero : (0 : BitVec 16).toNat = 0 := rfl
      have one : (1 : BitVec 16).toNat = 1 := rfl
      omega
    congr 1
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub_of_le positive, countDown]
    rfl
  · -- a row without a countdown is native, so not first in a sequence
    intro i noCount
    have member : (instructions.flatten.toArray)[i] ∈ instructions.flatten := by
      simp only [Fin.getElem_fin, List.getElem_toArray]
      exact List.getElem_mem _
    obtain ⟨rows, inInstructions, inRows⟩ := List.mem_flatten.mp member
    obtain ⟨k, inRange, atK⟩ := List.mem_iff_getElem.mp inRows
    obtain ⟨_, _, expandedRows⟩ := valid rows inInstructions
    rw [← atK] at noCount ⊢
    exact expandedRows.ordinary k inRange noCount

-- The bytecode of an honest trace has this layout.
theorem HonestTrace.layout {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs) :
    BytecodeLayout trace.bytecode :=
  expand_program_layout joltInstance.program trace.bytecode trace.expands

-- In rows laid end to end, every row comes from a source instruction with the row's
-- address, and the row's countdown ends on that instruction's last row, which carries
-- the instruction's compressed flag.
theorem rows_source_of_row (instructions : List (List JoltInstructionRow))
    (sources : List (SourceInstructionRow SourceInstruction))
    (lengths : instructions.length = sources.length)
    (each : ∀ (position : Nat) (inSources : position < sources.length)
      (inRows : position < instructions.length),
      ExpandedRows sources[position].address sources[position].is_compressed
        instructions[position])
    (i : Nat) (inRange : i < instructions.flatten.length) :
    ∃ source ∈ sources, instructions.flatten[i].address = source.address ∧
      (instructions.flatten[i +
          (instructions.flatten[i].virtual_sequence_remaining.getD 0).toNat]?.map
            (·.is_compressed)).getD false = source.is_compressed := by
  induction instructions generalizing sources i with
  | nil =>
    simp only [List.flatten_nil, List.length_nil] at inRange
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
      simp only [List.flatten_cons, List.length_append] at inRange ⊢
      by_cases inside : i < rows.length
      · -- the row belongs to this instruction: its last row is the instruction's last row
        refine ⟨source, List.mem_cons_self, ?_, ?_⟩
        · rw [List.getElem_append_left inside]
          exact firstRows.same_address _ (List.getElem_mem _)
        · rw [List.getElem_append_left inside, firstRows.countdown i inside]
          have lastInside : i + (rows.length - 1 - i) < rows.length := by omega
          rw [List.getElem?_append_left lastInside, List.getElem?_eq_getElem lastInside,
            Option.map_some, Option.getD_some, firstRows.compressed _ lastInside]
          have lastIs : i + (rows.length - 1 - i) = rows.length - 1 := by omega
          simp only [lastIs, beq_self_eq_true, Bool.true_and]
      · -- the row belongs to a later instruction: use the same fact for the rest
        have outside : rows.length ≤ i := by omega
        obtain ⟨later, member, sameAddress, sameFlag⟩ :=
          ih moreSources lengthsRest eachRest (i - rows.length) (by omega)
        refine ⟨later, List.mem_cons_of_mem _ member, ?_, ?_⟩
        · rw [List.getElem_append_right outside]
          exact sameAddress
        · rw [List.getElem_append_right outside, List.getElem?_append_right (by omega)]
          have shift : i + (rest.flatten[i - rows.length].virtual_sequence_remaining.getD 0).toNat -
              rows.length = i - rows.length +
                (rest.flatten[i - rows.length].virtual_sequence_remaining.getD 0).toNat := by
            omega
          rw [shift]
          exact sameFlag

-- No row's source instruction has a next PC past 2^64, given the image's NextPCNoWrap
-- (assumed, see program_fresh.lean).
theorem expand_program_next_pc_no_wrap (image : Rv64ProgramImage SourceInstruction)
    (bytecode : Array JoltInstructionRow) (expanded : expand_program image = some bytecode)
    (noWrap : image.NextPCNoWrap) (i : Fin bytecode.size) :
    bytecode[i].address.toNat + (if source_is_compressed bytecode i then 2 else 4) < 2 ^ 64 := by
  obtain ⟨instructions, isFlatten, lengths, each⟩ := expand_program_rows image bytecode expanded
  subst isFlatten
  have inRange : i.val < instructions.flatten.length := by
    have := i.isLt
    simp only [List.size_toArray] at this
    exact this
  obtain ⟨source, member, sameAddress, sameFlag⟩ := rows_source_of_row instructions
    image.instructions.toList (by rw [lengths, Array.length_toList])
    (fun position inSources inRows => by
      rw [Array.getElem_toList (by rw [Array.length_toList] at inSources; exact inSources)]
      exact each position (by rw [Array.length_toList] at inSources; exact inSources) inRows)
    i.val inRange
  unfold source_is_compressed
  simp only [Fin.getElem_fin, List.getElem_toArray, List.getElem?_toArray]
  rw [sameAddress, sameFlag]
  exact noWrap source (Array.mem_toList_iff.mp member)

-- In an honest trace, no row's source instruction has a next PC past 2^64.
theorem HonestTrace.next_pc_no_wrap {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (noWrap : joltInstance.program.NextPCNoWrap) (i : Fin trace.bytecode.size) :
    trace.bytecode[i].address.toNat +
      (if source_is_compressed trace.bytecode i then 2 else 4) < 2 ^ 64 :=
  expand_program_next_pc_no_wrap joltInstance.program trace.bytecode trace.expands noWrap i
