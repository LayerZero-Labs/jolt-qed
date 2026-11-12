import JoltConstraints.program_facts
import JoltConstraints.inline_rows_ok

open LeanRV64D

/-!
# Preprocessing a registered inline

Rust's `BytecodePCMapper::try_new` rejects a run of rows at one address unless the
rows count down to 0 in 16 bits. Registered inlines are the longest sequences one
source instruction expands to, so this file checks that the model's capacity and
countdown let preprocessing accept them. `expand_instruction_preprocess` covers any
one source instruction at a valid address, and `keccak256AbsorbPermute_preprocess`
applies it to the longest supported inline, KECCAK256_ABSORB_PERMUTE (3,121 rows).
See jolt/crates/jolt-program/src/preprocess/bytecode.rs:119-205 at a6b6dc717.
-/

set_option autoImplicit false

/-- Preprocessing accepts the rows of one source instruction at a valid address.
For example, `ADD x1 x2 x3` at `RAM_START_ADDRESS` expands to one row, and preprocessing
gives the leading NoOp and that row, with no padding NoOps. -/
theorem expand_instruction_preprocess (source : SourceInstructionRow SourceInstruction)
    (rows : List JoltInstructionRow) (expanded : expand_instruction source = some rows)
    (addressOk : bytecode_address_ok source.address = true) :
    (preprocess rows.toArray).isSome = true := by
  have nonempty := expand_instruction_nonempty source rows expanded
  have same := expand_instruction_address source rows expanded
  have short := expand_instruction_length_le source rows expanded
  have split : rows.splitBy (fun a b : JoltInstructionRow => a.address == b.address) =
      [rows] :=
    List.splitBy_of_isChain nonempty (same_address_chain rows source.address same)
  have countdown : valid_run rows = true := by
    unfold valid_run
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.length_map]
    refine ⟨?_, by omega⟩
    apply List.ext_getElem (by simp)
    intro k inMap inRange
    simp only [List.getElem_map, List.getElem_reverse, List.getElem_range,
      List.length_range]
    rw [expand_instruction_countdown source rows expanded k (by simpa using inMap)]
  have firstAddress : rows.head?.map (·.address) = some source.address := by
    cases rows with
    | nil => exact absurd rfl nonempty
    | cons first _ => simp [same first List.mem_cons_self]
  unfold preprocess pc_map_ok
  simp only [split, List.all_cons, List.all_nil, Bool.and_true,
    List.filterMap_cons, List.filterMap_nil, firstAddress, List.nodup_singleton,
    decide_true, countdown, List.size_toArray]
  have allOk : rows.all (fun row => bytecode_address_ok row.address) = true :=
    List.all_eq_true.mpr fun row member => by rw [same row member]; exact addressOk
  simp only [allOk, Bool.true_and, decide_eq_true_eq]
  rw [ite_eq_left (by omega)]
  rfl

/-- KECCAK256_ABSORB_PERMUTE expands to its 3,121 rows at any valid address, whether
or not its encoding is compressed and whatever its registers, and preprocessing
accepts them. For example, the `rd = x0` form with `rs1 = x10` and `rs2 = x11` at
`RAM_START_ADDRESS` preprocesses. -/
theorem keccak256AbsorbPermute_preprocess (address : BitVec 64) (compressed : Bool)
    (rs1 rs2 rd : regidx) (addressOk : bytecode_address_ok address = true) :
    ∃ rows, expand_instruction
        ⟨address, .inline .keccak256AbsorbPermute rs1 rs2 rd, compressed⟩ = some rows ∧
      rows.length = 3121 ∧ (preprocess rows.toArray).isSome = true := by
  have length := JoltISA.Inlines.InlineKey.expandRows_length .keccak256AbsorbPermute rs1 rs2 rd
  have expanded : expand_instruction
      ⟨address, .inline .keccak256AbsorbPermute rs1 rs2 rd, compressed⟩ =
      some (stamp_sequence address compressed
        (JoltISA.Inlines.InlineKey.expandRows .keccak256AbsorbPermute rs1 rs2 rd)) := by
    have notEmpty : (JoltISA.Inlines.InlineKey.expandRows .keccak256AbsorbPermute rs1 rs2
        rd).isEmpty = false := by
      rw [List.isEmpty_eq_false_iff_exists_mem]
      exact List.exists_mem_of_length_pos (by rw [length]; decide)
    simp only [expand_instruction, SourceInstruction.expand, notEmpty,
      SourceInstruction.rowCapacity, MAX_INLINE_ROWS_PER_SOURCE, length,
      JoltISA.Inlines.InlineKey.rowCount, Bool.false_or]
    rfl
  refine ⟨_, expanded, ?_, expand_instruction_preprocess _ _ expanded addressOk⟩
  simp only [stamp_sequence, List.length_map, List.length_zipIdx, length,
    JoltISA.Inlines.InlineKey.rowCount]
