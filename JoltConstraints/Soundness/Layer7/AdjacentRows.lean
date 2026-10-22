import JoltConstraints.program_facts

/-! Transport local instruction-pair facts through materialization and concatenation.
No expansion checker is imported: its list property is a parameter.
Jolt's materializer stamps each sequence before concatenating the program rows;
see `jolt/crates/jolt-program/src/expand/materialize.rs:71-101,150-175` and
`jolt/crates/jolt-program/src/expand/mod.rs:281-307` at 8bbb2357. -/

set_option autoImplicit false

namespace JoltConstraints.Soundness.AdjacentRows

/-- Every selected item belongs to a consecutive pair satisfying `relation`.
`side = 0` selects the earlier item, and `side = 1` selects the later item.
For example, an advice load selects the earlier item of its load/multiply pair;
a register shift selects the later item of its mask/shift pair. -/
def Pairs {α : Type} (selected : α → Prop) (relation : α → α → Prop)
    (side : Fin 2) (items : List α) : Prop :=
  ∀ (k : Nat) (inRange : k < items.length), selected items[k] →
    ∃ j, ∃ next : j + 1 < items.length,
      k = j + side.val ∧ relation (items[j]'(by omega)) items[j + 1]

private theorem pairs_append {α : Type} (selected : α → Prop)
    (relation : α → α → Prop) (side : Fin 2) (front back : List α)
    (frontPairs : Pairs selected relation side front)
    (backPairs : Pairs selected relation side back) :
    Pairs selected relation side (front ++ back) := by
  intro k inRange choose
  rw [List.length_append] at inRange
  by_cases inFront : k < front.length
  · rw [List.getElem_append_left inFront] at choose
    obtain ⟨j, next, position, related⟩ := frontPairs k inFront choose
    refine ⟨j, by simp only [List.length_append]; omega, position, ?_⟩
    rw [List.getElem_append_left (by omega), List.getElem_append_left next]
    exact related
  · rw [List.getElem_append_right (by omega)] at choose
    obtain ⟨j, next, position, related⟩ := backPairs (k - front.length) (by omega) choose
    refine ⟨front.length + j, by simp only [List.length_append]; omega, by omega, ?_⟩
    rw [List.getElem_append_right (by omega), List.getElem_append_right (by omega)]
    simpa only [Nat.add_sub_cancel_left, Nat.add_assoc] using related

private theorem pairs_flatten {α : Type} (selected : α → Prop)
    (relation : α → α → Prop) (side : Fin 2) (chunks : List (List α))
    (each : ∀ chunk ∈ chunks, Pairs selected relation side chunk) :
    Pairs selected relation side chunks.flatten := by
  induction chunks with
  | nil => intro k inRange; simp at inRange
  | cons front rest ih =>
    exact pairs_append selected relation side front rest.flatten
      (each front List.mem_cons_self)
      (ih (fun chunk member => each chunk (List.mem_cons_of_mem _ member)))

/-- Lift an arbitrary instruction-list property `property` to its materialized rows.
The supplied `pairs` consequence identifies adjacent instructions within that list.
The earlier row continues its expansion and the later row does not start a source.
For example, a load followed by a multiply has positive countdown at the load.
Only `ExpandedRows` metadata and the rows' instructions are used. -/
theorem materialized_pairs (property : List JoltISA.Instr → Prop)
    (selected : JoltISA.Instr → Prop) (relation : JoltISA.Instr → JoltISA.Instr → Prop)
    (side : Fin 2)
    (pairs : ∀ instructions, property instructions → Pairs selected relation side instructions)
    (rows : List JoltInstructionRow) (address : BitVec 64) (compressed : Bool)
    (layout : ExpandedRows address compressed rows)
    (holds : property (rows.map (·.instruction))) :
    Pairs (fun row => selected row.instruction)
      (fun first second => relation first.instruction second.instruction ∧
        first.continues = true ∧ second.starts_source = false) side rows := by
  intro k inRange choose
  obtain ⟨j, next, position, related⟩ := pairs _ holds k
    (by simpa only [List.length_map] using inRange)
    (by simpa only [List.getElem_map] using choose)
  simp only [List.length_map] at next
  simp only [List.getElem_map] at related
  refine ⟨j, next, position, related, ?_, ?_⟩
  · have countdown := layout.countdown j (by omega)
    simp only [JoltInstructionRow.continues, bne_iff_ne]
    intro zero
    rw [zero] at countdown
    change 0 = rows.length - 1 - j at countdown
    omega
  · rw [layout.starts (j + 1) next]
    simp

/-- Lift a list property of every materialized expansion to the program's bytecode.
`pairs` interprets that property as adjacent instruction pairs, choosing either
the earlier (`side = 0`) or later (`side = 1`) instruction.
For example, a future advice checker can supply load/multiply pairs without this
theorem knowing that checker's definition.
Every resulting pair stays within one expansion, as witnessed by continuation
of its earlier row and the later row's false `starts_source` flag. -/
theorem expand_program_pairs (property : List JoltISA.Instr → Prop)
    (selected : JoltISA.Instr → Prop) (relation : JoltISA.Instr → JoltISA.Instr → Prop)
    (side : Fin 2)
    (pairs : ∀ instructions, property instructions → Pairs selected relation side instructions)
    (each : ∀ source rows, expand_instruction source = some rows →
      property (rows.map (·.instruction)))
    (image : Rv64ProgramImage SourceInstruction) (bytecode : Array JoltInstructionRow)
    (expanded : expand_program image = some bytecode) :
    Pairs (fun row => selected row.instruction)
      (fun first second => relation first.instruction second.instruction ∧
        first.continues = true ∧ second.starts_source = false) side bytecode.toList := by
  unfold expand_program at expanded
  cases mapped : image.instructions.toList.mapM expand_instruction with
  | none => rw [mapped] at expanded; cases expanded
  | some chunks =>
    rw [mapped, Option.map_some, Option.some.injEq] at expanded
    subst expanded
    rw [List.toList_toArray]
    apply pairs_flatten
    intro rows member
    obtain ⟨k, inRange, rfl⟩ := List.mem_iff_getElem.mp member
    obtain ⟨lengths, steps⟩ := option_mapM_results expand_instruction _ chunks mapped
    have step := steps k (by omega) inRange
    exact materialized_pairs property selected relation side pairs _ _ _
      (expand_instruction_expandedRows _ _ step) (each _ _ step)

end JoltConstraints.Soundness.AdjacentRows
