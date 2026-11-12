import JoltConstraints.program_facts

open LeanRV64D

/-! Transport local facts about windows of consecutive instructions through
materialization and concatenation.
No expansion checker is imported: its list property is a parameter.
Jolt's materializer stamps each sequence before concatenating the program rows;
see `jolt/crates/jolt-program/src/expand/materialize.rs:71-101,150-175` and
`jolt/crates/jolt-program/src/expand/mod.rs:281-307` at 8bbb2357. -/

set_option autoImplicit false

namespace JoltConstraints.Soundness.AdjacentRows

/-- Index `i` of a window starting at `j` stays inside a list that holds the window.
For example, a window of width 3 starting at `j = 4` in a list of length 7 has its last
index `4 + 2 = 6 < 7`. -/
theorem window_bound {length j width : Nat} (fits : j + width ≤ length) (i : Fin width) :
    j + i.val < length := by
  have := i.isLt
  omega

/-- Every selected item sits at position `side` of a window of `width` consecutive items
satisfying `relation`.
For example, a narrow load selects the first item of its load/mask/consumer window. -/
def Windows {α : Type} (selected : α → Prop) {width : Nat}
    (relation : (Fin width → α) → Prop) (side : Fin width) (items : List α) : Prop :=
  ∀ (k : Nat) (inRange : k < items.length), selected items[k] →
    ∃ j, ∃ fits : j + width ≤ items.length,
      k = j + side.val ∧ relation (fun i => items[j + i.val]'(window_bound fits i))

/-- Every selected item belongs to a consecutive pair satisfying `relation`.
`side = 0` selects the earlier item, and `side = 1` selects the later item.
For example, an advice load selects the earlier item of its load/multiply pair;
a register shift selects the later item of its mask/shift pair. -/
def Pairs {α : Type} (selected : α → Prop) (relation : α → α → Prop)
    (side : Fin 2) (items : List α) : Prop :=
  ∀ (k : Nat) (inRange : k < items.length), selected items[k] →
    ∃ j, ∃ next : j + 1 < items.length,
      k = j + side.val ∧ relation (items[j]'(by omega)) items[j + 1]

private theorem windows_append {α : Type} (selected : α → Prop) {width : Nat}
    (relation : (Fin width → α) → Prop) (side : Fin width) (front back : List α)
    (frontWindows : Windows selected relation side front)
    (backWindows : Windows selected relation side back) :
    Windows selected relation side (front ++ back) := by
  intro k inRange choose
  rw [List.length_append] at inRange
  by_cases inFront : k < front.length
  · rw [List.getElem_append_left inFront] at choose
    obtain ⟨j, fits, position, related⟩ := frontWindows k inFront choose
    have bound : j + width ≤ (front ++ back).length := by
      simp only [List.length_append]; omega
    refine ⟨j, bound, position, ?_⟩
    have same : (fun i : Fin width => (front ++ back)[j + i.val]'(window_bound bound i)) =
        fun i => front[j + i.val]'(window_bound fits i) :=
      funext fun i => List.getElem_append_left (window_bound fits i)
    rw [same]
    exact related
  · rw [List.getElem_append_right (by omega)] at choose
    obtain ⟨j, fits, position, related⟩ := backWindows (k - front.length) (by omega) choose
    have bound : front.length + j + width ≤ (front ++ back).length := by
      simp only [List.length_append]; omega
    refine ⟨front.length + j, bound, by omega, ?_⟩
    have same : (fun i : Fin width =>
          (front ++ back)[front.length + j + i.val]'(window_bound bound i)) =
        fun i => back[j + i.val]'(window_bound fits i) := by
      funext i
      rw [List.getElem_append_right (by omega)]
      simp only [Nat.add_assoc, Nat.add_sub_cancel_left]
    rw [same]
    exact related

private theorem windows_flatten {α : Type} (selected : α → Prop) {width : Nat}
    (relation : (Fin width → α) → Prop) (side : Fin width) (chunks : List (List α))
    (each : ∀ chunk ∈ chunks, Windows selected relation side chunk) :
    Windows selected relation side chunks.flatten := by
  induction chunks with
  | nil => intro k inRange; simp at inRange
  | cons front rest ih =>
    exact windows_append selected relation side front rest.flatten
      (each front List.mem_cons_self)
      (ih (fun chunk member => each chunk (List.mem_cons_of_mem _ member)))

/-- A window of rows inside one source instruction's expansion whose instructions satisfy
`relation`.
Every row but the last continues the expansion, and no row after the first starts a
source instruction.
For example, the three rows of an `LB` expansion (`VirtualLoadB`, `VirtualWindowMaskB`,
`VirtualPextSigned`) form such a window: the first two continue the expansion, and the
last two do not start a source instruction. -/
def WithinSource {width : Nat} (relation : (Fin width → JoltISA.Instr) → Prop)
    (window : Fin width → JoltInstructionRow) : Prop :=
  relation (fun i => (window i).instruction) ∧
    (∀ i : Fin width, i.val + 1 < width → (window i).continues = true) ∧
    (∀ i : Fin width, 0 < i.val → (window i).starts_source = false)

/-- Lift an arbitrary instruction-list property `property` to its materialized rows.
The supplied `windows` consequence identifies windows of consecutive instructions within
that list.
Only `ExpandedRows` metadata and the rows' instructions are used.
For example, with `property := fun l => ExpansionFacts.loadWindowsOk l = true`, it turns
the load windows of one expansion's instruction list into load windows of its
materialized rows. -/
theorem materialized_windows (property : List JoltISA.Instr → Prop)
    (selected : JoltISA.Instr → Prop) {width : Nat}
    (relation : (Fin width → JoltISA.Instr) → Prop) (side : Fin width)
    (windows : ∀ instructions, property instructions →
      Windows selected relation side instructions)
    (rows : List JoltInstructionRow) (address : BitVec 64) (compressed : Bool)
    (layout : ExpandedRows address compressed rows)
    (holds : property (rows.map (·.instruction))) :
    Windows (fun row => selected row.instruction) (WithinSource relation) side rows := by
  intro k inRange choose
  obtain ⟨j, fits, position, related⟩ := windows _ holds k
    (by simpa only [List.length_map] using inRange)
    (by simpa only [List.getElem_map] using choose)
  simp only [List.length_map] at fits
  refine ⟨j, fits, position, by simpa only [List.getElem_map] using related, ?_, ?_⟩
  · intro i last
    have countdown := layout.countdown (j + i.val) (by omega)
    simp only [JoltInstructionRow.continues, bne_iff_ne]
    intro zero
    rw [zero] at countdown
    change 0 = rows.length - 1 - (j + i.val) at countdown
    omega
  · intro i later
    rw [layout.starts (j + i.val) (window_bound fits i)]
    exact beq_false_of_ne (by omega)

/-- Lift a list property of every materialized expansion to the program's bytecode.
`windows` interprets that property as windows of consecutive instructions.
Every resulting window stays within one expansion, as witnessed by continuation of all
but its last row and the false `starts_source` flag of all but its first row.
For example, `expand_program_loadWindows` uses it with the width-3 relation `LoadWindow`
to place every narrow load of the program at the start of a load window inside its own
expansion. -/
theorem expand_program_windows (property : List JoltISA.Instr → Prop)
    (selected : JoltISA.Instr → Prop) {width : Nat}
    (relation : (Fin width → JoltISA.Instr) → Prop) (side : Fin width)
    (windows : ∀ instructions, property instructions →
      Windows selected relation side instructions)
    (each : ∀ source rows, expand_instruction source = some rows →
      property (rows.map (·.instruction)))
    (image : Rv64ProgramImage SourceInstruction) (bytecode : Array JoltInstructionRow)
    (expanded : expand_program image = some bytecode) :
    Windows (fun row => selected row.instruction) (WithinSource relation) side
      bytecode.toList := by
  unfold expand_program at expanded
  cases mapped : image.instructions.toList.mapM expand_instruction with
  | none => rw [mapped] at expanded; cases expanded
  | some chunks =>
    rw [mapped, Option.map_some, Option.some.injEq] at expanded
    subst expanded
    rw [List.toList_toArray]
    apply windows_flatten
    intro rows member
    obtain ⟨k, inRange, rfl⟩ := List.mem_iff_getElem.mp member
    obtain ⟨lengths, steps⟩ := option_mapM_results expand_instruction _ chunks mapped
    have step := steps k (by omega) inRange
    exact materialized_windows property selected relation side windows _ _ _
      (expand_instruction_expandedRows _ _ step) (each _ _ step)

/-- Lift a list property of every materialized expansion to adjacent bytecode pairs.
`pairs` interprets that property as adjacent instruction pairs, choosing either
the earlier (`side = 0`) or later (`side = 1`) instruction.
For example, a future advice checker can supply load/multiply pairs without this
theorem knowing that checker's definition.
This is the width-two case of `expand_program_windows`. -/
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
  have windows := expand_program_windows property selected
    (fun window : Fin 2 → JoltISA.Instr => relation (window 0) (window 1)) side
    (by
      intro instructions holds k inRange choose
      obtain ⟨j, next, position, related⟩ := pairs instructions holds k inRange choose
      exact ⟨j, by omega, position, by simpa using related⟩)
    each image bytecode expanded
  intro k inRange choose
  obtain ⟨j, fits, position, related, continues, starts⟩ := windows k inRange choose
  exact ⟨j, by omega, position, by simpa using related,
    by simpa using continues 0 (by decide), by simpa using starts 1 (by decide)⟩

end JoltConstraints.Soundness.AdjacentRows
