import JoltConstraints.trace

set_option autoImplicit false

namespace JoltProgram.SequenceLayout

private theorem array_fin_index {α : Type} (a : Array α) (i : Fin a.size) :
    a[i] = a[i.val] := rfl

/-- Following a static countdown preserves its address and decreases its count.
Every row reached at a positive offset is inside the sequence, not an entry. -/
theorem row_at_offset {program : JoltProgram} (layout : program.SequenceLayout)
    (i j : Fin program.expandedBytecode.size) (offset : Nat)
    (index : j.val = i.val + offset)
    (within : offset ≤ (program.expandedBytecode[i.val].virtualSequenceRemaining.getD 0).toNat) :
    program.expandedBytecode[j.val].address = program.expandedBytecode[i.val].address ∧
    (program.expandedBytecode[j.val].virtualSequenceRemaining.getD 0).toNat =
      (program.expandedBytecode[i.val].virtualSequenceRemaining.getD 0).toNat - offset ∧
    (0 < offset → ¬ program.expandedBytecode[j.val].isEntry) := by
  induction offset generalizing j with
  | zero =>
      have : j = i := Fin.ext (by omega)
      subst j
      simp
  | succ offset ih =>
      let k : Fin program.expandedBytecode.size := ⟨i.val + offset, by omega⟩
      have prev := ih k rfl (by omega)
      have positive : 0 <
          (program.expandedBytecode[k.val].virtualSequenceRemaining.getD 0).toNat := by
        omega
      have continues : program.expandedBytecode[k.val].continues = true := by
        simp only [JoltProgramRow.continues, ne_eq, bne_iff_ne, ne_eq]
        intro hz
        rw [hz] at positive
        contradiction
      have step := layout.next k j (by dsimp [k]; omega) continues
      simp only [array_fin_index] at step
      refine ⟨step.1.trans prev.1, ?_, ?_⟩
      · have le : (1 : BitVec 16) ≤
            program.expandedBytecode[k.val].virtualSequenceRemaining.getD 0 := by
          exact BitVec.le_def.mpr (by simpa using positive)
        simp only [step.2.1, Option.getD_some, BitVec.toNat_sub_of_le le]
        change _ = _ - (offset + 1)
        have one : (1 : BitVec 16).toNat = 1 := rfl
        rw [one]
        omega
      · intro _
        simp [JoltProgramRow.isEntry, step.2.1, step.2.2.1]

/-- An entry row is the unique entry at its address. The proof uses Rust's
address/count uniqueness together with the existing descending-count layout. -/
theorem entry_address_unique {program : JoltProgram} (layout : program.SequenceLayout)
    (i j : Fin program.expandedBytecode.size)
    (hi : program.expandedBytecode[i.val].isEntry)
    (hj : program.expandedBytecode[j.val].isEntry)
    (address : program.expandedBytecode[i.val].address = program.expandedBytecode[j.val].address) :
    i = j := by
  suffices ordered : ∀ (a b : Fin program.expandedBytecode.size),
      program.expandedBytecode[a.val].isEntry →
      program.expandedBytecode[a.val].address = program.expandedBytecode[b.val].address →
      (program.expandedBytecode[a.val].virtualSequenceRemaining.getD 0).toNat ≤
        (program.expandedBytecode[b.val].virtualSequenceRemaining.getD 0).toNat → a = b by
    rcases le_total
        (program.expandedBytecode[i.val].virtualSequenceRemaining.getD 0).toNat
        (program.expandedBytecode[j.val].virtualSequenceRemaining.getD 0).toNat with h | h
    · exact ordered i j hi address h
    · exact (ordered j i hj address.symm h).symm
  intro a b ha hab hle
  let offset := (program.expandedBytecode[b.val].virtualSequenceRemaining.getD 0).toNat -
    (program.expandedBytecode[a.val].virtualSequenceRemaining.getD 0).toNat
  have offset_eq : offset +
      (program.expandedBytecode[a.val].virtualSequenceRemaining.getD 0).toNat =
      (program.expandedBytecode[b.val].virtualSequenceRemaining.getD 0).toNat :=
    Nat.sub_add_cancel hle
  have bound := layout.endInBounds b
  simp only [array_fin_index] at bound
  let k : Fin program.expandedBytecode.size := ⟨b.val + offset, by omega⟩
  have walk := layout.row_at_offset b k offset rfl (by omega)
  have counts : program.expandedBytecode[a.val].virtualSequenceRemaining.getD 0 =
      program.expandedBytecode[k.val].virtualSequenceRemaining.getD 0 := by
    apply BitVec.eq_of_toNat_eq
    omega
  have same : a = k := layout.addressSequenceUnique a k (hab.trans walk.1.symm) counts
  have zero : offset = 0 := by
    by_contra hn
    have notEntry := walk.2.2 (by omega)
    apply notEntry
    simpa only [← same] using ha
  apply Fin.ext
  have := congrArg Fin.val same
  dsimp [k] at this
  omega

end JoltProgram.SequenceLayout
