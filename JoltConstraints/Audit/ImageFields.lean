import JoltConstraints.theorems.WholeRun.Elf

/-!
# Image fields that the transcription of `decode_elf` guarantees

`Rv64ProgramImage` carries four proof fields. Each one states a fact of Jolt's ELF loader
(Jolt at ff6fc6568: `crates/jolt-program/src/image/elf.rs` (`decode_elf`,
`decode_text_section`)). Since the ELF loader is transcribed (`ElfSections.layout?` in
`JoltConstraints/theorems/WholeRun/Elf.lean`), those facts should follow from it. This file
proves three of them from the transcription alone, without reading the fields:

* `next_pc_no_wrap`: `Rv64ProgramImage.DecodedFrom.nextPCNoWrap`;
* `instruction_loaded`: `Rv64ProgramImage.DecodedFrom.instructionLoaded`;
* `program_end_ge_ram_start`: `Rv64ProgramImage.DecodedFrom.programEndGeRamStart`.

The fourth, `memory_init_in_program`, does not follow: `ElfSection` records that a loaded text
section has exactly `size` bytes of data, but says nothing about the data of other sections.
`JoltConstraints.Audit.memoryInitInProgram_not_derived` (`JoltConstraints/Audit/Necessity.lean`)
gives a parsed ELF whose layout breaks it.

Each fact is first proved for the layout (`ElfSections.layout?_…`), where nothing else could
supply it, and then for a program that agrees with the layout.
-/

set_option autoImplicit false

namespace WholeRun

/-- A byte that `lastByte` finds comes from an entry at that address.
For example, `lastByte [(0x80000000, 1)] 0x80000000 = some 1` comes from the only entry. -/
theorem exists_of_lastByte_isSome {l : List (BitVec 64 × BitVec 8)} {a : Nat}
    (h : (lastByte l a).isSome) : ∃ e ∈ l, e.1.toNat = a := by
  induction l with
  | nil => simp [lastByte] at h
  | cons x t ih =>
    simp only [lastByte] at h
    split at h
    · rename_i b hb
      obtain ⟨e, he, hea⟩ := ih (by simp [hb])
      exact ⟨e, List.mem_cons_of_mem _ he, hea⟩
    · split at h
      · exact ⟨x, by simp, by assumption⟩
      · simp at h

/-- `rangeBytes` gives one byte per address of the range.
For example, the range `(0x80000000, 0x80000004)` gives four bytes. -/
theorem rangeBytes_length (memoryInit : List (BitVec 64 × BitVec 8)) (range : Nat × Nat) :
    (rangeBytes memoryInit range).length = range.2 - range.1 := by
  simp [rangeBytes]

/-- **Every instruction `decodeText` finds lies inside the decoded bytes.** It starts at or
after `address` and ends, after its 2 or 4 bytes, at or before the end of the bytes.
For example, the four bytes of `addi x1, x0, 1` at `0x80000000` give one word at
`0x80000000`, which ends at `0x80000004`. -/
theorem decodeText_extent :
    ∀ (address : Nat) (bytes : List (BitVec 8)) (parcels : List (Nat × BlockEncoding)),
      decodeText address bytes = some parcels → ∀ p ∈ parcels,
        address ≤ p.1 ∧ p.1 + (if p.2.isCompressed then 2 else 4) ≤ address + bytes.length
  | _, [], _, hdecode => by
    simp only [decodeText, Option.some.injEq] at hdecode
    subst hdecode
    simp
  | _, [_], _, hdecode => by simp [decodeText] at hdecode
  | address, b0 :: b1 :: rest, parcels, hdecode => by
    unfold decodeText at hdecode
    split at hdecode
    · cases hdecode
    split at hdecode
    · obtain ⟨tail, htail, rfl⟩ := Option.map_eq_some_iff.mp hdecode
      have ih := decodeText_extent (address + 2) rest tail htail
      intro p hp
      split at hp
      · have := ih p hp
        simp only [List.length_cons]
        omega
      · rcases List.mem_cons.mp hp with rfl | hp
        · simp only [BlockEncoding.isCompressed, List.length_cons, ite_true]
          omega
        · have := ih p hp
          simp only [List.length_cons]
          omega
    · split at hdecode
      · rename_i b2 b3 rest'
        obtain ⟨tail, htail, rfl⟩ := Option.map_eq_some_iff.mp hdecode
        have ih := decodeText_extent (address + 4) rest' tail htail
        intro p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · simp only [BlockEncoding.isCompressed, List.length_cons, Bool.false_eq_true, ite_false]
          omega
        · have := ih p hp
          simp only [List.length_cons]
          omega
      · simp at hdecode
termination_by _ bytes => bytes.length

/-- An instruction is 2 or 4 bytes long, so at least 2. -/
theorem two_le_width (e : BlockEncoding) : 2 ≤ (if e.isCompressed then 2 else 4) := by
  split <;> omega

/-- **Every byte of every instruction of the layout lies in a loaded text section.**
For example, the four bytes of the word at `0x80000000` in a one-instruction `.text` section at
`0x80000000` lie in that section. -/
theorem ElfSections.layout?_parcel_in_section {elf : ElfSections} {layout : ElfLayout}
    (h : elf.layout? = some layout) {p : Nat × BlockEncoding} (hp : p ∈ layout.parcels)
    {a : Nat} (hstart : p.1 ≤ a) (hlt : a < p.1 + (if p.2.isCompressed then 2 else 4)) :
    ∃ section_ ∈ elf.loaded, section_.isText = true ∧ section_.address.toNat ≤ a ∧
      a < section_.endAddress := by
  obtain ⟨-, -, range, hrange, dataRanges, segment, hsegment, ps, hdecode, hpin⟩ :=
    ElfSections.layout?_parcel h hp
  have hext := decodeText_extent segment.1 _ ps hdecode p hpin
  rw [rangeBytes_length] at hext
  have hw := two_le_width p.2
  obtain ⟨hr1, hr2⟩ := textSegments_within hsegment (a := a) (by omega) (by omega)
  obtain ⟨q, hq, hq1, hq2⟩ := mergeRanges_covered hrange hr1 hr2
  simp only [List.mem_map, List.mem_filter] at hq
  obtain ⟨section_, ⟨hloaded, htext⟩, rfl⟩ := hq
  exact ⟨section_, hloaded, htext, hq1, hq2⟩

/-- **No instruction of the layout ends past `2^64`.** Its last byte lies in a loaded section,
and `decode_elf` rejects a section that ends past `2^64`.
For example, a text section at `2^64 - 4` of size 4 ends at `2^64` and is rejected, so no
instruction of an accepted ELF sits there. -/
theorem ElfSections.layout?_next_pc_no_wrap {elf : ElfSections} {layout : ElfLayout}
    (h : elf.layout? = some layout) :
    ∀ p ∈ layout.parcels, p.1 + (if p.2.isCompressed then 2 else 4) < 2 ^ 64 := by
  intro p hp
  have hw := two_le_width p.2
  obtain ⟨section_, hloaded, -, -, hlt⟩ := ElfSections.layout?_parcel_in_section h hp
    (a := p.1 + (if p.2.isCompressed then 2 else 4) - 1) (by omega) (by omega)
  have hend := (ElfSections.layout?_parcel h hp).1 section_ hloaded
  omega

/-- **The memory image has a byte at the address of every instruction of the layout.** The
address lies in a loaded text section, whose data covers it.
For example, a one-instruction `.text` section at `0x80000000` puts a byte at `0x80000000`. -/
theorem ElfSections.layout?_parcel_loaded {elf : ElfSections} {layout : ElfLayout}
    (h : elf.layout? = some layout) :
    ∀ p ∈ layout.parcels, ∃ entry ∈ layout.memory_init, entry.1.toNat = p.1 := by
  intro p hp
  obtain ⟨hall, hinit, -⟩ := ElfSections.layout?_parcel h hp
  have hw := two_le_width p.2
  obtain ⟨section_, hloaded, htext, hstart, hlt⟩ :=
    ElfSections.layout?_parcel_in_section h hp (a := p.1) le_rfl (by omega)
  have hsome := ElfSection.lastByte_isSome (memoryInit := layout.memory_init)
    (fun e he => by rw [hinit]; exact List.mem_flatMap.mpr ⟨section_, hloaded, he⟩)
    (of_decide_eq_true (List.mem_filter.mp hloaded).2) htext (hall section_ hloaded)
    hstart hlt
  exact exists_of_lastByte_isSome hsome

/-- The layout's `program_end` is the largest end of a loaded section, at least
`RAM_START_ADDRESS`, and every loaded section ends below `2^64`.
For example, one section `[0x80000000, 0x80000004)` gives `program_end = 0x80000004`. -/
theorem ElfSections.layout?_program_end {elf : ElfSections} {layout : ElfLayout}
    (h : elf.layout? = some layout) :
    layout.program_end = BitVec.ofNat 64 (elf.loaded.foldl
      (fun e section_ => max e section_.endAddress) JoltISA.RAM_START_ADDRESS) ∧
    ∀ section_ ∈ elf.loaded, section_.endAddress < 2 ^ 64 := by
  dsimp only [ElfSections.layout?] at h
  split at h
  · rename_i hall
    obtain ⟨parcelLists, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨code, -, h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    · cases h
      exact ⟨rfl, fun section_ hs => of_decide_eq_true (List.all_eq_true.mp hall section_ hs)⟩
    · cases h
  · cases h

/-- A running maximum never drops below its start. -/
theorem le_foldl_max {α : Type} (f : α → Nat) :
    ∀ (l : List α) (init : Nat), init ≤ l.foldl (fun e x => max e (f x)) init
  | [], _ => le_rfl
  | x :: l, init => le_trans (le_max_left init (f x)) (le_foldl_max f l _)

/-- A running maximum of values below `bound`, started below `bound`, stays below `bound`. -/
theorem foldl_max_lt {α : Type} (f : α → Nat) {bound : Nat} :
    ∀ (l : List α) (init : Nat), init < bound → (∀ x ∈ l, f x < bound) →
      l.foldl (fun e x => max e (f x)) init < bound
  | [], _, h, _ => h
  | x :: l, _, h, hl =>
    foldl_max_lt f l _ (max_lt h (hl x (by simp))) (fun y hy => hl y (by simp [hy]))

/-! ## The fields, for a program built from the ELF -/

/-- **`next_pc_no_wrap` follows from `DecodedFrom`.** The proof reads only the layout, not the
field. For example, the ADDI row at `0x80000000` of a one-instruction `.text` section ends at
`0x80000004`. -/
theorem _root_.Rv64ProgramImage.DecodedFrom.nextPCNoWrap
    {program : Rv64ProgramImage SourceInstruction} {elf : ElfSections}
    (hdecoded : program.DecodedFrom elf) : program.NextPCNoWrap := by
  obtain ⟨layout, hlayout, -, -, -, hrows⟩ := hdecoded
  intro row hrow
  obtain ⟨p, hp, haddr, hcomp, -⟩ :=
    exists_of_forall₂_right hrows row (Array.mem_toList_iff.mpr hrow)
  rw [haddr, hcomp]
  exact ElfSections.layout?_next_pc_no_wrap hlayout p hp

/-- **`instruction_loaded` follows from `DecodedFrom`.** The memory image has a byte at every
row's own address. For example, the ADDI row at `0x80000000` has the byte `0x93` there. -/
theorem _root_.Rv64ProgramImage.DecodedFrom.instructionLoaded
    {program : Rv64ProgramImage SourceInstruction} {elf : ElfSections}
    (hdecoded : program.DecodedFrom elf) :
    ∀ row ∈ program.instructions, ∃ entry ∈ program.memory_init,
      row.address.toNat ≤ entry.1.toNat ∧ entry.1.toNat < row.address.toNat + 2 := by
  obtain ⟨layout, hlayout, hmem, -, -, hrows⟩ := hdecoded
  intro row hrow
  obtain ⟨p, hp, haddr, -, -⟩ :=
    exists_of_forall₂_right hrows row (Array.mem_toList_iff.mpr hrow)
  obtain ⟨entry, hentry, heq⟩ := ElfSections.layout?_parcel_loaded hlayout p hp
  refine ⟨entry, by rw [hmem]; exact hentry, by omega, by omega⟩

/-- **`program_end_ge_ram_start` follows from `DecodedFrom`.** `decode_elf` starts
`program_end` at `RAM_START_ADDRESS` and only raises it, and every section end it takes is
below `2^64`. For example, an ELF with no loaded section has `program_end = RAM_START_ADDRESS`. -/
theorem _root_.Rv64ProgramImage.DecodedFrom.programEndGeRamStart
    {program : Rv64ProgramImage SourceInstruction} {elf : ElfSections}
    (hdecoded : program.DecodedFrom elf) :
    JoltISA.RAM_START_ADDRESS ≤ program.program_end.toNat := by
  obtain ⟨layout, hlayout, -, hend, -, -⟩ := hdecoded
  obtain ⟨hpe, hall⟩ := ElfSections.layout?_program_end hlayout
  have hlt := foldl_max_lt ElfSection.endAddress elf.loaded JoltISA.RAM_START_ADDRESS
    (by norm_num [JoltISA.RAM_START_ADDRESS]) hall
  rw [hend, hpe, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  exact le_foldl_max _ _ _

end WholeRun
