import JoltConstraints.WholeRun.Decoded

/-!
# The program image built from the ELF's sections

Jolt's `decode_elf` (`jolt/crates/jolt-program/src/image/elf.rs` at `c336a6da7`) builds the
program image from the guest ELF. This file transcribes it and proves that every image it builds
satisfies `ImageDecoded`. The whole-run theorems therefore need no premise on the decoder beyond
"the program was built from this ELF".

* `ElfSection`, `ElfSections`: the sections of the ELF and its entry point, as the `object` crate
  parses them. That parsing step stays trusted.
* `ElfSections.layout?`: `decode_elf` up to the call of `decode_instruction`. It gives the memory
  image, the program end, the entry point and the address and encoding of every instruction.
* `Rv64ProgramImage.DecodedFrom`: the program agrees with what `decode_elf` builds from the
  sections. Every program Jolt builds satisfies it.
* `Rv64ProgramImage.DecodedFrom.imageDecoded`: such a program satisfies `ImageDecoded`.

`decode_elf` reads each text range from its byte map with `unwrap_or(0)`. When `decode_elf`
succeeds, the `object` crate has given every loaded text section, at or above
`RAM_START_ADDRESS`, exactly `size` bytes of data (`ElfSection.text_data_length`). Every address
of a merged text range therefore has a byte, and the default never applies
(`mergeRanges_covered`, `ElfSection.lastByte_isSome`).
-/

set_option autoImplicit false

namespace WholeRun

/-! ## The parsed ELF -/

/-- **One section of the guest ELF**, as the `object` crate (0.40.0) reports it to `decode_elf`:
`address` is `section.address()`, `size` is `section.size()` and `isText` is
`section.kind() == SectionKind::Text`. For a section at or above `RAM_START_ADDRESS`, `data` is
`section.data()`. `decode_elf` never reads the data of a section below `RAM_START_ADDRESS`.
Below that address, `data` may be any list, for example `[]` when the section's file extent is
unreadable.

`text_data_length` records how the crate reads a text section that `decode_elf` loads.
`kind()` returns `Text` only for an `SHT_PROGBITS` section with `SHF_ALLOC` and `SHF_EXECINSTR`,
never for `SHT_NOBITS`. `data()` of a section that is not `SHT_NOBITS` returns exactly `sh_size`
bytes of the file or fails, and `decode_elf` reports a failure as "section data is not
readable".
See `object-0.40.0/src/read/elf/section.rs` (`ElfSection::kind`, `SectionHeader::data`).

For example, a `.text` section at `0x80000000` holding `addi x1, x0, 1` has `size = 4`,
`data = [0x93, 0x00, 0x10, 0x00]` and `isText = true`, while a `.bss` section has
`isText = false`, a nonzero `size` and `data = []`. -/
structure ElfSection where
  address : BitVec 64
  size : BitVec 64
  data : List (BitVec 8)
  isText : Bool
  text_data_length : JoltISA.RAM_START_ADDRESS ≤ address.toNat → isText = true →
    data.length = size.toNat

/-- **The parsed guest ELF**: its sections in section-header order and its entry point
(`obj.entry()`). Producing this from the file is the trusted parsing step.
For example, an ELF with one `.text` section at `0x80000000` and entry `0x80000000` has
`sections` of length one and `entry = 0x80000000`. -/
structure ElfSections where
  sections : List ElfSection
  entry : BitVec 64

/-- The end of a section, its address plus its size, as a natural number; `decode_elf` rejects
a section whose end is `2^64` or more. For example, a 4-byte section at `0x80000000` ends at
`0x80000004`. -/
def ElfSection.endAddress (section_ : ElfSection) : Nat :=
  section_.address.toNat + section_.size.toNat

/-- The `memory_init` entries of one section: each byte of its data at the section's address
plus its offset. For example, data `[0x93, 0x00]` at `0x80000000` gives
`[(0x80000000, 0x93), (0x80000001, 0x00)]`.
See : `jolt/crates/jolt-program/src/image/elf.rs` (`decode_elf`, `memory_init.extend`). -/
def ElfSection.bytes (section_ : ElfSection) : List (BitVec 64 × BitVec 8) :=
  section_.data.mapIdx fun offset byte => (BitVec.ofNat 64 (section_.address.toNat + offset), byte)

/-! ## Transcription of `decode_elf` -/

/-- One step of Jolt's `merge_ranges` over sorted ranges. `merged` holds the ranges merged so
far, the last one first. A range whose start is at most the previous end joins the previous
range; any other range starts a new one. For example, `mergeStep [(0, 10)] (10, 20)` is
`[(0, 20)]` and `mergeStep [(0, 10)] (12, 20)` is `[(12, 20), (0, 10)]`.
See : `jolt/crates/jolt-program/src/image/elf.rs` (`merge_ranges`). -/
def mergeStep (merged : List (Nat × Nat)) (range : Nat × Nat) : List (Nat × Nat) :=
  match merged with
  | (start, previousEnd) :: rest =>
    if range.1 ≤ previousEnd then (start, max previousEnd range.2) :: rest else range :: merged
  | [] => [range]

/-- Jolt's `merge_ranges`: sort the ranges by start, then join each range to the previous one
when its start is at most the previous end. Jolt's sort is unstable, but ranges with the same
start always merge into one, and the order among them does not change the result.
For example, `mergeRanges [(20, 30), (0, 10), (10, 20)]` is `[(0, 30)]`.
See : `jolt/crates/jolt-program/src/image/elf.rs` (`merge_ranges`). -/
def mergeRanges (ranges : List (Nat × Nat)) : List (Nat × Nat) :=
  ((ranges.mergeSort fun a b => a.1 ≤ b.1).foldl mergeStep []).reverse

/-- Jolt's `decode_text_section` without the call of `decode_instruction`: the address and
encoding of every instruction in the bytes of a text range that starts at `address`, or none
where Jolt reports a truncated halfword or word.
A halfword whose low two bits are not `0b11` is a compressed parcel; a zero parcel gives no
instruction. Any other halfword starts a 32-bit word.
For example, the bytes `[0x01, 0x45, 0x93, 0x80, 0x10, 0x00, 0x00, 0x00]` at `0x80000000` give
`[(0x80000000, .compressed 0x4501), (0x80000002, .base 0x00108093)]`, and `[0x93, 0x80]` gives
none.
See : `jolt/crates/jolt-program/src/image/elf.rs` (`decode_text_section`). -/
def decodeText (address : Nat) : List (BitVec 8) → Option (List (Nat × BlockEncoding))
  | [] => some []
  | [_] => none
  | b0 :: b1 :: rest =>
    if (b1 ++ b0).extractLsb 1 0 ≠ 0b11#2 then
      (decodeText (address + 2) rest).map fun parcels =>
        if b1 ++ b0 = 0#16 then parcels else (address, .compressed (b1 ++ b0)) :: parcels
    else
      match rest with
      | b2 :: b3 :: rest' =>
        (decodeText (address + 4) rest').map ((address, .base ((b3 ++ b2) ++ (b1 ++ b0))) :: ·)
      | _ => none

/-- The bytes `decode_elf` decodes for the range `[start, end)`: the byte the memory map holds at
each address, or 0 where it holds none. Jolt's map is a `BTreeMap` extended with the entries of
`memory_init` in order. It holds the last byte written at each address (`lastByte`).
For example, with `memoryInit = [(0x80000000, 0x01), (0x80000001, 0x45)]` the range
`(0x80000000, 0x80000003)` gives `[0x01, 0x45, 0x00]`.
See : `jolt/crates/jolt-program/src/image/elf.rs` (`decode_elf`, `unwrap_or(0)`). -/
def rangeBytes (memoryInit : List (BitVec 64 × BitVec 8)) (range : Nat × Nat) :
    List (BitVec 8) :=
  (List.range (range.2 - range.1)).map fun offset => (lastByte memoryInit (range.1 + offset)).getD 0

/-- What `decode_elf` computes before it decodes each instruction: `memory_init`,
`program_end`, `entry_address`, and the address and encoding of every instruction in decode
order (`parcels`). For example, an ELF with one text section holding `addi x1, x0, 1` at
`0x80000000` gives `parcels = [(0x80000000, .base 0x00100093)]` and
`program_end = 0x80000004`. -/
structure ElfLayout where
  memory_init : List (BitVec 64 × BitVec 8)
  program_end : BitVec 64
  entry_address : BitVec 64
  parcels : List (Nat × BlockEncoding)

/-- The sections `decode_elf` loads: those at or above `RAM_START_ADDRESS`, in section-header
order. For example, a section at `0x1000` is dropped.
See : `jolt/crates/jolt-program/src/image/elf.rs` (`decode_elf`, the `filter`). -/
def ElfSections.loaded (elf : ElfSections) : List ElfSection :=
  elf.sections.filter fun section_ => JoltISA.RAM_START_ADDRESS ≤ section_.address.toNat

/-- **Jolt's `decode_elf`, up to the call of `decode_instruction`.** It is none where `decode_elf`
fails because a section's end overflows `u64` or a text range ends inside an instruction.
`decode_elf`'s other failures (a malformed file, ELF32, unreadable data) belong to the parsing
step, and the failures of `decode_instruction` are left out, which only admits more ELFs.

The memory image lists every byte of every loaded section in order; `program_end` is the largest
section end, at least `RAM_START_ADDRESS`; each merged text range is decoded from the bytes the
memory image holds there.
For example, one `.text` section at `0x80000000` with data `[0x93, 0x00, 0x10, 0x00]` gives the
four `memory_init` entries, `program_end = 0x80000004`, and the single parcel
`(0x80000000, .base 0x00100093)`.
See : `jolt/crates/jolt-program/src/image/elf.rs` (`decode_elf`). -/
def ElfSections.layout? (elf : ElfSections) : Option ElfLayout :=
  let loaded := elf.loaded
  if loaded.all fun section_ => section_.endAddress < 2 ^ 64 then
    let memoryInit := loaded.flatMap ElfSection.bytes
    let programEnd := loaded.foldl (fun e section_ => max e section_.endAddress)
      JoltISA.RAM_START_ADDRESS
    let textRanges := (loaded.filter (·.isText)).map fun section_ =>
      (section_.address.toNat, section_.endAddress)
    ((mergeRanges textRanges).mapM fun range => decodeText range.1 (rangeBytes memoryInit range))
      |>.map fun parcels =>
        { memory_init := memoryInit
          program_end := BitVec.ofNat 64 programEnd
          entry_address := elf.entry
          parcels := parcels.flatten }
  else none

/-- The 32-bit word Jolt passes to `decode_instruction` for an encoding: the word itself, or the
uncompressed form of a compressed parcel. For example, `.compressed 0x0001` gives
`joltUncompress 0x0001`, the ADDI x0,x0,0 word `0x00000013`. -/
def BlockEncoding.decodedWord : BlockEncoding → BitVec 32
  | .base w => w
  | .compressed h => Decode.joltUncompress h

/-- A source row is what `decode_instruction` makes of a parcel: it has the parcel's address
and width, and a RISC-V row is `joltDecode` of the parcel's word for some advice operand, which
the encoding does not carry. A row of one of Jolt's own instructions (`SourceInstruction.jolt`)
is constrained only in address and width, because Lean has no transcription of Jolt's
`decode_custom`.
For example, the parcel `(0x80000000, .base 0x00100093)` gives the row at `0x80000000`, not
compressed, holding `.riscv (.ADDI x1 x0 1)`. -/
def RowFromParcel (parcel : Nat × BlockEncoding) (row : SourceInstructionRow SourceInstruction) :
    Prop :=
  row.address.toNat = parcel.1 ∧ row.is_compressed = parcel.2.isCompressed ∧
    ∀ i, row.instruction = .riscv i →
      ∃ advice, Decode.joltDecode parcel.2.decodedWord advice = some i

/-- **The program agrees with what `decode_elf` builds from the ELF's sections.** The layout of
`elf` exists; the program's `memory_init`, `program_end` and `entry_address` are the layout's;
and its rows correspond, one to one and in order, to the layout's parcels (`RowFromParcel`).

The relation fixes the layout and the decoding of every RISC-V row. It does not fix which of
Jolt's own instructions a `.jolt` row holds, and it leaves out the checks by which
`decode_instruction` rejects a program. Every program Jolt builds from the ELF satisfies it.
This premise replaces `ImageDecoded` in the whole-run theorems. What stays trusted is that
`elf` is what the `object` crate parses from the guest ELF, and that Jolt's preprocessing and the
verifier key were built from this program.
For example, for one `.text` section at `0x80000000` holding `addi x1, x0, 1`, the program Jolt
builds, with the single row ADDI x1,x0,1 at `0x80000000` and the four bytes of the section as
`memory_init`, satisfies the relation. -/
def _root_.Rv64ProgramImage.DecodedFrom (program : Rv64ProgramImage SourceInstruction)
    (elf : ElfSections) : Prop :=
  ∃ layout, elf.layout? = some layout ∧ program.memory_init = layout.memory_init ∧
    program.program_end = layout.program_end ∧ program.entry_address = layout.entry_address ∧
    List.Forall₂ RowFromParcel layout.parcels program.instructions.toList

/-! ## Every address of a text range has a byte -/

/-- `lastByte` finds a byte at every address that some entry names.
For example, `[(0x80000000, 1)]` has a byte at `0x80000000`. -/
theorem lastByte_isSome_of_mem {l : List (BitVec 64 × BitVec 8)} {a : Nat}
    {e : BitVec 64 × BitVec 8} (he : e ∈ l) (ha : e.1.toNat = a) : (lastByte l a).isSome := by
  induction l with
  | nil => cases he
  | cons x t ih =>
    simp only [lastByte]
    rcases List.mem_cons.mp he with rfl | ht
    · split <;> simp_all
    · have := ih ht
      split <;> simp_all

/-- A loaded text section's memory image has a byte at every address of the section.
For example, the `.text` section at `0x80000000` with data `[0x93, 0x00, 0x10, 0x00]` has a
byte at `0x80000003`. -/
theorem ElfSection.lastByte_isSome {memoryInit : List (BitVec 64 × BitVec 8)}
    {section_ : ElfSection} (hbytes : ∀ e ∈ section_.bytes, e ∈ memoryInit)
    (hram : JoltISA.RAM_START_ADDRESS ≤ section_.address.toNat) (htext : section_.isText = true)
    (hend : section_.endAddress < 2 ^ 64) {a : Nat}
    (hstart : section_.address.toNat ≤ a) (hlt : a < section_.endAddress) :
    (lastByte memoryInit a).isSome := by
  have hlen := section_.text_data_length hram htext
  unfold ElfSection.endAddress at hend hlt
  have hk : a - section_.address.toNat < section_.bytes.length := by
    simp only [ElfSection.bytes, List.length_mapIdx]
    omega
  apply lastByte_isSome_of_mem (hbytes _ (List.getElem_mem hk))
  simp only [ElfSection.bytes, List.getElem_mapIdx, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

/-- One `mergeStep` adds no address outside the input ranges: if every merged range so far is
covered by `ranges` and the new range is one of `ranges`, every merged range is still covered.
For example, merging `(10, 20)` into `[(0, 10)]` gives `(0, 20)`, whose addresses lie in
`(0, 10)` or `(10, 20)`. -/
theorem mergeStep_covered {ranges merged : List (Nat × Nat)} {range : Nat × Nat}
    (hrange : range ∈ ranges)
    (hmerged : ∀ m ∈ merged, ∀ a, m.1 ≤ a → a < m.2 → ∃ q ∈ ranges, q.1 ≤ a ∧ a < q.2) :
    ∀ m ∈ mergeStep merged range, ∀ a, m.1 ≤ a → a < m.2 →
      ∃ q ∈ ranges, q.1 ≤ a ∧ a < q.2 := by
  intro m hm a hstart hlt
  unfold mergeStep at hm
  split at hm
  · rename_i start previousEnd rest
    split at hm
    · rename_i hle
      rcases List.mem_cons.mp hm with rfl | hm
      · by_cases ha : a < previousEnd
        · exact hmerged (start, previousEnd) (by simp) a hstart ha
        · exact ⟨range, hrange, by omega, by simp only at hlt; omega⟩
      · exact hmerged m (List.mem_cons_of_mem _ hm) a hstart hlt
    · rcases List.mem_cons.mp hm with rfl | hm
      · exact ⟨_, hrange, hstart, hlt⟩
      · exact hmerged m hm a hstart hlt
  · rcases List.mem_singleton.mp hm with rfl
    exact ⟨_, hrange, hstart, hlt⟩

/-- Folding `mergeStep` over ranges taken from `ranges` adds no address outside `ranges`.
For example, folding `[(0, 10), (10, 20)]` from `[]` gives `[(0, 20)]`, covered by the two
inputs. -/
theorem foldl_mergeStep_covered (ranges : List (Nat × Nat)) :
    ∀ (todo merged : List (Nat × Nat)), (∀ r ∈ todo, r ∈ ranges) →
      (∀ m ∈ merged, ∀ a, m.1 ≤ a → a < m.2 → ∃ q ∈ ranges, q.1 ≤ a ∧ a < q.2) →
      ∀ m ∈ todo.foldl mergeStep merged, ∀ a, m.1 ≤ a → a < m.2 →
        ∃ q ∈ ranges, q.1 ≤ a ∧ a < q.2
  | [], _, _, hmerged => hmerged
  | r :: rs, merged, htodo, hmerged =>
    foldl_mergeStep_covered ranges rs (mergeStep merged r)
      (fun x hx => htodo x (List.mem_cons_of_mem _ hx))
      (mergeStep_covered (htodo r (by simp)) hmerged)

/-- **`mergeRanges` adds no address.** Every address of a merged range lies in one of the input
ranges. For example, `mergeRanges [(20, 30), (0, 10), (10, 20)] = [(0, 30)]`, and address 15
lies in `(10, 20)`. -/
theorem mergeRanges_covered {ranges : List (Nat × Nat)} {range : Nat × Nat}
    (hrange : range ∈ mergeRanges ranges) {a : Nat} (hstart : range.1 ≤ a) (hlt : a < range.2) :
    ∃ q ∈ ranges, q.1 ≤ a ∧ a < q.2 :=
  foldl_mergeStep_covered ranges _ [] (fun _ hr => List.mem_mergeSort.mp hr) (by simp) range
    (List.mem_reverse.mp hrange) a hstart hlt

/-! ## The parcels are the image's bytes -/

/-- The low two bits of a word are those of its low halfword.
For example, the word `0x00108093` and its low halfword `0x8093` both end in `0b11`. -/
theorem extractLsb_one_zero_append (hi lo : BitVec 16) :
    (hi ++ lo).extractLsb 1 0 = lo.extractLsb 1 0 := by
  ext i hi'
  simp only [BitVec.extractLsb, BitVec.getElem_extractLsb', BitVec.getLsbD_append]
  rw [ite_eq_left (by omega)]

/-- **Every parcel `decodeText` finds is in the image.** If the bytes of a text range are the
image's bytes at the range's addresses, each compressed parcel is the image's halfword at its
address, with low bits other than `0b11`, and each word is the image's word there, with low bits
`0b11`. For example, the bytes `[0x93, 0x00, 0x10, 0x00]` at `0x80000000` give the word
`0x00100093`, which is `imageWord?` at `0x80000000`. -/
theorem decodeText_parcels (program : Rv64ProgramImage SourceInstruction) :
    ∀ (address : Nat) (bytes : List (BitVec 8)) (parcels : List (Nat × BlockEncoding)),
      (∀ k (b : BitVec 8), bytes[k]? = some b → imageByte? program (address + k) = some b) →
      decodeText address bytes = some parcels → ∀ p ∈ parcels,
        (∀ w, p.2 = .base w → imageWord? program p.1 = some w ∧ w.extractLsb 1 0 = 0b11#2) ∧
        (∀ h, p.2 = .compressed h →
          imageParcel? program p.1 = some h ∧ h.extractLsb 1 0 ≠ 0b11#2)
  | _, [], _, _, hdecode => by
    simp only [decodeText, Option.some.injEq] at hdecode
    subst hdecode
    simp
  | _, [_], _, _, hdecode => by simp [decodeText] at hdecode
  | address, b0 :: b1 :: rest, parcels, hbytes, hdecode => by
    have h0 : imageByte? program address = some b0 := by simpa using hbytes 0 b0 rfl
    have h1 : imageByte? program (address + 1) = some b1 := hbytes 1 b1 rfl
    have hparcel : imageParcel? program address = some (b1 ++ b0) := by
      simp [imageParcel?, h0, h1]
    unfold decodeText at hdecode
    split at hdecode
    · rename_i hlow
      obtain ⟨tail, htail, rfl⟩ := Option.map_eq_some_iff.mp hdecode
      have ih := decodeText_parcels program (address + 2) rest tail (fun k b hk => by
        have := hbytes (k + 2) b (by simpa using hk)
        rwa [show address + (k + 2) = address + 2 + k by omega] at this) htail
      intro p hp
      split at hp
      · exact ih p hp
      · rcases List.mem_cons.mp hp with rfl | hp
        · refine ⟨fun w hw => by simp at hw, fun h hh => ?_⟩
          simp only [BlockEncoding.compressed.injEq] at hh
          subst hh
          exact ⟨hparcel, hlow⟩
        · exact ih p hp
    · rename_i hlow
      split at hdecode
      · rename_i b2 b3 rest'
        obtain ⟨tail, htail, rfl⟩ := Option.map_eq_some_iff.mp hdecode
        have h2 : imageByte? program (address + 2) = some b2 := hbytes 2 b2 rfl
        have h3 : imageByte? program (address + 2 + 1) = some b3 := hbytes 3 b3 rfl
        have ih := decodeText_parcels program (address + 4) rest' tail (fun k b hk => by
          have := hbytes (k + 4) b (by simpa using hk)
          rwa [show address + (k + 4) = address + 4 + k by omega] at this) htail
        intro p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · refine ⟨fun w hw => ?_, fun h hh => by simp at hh⟩
          cases hw
          refine ⟨by simp [imageWord?, imageParcel?, h0, h1, h2, h3], ?_⟩
          rw [extractLsb_one_zero_append]
          exact Decidable.of_not_not hlow
        · exact ih p hp
      · simp at hdecode

termination_by _ bytes => bytes.length

/-- An element of the result of an `Option`-valued `mapM` comes from some input.
For example, `[1, 2].mapM (fun n => some (n + 1)) = some [2, 3]`, and 3 comes from 2. -/
theorem exists_of_mapM_eq_some {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {l' : List β}, l.mapM f = some l' → ∀ y ∈ l', ∃ x ∈ l, f x = some y
  | [], l', h => by
    simp only [List.mapM_nil] at h
    cases h
    simp
  | a :: l, l', h => by
    simp only [List.mapM_cons] at h
    cases hfa : f a with
    | none => simp [hfa] at h
    | some b =>
      cases hl : l.mapM f with
      | none => simp [hfa, hl] at h
      | some bs =>
        simp only [hfa, hl, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
          Option.some.injEq] at h
        subst h
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact ⟨a, by simp, hfa⟩
        · obtain ⟨x, hx, hfx⟩ := exists_of_mapM_eq_some hl y hy
          exact ⟨x, List.mem_cons_of_mem _ hx, hfx⟩

/-- An element of the right list of `Forall₂ R` is related to some element of the left list.
For example, `Forall₂ (· < ·) [1] [2]` relates 2 to 1. -/
theorem exists_of_forall₂_right {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ y ∈ l₂, ∃ x ∈ l₁, R x y
  | _, _, .nil, _, hy => by cases hy
  | _, _, .cons hr hrest, y, hy => by
    rcases List.mem_cons.mp hy with rfl | hy
    · exact ⟨_, by simp, hr⟩
    · obtain ⟨x, hx, hxy⟩ := exists_of_forall₂_right hrest y hy
      exact ⟨x, List.mem_cons_of_mem _ hx, hxy⟩

/-! ## The image is decoded -/

/-- **A program built from the ELF's sections satisfies `ImageDecoded`.** Each RISC-V row comes
from a parcel `decodeText` found in a merged text range. Every address of that range has a byte
in `memory_init`, because each address lies in a text section, whose data covers it
(`mergeRanges_covered`, `ElfSection.lastByte_isSome`). The bytes `decode_elf` reads are
therefore the image's bytes, and the row is what `joltDecode` makes of them.
For example, for the `.text` section at `0x80000000` holding `addi x1, x0, 1`, the ADDI row has
`RowDecodes … (.base 0x00100093)`. -/
theorem _root_.Rv64ProgramImage.DecodedFrom.imageDecoded
    {program : Rv64ProgramImage SourceInstruction} {elf : ElfSections}
    (hdecoded : program.DecodedFrom elf) : ImageDecoded program := by
  obtain ⟨layout, hlayout, hmem, -, -, hrows⟩ := hdecoded
  intro row hrow i hi
  obtain ⟨p, hp, haddr, hcomp, hdec⟩ :=
    exists_of_forall₂_right hrows row (Array.mem_toList_iff.mpr hrow)
  obtain ⟨advice, hadvice⟩ := hdec i hi
  dsimp only [ElfSections.layout?] at hlayout
  split at hlayout
  · rename_i hall
    obtain ⟨parcelLists, hmapM, rfl⟩ := Option.map_eq_some_iff.mp hlayout
    simp only at hp hmem
    obtain ⟨ps, hps, hpin⟩ := List.mem_flatten.mp hp
    obtain ⟨range, hrange, hdecode⟩ := exists_of_mapM_eq_some hmapM ps hps
    have hbytes : ∀ k (b : BitVec 8), (rangeBytes (elf.loaded.flatMap ElfSection.bytes) range)[k]?
        = some b → imageByte? program (range.1 + k) = some b := by
      intro k b hk
      simp only [rangeBytes, List.getElem?_map, Option.map_eq_some_iff] at hk
      obtain ⟨offset, hoffset, rfl⟩ := hk
      obtain ⟨hklt, rfl⟩ := List.getElem?_eq_some_iff.mp hoffset
      rw [List.length_range] at hklt
      rw [List.getElem_range]
      obtain ⟨q, hq, hq1, hq2⟩ := mergeRanges_covered hrange (a := range.1 + k) (by omega)
        (by omega)
      simp only [List.mem_map, List.mem_filter] at hq
      obtain ⟨section_, ⟨hloaded, htext⟩, rfl⟩ := hq
      have hsome := ElfSection.lastByte_isSome
        (fun e he => List.mem_flatMap.mpr ⟨section_, hloaded, he⟩)
        (of_decide_eq_true (List.mem_filter.mp hloaded).2) htext
        (of_decide_eq_true (List.all_eq_true.mp hall section_ hloaded)) hq1 hq2
      obtain ⟨b', hb'⟩ := Option.isSome_iff_exists.mp hsome
      unfold imageByte?
      rw [hmem, hb']
      rfl
    obtain ⟨hword, hparcel⟩ := decodeText_parcels program range.1 _ ps hbytes hdecode p hpin
    cases hp2 : p.2 with
    | base w =>
      obtain ⟨hw, hlow⟩ := hword w hp2
      refine ⟨.base w, ?_, by rw [haddr]; exact hw, hlow, advice, ?_⟩
      · rw [hcomp, hp2]
        rfl
      · simpa [BlockEncoding.decodedWord, hp2] using hadvice
    | compressed h =>
      obtain ⟨hh, hlow⟩ := hparcel h hp2
      refine ⟨.compressed h, ?_, by rw [haddr]; exact hh, hlow, advice, ?_⟩
      · rw [hcomp, hp2]
        rfl
      · simpa [BlockEncoding.decodedWord, hp2] using hadvice
  · simp at hlayout

end WholeRun
