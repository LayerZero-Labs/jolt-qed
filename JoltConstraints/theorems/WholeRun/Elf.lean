import JoltConstraints.theorems.WholeRun.Decoded

/-!
# The program image built from the ELF's sections

Jolt's `decode_elf` (`jolt/crates/jolt-program/src/image/elf.rs` at `ff6fc6568`) builds the
program image from the guest ELF. This file transcribes it and proves that every image it builds
satisfies `ImageDecoded` and has only even row addresses (`RowsAligned`). The whole-run theorems
therefore need no premise on the decoder beyond "the program was built from this ELF".

* `ElfSection`, `ElfSections`: the sections of the ELF, with their mapping symbols, and its entry
  point, as the `object` crate parses them. That parsing step stays trusted.
* `codeRegionAt`: Jolt's `code_region`, which `decode_elf` and the tracer's code guard share.
* `ElfSections.layout?`: `decode_elf` up to the call of `decode_instruction`. It gives the memory
  image, the program end, the entry point and the address and encoding of every instruction.
* `JoltCustomInstruction.decode?`: Jolt's `decode_custom`, the decoder of Jolt's own
  instructions, with their operands. `jolt.success` decodes only from the word `0x0000305B`.
* `Rv64ProgramImage.DecodedFrom`: the program agrees with what `decode_elf` builds from the
  sections, and every row, RISC-V or Jolt's own, decodes from its bytes. Every program Jolt
  builds satisfies it.
* `Rv64ProgramImage.DecodedFrom.rowEncoding`: every row decodes from the image's bytes at its
  address; `DecodedFrom.joltSuccess_word` specializes it to the success word.
* `Rv64ProgramImage.DecodedFrom.imageDecoded`: such a program satisfies `ImageDecoded`.
* `Rv64ProgramImage.DecodedFrom.rowsAligned`: such a program satisfies `RowsAligned`.

`decode_elf` decodes each merged text range, except the data ranges that `$d` mapping symbols
mark, from its byte map with `unwrap_or(0)`. When `decode_elf` succeeds, the `object` crate has
given every loaded text section, at or above `RAM_START_ADDRESS`, exactly `size` bytes of data
(`ElfSection.text_data_length`). Every decoded address lies in a merged text range
(`textSegments_within`), so it has a byte, and the default never applies (`mergeRanges_covered`,
`ElfSection.lastByte_isSome`).
-/

set_option autoImplicit false

namespace WholeRun

open JoltISA (codeRegionAt)

/-! ## The parsed ELF -/

/-- The kind of an ELF mapping symbol: `$x` (and any name that starts with `$x`) marks the start
of code, `$d` (and any name that starts with `$d.`) marks the start of data.
See : `jolt/crates/jolt-program/src/image/elf.rs` (`MappingSymbol`). -/
inductive MappingSymbol where
  | code
  | data
  deriving DecidableEq

/-- **One section of the guest ELF**, as the `object` crate (0.41.0, the version Jolt locks at `ff6fc6568`) reports it to `decode_elf`:
`address` is `section.address()`, `size` is `section.size()`, `isText` is
`section.kind() == SectionKind::Text` and `isWritable` says that `sh_flags` contains
`SHF_WRITE`. For a section at or above `RAM_START_ADDRESS`, `data` is `section.data()`.
`decode_elf` never reads the data of a section below `RAM_START_ADDRESS`. Below that address,
`data` may be any list, for example `[]` when the section's file extent is unreadable.

`mappingSymbols` lists, in symbol-table order, the address (`symbol.address()`) and kind of
every mapping symbol whose section index (`symbol.section_index()`) is this section's index: every
symbol of `obj.symbols()` that is local (`is_local()`), has kind `SymbolKind::Unknown` (the
`object` crate's kind for `STT_NOTYPE`), and whose name starts with `$x`, is `$d` or starts with
`$d.` (`decode_elf`, the loop over `obj.symbols()`).

`text_data_length` records how the crate reads a text section that `decode_elf` loads.
`kind()` returns `Text` only for an `SHT_PROGBITS` section with `SHF_ALLOC` and `SHF_EXECINSTR`,
never for `SHT_NOBITS`. `data()` of a section that is not `SHT_NOBITS` returns exactly `sh_size`
bytes of the file or fails, and `decode_elf` reports a failure as "section data is not
readable".
See `object-0.41.0/src/read/elf/section.rs` (`ElfSection::kind`, `SectionHeader::data`).

For example, a `.text` section at `0x80000000` holding `addi x1, x0, 1` has `size = 4`,
`data = [0x93, 0x00, 0x10, 0x00]`, `isText = true`, `isWritable = false` and, if the assembler
emitted one, the mapping symbol `(0x80000000, .code)`, while a `.bss` section has
`isText = false`, `isWritable = true`, a nonzero `size` and `data = []`. -/
structure ElfSection where
  address : BitVec 64
  size : BitVec 64
  data : List (BitVec 8)
  isText : Bool
  isWritable : Bool
  mappingSymbols : List (BitVec 64 × MappingSymbol)
  text_data_length : JoltISA.RAM_START_ADDRESS ≤ address.toNat → isText = true →
    data.length = size.toNat

/-- **The parsed guest ELF**: its sections in section-header order and its entry point
(`obj.entry()`). Producing this from the file, including each section's mapping symbols, is the
trusted parsing step.
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

/-! ## The code region -/

/-- The code region of a memory layout is `codeRegionAt` at the layout's lowest address.
For example, both give the same interval for the source rows of a program. -/
theorem codeRegionOf_eq (layout : MemoryLayout) (sources : List (BitVec 64 × Bool)) :
    JoltISA.codeRegionOf layout sources = codeRegionAt layout.get_lowest_address.toNat sources :=
  rfl

/-- The word interval `region`, counted from `lowest`, covers the source `x`: `x` lies at or
above `lowest` at an even address, and the interval contains every doubleword that holds a byte
of `x`. For example, `(0, 1)` covers a 4-byte source at `lowest + 4`. -/
def RegionCovers (lowest : Nat) (region : Nat × Nat) (x : BitVec 64 × Bool) : Prop :=
  lowest ≤ x.1.toNat ∧ x.1.toNat % 2 = 0 ∧ region.1 ≤ (x.1.toNat - lowest) / 8 ∧
    (x.1.toNat + (if x.2 then 2 else 4) - lowest + 7) / 8 ≤ region.2

/-- The interval `r'` contains the interval `r`, if `r` exists. -/
private def Widens (r r' : Option (Nat × Nat)) : Prop :=
  ∀ a b, r = some (a, b) → ∃ a' b', r' = some (a', b') ∧ a' ≤ a ∧ b ≤ b'

/-- The loop of `codeRegionAt` only widens its interval, and the final interval covers every
nonzero source. -/
private theorem forIn_region (lowest : Nat)
    (f : (BitVec 64 × Bool) → Option (Nat × Nat) → Option (ForInStep (Option (Nat × Nat))))
    (hf : ∀ x r y, f x r = some y → ∃ r', y = .yield r' ∧ Widens r r' ∧
      (x.1 ≠ 0 → ∃ c, r' = some c ∧ RegionCovers lowest c x)) :
    ∀ (l : List (BitVec 64 × Bool)) (r r' : Option (Nat × Nat)), forIn l r f = some r' →
      Widens r r' ∧ ∀ x ∈ l, x.1 ≠ 0 → ∃ c, r' = some c ∧ RegionCovers lowest c x
  | [], r, r', h => by
    simp only [List.forIn_nil] at h
    cases h
    exact ⟨fun a b h => ⟨a, b, h, le_refl _, le_refl _⟩, by simp⟩
  | x :: l, r, r', h => by
    simp only [List.forIn_cons] at h
    obtain ⟨y, hy, hrest⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨r₁, rfl, hw, hc⟩ := hf x r _ hy
    obtain ⟨hw', hl⟩ := forIn_region lowest f hf l r₁ r' hrest
    refine ⟨fun a b hab => ?_, fun z hz hne => ?_⟩
    · obtain ⟨a₁, b₁, h₁, ha₁, hb₁⟩ := hw a b hab
      obtain ⟨a₂, b₂, h₂, ha₂, hb₂⟩ := hw' a₁ b₁ h₁
      exact ⟨a₂, b₂, h₂, by omega, by omega⟩
    · rcases List.mem_cons.mp hz with rfl | hz
      · obtain ⟨⟨c₁, c₂⟩, rfl, hcov⟩ := hc hne
        obtain ⟨a₂, b₂, h₂, ha₂, hb₂⟩ := hw' c₁ c₂ rfl
        refine ⟨(a₂, b₂), h₂, hcov.1, hcov.2.1, ?_, ?_⟩
        · have := hcov.2.2.1; simp only at this ⊢; omega
        · have := hcov.2.2.2; simp only at this ⊢; omega
      · exact hl z hz hne

/-- **The code region covers every source.** If `codeRegionAt` succeeds, `lowest` is doubleword
aligned and the interval covers every source at a nonzero address.
For example, the interval of a program's rows contains the doubleword of each row's bytes. -/
theorem codeRegionAt_covers {lowest : Nat} {sources : List (BitVec 64 × Bool)}
    {region : Nat × Nat} (h : codeRegionAt lowest sources = some region)
    {x : BitVec 64 × Bool} (hx : x ∈ sources) (hne : x.1 ≠ 0) :
    lowest % 8 = 0 ∧ RegionCovers lowest region x := by
  unfold codeRegionAt at h
  simp only [Option.bind_eq_bind] at h
  obtain ⟨u, hg, h⟩ := Option.bind_eq_some_iff.mp h
  have hlow : lowest % 8 = 0 := by
    simpa [guard, failure] using hg
  refine ⟨hlow, ?_⟩
  obtain ⟨r, hr, h⟩ := Option.bind_eq_some_iff.mp h
  have key := forIn_region lowest _ ?_ sources none r hr
  · obtain ⟨-, hcov⟩ := key
    obtain ⟨c, rfl, hc⟩ := hcov x hx hne
    simp only [Option.getD_some, pure, Option.some.injEq] at h
    subst h
    exact hc
  · rintro ⟨address, compressed⟩ r y hy
    simp only at hy
    split at hy
    · obtain ⟨stop, hstop, hy⟩ := Option.bind_eq_some_iff.mp hy
      obtain ⟨u, hg, hy⟩ := Option.bind_eq_some_iff.mp hy
      have hg' : lowest ≤ address.toNat ∧ address.toNat % 2 = 0 := by
        simpa [guard, failure] using hg
      have hstop' : stop = address.toNat + (if compressed then 2 else 4) := by
        unfold MemoryLayout.checkedAdd at hstop
        generalize (if compressed = true then 2 else 4) = w at hstop ⊢
        by_cases hw : address.toNat + w < 2 ^ 64
        · simp only [hw, ↓reduceIte, Option.some.injEq] at hstop
          exact hstop.symm
        · simp only [hw, ↓reduceIte, reduceCtorEq] at hstop
      subst hstop'
      simp only [pure, Option.some.injEq] at hy
      subst hy
      refine ⟨_, rfl, ?_, fun _ => ⟨_, rfl, ?_⟩⟩
      · rintro a b rfl
        exact ⟨_, _, rfl, Nat.min_le_left _ _, Nat.le_max_left _ _⟩
      · refine ⟨hg'.1, hg'.2, ?_, ?_⟩
        · cases r with
          | none => exact le_refl _
          | some ab => exact Nat.min_le_right _ _
        · cases r with
          | none => exact le_refl _
          | some ab => exact Nat.le_max_right _ _
    · rename_i hzero
      simp only [pure, Option.some.injEq] at hy
      subst hy
      refine ⟨_, rfl, fun a b h => ⟨a, b, h, le_refl _, le_refl _⟩, fun hne' => ?_⟩
      exact absurd (by simpa using hzero) hne'

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
where Jolt reports an odd instruction address or a truncated halfword or word. Every instruction
address has the parity of `address`, so Jolt rejects nonempty bytes at an odd `address`.
A halfword whose low two bits are not `0b11` is a compressed parcel; a zero parcel gives no
instruction. Any other halfword starts a 32-bit word.
For example, the bytes `[0x01, 0x45, 0x93, 0x80, 0x10, 0x00, 0x00, 0x00]` at `0x80000000` give
`[(0x80000000, .compressed 0x4501), (0x80000002, .base 0x00108093)]`, and `[0x93, 0x80]` gives
none, as does any nonempty list at `0x80000001`.
See : `jolt/crates/jolt-program/src/image/elf.rs` (`decode_text_section`). -/
def decodeText (address : Nat) : List (BitVec 8) → Option (List (Nat × BlockEncoding))
  | [] => some []
  | [_] => none
  | b0 :: b1 :: rest =>
    if address % 2 ≠ 0 then none
    else if (b1 ++ b0).extractLsb 1 0 ≠ 0b11#2 then
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

/-- Sort mapping symbols by address, a code symbol after a data symbol at the same address, as
`sort_by_key(|&(address, kind)| (address, matches!(kind, MappingSymbol::Code)))`. -/
def mappingLe (a b : Nat × MappingSymbol) : Bool :=
  a.1 < b.1 || (a.1 == b.1 && (a.2 == .data || b.2 == .code))

/-- The data ranges of a sorted list of mapping symbols in a section that ends at `stop`: each
data symbol starts a range that ends at the next symbol's address, or at `stop` after the last
symbol; an empty range is dropped.
For example, symbols `[(0, .code), (8, .data), (12, .code)]` give `[(8, 12)]`, and
`[(8, .data), (8, .code)]` gives `[]`.
See : `jolt/crates/jolt-program/src/image/elf.rs` (`decode_elf`, the loop that pushes to
`data_ranges`). -/
def dataRangesFrom (stop : Nat) : List (Nat × MappingSymbol) → List (Nat × Nat)
  | [] => []
  | (address, kind) :: rest =>
    let next := match rest with
      | (nextAddress, _) :: _ => nextAddress
      | [] => stop
    if address < next ∧ kind = .data then (address, next) :: dataRangesFrom stop rest
    else dataRangesFrom stop rest

/-- **The data ranges a text section's mapping symbols mark.** Keep the symbols inside the
section, sort them by `mappingLe`, and take `dataRangesFrom` the section's end.
Rust's sort is stable, and two symbols with the same key are equal, so `mergeSort` gives the
same list.
For example, a section `[0x80000000, 0x80000010)` with symbols `(0x80000000, .code)` and
`(0x80000008, .data)` gives `[(0x80000008, 0x80000010)]`.
See : `jolt/crates/jolt-program/src/image/elf.rs` (`decode_elf`, `retain`, `sort_by_key`). -/
def ElfSection.dataRanges (section_ : ElfSection) : List (Nat × Nat) :=
  let inSection := (section_.mappingSymbols.map fun symbol => (symbol.1.toNat, symbol.2)).filter
    fun symbol => decide (section_.address.toNat ≤ symbol.1 ∧ symbol.1 < section_.endAddress)
  dataRangesFrom section_.endAddress (inSection.mergeSort mappingLe)

/-- The pieces of a text range between the data ranges, from `cursor` to `stop`: each data range
ends the current piece at its start and starts the next piece at its end. A piece may be empty,
or even have its end before its start, in which case Jolt decodes no bytes from it.
See : `jolt/crates/jolt-program/src/image/elf.rs` (`decode_elf`, `cursor`). -/
def segmentsFrom (cursor stop : Nat) : List (Nat × Nat) → List (Nat × Nat)
  | [] => [(cursor, stop)]
  | data :: rest => (cursor, data.1) :: segmentsFrom data.2 stop rest

/-- **The pieces of a merged text range that `decode_elf` decodes**: the range with the merged
data ranges that overlap it cut out, in order.
For example, the range `(0, 16)` with the data range `(8, 12)` gives `[(0, 8), (12, 16)]`.
See : `jolt/crates/jolt-program/src/image/elf.rs` (`decode_elf`, the loop over
`merge_ranges(text_ranges)`). -/
def textSegments (dataRanges : List (Nat × Nat)) (range : Nat × Nat) : List (Nat × Nat) :=
  segmentsFrom range.1 range.2
    (dataRanges.filter fun data => decide (data.1 < range.2 ∧ range.1 < data.2))

/-- Whether `decode_elf` rejects a writable section that overlaps the code region `code`: the
doublewords from the one holding the section's start to the one holding its last byte meet the
code region's doublewords. For example, with code region `(0, 2)`, a section at `8` overlaps
and a section at `16` does not.
See : `jolt/crates/jolt-program/src/image/elf.rs` (`decode_elf`, `writable_ranges`). -/
def ElfSection.overlapsCode (section_ : ElfSection) (code : Nat × Nat) : Bool :=
  decide (code.1 < (section_.endAddress + 7) / 8 ∧ section_.address.toNat / 8 < code.2)

/-- **Jolt's `decode_elf`, up to the call of `decode_instruction`.** It is none where `decode_elf`
fails because a section's end overflows `u64`, a decoded piece of text starts at an odd address
or ends inside an instruction, the instructions' code region is invalid, or a writable section
overlaps that code region.
`decode_elf`'s other failures (a malformed file, ELF32, unreadable data) belong to the parsing
step, and the failures of `decode_instruction` are left out, which only admits more ELFs.

The memory image lists every byte of every loaded section in order; `program_end` is the largest
section end, at least `RAM_START_ADDRESS`; each merged text range is decoded, without the data
ranges its sections' mapping symbols mark, from the bytes the memory image holds there.
The code region is `code_region` of the decoded instructions with lowest address 0
(`codeRegionAt 0`), and only a writable section with a nonzero size can overlap it.
For example, one `.text` section at `0x80000000` with data `[0x93, 0x00, 0x10, 0x00]` and no
mapping symbols gives the four `memory_init` entries, `program_end = 0x80000004`, and the
single parcel `(0x80000000, .base 0x00100093)`.
See : `jolt/crates/jolt-program/src/image/elf.rs` (`decode_elf`). -/
def ElfSections.layout? (elf : ElfSections) : Option ElfLayout :=
  let loaded := elf.loaded
  if loaded.all fun section_ => section_.endAddress < 2 ^ 64 then
    let memoryInit := loaded.flatMap ElfSection.bytes
    let programEnd := loaded.foldl (fun e section_ => max e section_.endAddress)
      JoltISA.RAM_START_ADDRESS
    let texts := loaded.filter (·.isText)
    let textRanges := texts.map fun section_ => (section_.address.toNat, section_.endAddress)
    let dataRanges := mergeRanges (texts.flatMap ElfSection.dataRanges)
    let segments := (mergeRanges textRanges).flatMap (textSegments dataRanges)
    (segments.mapM fun range => decodeText range.1 (rangeBytes memoryInit range)).bind
      fun parcelLists =>
        let parcels := parcelLists.flatten
        (codeRegionAt 0 (parcels.map fun p => (BitVec.ofNat 64 p.1, p.2.isCompressed))).bind
          fun code =>
            let writable := loaded.filter fun section_ =>
              section_.isWritable && decide (section_.address.toNat < section_.endAddress)
            if writable.all fun section_ => !section_.overlapsCode code then
              some
                { memory_init := memoryInit
                  program_end := BitVec.ofNat 64 programEnd
                  entry_address := elf.entry
                  parcels := parcels }
            else none
  else none

/-- The 32-bit word Jolt passes to `decode_instruction` for an encoding: the word itself, or the
uncompressed form of a compressed parcel. For example, `.compressed 0x0001` gives
`joltUncompress 0x0001`, the ADDI x0,x0,0 word `0x00000013`. -/
def BlockEncoding.decodedWord : BlockEncoding → BitVec 32
  | .base w => w
  | .compressed h => Decode.joltUncompress h

/-- **Jolt's `decode_custom`, with the operand formats of its instructions.** It decodes a word
of Jolt's custom opcode `0x5B` into one of Jolt's own source instructions, or none where Jolt
reports an invalid custom instruction. `funct3` selects the kind, and for `funct3 = 0`, `funct7`
selects the advice load or `VirtualRev8W`. The operands come from `format_advice_load_operands`
(`rd`), `format_t_operands` (`rd`, `rs1`) and `format_b_operands` (`rs1`, `rs2`, branch
immediate). `VirtualHostIO` keeps no operand and requires `rd = 0`, and `jolt.success` requires
the exact word `Decode.joltSuccessWord`, `0x0000305B`, whose `rd`, `rs1` and immediate are zero.
For example, `0x0000305B` gives `JoltSuccess`, while `0x0000315B` (the same word with `rd = 2`)
and the ADDI word `0x00100093` give none.
Jolt at ff6fc6568: `crates/jolt-program/src/image/decode.rs` (`decode_instruction`, the
`0b1011011` arm; `decode_custom`; `operands`). -/
def JoltCustomInstruction.decode? (word : BitVec 32) : Option JoltCustomInstruction :=
  if (word.extractLsb 6 0).toNat = 0x5b then
    match Decode.funct3 word, Decode.funct7 word with
    | 0, 0 => some (.AdviceLB (Decode.rd word))
    | 0, 1 => some (.AdviceLH (Decode.rd word))
    | 0, 2 => some (.AdviceLW (Decode.rd word))
    | 0, 3 => some (.AdviceLD (Decode.rd word))
    | 0, 5 => some (.VirtualRev8W (Decode.rd word) (Decode.rs1 word))
    | 1, _ => some (.VirtualAssertEQ (Decode.rs1 word) (Decode.rs2 word) (Decode.immB word))
    | 2, _ => if word.extractLsb 11 7 = 0 then some .VirtualHostIO else none
    | 3, _ => if word = Decode.joltSuccessWord then some .JoltSuccess else none
    | _, _ => none
  else none

/-- The custom decoder gives `JoltSuccess` only for the exact success word `0x0000305B`.
For example, the ADDI word `0x00100093` and the word `0x0000315B`, which sets `rd = 2`, are
rejected. Jolt at ff6fc6568: `crates/jolt-program/src/image/decode.rs` (`decode_custom`). -/
theorem JoltCustomInstruction.decode?_eq_joltSuccess {word : BitVec 32}
    (h : JoltCustomInstruction.decode? word = some .JoltSuccess) :
    word = Decode.joltSuccessWord := by
  unfold JoltCustomInstruction.decode? at h
  split at h
  · split at h <;> first | cases h | (split at h <;> first | assumption | cases h)
  · cases h

/-- **Jolt's `decode_instruction` gives this source instruction for `word`**, up to the
legality checks that only reject programs. A RISC-V instruction is `joltDecode` of the word for
some advice operand, which the encoding does not carry; one of Jolt's own instructions is
`JoltCustomInstruction.decode?` of the word.
For example, `.riscv (.ADDI x1 x0 1)` decodes from `0x00100093`, and `.jolt .JoltSuccess`
decodes only from `0x0000305B`.
Jolt at ff6fc6568: `crates/jolt-program/src/image/decode.rs` (`decode_instruction`). -/
def _root_.SourceInstruction.DecodesFrom : SourceInstruction → BitVec 32 → Prop
  | .riscv i, word => ∃ advice, Decode.joltDecode word advice = some i
  | .jolt c, word => JoltCustomInstruction.decode? word = some c

/-- A source row is what `decode_instruction` makes of a parcel: it has the parcel's address
and width, and its instruction decodes from the parcel's word (`SourceInstruction.DecodesFrom`).
Every row is constrained, including a row of one of Jolt's own instructions and the terminal
`jolt.success` row.
For example, the parcel `(0x80000000, .base 0x00100093)` gives the row at `0x80000000`, not
compressed, holding `.riscv (.ADDI x1 x0 1)`, and no `.jolt .JoltSuccess` row; only the parcel
`(a, .base 0x0000305B)` gives a `.jolt .JoltSuccess` row at `a`.
Jolt at ff6fc6568: `crates/jolt-program/src/image/decode.rs` (`decode_instruction`). -/
def RowFromParcel (parcel : Nat × BlockEncoding) (row : SourceInstructionRow SourceInstruction) :
    Prop :=
  row.address.toNat = parcel.1 ∧ row.is_compressed = parcel.2.isCompressed ∧
    row.instruction.DecodesFrom parcel.2.decodedWord

/-- **The program agrees with what `decode_elf` builds from the ELF's sections.** The layout of
`elf` exists; the program's `memory_init`, `program_end` and `entry_address` are the layout's;
and its rows correspond, one to one and in order, to the layout's parcels (`RowFromParcel`).

The relation fixes the layout and the instruction of every row: a RISC-V row is `joltDecode` of
its parcel's word, and a row of one of Jolt's own instructions, the terminal `jolt.success` row
included, is `JoltCustomInstruction.decode?` of it. It leaves out the checks by which
`decode_instruction` rejects a program (the instruction profile and, without the compressed
extension, 4-byte alignment). Every program Jolt builds from the ELF satisfies it.
This premise replaces `ImageDecoded` in the whole-run theorems. What stays trusted is that
`elf` is what the `object` crate parses from the guest ELF, and that Jolt's preprocessing and the
verifier key were built from this program.
For example, for one `.text` section at `0x80000000` holding `addi x1, x0, 1`, the program Jolt
builds, with the single row ADDI x1,x0,1 at `0x80000000` and the four bytes of the section as
`memory_init`, satisfies the relation, and the same program with the row `.jolt .JoltSuccess`
does not (`WholeRun/ElfRegression.lean`). -/
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
    · cases hdecode
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

/-- **Every instruction address `decodeText` finds is even.** `decode_text_section` rejects an
odd address. For example, `decodeText 0x80000001 [0x01, 0x45]` is none. -/
theorem decodeText_even :
    ∀ (address : Nat) (bytes : List (BitVec 8)) (parcels : List (Nat × BlockEncoding)),
      decodeText address bytes = some parcels → ∀ p ∈ parcels, p.1 % 2 = 0
  | _, [], _, hdecode => by
    simp only [decodeText, Option.some.injEq] at hdecode
    subst hdecode
    simp
  | _, [_], _, hdecode => by simp [decodeText] at hdecode
  | address, b0 :: b1 :: rest, parcels, hdecode => by
    unfold decodeText at hdecode
    split at hdecode
    · cases hdecode
    rename_i heven
    split at hdecode
    · obtain ⟨tail, htail, rfl⟩ := Option.map_eq_some_iff.mp hdecode
      have ih := decodeText_even (address + 2) rest tail htail
      intro p hp
      split at hp
      · exact ih p hp
      · rcases List.mem_cons.mp hp with rfl | hp
        · simp only; omega
        · exact ih p hp
    · split at hdecode
      · rename_i b2 b3 rest'
        obtain ⟨tail, htail, rfl⟩ := Option.map_eq_some_iff.mp hdecode
        have ih := decodeText_even (address + 4) rest' tail htail
        intro p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · simp only; omega
        · exact ih p hp
      · simp at hdecode
termination_by _ bytes => bytes.length

/-- Every address of a piece `segmentsFrom` makes lies between the first `cursor` and `stop`,
when every cut lies inside that interval. -/
theorem segmentsFrom_within {start stop : Nat} :
    ∀ (cursor : Nat) (cuts : List (Nat × Nat)), start ≤ cursor →
      (∀ cut ∈ cuts, cut.1 < stop ∧ start < cut.2) →
      ∀ segment ∈ segmentsFrom cursor stop cuts, ∀ a, segment.1 ≤ a → a < segment.2 →
        start ≤ a ∧ a < stop
  | cursor, [], hcursor, _, segment, hsegment, a, hstart, hlt => by
    simp only [segmentsFrom, List.mem_singleton] at hsegment
    subst hsegment
    exact ⟨by simp only at hstart; omega, hlt⟩
  | cursor, cut :: cuts, hcursor, hcuts, segment, hsegment, a, hstart, hlt => by
    have hcut := hcuts cut (by simp)
    rcases List.mem_cons.mp hsegment with rfl | hsegment
    · simp only at hstart hlt
      omega
    · exact segmentsFrom_within cut.2 cuts (by omega)
        (fun c hc => hcuts c (List.mem_cons_of_mem _ hc)) segment hsegment a hstart hlt

/-- **Every decoded address lies in its text range.** Every address of a piece of a text range
that `textSegments` makes lies in the range. For example, the pieces `(0, 8)` and `(12, 16)` of
`(0, 16)` lie in it. -/
theorem textSegments_within {dataRanges : List (Nat × Nat)} {range segment : Nat × Nat}
    (hsegment : segment ∈ textSegments dataRanges range) {a : Nat} (hstart : segment.1 ≤ a)
    (hlt : a < segment.2) : range.1 ≤ a ∧ a < range.2 :=
  segmentsFrom_within range.1 _ (le_refl _)
    (fun cut hcut => by simpa using (List.mem_filter.mp hcut).2) segment hsegment a hstart hlt

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

/-- **Where a parcel of the layout comes from.** If `decode_elf` succeeds, every loaded section
ends below `2^64`, the memory image is the bytes of the loaded sections, and every parcel is one
that `decodeText` finds in a piece of a merged text range.
For example, the parcel `(0x80000000, .base 0x00100093)` of a one-instruction `.text` section
comes from the piece `(0x80000000, 0x80000004)` of the range `(0x80000000, 0x80000004)`. -/
theorem ElfSections.layout?_parcel {elf : ElfSections} {layout : ElfLayout}
    (h : elf.layout? = some layout) {p : Nat × BlockEncoding} (hp : p ∈ layout.parcels) :
    (∀ section_ ∈ elf.loaded, section_.endAddress < 2 ^ 64) ∧
    layout.memory_init = elf.loaded.flatMap ElfSection.bytes ∧
    ∃ range ∈ mergeRanges ((elf.loaded.filter (·.isText)).map fun section_ =>
        (section_.address.toNat, section_.endAddress)),
      ∃ dataRanges, ∃ segment ∈ textSegments dataRanges range, ∃ ps,
        decodeText segment.1 (rangeBytes (elf.loaded.flatMap ElfSection.bytes) segment) =
          some ps ∧ p ∈ ps := by
  dsimp only [ElfSections.layout?] at h
  split at h
  · rename_i hall
    obtain ⟨parcelLists, hmapM, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨code, -, h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    · cases h
      refine ⟨fun section_ hs => of_decide_eq_true (List.all_eq_true.mp hall section_ hs), rfl,
        ?_⟩
      obtain ⟨ps, hps, hpin⟩ := List.mem_flatten.mp hp
      obtain ⟨segment, hsegment, hdecode⟩ := exists_of_mapM_eq_some hmapM ps hps
      obtain ⟨range, hrange, hsegment⟩ := List.mem_flatMap.mp hsegment
      exact ⟨range, hrange, _, segment, hsegment, ps, hdecode, hpin⟩
    · cases h
  · cases h

/-- The image holds the encoding `e` at the row's address, with the row's width: a word whose
low two bits are `0b11` for a 4-byte row, a halfword whose low two bits are not `0b11` for a
compressed row. For example, the ADDI row at `0x80000000` whose image bytes are
`93 00 10 00` has `RowEncoding … (.base 0x00100093)`. -/
def RowEncoding (program : Rv64ProgramImage SourceInstruction)
    (row : SourceInstructionRow SourceInstruction) : BlockEncoding → Prop
  | .base w => row.is_compressed = false ∧
      imageWord? program row.address.toNat = some w ∧ w.extractLsb 1 0 = 0b11#2
  | .compressed h => row.is_compressed = true ∧
      imageParcel? program row.address.toNat = some h ∧ h.extractLsb 1 0 ≠ 0b11#2

/-- **Every row of a program built from the ELF's sections is what Jolt decodes from the
image's bytes at its address.** Each row comes from a parcel `decodeText` found in a piece of a
merged text range. Every address of that piece lies in the range (`textSegments_within`) and has
a byte in `memory_init`, because each address of the range lies in a text section, whose data
covers it (`mergeRanges_covered`, `ElfSection.lastByte_isSome`). The bytes `decode_elf` reads are
therefore the image's bytes, and the row's instruction decodes from them.
For example, the `jolt.success` row of a program built from the bytes `5B 30 00 00` has the
encoding `.base 0x0000305B`. -/
theorem _root_.Rv64ProgramImage.DecodedFrom.rowEncoding
    {program : Rv64ProgramImage SourceInstruction} {elf : ElfSections}
    (hdecoded : program.DecodedFrom elf) {row : SourceInstructionRow SourceInstruction}
    (hrow : row ∈ program.instructions) :
    ∃ e : BlockEncoding, RowEncoding program row e ∧ row.instruction.DecodesFrom e.decodedWord := by
  obtain ⟨layout, hlayout, hmem, -, -, hrows⟩ := hdecoded
  obtain ⟨p, hp, haddr, hcomp, hdec⟩ :=
    exists_of_forall₂_right hrows row (Array.mem_toList_iff.mpr hrow)
  obtain ⟨hall, hinit, range, hrange, dataRanges, segment, hsegment, ps, hdecode, hpin⟩ :=
    ElfSections.layout?_parcel hlayout hp
  have hbytes : ∀ k (b : BitVec 8),
      (rangeBytes (elf.loaded.flatMap ElfSection.bytes) segment)[k]? = some b →
        imageByte? program (segment.1 + k) = some b := by
    intro k b hk
    simp only [rangeBytes, List.getElem?_map, Option.map_eq_some_iff] at hk
    obtain ⟨offset, hoffset, rfl⟩ := hk
    obtain ⟨hklt, rfl⟩ := List.getElem?_eq_some_iff.mp hoffset
    rw [List.length_range] at hklt
    rw [List.getElem_range]
    obtain ⟨hr1, hr2⟩ := textSegments_within hsegment (a := segment.1 + k) (by omega) (by omega)
    obtain ⟨q, hq, hq1, hq2⟩ := mergeRanges_covered hrange hr1 hr2
    simp only [List.mem_map, List.mem_filter] at hq
    obtain ⟨section_, ⟨hloaded, htext⟩, rfl⟩ := hq
    have hsome := ElfSection.lastByte_isSome
      (fun e he => List.mem_flatMap.mpr ⟨section_, hloaded, he⟩)
      (of_decide_eq_true (List.mem_filter.mp hloaded).2) htext (hall section_ hloaded) hq1 hq2
    obtain ⟨b', hb'⟩ := Option.isSome_iff_exists.mp hsome
    unfold imageByte?
    rw [hmem, hinit, hb']
    rfl
  obtain ⟨hword, hparcel⟩ := decodeText_parcels program segment.1 _ ps hbytes hdecode p hpin
  refine ⟨p.2, ?_, hdec⟩
  cases hp2 : p.2 with
  | base w =>
    obtain ⟨hw, hlow⟩ := hword w hp2
    refine ⟨?_, by rw [haddr]; exact hw, hlow⟩
    rw [hcomp, hp2]
    rfl
  | compressed h =>
    obtain ⟨hh, hlow⟩ := hparcel h hp2
    refine ⟨?_, by rw [haddr]; exact hh, hlow⟩
    rw [hcomp, hp2]
    rfl

/-- **A program built from the ELF's sections satisfies `ImageDecoded`.** Each RISC-V row is
`joltDecode` of the encoding the image holds at its address (`DecodedFrom.rowEncoding`).
For example, for the `.text` section at `0x80000000` holding `addi x1, x0, 1`, the ADDI row has
`RowDecodes … (.base 0x00100093)`. -/
theorem _root_.Rv64ProgramImage.DecodedFrom.imageDecoded
    {program : Rv64ProgramImage SourceInstruction} {elf : ElfSections}
    (hdecoded : program.DecodedFrom elf) : ImageDecoded program := by
  intro row hrow i hi
  obtain ⟨e, henc, hdec⟩ := hdecoded.rowEncoding hrow
  rw [hi] at hdec
  obtain ⟨advice, hadvice⟩ := hdec
  cases e with
  | base w => exact ⟨.base w, henc.1, henc.2.1, henc.2.2, advice, hadvice⟩
  | compressed h => exact ⟨.compressed h, henc.1, henc.2.1, henc.2.2, advice, hadvice⟩

/-- **A `jolt.success` row of a program built from the ELF's sections sits on the success
word.** The image holds, at the row's address, an encoding whose decoded word is
`Decode.joltSuccessWord`, `0x0000305B`, because Jolt's `decode_custom` accepts `jolt.success`
only at that exact word. For example, a program whose image holds the ADDI bytes `93 00 10 00`
at `0x80000000` has no `jolt.success` row there.
Jolt at ff6fc6568: `crates/jolt-program/src/image/decode.rs` (`decode_custom`). -/
theorem _root_.Rv64ProgramImage.DecodedFrom.joltSuccess_word
    {program : Rv64ProgramImage SourceInstruction} {elf : ElfSections}
    (hdecoded : program.DecodedFrom elf) {row : SourceInstructionRow SourceInstruction}
    (hrow : row ∈ program.instructions) (hsuccess : row.instruction = .jolt .JoltSuccess) :
    ∃ e : BlockEncoding, RowEncoding program row e ∧ e.decodedWord = Decode.joltSuccessWord := by
  obtain ⟨e, henc, hdec⟩ := hdecoded.rowEncoding hrow
  rw [hsuccess] at hdec
  exact ⟨e, henc, JoltCustomInstruction.decode?_eq_joltSuccess hdec⟩

/-- **A program built from the ELF's sections has only even row addresses.** Each row has the
address of a parcel `decodeText` found, and `decode_text_section` rejects an odd address
(`decodeText_even`).
For example, the ADDI row at `0x80000000` of a one-instruction `.text` section is even. -/
theorem _root_.Rv64ProgramImage.DecodedFrom.rowsAligned
    {program : Rv64ProgramImage SourceInstruction} {elf : ElfSections}
    (hdecoded : program.DecodedFrom elf) : program.RowsAligned := by
  obtain ⟨layout, hlayout, -, -, -, hrows⟩ := hdecoded
  intro row hrow
  obtain ⟨p, hp, haddr, -, -⟩ :=
    exists_of_forall₂_right hrows row (Array.mem_toList_iff.mpr hrow)
  obtain ⟨-, -, -, -, -, segment, -, ps, hdecode, hpin⟩ := ElfSections.layout?_parcel hlayout hp
  have heven := decodeText_even segment.1 _ ps hdecode p hpin
  rw [← haddr] at heven
  simp only [BitVec.getLsbD, Nat.testBit, Nat.shiftRight_zero, Nat.one_and_eq_mod_two, heven,
    bne_self_eq_false]

end WholeRun
