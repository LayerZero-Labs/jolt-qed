import JoltConstraints.theorems.WholeRun.Top
import JoltConstraints.Audit.ImageFields
import Mathlib.Algebra.Field.ZMod

/-!
# Necessity witnesses

A premise of a headline theorem claims that the model does *not* already guarantee something.
Each theorem here tests that claim on concrete data: it builds a model object that breaks the
premise. If a later re-pin transcribes a Jolt check that makes the premise provable at the
boundary the witness tests, the witness stops building, and the premise has to be removed (see
`reports/2026-11-25-stale-assumptions.md`). `assumptions.toml` names each witness in the
`witness` field of its entry, and says in `witness_shows` what it proves.

A witness shows that a headline theorem needs its premise only if the object it builds meets
every other premise of that theorem. The first two witnesses below do not: each tests its
premise against a weaker boundary than the theorem's, so a change that made the premise
redundant given the theorem's other premises would leave them building.

* `joltField_not_implied`: `ZMod 2` is a field that breaks `JoltField`. This shows only that
  `[Field F]` does not imply `JoltField F`. It builds no instance and no assignment of
  `AllConstraints` over `ZMod 2`.
* `blockConformsRiscv_not_implied`: a program that `decode_elf` accepts, with a row of one of
  Jolt's own instructions, so `DecodedFrom` alone does not exclude such rows. It builds no
  trace, so it does not show that a block of an accepted run can break `BlockConforms.riscv`.
* `memoryInitInProgram_not_derived`: a parsed ELF whose layout breaks the image field
  `memory_init_in_program`, so that field is not yet implied by the transcription of
  `decode_elf` (the other three image fields are, see `JoltConstraints/Audit/ImageFields.lean`).

Stronger witnesses for the first two need a concrete program run: an instance outside the
language with a satisfying assignment over a small field, and a `HonestTrace` whose
`HaltPrefix` has a block with a `.jolt` row. `assumptions.toml` lists both as follow-ups.
-/

set_option autoImplicit false

open WholeRun

namespace JoltConstraints.Audit

/-! ## `JoltField` -/

/-- **`[Field F]` does not imply `JoltField F`.** `ZMod 2` is a field of characteristic 2, far
below `2^128 - 2^64`. If the model ever restricted its field so that `JoltField` always held,
this witness would stop building. It says nothing about whether `AllConstraints` can be
satisfied over `ZMod 2` by an instance outside the language. -/
theorem joltField_not_implied : ¬ JoltField (ZMod 2) := by
  rw [JoltField, ZMod.ringChar_zmod_n]
  norm_num

/-! ## `BlockConforms.riscv`

The program below has one `.text` section at `RAM_START_ADDRESS` that holds one word of Jolt's
custom opcode `0x5B`: `0x060000DB`, the advice load `AdviceLD x1` (funct3 `0b000`, funct7 `0x03`;
Jolt at ff6fc6568: `crates/jolt-program/src/image/decode.rs` (`decode_custom`)). -/

/-- One `.text` section at `0x80000000` holding the word `0x060000DB`, little-endian. -/
def customSection : ElfSection where
  address := 0x80000000#64
  size := 4#64
  data := [0xDB#8, 0x00#8, 0x00#8, 0x06#8]
  isText := true
  isWritable := false
  mappingSymbols := []
  text_data_length := fun _ _ => rfl

/-- The parsed ELF: `customSection` and the entry point `0x80000000`. -/
def customElf : ElfSections where
  sections := [customSection]
  entry := 0x80000000#64

/-- What `decode_elf` computes for `customElf`: the four bytes, `program_end = 0x80000004`, and
one 4-byte parcel. -/
def customLayout : ElfLayout where
  memory_init := customSection.bytes
  program_end := 0x80000004#64
  entry_address := 0x80000000#64
  parcels := [(0x80000000, .base 0x060000DB#32)]

theorem customElf_layout : customElf.layout? = some customLayout := by
  simp [ElfSections.layout?, ElfSections.loaded, customElf, customSection, customLayout,
    mergeRanges, ElfSection.endAddress, ElfSection.dataRanges, dataRangesFrom,
    JoltISA.RAM_START_ADDRESS]
  rfl

/-- The one row: `AdviceLD x1` at `0x80000000`, not compressed. -/
def customRow : SourceInstructionRow SourceInstruction where
  address := 0x80000000#64
  instruction := .jolt (.AdviceLD (LeanRV64D.regidx.Regidx 1))
  is_compressed := false

/-- The program Jolt builds from `customElf`. -/
def customProgram : Rv64ProgramImage SourceInstruction where
  instructions := #[customRow]
  memory_init := customSection.bytes
  program_end := 0x80000004#64
  entry_address := 0x80000000#64
  program_end_ge_ram_start := by decide
  memory_init_in_program := by decide
  next_pc_no_wrap := by
    intro row hrow
    simp only [Array.mem_singleton] at hrow
    subst hrow
    decide
  instruction_loaded := by
    intro row hrow
    simp only [Array.mem_singleton] at hrow
    subst hrow
    decide

/-- **`DecodedFrom` admits a row of one of Jolt's own instructions.** `decode_elf` accepts a
program whose only row is `AdviceLD`, which no block theorem covers yet, so `DecodedFrom` alone
does not exclude a program on which `BlockConforms.riscv` could fail. If a re-pin made
`DecodedFrom` reject Jolt's own instructions, this witness would stop building. It builds no
trace, halt or prover configuration, so it does not show that a block of an accepted run breaks
`BlockConforms.riscv`. -/
theorem blockConformsRiscv_not_implied :
    ∃ (elf : ElfSections) (program : Rv64ProgramImage SourceInstruction),
      program.DecodedFrom elf ∧
      ∃ row ∈ program.instructions, ∀ i, row.instruction ≠ .riscv i := by
  refine ⟨customElf, customProgram, ⟨customLayout, customElf_layout, rfl, rfl, rfl, ?_⟩,
    customRow, by simp [customProgram], fun i h => by cases h⟩
  -- The word `0x060000DB` decodes to `AdviceLD x1` through `decode_custom`.
  refine List.Forall₂.cons ⟨rfl, rfl, by rfl⟩ List.Forall₂.nil

/-! ## `memory_init_in_program`

`ElfSection.text_data_length` records that the `object` crate gives a loaded text section
exactly `size` bytes of data. For any other section it records nothing, so the transcription
admits a data section with more bytes than its size, and a byte past `program_end`. The
`object` crate never returns such data (`section.data()` is `sh_size` bytes, or empty for
`SHT_NOBITS`), so this is a gap in what the transcription records, not a difference from Jolt. -/

/-- A non-text section at `0x80000000` with size 0 and one byte of data. -/
def overlongSection : ElfSection where
  address := 0x80000000#64
  size := 0#64
  data := [0#8]
  isText := false
  isWritable := false
  mappingSymbols := []
  text_data_length := fun _ h => absurd h (by decide)

/-- The parsed ELF: `overlongSection` and the entry point `0x80000000`. -/
def overlongElf : ElfSections where
  sections := [overlongSection]
  entry := 0x80000000#64

/-- **The transcription of `decode_elf` does not yet imply `memory_init_in_program`.** The
layout of `overlongElf` loads a byte at `0x80000000` and has `program_end = 0x80000000`.
Recording in `ElfSection` that every loaded section has at most `size` bytes of data would make
the field provable from `DecodedFrom`, and this witness would stop building. -/
theorem memoryInitInProgram_not_derived :
    ∃ (elf : ElfSections) (layout : ElfLayout), elf.layout? = some layout ∧
      ∃ entry ∈ layout.memory_init, layout.program_end.toNat ≤ entry.1.toNat := by
  refine ⟨overlongElf, ⟨overlongSection.bytes, 0x80000000#64, 0x80000000#64, []⟩, ?_,
    (0x80000000#64, 0#8), by decide, by decide⟩
  simp [ElfSections.layout?, ElfSections.loaded, overlongElf, overlongSection,
    mergeRanges, ElfSection.endAddress]
  rfl

end JoltConstraints.Audit
