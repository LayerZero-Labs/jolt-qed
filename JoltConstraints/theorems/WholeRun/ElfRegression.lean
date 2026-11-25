import JoltConstraints.theorems.WholeRun.Elf

/-!
# Regression: a `jolt.success` row must sit on the success word

The audit of 2026-11-25 (finding F1) showed that `Rv64ProgramImage.DecodedFrom` once constrained
only the address and width of a row of one of Jolt's own instructions. A program whose ELF holds
the ADDI bytes `93 00 10 00` at `0x80000000` could then carry the row `.jolt .JoltSuccess` there,
and the whole-run theorems would read that address as a success halt. Jolt's `decode_custom`
accepts `jolt.success` only at the exact word `0x0000305B`.

This file keeps the auditor's example. `uncheckedDecodedFrom` is the relation before the fix:
the example satisfies it, and it does not satisfy `DecodedFrom`. The program built from the
bytes `5B 30 00 00` does satisfy `DecodedFrom` with the row `.jolt .JoltSuccess`, and the ADDI
program does with the row ADDI x1,x0,1.
Jolt at ff6fc6568: `crates/jolt-program/src/image/decode.rs` (`decode_custom`).
-/

set_option autoImplicit false

namespace WholeRun.ElfRegression

/-- One text section at `0x80000000` holding the four bytes `b0 b1 b2 b3`. -/
def wordSection (b0 b1 b2 b3 : BitVec 8) : ElfSection where
  address := 0x80000000
  size := 4
  data := [b0, b1, b2, b3]
  isText := true
  isWritable := false
  mappingSymbols := []
  text_data_length := fun _ _ => rfl

/-- The ELF with the single section `wordSection b0 b1 b2 b3` and entry `0x80000000`. -/
def wordElf (b0 b1 b2 b3 : BitVec 8) : ElfSections where
  sections := [wordSection b0 b1 b2 b3]
  entry := 0x80000000

/-- The one-row program whose image holds `b0 b1 b2 b3` at `0x80000000`, with the row `source`
there. -/
def wordProgram (b0 b1 b2 b3 : BitVec 8) (source : SourceInstruction) :
    Rv64ProgramImage SourceInstruction where
  instructions := #[{ address := 0x80000000, instruction := source, is_compressed := false }]
  memory_init := [(0x80000000, b0), (0x80000001, b1), (0x80000002, b2), (0x80000003, b3)]
  program_end := 0x80000004
  entry_address := 0x80000000
  program_end_ge_ram_start := by decide
  memory_init_in_program := by simp [JoltISA.RAM_START_ADDRESS]
  next_pc_no_wrap := by simp
  instruction_loaded := by simp

/-- The ELF and program with the ADDI x1,x0,1 bytes `93 00 10 00`. -/
abbrev addiElf : ElfSections := wordElf 0x93 0x00 0x10 0x00
abbrev addiProgram (source : SourceInstruction) := wordProgram 0x93 0x00 0x10 0x00 source

/-- The ELF and program with the `jolt.success` bytes `5B 30 00 00`, the word `0x0000305B`. -/
abbrev successElf : ElfSections := wordElf 0x5B 0x30 0x00 0x00
abbrev successProgram (source : SourceInstruction) := wordProgram 0x5B 0x30 0x00 0x00 source

theorem addiElf_layout : addiElf.layout? = some
    { memory_init := (addiProgram (.jolt .JoltSuccess)).memory_init
      program_end := 0x80000004
      entry_address := 0x80000000
      parcels := [(0x80000000, .base 0x00100093)] } := by
  simp [ElfSections.layout?, wordElf, wordSection, ElfSections.loaded, ElfSection.endAddress,
    mergeRanges, ElfSection.dataRanges, dataRangesFrom, textSegments, segmentsFrom, mergeStep,
    ElfSection.bytes, JoltISA.RAM_START_ADDRESS, wordProgram]
  rfl

theorem successElf_layout : successElf.layout? = some
    { memory_init := (successProgram (.jolt .JoltSuccess)).memory_init
      program_end := 0x80000004
      entry_address := 0x80000000
      parcels := [(0x80000000, .base 0x0000305B)] } := by
  simp [ElfSections.layout?, wordElf, wordSection, ElfSections.loaded, ElfSection.endAddress,
    mergeRanges, ElfSection.dataRanges, dataRangesFrom, textSegments, segmentsFrom, mergeStep,
    ElfSection.bytes, JoltISA.RAM_START_ADDRESS, wordProgram]
  rfl

/-- The relation before the fix: a RISC-V row decodes from its parcel's word, and any other row
is constrained only in address and width. -/
def uncheckedRowFromParcel (parcel : Nat × BlockEncoding)
    (row : SourceInstructionRow SourceInstruction) : Prop :=
  row.address.toNat = parcel.1 ∧ row.is_compressed = parcel.2.isCompressed ∧
    ∀ i, row.instruction = .riscv i →
      ∃ advice, Decode.joltDecode parcel.2.decodedWord advice = some i

/-- `DecodedFrom` before the fix, with `uncheckedRowFromParcel` for the rows. -/
def uncheckedDecodedFrom (program : Rv64ProgramImage SourceInstruction) (elf : ElfSections) :
    Prop :=
  ∃ layout, elf.layout? = some layout ∧ program.memory_init = layout.memory_init ∧
    program.program_end = layout.program_end ∧ program.entry_address = layout.entry_address ∧
    List.Forall₂ uncheckedRowFromParcel layout.parcels program.instructions.toList

/-- **The auditor's example.** Before the fix, the ADDI bytes at `0x80000000` with the row
`.jolt .JoltSuccess` satisfied the relation. -/
example : uncheckedDecodedFrom (addiProgram (.jolt .JoltSuccess))
    addiElf :=
  ⟨_, addiElf_layout, rfl, rfl, rfl, .cons ⟨rfl, rfl, fun _ h => by cases h⟩ .nil⟩

/-- **The fix.** `DecodedFrom` rejects the auditor's example: Jolt's custom decoder gives no
`jolt.success` for the ADDI word `0x00100093`. -/
example :
    ¬ (addiProgram (.jolt .JoltSuccess)).DecodedFrom addiElf := by
  rintro ⟨layout, built, -, -, -, rows⟩
  rw [addiElf_layout] at built
  cases built
  obtain ⟨⟨-, -, decodes⟩, -⟩ := List.forall₂_cons.mp rows
  have rejected : JoltCustomInstruction.decode? 0x00100093 = none := rfl
  simp only [SourceInstruction.DecodesFrom, BlockEncoding.decodedWord, rejected,
    reduceCtorEq] at decodes

/-- The same bytes with the row ADDI x1,x0,1 satisfy `DecodedFrom`. -/
example : (addiProgram (.riscv (.ADDI (.Regidx 1) (.Regidx 0) 1))).DecodedFrom
    addiElf :=
  ⟨_, addiElf_layout, rfl, rfl, rfl, .cons ⟨rfl, rfl, 0, rfl⟩ .nil⟩

/-- The success word with the row `.jolt .JoltSuccess` satisfies `DecodedFrom`. -/
example : (successProgram (.jolt .JoltSuccess)).DecodedFrom
    successElf :=
  ⟨_, successElf_layout, rfl, rfl, rfl, .cons ⟨rfl, rfl, rfl⟩ .nil⟩

/-- Jolt's custom decoder rejects the success opcode with a nonzero `rd`: the word `0x0000315B`
sets `rd = 2`. -/
example : JoltCustomInstruction.decode? 0x0000315B = none := rfl

end WholeRun.ElfRegression
