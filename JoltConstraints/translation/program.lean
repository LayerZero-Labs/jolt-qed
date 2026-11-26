/-
The program Jolt is asked to prove, and the public instance the verifier checks it
against. Each definition is checked against the Rust source.
-/
import JoltConstraints.translation.expansions
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Nat.Log

open LeanRV64D

set_option autoImplicit false

-- `Register` is a Sail enumeration of 181 constructors.
-- Mathlib's `deriving instance Fintype` needs a raised recursion depth and a relaxed
-- transparency setting at this size, so the instance goes through the constructor index instead.
-- The bound `181` only has to be an upper bound on the number of constructors.
-- (`Register.ofNat_ctorIdx` is generated with the enumeration.)
theorem LeanRV64D.Register.ctorIdx_lt (r : Register) : r.ctorIdx < 181 := by
  cases r <;> decide

theorem LeanRV64D.Register.ctorIdx_injective : Function.Injective Register.ctorIdx := fun a b h =>
  (Register.ofNat_ctorIdx a).symm.trans ((congrArg Register.ofNat h).trans (Register.ofNat_ctorIdx b))

noncomputable instance : Fintype Register :=
  haveI : Finite Register :=
    Finite.of_injective (β := Fin 181) (fun r => ⟨r.ctorIdx, r.ctorIdx_lt⟩)
      (fun _ _ h => Register.ctorIdx_injective (congrArg Fin.val h))
  Fintype.ofFinite Register

def ramPmaRegion (ramSize : Nat) : PMA_Region :=
  { base := BitVec.ofNat 64 JoltISA.RAM_START_ADDRESS
    size := BitVec.ofNat 64 ramSize
    attributes :=
      { cacheable := true
        coherent := true
        executable := true
        readable := true
        writable := true
        read_idempotent := true
        write_idempotent := true
        misaligned_fault := .NoFault
        atomic_support := .AMOArithmetic
        reservability := .RsrvEventual
        supports_cbo_zero := false
        supports_pte_read := false
        supports_pte_write := false }
    include_in_device_tree := false }

/-
Jolt initialises its register file according to this rule. 
See : jolt/tracer/src/emulator/cpu.rs:463-495 (Cpu::new)
      jolt/tracer/src/emulator/mod.rs:359 (setup_program sets the PC to the ELF entry)
-/
def initialRegisterValue (entryAddress : BitVec 64) (ramSize : Nat)
    (register : Register) : RegisterType register :=
  match register with
  | .PC | .nextPC => entryAddress
  | .misa => 0x800000008014312f
  | .cur_privilege => .Machine
  | .hart_state => .HART_ACTIVE ()
  | .pma_regions => [ramPmaRegion ramSize]
  | register => by cases register <;> exact default

/-
Before anythign happens Jolt's inital CPU states based on this function.
-/ 
noncomputable def init_state
    (entryAddress : BitVec 64)
    (ram : Array (BitVec 8))
    (io : JoltDevice)
    (adviceTape : JoltAdviceTape)
    (hostIO : JoltHostIOConfig := {}) :
    SailJoltState :=

  -- In the Lean model for Jolt the RISC-V general purpose registers 
  -- are not the first 32 virtual registers,
  -- but they are instead stored in the Sail Hashmap.
  -- So we need to set them to zero explicitly.
  let registers : Std.ExtDHashMap Register RegisterType :=
    (Finset.univ.toList : List Register).foldl
      (fun regs r => regs.insert r (initialRegisterValue entryAddress ram.size r))
      {}

  -- The bootstrap map contains the program/RAM bytes.
  -- `JoltISA.initialState` installs I/O bytes and the code guard in this same map.
  let memory : Std.ExtHashMap Nat (BitVec 8) :=
    ram.toList.zipIdx.foldl
      (fun mem (byte, offset) => mem.insert (JoltISA.RAM_START_ADDRESS + offset) byte)
      {}

  let sail : SailState :=
    { regs := registers
      mem := memory
      choiceState := ()
      tags := ()
      cycleCount := 0
      sailOutput := #[] }

  { sail := sail
    vregs := fun _ => 0 -- Jolt initialises all virtual registers to zero.
    jolt_device := { io with panic := false } -- TODO: (ari) draw this out and link later
    adviceTape := { adviceTape with readPosition := 0 }-- TODO: (ari) draw this out and link later
    hostIO := hostIO -- TODO: (ari) draw this out and link later
  }

/-
DRAFT: the program image Jolt builds from the guest ELF.
Parsing the ELF and decoding bytes into instructions are not modelled; the model
starts from the decoded image.
See : jolt/crates/jolt-program/src/image/elf.rs:26-44 (Rv64ProgramImage)
      jolt/crates/jolt-program/src/image/decode.rs (decode_instruction)
-/

-- The source instruction types and `SourceInstruction.expand` are in
-- `expansion_helpers.lean` and `expansions.lean`.

-- See : jolt/crates/jolt-riscv/src/row.rs:74-82 (JoltInstructionRow)
structure JoltInstructionRow where
  instruction : JoltISA.Instr
  address : BitVec 64
  virtual_sequence_remaining : Option (BitVec 16)
  is_first_in_sequence : Bool
  is_compressed : Bool

-- A row where a source instruction's rows begin: a native row, or the first row
-- of a sequence.
def JoltInstructionRow.starts_source (row : JoltInstructionRow) : Bool :=
  row.virtual_sequence_remaining.isNone || row.is_first_in_sequence

-- A row that is not the last row of its source instruction: more rows of the same
-- instruction follow. Rust's DoNotUpdateUnexpandedPC flag.
-- See : jolt/crates/jolt-riscv/src/lib.rs:487-489 (circuit_flags)
def JoltInstructionRow.continues (row : JoltInstructionRow) : Bool :=
  row.virtual_sequence_remaining.getD 0 != 0

-- See : jolt/crates/jolt-program/src/expand/metadata.rs:25-53 (stamp_sequence_metadata)
def stamp_sequence (address : BitVec 64) (is_compressed : Bool)
    (instructions : List JoltISA.Instr) : List JoltInstructionRow :=
  let len := instructions.length
  instructions.zipIdx.map fun (instruction, index) =>
    { instruction := instruction
      address := address
      virtual_sequence_remaining := some (BitVec.ofNat 16 (len - index - 1))
      is_first_in_sequence := index == 0
      is_compressed := index == len - 1 && is_compressed }

-- See : jolt/crates/jolt-riscv/src/row.rs:45-51 (SourceInstructionRow)
structure SourceInstructionRow (Source : Type) where
  address : BitVec 64
  instruction : Source
  is_compressed : Bool

-- See : jolt/crates/jolt-program/src/expand/materialize.rs:20
def MAX_FINAL_ROWS_PER_SOURCE : Nat := 64

-- The final rows for one source row; none where Rust returns an error.
-- Rust also checks every final row against the profile
-- (crates/jolt-program/src/expand/metadata.rs:39-45); for
-- RV64IMAC_JOLT that check always passes, so it is left out.
-- See : jolt/crates/jolt-program/src/expand/materialize.rs:75-105, 150-175
--       jolt/crates/jolt-program/src/expand/metadata.rs:25-53
--       jolt/crates/jolt-riscv/src/row.rs:53-68 (native rows)
def expand_instruction (row : SourceInstructionRow SourceInstruction) :
    Option (List JoltInstructionRow) :=
  match row.instruction.expand with
  | none => none
  | some (.native instruction) =>
      some [{ instruction := instruction
              address := row.address
              virtual_sequence_remaining := none
              is_first_in_sequence := false
              is_compressed := row.is_compressed }]
  | some (.sequence instructions) =>
      if instructions.isEmpty || MAX_FINAL_ROWS_PER_SOURCE < instructions.length then none
      else some (stamp_sequence row.address row.is_compressed instructions)

-- Source is RiscvInstruction for a pure RISC-V ELF, and SourceInstruction for
-- any ELF Jolt's base profile accepts.
-- See : jolt/crates/jolt-program/src/image/elf.rs:26-44 (Rv64ProgramImage)
structure Rv64ProgramImage (Source : Type) where
  instructions : Array (SourceInstructionRow Source)
  memory_init : List (BitVec 64 × BitVec 8)
  program_end : BitVec 64
  entry_address : BitVec 64

  -- Facts that the fields above must satisfy.
  -- Provide proofs of these facts when constructing the image.
  -- decode_elf starts program_end at RAM_START_ADDRESS and only raises it.
  -- See : jolt/crates/jolt-program/src/image/elf.rs:57, 52
  program_end_ge_ram_start : JoltISA.RAM_START_ADDRESS ≤ program_end.toNat
  -- decode_elf takes memory_init only from sections at or above RAM_START_ADDRESS,
  -- and program_end is the end of the last such section. So every ELF byte lies
  -- in [RAM_START_ADDRESS, program_end), which is below stack_end.
  -- See : jolt/crates/jolt-program/src/image/elf.rs:83-125
  memory_init_in_program : ∀ entry ∈ memory_init,
    (JoltISA.RAM_START_ADDRESS ≤ entry.1.toNat) ∧ (entry.1.toNat < program_end.toNat)
  -- decode_elf rejects a section whose end, its start plus its size, passes 2^64 - 1,
  -- and decode_text_section rejects an instruction cut off at the end of its text
  -- range. So every instruction's next PC, its address plus its length (2 if
  -- compressed, else 4), is below 2^64. For example, an ELF with an instruction
  -- at 2^64 - 4 is rejected with "section extent overflows address space".
  -- Jolt added the check in a16z/jolt#2129.
  -- See : jolt/crates/jolt-program/src/image/elf.rs:88-97 (decode_elf),
  --       118-141 (decode_text_section)
  next_pc_no_wrap : ∀ row ∈ instructions,
    row.address.toNat + (if row.is_compressed then 2 else 4) < 2 ^ 64
  -- decode_text_section emits an instruction only when its first halfword is nonzero:
  -- it skips a zero halfword as padding, and a 4-byte instruction's first byte ends in
  -- binary 11. decode_elf reads that halfword from the section bytes it also puts in
  -- memory_init, and reads an address that no section loads as 0. So memory_init holds
  -- a byte at each instruction's address or at the next address.
  -- For example, an ELF whose text section is empty has no instructions.
  -- See : jolt/crates/jolt-program/src/image/elf.rs:121-140 (decode_elf),
  --       201-228 (decode_text_section)
  instruction_loaded : ∀ row ∈ instructions, ∃ entry ∈ memory_init,
    row.address.toNat ≤ entry.1.toNat ∧ entry.1.toNat < row.address.toNat + 2

-- No instruction's next PC, its address plus its length (2 if compressed, else 4),
-- passes 2^64. Every image meets this: it is the field `next_pc_no_wrap`, which
-- holds because Jolt's ELF decoder rejects any program that breaks it.
def Rv64ProgramImage.NextPCNoWrap {Source : Type} (image : Rv64ProgramImage Source) : Prop :=
  ∀ row ∈ image.instructions, row.address.toNat + (if row.is_compressed then 2 else 4) < 2 ^ 64

-- The program is not empty: its memory image loads at least one byte.
-- Every program whose run passes the prover's sizing meets this
-- (`HonestTrace.prover_config_image_nonempty`): the prover rejects an empty trace,
-- and a program with an instruction loads that instruction's bytes.
def Rv64ProgramImage.ImageNonempty {Source : Type} (image : Rv64ProgramImage Source) : Prop :=
  image.memory_init ≠ []

-- The host sets the program size from the image.
-- See : jolt/crates/jolt-host/src/program.rs:357-358, 482-492 (ff6fc6568)
def Rv64ProgramImage.program_size {Source : Type} (image : Rv64ProgramImage Source) :
    BitVec 64 :=
  image.program_end - BitVec.ofNat 64 JoltISA.RAM_START_ADDRESS

-- A pure RISC-V image is a Jolt image with no custom instructions.
def Rv64ProgramImage.toJolt (image : Rv64ProgramImage RiscvInstruction) : Rv64ProgramImage SourceInstruction :=
  { image with
    instructions := image.instructions.map fun row =>
      { row with instruction := .riscv row.instruction }
    next_pc_no_wrap := fun row member => by
      obtain ⟨source, inImage, rfl⟩ := Array.mem_map.mp member
      exact image.next_pc_no_wrap source inImage
    instruction_loaded := fun row member => by
      obtain ⟨source, inImage, rfl⟩ := Array.mem_map.mp member
      exact image.instruction_loaded source inImage }

-- Every source row's final rows, in order; none if any source row fails.
-- Rust's preprocessing then puts a NoOp at slot 0 and pads with NoOps (preprocess below).
-- See : jolt/crates/jolt-program/src/expand/mod.rs:286-312 (expand_program)
def expand_program (image : Rv64ProgramImage SourceInstruction) :
    Option (Array JoltInstructionRow) :=
  (image.instructions.toList.mapM expand_instruction).map fun rows => rows.flatten.toArray

-- One slot of Rust's preprocessed bytecode.
-- See : jolt/crates/jolt-program/src/preprocess/bytecode.rs:307-321 (noop_instruction)
inductive BytecodeSlot where
  | noop
  | row (row : JoltInstructionRow)

-- Rust accepts a bytecode address when it is at least RAM_START_ADDRESS and even.
-- See : jolt/crates/jolt-program/src/preprocess/bytecode.rs:250-258 (try_get_index)
--       jolt/common/src/constants.rs:7 (ALIGNMENT_FACTOR_BYTECODE)
def bytecode_address_ok (address : BitVec 64) : Bool :=
  JoltISA.RAM_START_ADDRESS ≤ address.toNat && address.toNat % 2 == 0

/-- The explicit halt kind of a bytecode instruction, if it has one.
For example, `Panic` is a panic halt and `JAL` has no halt kind.
Jolt at `ff6fc6568`: `tracer/src/emulator/cpu.rs` (`Cpu::halt`).
This instruction classifier is a candidate to move into JoltBytecode. -/
def JoltISA.Instr.haltKind? : JoltISA.Instr → Option JoltHaltKind
  | .JoltSuccess _ => some .success
  | .Panic _ => some .panic
  | _ => none

-- The rows of one address count down to 0 one step at a time; none counts as 0.
-- Jolt at ff6fc6568: crates/jolt-program/src/preprocess/bytecode.rs
-- (BytecodePCMapper::validate_run, BytecodePCMapper::try_new).
-- A halt can occupy only a one-row source instruction.
def valid_run (run : List JoltInstructionRow) : Bool :=
  let counts := run.map fun row => (row.virtual_sequence_remaining.getD 0).toNat
  (counts == (List.range counts.length).reverse && counts.length < 2 ^ 16) &&
    (counts.length ≤ 1 || run.all fun row => row.instruction.haltKind?.isNone)

-- true exactly when Rust's BytecodePCMapper::try_new accepts the expanded rows.
-- See : jolt/crates/jolt-program/src/preprocess/bytecode.rs:128-187 (try_new)
def pc_map_ok (rows : Array JoltInstructionRow) : Bool :=
  let runs := rows.toList.splitBy fun a b => a.address == b.address
  let addresses : List (BitVec 64) := runs.filterMap fun run => run.head?.map (·.address)
  runs.all (fun run => run.all (bytecode_address_ok ·.address) && valid_run run) &&
    decide addresses.Nodup && rows.size < 2 ^ 32

-- Rust's preprocess: reject what the PC map rejects, then a NoOp at slot 0, the
-- expanded rows, and NoOps up to a power of two, at least 2.
-- Rust also checks each row against the profile and that no store names rd; the
-- first always passes for RV64IMAC_JOLT and Lean's SD has no destination.
-- See : jolt/crates/jolt-program/src/preprocess/bytecode.rs:32-58 (preprocess)
def preprocess (rows : Array JoltInstructionRow) : Option (Array BytecodeSlot) :=
  if pc_map_ok rows then
    let slots : Array BytecodeSlot := #[.noop] ++ rows.map .row
    some (slots ++ Array.replicate (max 2 (2 ^ Nat.clog 2 slots.size) - slots.size) .noop)
  else none

-- The slot where the source instruction at `address` starts; address 0 is the
-- NoOp at slot 0. Matches Rust whenever pc_map_ok holds.
-- See : jolt/crates/jolt-program/src/preprocess/bytecode.rs:246-254 (get_first_pc)
def get_first_pc (bytecode : Array BytecodeSlot) (address : BitVec 64) : Option Nat :=
  if address = 0 then some 0
  else bytecode.findIdx? fun
    | .row row => row.address == address
    | .noop => false

/-- Source byte extents extracted from the last row at each expanded source address.
For example, a compressed source contributes two bytes even if its earlier rows
carry an uncompressed stamp.
Jolt at `ff6fc6568`: `crates/jolt-program/src/preprocess/ram.rs`
(`bytecode_source_extents`). -/
def bytecode_source_extents (rows : Array JoltInstructionRow) : List (BitVec 64 × Bool) :=
  (rows.toList.filter fun row => row.virtual_sequence_remaining.getD 0 == 0).map
    fun row => (row.address, row.is_compressed)

/-- Compute a checked code-word interval within the layout's maximum RAM domain.
For example, a source beyond the maximum padded RAM end is rejected.
An empty interval has the unique encoding `(0, 0)`.
Jolt at `ff6fc6568`: `crates/jolt-program/src/preprocess/ram.rs`
(`code_region`, `validate_code_region`).
This checked primitive is a candidate to move into JoltBytecode. -/
def JoltISA.checkedCodeRegion (layout : MemoryLayout) (sources : List (BitVec 64 × Bool)) :
    Option (Nat × Nat) := do
  let region ← JoltISA.codeRegionOf layout sources
  let maximum ← layout.max_ram_k?
  guard (region.1 ≤ region.2 ∧ region.2 ≤ maximum ∧
    (region.1 = region.2 → region.1 = 0))
  pure region

-- The lowest address of the program image; 0 if the image is empty.
-- See : jolt/crates/jolt-program/src/preprocess/ram.rs:55-59
def min_bytecode_address (memory_init : List (BitVec 64 × BitVec 8)) : Nat :=
  ((memory_init.map (·.1.toNat)).min?).getD 0

-- The number of 64-bit slots the program image spans: from the slot of its lowest
-- byte to the slot of its highest byte plus 3 (the rest of a 4-byte instruction).
-- See : jolt/crates/jolt-program/src/preprocess/ram.rs:61-68
--       jolt/common/src/constants.rs:6 (BYTES_PER_INSTRUCTION = 4)
def program_image_len_words (memory_init : List (BitVec 64 × BitVec 8)) : Nat :=
  let highest := ((memory_init.map (·.1.toNat)).max?).getD 0 + 3
  (highest + 7) / 8 - min_bytecode_address memory_init / 8 + 1

-- Jolt RAM before the first instruction: zeros for Rust's whole RAM, with the ELF
-- bytes written over them in order. Rust allocates RAM in whole 64-bit units, so
-- its size is the total memory size rounded up to a multiple of 8.
-- See : jolt/tracer/src/emulator/mod.rs:320-336 at ff6fc6568
--       jolt/tracer/src/emulator/memory.rs:76-78 (init_with_capacity)
-- TODO: (claude) the tracer loads RAM from the ELF section headers, while
-- preprocessing uses decode_elf's memory_init; check that they always agree.
def initialRam (layout : MemoryLayout) (memory_init : List (BitVec 64 × BitVec 8)) :
    Array (BitVec 8) :=
  let zeros := Array.replicate (8 * ((layout.get_total_memory_size.toNat + 7) / 8)) 0
  memory_init.foldl
    (fun ram (address, byte) =>
      if JoltISA.RAM_START_ADDRESS ≤ address.toNat then
        ram.setIfInBounds (address.toNat - JoltISA.RAM_START_ADDRESS) byte
      else ram)
    zeros

/-
The fixed instance and the prover's private execution inputs.
See : jolt/crates/jolt-verifier/src/verifier.rs:51-56 (verify takes preprocessing,
      public_io : JoltDevice, proof, optional trusted advice commitment)
      jolt/crates/jolt-verifier/src/verifier.rs:491-557 (validate_inputs)
The program and memory configuration stand in for verifier preprocessing.

NOTE: the PCS is ignored for now. This differs from the inputs of Jolt's verifier
in two ways:
1. Trusted advice. Jolt's verifier receives only a commitment to it
   (`trusted_advice_commitment`); this relation holds the bytes themselves. That
   the commitment fixes the bytes is a PCS property, outside this model. This
   representation does not assert that the verifier learns the bytes.
2. Omitted: `preprocessing.pcs_setup`, `preprocessing.vc_setup` and
   `preprocessing.preprocessing_digest`. They serve only the PCS and transcript.
   See : jolt/crates/jolt-verifier/src/preprocessing.rs:241-252 at ff6fc6568
-/
structure JoltInstance (Source : Type) where
  program : Rv64ProgramImage Source
  -- NOTE: memory_config.program_size is ignored; it is always computed from the
  -- program image (see JoltInstance.memory_layout).
  memory_config : MemoryConfig
  -- Trusted advice is fixed by the instance; we model its contents directly.
  -- In Jolt an absent commitment contributes the all-zero image (#[]).
  -- Differs from Rust: Jolt's verifier holds a commitment, not these bytes
  -- (NOTE above).
  trusted_advice : Array (BitVec 8)
  inputs : Array (BitVec 8)
  outputs : Array (BitVec 8)
  panic : Bool
  -- Part of the verifier's preprocessing; the padded trace length may not exceed it.
  -- A usize in Rust, so 64 bits.
  -- See : jolt/crates/jolt-program/src/preprocess/program.rs:20
  --       jolt/crates/jolt-verifier/src/verifier.rs:509-514
  max_padded_trace_length : BitVec 64

-- The pure RISC-V instance seen as a Jolt instance.
def JoltInstance.toJolt (joltInstance : JoltInstance RiscvInstruction) : JoltInstance SourceInstruction :=
  { joltInstance with program := joltInstance.program.toJolt }

-- Prover-chosen inputs. The execution tape is used by the tracer; the constraint
-- relation observes untrusted_advice through initial RAM, but not advice_tape.
structure JoltPrivateInputs where
  untrusted_advice : Array (BitVec 8)
  advice_tape : Array (BitVec 8)

-- The host overwrites program_size with the size of the program image.
-- Checked layout failures propagate as none, including a padded I/O start at zero.
-- Rust (ff6fc6568): jolt-sdk/src/host_utils.rs:111-126 (program_preprocessing)
-- https://github.com/a16z/jolt/blob/ff6fc656813d950565c9f6e1258b78bdaf0e60e8/jolt-sdk/src/host_utils.rs#L111-L126
def JoltInstance.memory_layout {Source : Type} (joltInstance : JoltInstance Source) :
    Option MemoryLayout :=
  MemoryLayout.new { joltInstance.memory_config with program_size := some joltInstance.program.program_size }

-- The verifier's checks on the instance alone; the proof's own parameters come
-- with the trace.
-- Jolt at ff6fc6568: crates/jolt-verifier/src/verifier.rs
-- (validate_inputs, validate_entry_row, validate_ram_remap_base).
def JoltInstance.validate_inputs {Source : Type} (joltInstance : JoltInstance Source) : Bool :=
  match joltInstance.memory_layout with
  | none => false
  | some layout =>
      8 < layout.get_lowest_address.toNat &&
      joltInstance.inputs.size ≤ layout.max_input_size.toNat &&
      joltInstance.outputs.size ≤ layout.max_output_size.toNat &&
      (joltInstance.program.entry_address != 0 &&
        (JoltISA.checkedCodeRegion layout
          (joltInstance.program.instructions.toList.map fun row =>
            (row.address, row.is_compressed))).isSome)

-- The bytes without their trailing zero bytes, as Rust's verifier trims the claimed
-- outputs.
-- See : jolt/crates/jolt-verifier/src/verifier.rs:563-570
def trimTrailingZeros (bytes : Array (BitVec 8)) : Array (BitVec 8) :=
  (bytes.toList.reverse.dropWhile (· == 0)).reverse.toArray

/-- Public statement bytes and the halt claim, separate from the execution device.
For example, a success statement contains output bytes and `panic = false`.
Jolt at `ff6fc6568`: `common/src/jolt_device.rs` (`JoltDevice`) and
`crates/jolt-program/src/preprocess/public_io.rs` (`PublicIoMemory::new`). -/
structure JoltPublicIo where
  memory_layout : MemoryLayout
  inputs : Array (BitVec 8)
  outputs : Array (BitVec 8)
  panic : Bool

/-- The verifier's public I/O statement, with trailing output zeros removed.
For example, output `[1, 0]` is represented by `[1]`.
Jolt at `ff6fc6568`: `crates/jolt-program/src/preprocess/public_io.rs`
(`PublicIoMemory::new`). -/
def JoltInstance.public_io {Source : Type} (joltInstance : JoltInstance Source) :
    Option JoltPublicIo := do
  let layout ← joltInstance.memory_layout
  pure { inputs := joltInstance.inputs
         outputs := trimTrailingZeros joltInstance.outputs
         panic := joltInstance.panic
         memory_layout := layout }

-- The verifier's bytecode for an instance; none where Rust rejects the program:
-- expansion fails, the PC map rejects the rows, or the entry address maps to no slot.
-- See : jolt/crates/jolt-program/src/preprocess/program.rs:24-42 (JoltProgramPreprocessing::new)
--       jolt/crates/jolt-prover/src/preprocessing.rs:56-63
--       jolt/crates/jolt-verifier/src/preprocessing.rs:172-181
def JoltInstance.bytecode (joltInstance : JoltInstance SourceInstruction) : Option (Array BytecodeSlot) := do
  let rows ← expand_program joltInstance.program
  let bytecode ← preprocess rows
  guard (get_first_pc bytecode joltInstance.program.entry_address).isSome
  guard (joltInstance.program.entry_address != 0)
  let layout ← joltInstance.memory_layout
  let _ ← JoltISA.checkedCodeRegion layout (bytecode_source_extents rows)
  pure bytecode

/-- **The modelled initial state for an instance and private inputs**, or none where a size
or layout check fails. It builds the checked memory layout, loads the program image as
preprocessing records it (`memory_init`) and the starting registers (`init_state`), and
installs the inputs, the advice and the code guard (`JoltISA.initialState`). The only size
checks are those of `JoltDevice.initialMem`, which, like Jolt's `JoltDevice::try_with_io`,
compare each length with the layout's capacity: the configured maximum rounded up to a
multiple of 8.
This is not exactly the state the tracer's `create_emulator` builds. The tracer loads only
some section types and caps its memory when the ELF has a nonzero `tohost` symbol, so a
readable NOTE section, for example, initializes model RAM but not tracer RAM
(`docs/whole-run-theorem.md`, "Initial memory is preprocessing's, not the tracer's").
For example, `max_input_size = 1` gives an input capacity of 8 bytes, so two input bytes are
accepted and nine are rejected (`initial_state_isSome_iff` in `theorems/layout_facts.lean`).
Jolt at ff6fc6568: `tracer/src/lib.rs` (`create_emulator`) and `common/src/jolt_device.rs`
(`JoltDevice::try_with_io`, `MemoryLayout::try_new`). -/
noncomputable def JoltInstance.initial_state {Source : Type} (joltInstance : JoltInstance Source)
    (privateInputs : JoltPrivateInputs) :
    Option SailJoltState := do
  let layout ← joltInstance.memory_layout
  let device : JoltDevice := { panic := false, memory_layout := layout }
  JoltISA.initialState
    (init_state joltInstance.program.entry_address
      (initialRam layout joltInstance.program.memory_init) device
      { bytes := privateInputs.advice_tape, readPosition := 0 })
    (joltInstance.program.instructions.toList.map fun row => (row.address, row.is_compressed))
    joltInstance.inputs joltInstance.trusted_advice privateInputs.untrusted_advice
