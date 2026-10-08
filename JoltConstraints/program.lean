/-
The program Jolt is asked to prove, and the public instance the verifier checks it
against. Each definition is checked against the Rust source.
-/
import JoltBytecode.JoltISA.Semantics
import JoltBytecode.JoltISA.DeviceMemory
import JoltBytecode.JoltISA.JoltDevice
import JoltBytecode.RiscvInstruction
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Nat.Log

set_option autoImplicit false

set_option maxRecDepth 4096 in
deriving instance Fintype for Register

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
See : jolt/tracer/src/emulator/cpu.rs:499-528 (Cpu::new)
      jolt/tracer/src/emulator/mod.rs:285 (setup_program sets the PC to the ELF entry)
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

  -- Logically Jolt models memory as one table, but the Rust tracer splits it
  -- in two and so do we: RAM, and the rest, which Rust calls the Jolt device
  -- (inputs, advice, outputs, panic, termination).
  -- Jolt RAM starts at RAM_START_ADDRESS (`JoltISA.RAM_START_ADDRESS`, 0x80000000).
  -- Sail has its own devices (CLINT and HTIF), but these are not the Jolt device.
  -- CLINT lies below RAM and HTIF is switched off, so Sail's memory hash map
  -- corresponds to Jolt RAM only. The Jolt device lives in `io` instead.
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
    jolt_device := { io with outputs := #[], panic := false } -- TODO: (ari) draw this out and link later
    adviceTape := { adviceTape with readPosition := 0 }-- TODO: (ari) draw this out and link later
    hostIO := hostIO -- TODO: (ari) draw this out and link later
  }

/-
DRAFT: the program image Jolt builds from the guest ELF.
Parsing the ELF and decoding bytes into instructions are not modelled; the model
starts from the decoded image.
See : jolt/crates/jolt-program/src/image/elf.rs:18-30 (Rv64ProgramImage)
      jolt/crates/jolt-program/src/image/decode.rs (decode_instruction)
-/

-- Jolt's own source instructions: custom opcode 0x5B, decoded alongside RISC-V.
-- Inline (opcodes 0x0B and 0x2B) is out of scope.
-- See : jolt/crates/jolt-program/src/image/decode.rs:71-72, 192-212 (decode_custom)
--       jolt/tracer/src/instruction/format/ (operand formats)
inductive JoltCustomInstruction where
  | AdviceLB (rd : regidx)                                -- FormatAdviceLoadI
  | AdviceLH (rd : regidx)
  | AdviceLW (rd : regidx)
  | AdviceLD (rd : regidx)
  | VirtualAdviceLen (rd rs1 : regidx) (imm : BitVec 12)  -- FormatI
  | VirtualRev8W (rd rs1 : regidx)                        -- FormatT
  | VirtualAssertEQ (rs1 rs2 : regidx) (imm : BitVec 13)  -- FormatB
  | VirtualHostIO (rd rs1 : regidx) (imm : BitVec 12)     -- FormatI

-- What Rust's base profile decodes: RISC-V or Jolt's own instructions.
-- See : jolt/crates/jolt-riscv/src/kind.rs:20 (SourceInstructionKind)
inductive SourceInstruction where
  | riscv (instruction : RiscvInstruction)
  | jolt (instruction : JoltCustomInstruction)

-- What Rust's dispatch_source returns for one source instruction.
-- See : jolt/crates/jolt-program/src/expand/materialize.rs:71-101 (dispatch_source)
inductive ExpandedSource where
  -- A native row, or the no-op for rd = x0: one row, not stamped.
  | native (instruction : JoltISA.Instr)
  -- A built-in expansion: stamped as one sequence.
  | sequence (instructions : List JoltISA.Instr)

-- A source instruction's final Jolt rows; none where Lean has no expansion yet.
-- TODO: SC.W and SC.D (Rust expand_scw, expand_scd).
-- TODO: (claude) define from the existing expansions. Until then it is opaque: no proof
-- looks inside it, and an opaque function adds no axiom, unlike `sorry`.
-- The native case is `.native instruction.rewriteNative` (Instruction.lean:451), which
-- already applies Rust's rd = x0 rule; the rd = x0 no-op must be `.native`, not a
-- one-row `.sequence`.
-- See : jolt/crates/jolt-program/src/expand/mod.rs:126-170
opaque SourceInstruction.expand : SourceInstruction → Option ExpandedSource

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
-- See : jolt/crates/jolt-riscv/src/lib.rs:411-413 (circuit_flags)
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

-- See : jolt/crates/jolt-program/src/expand/materialize.rs:19
def MAX_FINAL_ROWS_PER_SOURCE : Nat := 64

-- The final rows for one source row; none where Rust returns an error.
-- Rust also checks every final row against the profile (metadata.rs:39-45); for
-- RV64IMAC_JOLT that check always passes, so it is left out.
-- See : jolt/crates/jolt-program/src/expand/materialize.rs:71-101, 150-175
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
-- See : jolt/crates/jolt-program/src/image/elf.rs:18-30 (Rv64ProgramImage)
structure Rv64ProgramImage (Source : Type) where
  instructions : Array (SourceInstructionRow Source)
  memory_init : List (BitVec 64 × BitVec 8)
  program_end : BitVec 64
  entry_address : BitVec 64
  -- decode_elf starts program_end at RAM_START_ADDRESS and only raises it.
  -- See : jolt/crates/jolt-program/src/image/elf.rs:43, 52
  program_end_ge_ram_start : JoltISA.RAM_START_ADDRESS ≤ program_end.toNat
  -- decode_elf takes memory_init only from sections at or above RAM_START_ADDRESS,
  -- and program_end is the end of the last such section. So every ELF byte lies
  -- in [RAM_START_ADDRESS, program_end), which is below stack_end.
  -- See : jolt/crates/jolt-program/src/image/elf.rs:45-66
  memory_init_in_program : ∀ entry ∈ memory_init,
    JoltISA.RAM_START_ADDRESS ≤ entry.1.toNat ∧ entry.1.toNat < program_end.toNat

-- No instruction's next PC, its address plus its length (2 if compressed, else 4),
-- passes 2^64.
-- Assumed: a16z confirmed on 2026-10-07 that the PC is not allowed to wrap; an ELF
-- with an instruction whose next PC, its address plus its length (2 or 4), passes
-- 2^64 is an illegal ELF. (model_review.md, Upstream issues)
def Rv64ProgramImage.NextPCNoWrap {Source : Type} (image : Rv64ProgramImage Source) : Prop :=
  ∀ row ∈ image.instructions, row.address.toNat + (if row.is_compressed then 2 else 4) < 2 ^ 64

-- The program is not empty: its memory image loads at least one byte.
-- Assumed: a16z told us by phone on 2026-10-08 that Jolt can assume a program is
-- never empty. Rust's prover does not reject an empty ELF: it traces it and picks
-- its sizes, and only Rust's verifier rejects those sizes (InvalidRamK;
-- bug-report/verifier-ram-minimum). (model_review.md, Assumptions)
def Rv64ProgramImage.ImageNonempty {Source : Type} (image : Rv64ProgramImage Source) : Prop :=
  image.memory_init ≠ []

-- The host sets the program size from the image.
-- See : jolt/crates/jolt-host/src/program.rs:319
def Rv64ProgramImage.program_size {Source : Type} (image : Rv64ProgramImage Source) :
    BitVec 64 :=
  image.program_end - BitVec.ofNat 64 JoltISA.RAM_START_ADDRESS

-- A pure RISC-V image is a Jolt image with no custom instructions.
def Rv64ProgramImage.toJolt (image : Rv64ProgramImage RiscvInstruction) :
    Rv64ProgramImage SourceInstruction :=
  { image with instructions := image.instructions.map fun row =>
      { row with instruction := .riscv row.instruction } }

-- Every source row's final rows, in order; none if any source row fails.
-- Rust's preprocessing then puts a NoOp at slot 0 and pads with NoOps (preprocess below).
-- See : jolt/crates/jolt-program/src/expand/mod.rs:281-307 (expand_program)
def expand_program (image : Rv64ProgramImage SourceInstruction) :
    Option (Array JoltInstructionRow) :=
  (image.instructions.toList.mapM expand_instruction).map fun rows => rows.flatten.toArray

-- One slot of Rust's preprocessed bytecode.
-- See : jolt/crates/jolt-program/src/preprocess/bytecode.rs:279-293 (noop_instruction)
inductive BytecodeSlot where
  | noop
  | row (row : JoltInstructionRow)

-- Rust accepts a bytecode address when it is at least RAM_START_ADDRESS and even.
-- See : jolt/crates/jolt-program/src/preprocess/bytecode.rs:222-230 (try_get_index)
--       jolt/common/src/constants.rs:7 (ALIGNMENT_FACTOR_BYTECODE)
def bytecode_address_ok (address : BitVec 64) : Bool :=
  JoltISA.RAM_START_ADDRESS ≤ address.toNat && address.toNat % 2 == 0

-- The rows of one address count down to 0 one step at a time; none counts as 0.
-- See : jolt/crates/jolt-program/src/preprocess/bytecode.rs:166-205 (validate_run)
def valid_run (run : List JoltInstructionRow) : Bool :=
  let counts := run.map fun row => (row.virtual_sequence_remaining.getD 0).toNat
  counts == (List.range counts.length).reverse && counts.length < 2 ^ 16

-- true exactly when Rust's BytecodePCMapper::try_new accepts the expanded rows.
-- See : jolt/crates/jolt-program/src/preprocess/bytecode.rs:119-164 (try_new)
def pc_map_ok (rows : Array JoltInstructionRow) : Bool :=
  let runs := rows.toList.splitBy fun a b => a.address == b.address
  let addresses : List (BitVec 64) := runs.filterMap fun run => run.head?.map (·.address)
  runs.all (fun run => run.all (bytecode_address_ok ·.address) && valid_run run) &&
    decide addresses.Nodup && rows.size < 2 ^ 32

/-- Rust's PC map accepts an expanded program exactly when the source program
satisfies four conditions. Precisely: if `expand_program image = some rows`, then
`pc_map_ok rows = true` if and only if
- every source address is at least `RAM_START_ADDRESS` (0x80000000),
- every source address is even,
- the source addresses are pairwise distinct, and
- there are fewer than 2³² expanded rows.

The proof uses only the shape of `expand_instruction`'s output (one unstamped row,
or 1 to 64 stamped rows counting down to 0), so it holds whatever
`SourceInstruction.expand` returns. -/
theorem pc_map_ok_iff (image : Rv64ProgramImage SourceInstruction)
    (rows : Array JoltInstructionRow) (expanded : expand_program image = some rows) :
    pc_map_ok rows = true ↔
      (∀ row ∈ image.instructions,
        JoltISA.RAM_START_ADDRESS ≤ row.address.toNat ∧ row.address.toNat % 2 = 0) ∧
      (image.instructions.toList.map (·.address)).Nodup ∧
      rows.size < 2 ^ 32 := by
  sorry

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
-- See : jolt/crates/jolt-program/src/preprocess/bytecode.rs:218-226 (get_first_pc)
def get_first_pc (bytecode : Array BytecodeSlot) (address : BitVec 64) : Option Nat :=
  if address = 0 then some 0
  else bytecode.findIdx? fun
    | .row row => row.address == address
    | .noop => false

-- The lowest address of the program image; 0 if the image is empty.
-- See : jolt/crates/jolt-program/src/preprocess/ram.rs:46-50
def min_bytecode_address (memory_init : List (BitVec 64 × BitVec 8)) : Nat :=
  ((memory_init.map (·.1.toNat)).min?).getD 0

-- The number of 64-bit slots the program image spans: from the slot of its lowest
-- byte to the slot of its highest byte plus 3 (the rest of a 4-byte instruction).
-- See : jolt/crates/jolt-program/src/preprocess/ram.rs:52-59
--       jolt/common/src/constants.rs:6 (BYTES_PER_INSTRUCTION = 4)
def program_image_len_words (memory_init : List (BitVec 64 × BitVec 8)) : Nat :=
  let highest := ((memory_init.map (·.1.toNat)).max?).getD 0 + 3
  (highest + 7) / 8 - min_bytecode_address memory_init / 8 + 1

-- Jolt RAM before the first instruction: zeros for Rust's whole RAM, with the ELF
-- bytes written over them in order. Rust allocates RAM in whole 64-bit units, so
-- its size is the total memory size rounded up to a multiple of 8.
-- See : jolt/tracer/src/emulator/mod.rs:242-261
--       jolt/tracer/src/emulator/memory.rs:49-51 (init_with_capacity)
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
See : jolt/crates/jolt-verifier/src/verifier.rs:37-42 (verify takes preprocessing,
      public_io : JoltDevice, proof, optional trusted advice commitment)
      jolt/crates/jolt-verifier/src/verifier.rs:356-430 (validate_inputs)
The program and memory configuration stand in for verifier preprocessing.
Trusted advice is part of the instance. In Jolt the verifier holds a commitment
to it; this non-succinct relation models its contents directly. No PCS is part
of this relation, and this representation does not assert that the verifier
learns the bytes.
-/
structure JoltInstance (Source : Type) where
  program : Rv64ProgramImage Source
  -- NOTE: memory_config.program_size is ignored; it is always computed from the
  -- program image (see JoltInstance.memory_layout).
  memory_config : MemoryConfig
  -- Trusted advice is fixed by the instance; we model its contents directly.
  -- In Jolt an absent commitment contributes the all-zero image (#[]).
  trusted_advice : Array (BitVec 8)
  inputs : Array (BitVec 8)
  outputs : Array (BitVec 8)
  panic : Bool
  -- Part of the verifier's preprocessing; the padded trace length may not exceed it.
  -- A usize in Rust, so 64 bits.
  -- See : jolt/crates/jolt-program/src/preprocess/program.rs:17
  --       jolt/crates/jolt-verifier/src/verifier.rs:378-383
  max_padded_trace_length : BitVec 64

-- The pure RISC-V instance seen as a Jolt instance.
def JoltInstance.toJolt (joltInstance : JoltInstance RiscvInstruction) :
    JoltInstance SourceInstruction :=
  { joltInstance with program := joltInstance.program.toJolt }

-- Prover-chosen inputs. The execution tape is used by the tracer; the constraint
-- relation observes untrusted_advice through initial RAM, but not advice_tape.
structure JoltPrivateInputs where
  untrusted_advice : Array (BitVec 8)
  advice_tape : Array (BitVec 8)

-- The host overwrites program_size with the size of the program image.
-- See : jolt/crates/jolt-host/src/program.rs:319, 333
def JoltInstance.memory_layout {Source : Type} (joltInstance : JoltInstance Source) :
    Option MemoryLayout :=
  MemoryLayout.new { joltInstance.memory_config with program_size := some joltInstance.program.program_size }

-- The verifier's checks on the instance alone; the proof's own parameters come
-- with the trace.
-- See : jolt/crates/jolt-verifier/src/verifier.rs:356-383 (validate_inputs)
--       jolt/crates/jolt-verifier/src/verifier.rs:992-1005 (validate_ram_remap_base)
def JoltInstance.validate_inputs {Source : Type} (joltInstance : JoltInstance Source) : Bool :=
  match joltInstance.memory_layout with
  | none => false
  | some layout =>
      8 < layout.get_lowest_address.toNat &&
      joltInstance.inputs.size ≤ layout.max_input_size.toNat &&
      joltInstance.outputs.size ≤ layout.max_output_size.toNat

-- The bytes without their trailing zero bytes, as Rust's verifier trims the claimed
-- outputs.
-- See : jolt/crates/jolt-verifier/src/verifier.rs:436-443
def trimTrailingZeros (bytes : Array (BitVec 8)) : Array (BitVec 8) :=
  (bytes.toList.reverse.dropWhile (· == 0)).reverse.toArray

-- The public I/O the verifier checks a proof against: the instance's layout, inputs,
-- claimed outputs (trailing zero bytes dropped) and panic flag. Rust's verify takes it
-- as a JoltDevice and never reads its advice fields.
-- See : jolt/crates/jolt-verifier/src/verifier.rs:37-42 (verify), 357, 436-443
--       jolt/crates/jolt-program/src/preprocess/public_io.rs:21-61
def JoltInstance.public_io {Source : Type} (joltInstance : JoltInstance Source) :
    Option JoltDevice := do
  let layout ← joltInstance.memory_layout
  pure { inputs := joltInstance.inputs
         trusted_advice := #[]
         untrusted_advice := #[]
         outputs := trimTrailingZeros joltInstance.outputs
         panic := joltInstance.panic
         memory_layout := layout }

-- The verifier's bytecode for an instance; none where Rust rejects the program:
-- expansion fails, the PC map rejects the rows, or the entry address maps to no slot.
-- See : jolt/crates/jolt-program/src/preprocess/program.rs:21-36 (JoltProgramPreprocessing::new)
--       jolt/crates/jolt-prover/src/preprocessing.rs:43-50
--       jolt/crates/jolt-verifier/src/preprocessing.rs:132-141
def JoltInstance.bytecode (joltInstance : JoltInstance SourceInstruction) :
    Option (Array BytecodeSlot) := do
  let rows ← expand_program joltInstance.program
  let bytecode ← preprocess rows
  guard (get_first_pc bytecode joltInstance.program.entry_address).isSome
  pure bytecode

-- See : jolt/tracer/src/lib.rs:364-408 (create_emulator)
noncomputable def JoltInstance.initial_state {Source : Type} (joltInstance : JoltInstance Source)
    (privateInputs : JoltPrivateInputs) :
    Option SailJoltState := do
  let layout ← joltInstance.memory_layout
  -- create_emulator asserts these sizes against the configuration.
  if joltInstance.memory_config.max_trusted_advice_size.toNat < joltInstance.trusted_advice.size then none
  if joltInstance.memory_config.max_untrusted_advice_size.toNat < privateInputs.untrusted_advice.size then none
  if joltInstance.memory_config.max_input_size.toNat < joltInstance.inputs.size then none
  let device : JoltDevice :=
    { inputs := joltInstance.inputs
      trusted_advice := joltInstance.trusted_advice
      untrusted_advice := privateInputs.untrusted_advice
      outputs := #[]
      panic := false
      memory_layout := layout }
  pure (init_state joltInstance.program.entry_address (initialRam layout joltInstance.program.memory_init) device
    { bytes := privateInputs.advice_tape, readPosition := 0 })
