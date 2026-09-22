import JoltBytecode.JoltISA.Instruction
import JoltBytecode.JoltISA.Semantics
import JoltBytecode.JoltISA.DeviceMemory
import Mathlib.Tactic.DeriveFintype

set_option autoImplicit false

-- Rust paths are relative to /Users/ari.biswas/Work-with-A16z/jolt.

-- Derive the enumeration of all Sail registers and its completeness proofs.
-- Generating these proofs exceeds Lean's default elaboration recursion depth.
-- `in` raises the depth limit only for this declaration; runtime execution and
-- proof checking are unchanged, and the heartbeat limit still applies.
set_option maxRecDepth 4096 in
deriving instance Fintype for Register

-- Rust: [Cpu::new](/Users/ari.biswas/Work-with-A16z/jolt/tracer/src/emulator/cpu.rs:516).
-- Integer/FP registers and CSRs start at zero, except misa; privilege is Machine.
-- Sail-only registers use their type's default (zero, false, empty, or inactive).
private def initialRegisterValue (entryAddress : BitVec 64)
    (r : Register) : RegisterType r :=
  match r with
  | .PC | .nextPC => entryAddress
  | .misa => 0x800000008014312f
  | .cur_privilege => .Machine
  | .hart_state => .HART_ACTIVE ()
  | r => by cases r <;> exact default

/-- Assemble the initial ISA state from Rust's loaded RAM, entry address, device
and advice tape. `ram` includes every allocated byte, including zero-filled bytes.

Rust sources:
* [loaded RAM and entry PC](/Users/ari.biswas/Work-with-A16z/jolt/tracer/src/emulator/mod.rs:219)
* [RAM base](/Users/ari.biswas/Work-with-A16z/jolt/common/src/constants.rs:21)
* [device inputs and advice](/Users/ari.biswas/Work-with-A16z/jolt/tracer/src/lib.rs:366)
* [initial device](/Users/ari.biswas/Work-with-A16z/jolt/common/src/jolt_device.rs:110)
* [advice tape and cursor](/Users/ari.biswas/Work-with-A16z/jolt/tracer/src/emulator/cpu.rs:20)

Sail's `nextPC` has no separate Rust field; it starts at the entry address here.
The Sail bookkeeping fields below have no Rust architectural counterpart.
-/
noncomputable def init_state (entryAddress : BitVec 64)
    (ram : Array (BitVec 8)) (io : JoltIOState)
    (adviceTape : JoltAdviceTape) : SailJoltState :=
  { sail :=
      { regs := (Finset.univ.toList : List Register).foldl
          (fun regs r => regs.insert r (initialRegisterValue entryAddress r)) {}
        mem := ram.toList.zipIdx.foldl
          (fun mem (byte, offset) => mem.insert (0x80000000 + offset) byte) {}
        choiceState := ()
        tags := ()
        cycleCount := 0
        sailOutput := #[] }
    vregs := fun _ => 0
    io := io
    adviceTape := adviceTape }

-- Rust: crates/jolt-riscv/src/row.rs::JoltInstructionRow.
structure JoltProgramRow where
  -- Rust: JoltInstructionRow::instruction_kind and operands; ISA: JoltBytecode/JoltISA/Instruction.lean::Instr.
  instruction : JoltISA.Instr
  -- Rust: JoltInstructionRow::address (RV64 instruction byte address).
  address : BitVec 64
  -- Rust: JoltInstructionRow::virtual_sequence_remaining.
  virtualSequenceRemaining : Option (BitVec 16)
  -- Rust: JoltInstructionRow::is_first_in_sequence.
  isFirstInSequence : Bool
  -- Rust: JoltInstructionRow::is_compressed.
  isCompressed : Bool

/-- Static bytecode and the complete initial state for one execution.
Rust stores the [program image](/Users/ari.biswas/Work-with-A16z/jolt/crates/jolt-program/src/execution/trace.rs:17)
and [execution inputs](/Users/ari.biswas/Work-with-A16z/jolt/crates/jolt-program/src/execution/trace.rs:129)
separately; Lean packages the bytecode with the resulting initial ISA state.
-/
structure JoltProgram where
  -- Rust: JoltProgram::expanded_bytecode.
  expandedBytecode : Array JoltProgramRow
  -- Rust: [create_emulator](/Users/ari.biswas/Work-with-A16z/jolt/tracer/src/lib.rs:366).
  initialState : SailJoltState

-- Rust: tracer/src/instruction/format/format_r.rs::{capture_pre_execution_state,
-- capture_post_execution_state}; Lean retains full ISA states, not just captured operands.
structure JoltTraceRow (program : JoltProgram) where
  rowIndex : Fin program.expandedBytecode.size
  preState : SailJoltState
  postState : SailJoltState
  -- ISA: JoltBytecode/JoltISA/Semantics.lean::execInstr; this certificate is Lean-only.
  executes : JoltISA.execInstr program.expandedBytecode[rowIndex].instruction preState =
    .ok (.Retire_Success ()) postState
  -- Rust: [trace_store](/Users/ari.biswas/Work-with-A16z/jolt/tracer/src/emulator/mmu.rs:609)
  -- reads the old word before every store. For RAM, this certifies that all eight
  -- bytes exist in preState.sail.mem; for device memory, it certifies a valid read
  -- from preState.io. Successful Sail writes alone do not establish this fact.
  storeMemoryPresent :
    match program.expandedBytecode[rowIndex].instruction with
    | .SD base _ imm =>
        (JoltISA.memoryWord? preState
          (Memory.effectiveAddr12 (JoltISA.sourceValue base preState) imm)).isSome = true
    | _ => True

/-- Successful ISA rows linked from the program's initial state.
Control-flow validity remains a separate obligation: Rust also selects the next
instruction and advances the PC in
[tick_operate](/Users/ari.biswas/Work-with-A16z/jolt/tracer/src/emulator/cpu.rs:654).
-/
structure JoltTrace (program : JoltProgram) where
  -- Actual execution steps in order, including repeated instructions from loops.
  -- Witness padding is added separately; rows.size need not be a power of two.
  rows : Array (JoltTraceRow program)
  -- If a first row exists, its pre-state is the program's initial state.
  startsAtInitial : ∀ h : 0 < rows.size, (getElem rows 0 h).preState = program.initialState
  -- For consecutive rows, the state after the first equals the state before the second.
  linked : ∀ (i : Nat) (currentExists : i < rows.size) (nextExists : i + 1 < rows.size),
    (getElem rows i currentExists).postState = (getElem rows (i + 1) nextExists).preState
