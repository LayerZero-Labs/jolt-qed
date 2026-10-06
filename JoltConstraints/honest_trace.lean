/-
The honest trace: the rows Rust's tracer records for a program and its inputs,
over the bytecode built in `program_fresh.lean`. Definitions are added one at a
time, each checked against the Rust source.
-/
import JoltConstraints.program_fresh

set_option autoImplicit false

-- Rust patches each executed VirtualAdvice row with this execution's advice value;
-- every other row runs exactly as it is in the bytecode. VirtualAdvice is the only
-- instruction Rust patches: the advice loads read the advice tape as they run.
-- See : jolt/tracer/src/instruction/mod.rs:210-234 (trace_inline_sequence_with_advice)
--       jolt/tracer/src/instruction/virtual_advice.rs:22
def JoltISA.Instr.RuntimeAdvice : JoltISA.Instr → Type
  | .VirtualAdvice .. => BitVec 64
  | _ => Unit

def JoltISA.Instr.withRuntimeAdvice (instruction : JoltISA.Instr)
    (advice : instruction.RuntimeAdvice) : JoltISA.Instr :=
  match instruction with
  | .VirtualAdvice dst _ imm => .VirtualAdvice dst advice imm
  | instruction => instruction

-- One executed row of an honest run: it really executes and retires. Rust records
-- the row and the operand values before and after; Lean keeps the whole state.
-- See : jolt/tracer/src/instruction/mod.rs:480-492 (RISCVTrace::trace)
structure HonestTraceRow (bytecode : Array JoltInstructionRow) where
  rowIndex : Fin bytecode.size
  runtimeAdvice : bytecode[rowIndex].instruction.RuntimeAdvice
  preState : SailJoltState
  postState : SailJoltState
  executes : JoltISA.execInstr (bytecode[rowIndex].instruction.withRuntimeAdvice runtimeAdvice)
    preState = .ok (.Retire_Success ()) postState

-- The memory address one Jolt row reads or writes. For an LD or SD row it is the
-- value in the base register before the row runs, plus the immediate (wrapping at
-- 64 bits). Any other row does not read or write memory: none. After expansion,
-- LD and SD are the only rows that touch memory (LB, SB, ... become sequences
-- around them).
-- See : jolt/crates/jolt-prover/src/config.rs:91-98 (derive_compact)
--       jolt/tracer/src/instruction/ld.rs:16-30 (wrapping_add)
--       jolt/crates/jolt-program/src/expand/memory/shared.rs:36-58, 481-518
def HonestTraceRow.ram_address {bytecode : Array JoltInstructionRow}
    (row : HonestTraceRow bytecode) : Option Nat :=
  match bytecode[row.rowIndex].instruction with
  | .LD _ _ base imm | .SD base _ imm =>
      some (JoltISA.sourceValue base row.preState + imm).toNat
  | _ => none

-- Before a source instruction's rows run, Rust has already advanced the PC past it:
-- PC is the instruction's address, nextPC is 2 bytes on if compressed, else 4.
-- Sail PC stands for Rust's self.address and Sail nextPC for cpu.pc (Semantics.lean:77-82).
-- See : jolt/tracer/src/emulator/cpu.rs:628-632 (tick_operate)
def advance_pc (address : BitVec 64) (is_compressed : Bool)
    (state : SailJoltState) : SailJoltState :=
  let length : BitVec 64 := if is_compressed then 2 else 4
  let registers := (state.sail.regs.insert Register.PC address).insert Register.nextPC
    (address + length)
  { state with sail := { state.sail with regs := registers } }

-- Whether the source instruction whose rows start at `start` is compressed. Stamping
-- puts the source's flag on the last row of its block; a native row carries it itself.
-- See : jolt/crates/jolt-program/src/expand/metadata.rs:46-52 (stamp_sequence_metadata)
def source_is_compressed (bytecode : Array JoltInstructionRow)
    (start : Fin bytecode.size) : Bool :=
  let last := start.val + (bytecode[start].virtual_sequence_remaining.getD 0).toNat
  (bytecode[last]?.map (·.is_compressed)).getD false

-- The rows Rust's tracer records when it runs the instance's program on these
-- private inputs.
-- See : jolt/tracer/src/lib.rs:74-131 (trace)
structure HonestTrace (joltInstance : JoltInstance SourceInstruction)
    (privateInputs : JoltPrivateInputs) where
  bytecode : Array JoltInstructionRow
  expands : expand_program joltInstance.program = some bytecode
  -- Rust only proves programs it accepts: the PC map checks and the entry check
  -- pass during preprocessing, before any tracing.
  -- See : jolt/crates/jolt-prover/src/preprocessing.rs:43-50
  accepted : joltInstance.bytecode.isSome
  -- Rust's verifier rejects an instance whose inputs or layout fail its checks.
  -- See : jolt/crates/jolt-verifier/src/verifier.rs:356-383
  valid_inputs : joltInstance.validate_inputs = true
  rows : Array (HonestTraceRow bytecode)
  -- Rust starts from the emulator create_emulator builds.
  -- See : jolt/tracer/src/lib.rs:89-97, 364-408 (create_emulator)
  initialState : SailJoltState
  initialized : joltInstance.initial_state privateInputs = some initialState
  -- The trace begins where the program begins: Rust's first tick runs the
  -- instruction at the entry address, with the PC already advanced past it.
  -- See : jolt/tracer/src/lib.rs:327-337, jolt/tracer/src/emulator/cpu.rs:622-632
  starts : ∀ first ∈ rows[0]?,
    bytecode[first.rowIndex].address = joltInstance.program.entry_address ∧
    bytecode[first.rowIndex].starts_source ∧
    first.preState = advance_pc joltInstance.program.entry_address
      (source_is_compressed bytecode first.rowIndex) initialState
  -- How one row leads to the next. If the instruction still has rows left, the
  -- next row is its next row and starts from the state this row left. If this was
  -- its last row, the next row is the first row of the instruction at nextPC, and
  -- the PC is moved to that instruction before it starts.
  -- See : jolt/tracer/src/instruction/mod.rs:679-687 (rows of one instruction, in order)
  --       jolt/tracer/src/emulator/cpu.rs:622-632 (the next instruction is fetched at the PC)
  linked : ∀ (i : Nat) (current next : HonestTraceRow bytecode),
    rows[i]? = some current → rows[i + 1]? = some next →
    if bytecode[current.rowIndex].virtual_sequence_remaining.getD 0 ≠ 0 then
      next.rowIndex.val = current.rowIndex.val + 1 ∧
      next.preState = current.postState
    else
      ∃ address, current.postState.sail.regs.get? Register.nextPC = some address ∧
        bytecode[next.rowIndex].address = address ∧
        bytecode[next.rowIndex].starts_source ∧
        next.preState = advance_pc address (source_is_compressed bytecode next.rowIndex)
          current.postState
  -- The run ends on the last row of an instruction that left the PC pointing at
  -- itself. Rust's tracer stops there.
  -- See : jolt/tracer/src/lib.rs:113-120, 327-337 (trace, step_emulator)
  stops : ∀ last ∈ rows.back?,
    bytecode[last.rowIndex].virtual_sequence_remaining.getD 0 = 0 ∧
    last.postState.sail.regs.get? Register.nextPC = some bytecode[last.rowIndex].address
  -- The run does not end early: no earlier instruction left the PC pointing at itself.
  runs_until_stop : ∀ (i : Nat) (current next : HonestTraceRow bytecode),
    rows[i]? = some current → rows[i + 1]? = some next →
    bytecode[current.rowIndex].virtual_sequence_remaining.getD 0 = 0 →
    current.postState.sail.regs.get? Register.nextPC ≠ some bytecode[current.rowIndex].address
  -- The run is empty only when the entry address is 0: Rust compares the PC with a
  -- starting value of 0 and stops before running anything.
  nonempty : joltInstance.program.entry_address ≠ 0 → 0 < rows.size

-- The slot in Rust's RAM table that holds a memory address: the number of 64-bit
-- steps from the lowest address. Address 0 has no slot: it means the row does not
-- touch memory. Rust panics on an address below the lowest address; the prover
-- config checks for that before using this.
-- See : jolt/crates/jolt-prover/src/config.rs:183-195 (remap_address)
def remap_address (layout : MemoryLayout) (address : Nat) : Option Nat :=
  if address = 0 then none
  else some ((address - layout.get_lowest_address.toNat) / 8)

-- The witness length Rust's prover pads a run to: the smallest power of two that
-- is larger than the run, and at least 256.
-- See : jolt/crates/jolt-prover/src/config.rs:30, 113-118
def padded_trace_length (rows : Nat) : Nat :=
  if rows < 256 then 256 else 2 ^ Nat.clog 2 (rows + 1)

-- The two sizes Rust's prover picks from a run before it builds the witness.
-- See : jolt/crates/jolt-prover/src/config.rs:34-40 (ProverConfig)
structure ProverConfig where
  trace_length : Nat
  ram_K : Nat

-- How Rust's prover sizes the proof from a run; none where it refuses or panics.
-- It refuses a run whose padded length passes the instance's maximum, and panics
-- if a row touches an address below the lowest address. ram_K is the smallest
-- power of two at least every touched slot and the end of the program image.
-- WARNING: Rust's tracer lets a program read below the lowest address (allowed
-- since ZeroOS, #1229; mmu.rs:139, 154), but the prover panics on it
-- (config.rs:193). We follow the prover, so such runs have no config. Reported
-- upstream as a16z/jolt#1951 item 3 (model_review.md, Completeness conditions).
-- See : jolt/crates/jolt-prover/src/config.rs:103-152 (derive_from_rows)
--       jolt/crates/jolt-verifier/src/verifier.rs:378-383 (the length bound)
def HonestTrace.prover_config {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs) :
    Option ProverConfig := do
  let layout := trace.initialState.jolt_device.memory_layout
  let trace_length := padded_trace_length trace.rows.size
  guard (trace_length ≤ joltInstance.max_padded_trace_length)
  let addresses := trace.rows.toList.filterMap (·.ram_address)
  guard (addresses.all fun address => address == 0 || layout.get_lowest_address.toNat ≤ address)
  let touched := ((addresses.filterMap (remap_address layout)).max?).getD 0
  let image := joltInstance.program.memory_init
  let image_end := (remap_address layout (min_bytecode_address image)).getD 0 +
    program_image_len_words image + 1
  -- FIXME: this is what ram_K should be, not what Rust computes today. Rust rounds
  -- up `touched` instead of `touched + 1` (config.rs:143), so when the highest
  -- touched slot is a power of two its RAM table is one slot too small and its
  -- witness rejects the run. Reported as a16z/jolt#1951 item 4, with this fix;
  -- still present at 8e536f19 (bug-report/ram-k-off-by-one/run.sh). Recheck once
  -- Rust is fixed.
  pure { trace_length := trace_length, ram_K := 2 ^ Nat.clog 2 (max (touched + 1) image_end) }

-- Rust only proves a run in which every spoil assert that runs has equal sides. A
-- spoil assert is a VirtualAssertEQ with a nonzero immediate; when its sides differ,
-- Rust warns "proof will be unsatisfiable" and keeps going, so no proof exists.
-- In practice our understanding is: spoil asserts come only from a guest calling
-- jolt::spoil_proof() (directly or through unwrap_or_spoil_proof), which compares 0
-- with 1 and so always fails. Rust's expansions emit only asserts with immediate 0,
-- and those always pass (assert_eq_holds in execution_facts.lean). So this condition
-- says the guest never calls spoil_proof(); Rust means such runs to have no proof.
-- See : jolt/tracer/src/instruction/virtual_assert_eq.rs:18-32
--       jolt/jolt-platform/src/spoil.rs:1-20
--       jolt/crates/jolt-program/src/expand/memory/scw.rs:54-59 (and scd.rs: immediate 0)
def HonestTrace.SpoilAssertsPass {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs) : Prop :=
  ∀ row ∈ trace.rows, ∀ (lhs rhs : JoltISA.Src) (imm : BitVec 128),
    trace.bytecode[row.rowIndex].instruction = .VirtualAssertEQ lhs rhs imm → imm ≠ 0 →
    JoltISA.sourceValue lhs row.preState = JoltISA.sourceValue rhs row.preState

-- The run's outputs are the ones the instance claims: the same bytes once trailing
-- zero bytes are dropped, and the same panic flag. The termination word is left out
-- for now (model_review.md).
-- See : jolt/crates/jolt-program/src/preprocess/public_io.rs:21-61
--       jolt/crates/jolt-verifier/src/verifier.rs:436-443
def HonestTrace.matches_outputs {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs) : Prop :=
  let finalState := (trace.rows.back?.map (·.postState)).getD trace.initialState
  let trim (bytes : List (BitVec 8)) := (bytes.reverse.dropWhile (· == 0)).reverse
  trim finalState.jolt_device.outputs.toList = trim joltInstance.outputs.toList ∧
    finalState.jolt_device.panic = joltInstance.panic
