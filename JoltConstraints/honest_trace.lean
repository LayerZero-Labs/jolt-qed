/-
An honest trace is the general data from `trace.lean` with certificates for
instruction execution, initialization, row linkage and termination. The program
and input assumptions below are the existing conditions on Rust-accepted runs.
-/
import JoltConstraints.trace

set_option autoImplicit false

-- An individual transition with its execution certificate. Whole honest traces
-- store raw rows and certify each member; this view supports row-level proofs.
structure HonestTraceRow (bytecode : Array JoltInstructionRow) extends TraceRow bytecode where
  executes : JoltISA.execInstr (bytecode[rowIndex].instruction.withRuntimeAdvice runtimeAdvice)
    preState = .ok (.Retire_Success ()) postState

instance {bytecode : Array JoltInstructionRow} :
    CoeOut (HonestTraceRow bytecode) (TraceRow bytecode) := ⟨HonestTraceRow.toTraceRow⟩

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
-- private inputs. Every row runs a row of the decoded bytecode, as the proof does;
-- `code_unchanged` says the code in memory is still that bytecode when it runs.
-- See : jolt/tracer/src/lib.rs:74-131 (trace)
structure HonestTrace (joltInstance : JoltInstance SourceInstruction)
    (privateInputs : JoltPrivateInputs) extends Trace where
  expands : expand_program joltInstance.program = some bytecode
  -- Rust only proves programs it accepts: the PC map checks and the entry check
  -- pass during preprocessing, before any tracing.
  -- See : jolt/crates/jolt-prover/src/preprocessing.rs:43-50
  accepted : joltInstance.bytecode.isSome
  -- Rust's verifier rejects an instance whose inputs or layout fail its checks.
  -- See : jolt/crates/jolt-verifier/src/verifier.rs:356-383
  valid_inputs : joltInstance.validate_inputs = true
  -- The same successful-execution condition previously stored in every row.
  executes : ∀ row ∈ rows,
    JoltISA.execInstr (bytecode[row.rowIndex].instruction.withRuntimeAdvice row.runtimeAdvice)
      row.preState = .ok (.Retire_Success ()) row.postState
  -- Rust starts from the emulator create_emulator builds.
  -- See : jolt/tracer/src/lib.rs:89-97, 364-408 (create_emulator)
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
  linked : ∀ (i : Nat) (current next : TraceRow bytecode),
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
  -- When an instruction starts, the bytes at its address are the ones the program
  -- was loaded with. Rust's tracer reads and decodes the instruction from memory at
  -- that moment (cpu.rs:631-637, 695-717; stores clear its decode cache, mmu.rs:646,
  -- 689, 710, 731), so it then runs the same instruction as the bytecode.
  -- ASSUMPTION: a program does not change its own code. a16z confirmed on 2026-10-07
  -- that this is an assumption of Jolt: its tracer runs the code in memory, its proof
  -- checks the bytecode, and the two differ only when a program runs code it changed
  -- (a16z/jolt#1952; model_review.md, Upstream issues).
  code_unchanged : ∀ row ∈ rows, bytecode[row.rowIndex].starts_source →
    ∀ offset < (if source_is_compressed bytecode row.rowIndex then 2 else 4),
      row.preState.sail.mem.get? (bytecode[row.rowIndex].address.toNat + offset) =
        initialState.sail.mem.get? (bytecode[row.rowIndex].address.toNat + offset)
  -- The run ends on the last row of an instruction that left the PC pointing at
  -- itself. Rust's tracer stops there.
  -- See : jolt/tracer/src/lib.rs:113-120, 327-337 (trace, step_emulator)
  stops : ∀ last ∈ rows.back?,
    bytecode[last.rowIndex].virtual_sequence_remaining.getD 0 = 0 ∧
    last.postState.sail.regs.get? Register.nextPC = some bytecode[last.rowIndex].address
  -- The run does not end early: no earlier instruction left the PC pointing at itself.
  runs_until_stop : ∀ (i : Nat) (current next : TraceRow bytecode),
    rows[i]? = some current → rows[i + 1]? = some next →
    bytecode[current.rowIndex].virtual_sequence_remaining.getD 0 = 0 →
    current.postState.sail.regs.get? Register.nextPC ≠ some bytecode[current.rowIndex].address
  -- The run is empty only when the entry address is 0: Rust compares the PC with a
  -- starting value of 0 and stops before running anything.
  nonempty : joltInstance.program.entry_address ≠ 0 → 0 < rows.size

instance {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs} :
    CoeOut (HonestTrace joltInstance privateInputs) Trace := ⟨HonestTrace.toTrace⟩

-- Recover the certified view of a recorded row for execution proofs.
abbrev HonestTrace.row {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (i : Nat) (inBounds : i < trace.rows.size) : HonestTraceRow trace.bytecode :=
  { toTraceRow := trace.rows[i]
    executes := trace.executes _ (Array.getElem_mem inBounds) }

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

-- The rows that carry Rust's Jump circuit flag: JAL and JALR.
-- See : jolt/crates/jolt-riscv/src/instructions/i/jal.rs:6, jalr.rs:6
def JoltISA.Instr.is_jump : JoltISA.Instr → Bool
  | .JAL .. | .JALR .. => true
  | _ => false

-- The two sizes Rust's prover picks from a run before it builds the witness.
-- See : jolt/crates/jolt-prover/src/config.rs:34-40 (ProverConfig)
structure ProverConfig where
  trace_length : Nat
  ram_K : Nat

-- How Rust's prover sizes the proof from a run; none where it refuses or panics.
-- It refuses a run whose last row is not a jump (an empty run passes), and a run
-- whose padded length passes the instance's maximum; it panics if a row touches an
-- address below the lowest address. ram_K is the smallest power of two at least
-- every touched slot and the end of the program image.
-- The jump check came with a16z/jolt#1968 (merged 2026-10-06, upstream 00508a09),
-- which fixed #1916: a trace ending on a taken self-branch cannot be proved.
-- WARNING: Rust's tracer lets a program read below the lowest address (allowed
-- since ZeroOS, #1229; mmu.rs:139, 154), but the prover panics on it
-- (config.rs:193). We follow the prover, so such runs have no config. Reported
-- upstream as a16z/jolt#1951 item 3 (model_review.md, Upstream issues).
-- See : jolt/crates/jolt-prover/src/config.rs:103-152 (derive_from_rows)
--       jolt/crates/jolt-prover/src/config.rs:122-126 at upstream 629ed77b (the jump check)
--       jolt/crates/jolt-verifier/src/verifier.rs:378-383 (the length bound)
def HonestTrace.prover_config {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs) :
    Option ProverConfig := do
  guard (trace.rows.back?.all fun last => trace.bytecode[last.rowIndex].instruction.is_jump)
  let layout := trace.initialState.jolt_device.memory_layout
  let trace_length := padded_trace_length trace.rows.size
  guard (trace_length ≤ joltInstance.max_padded_trace_length.toNat)
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
  -- reproduced at 8e536f19 (bug-report/ram-k-off-by-one/run.sh), and the formula is
  -- unchanged at upstream 629ed77b (config.rs:159). Recheck once Rust is fixed.
  pure { trace_length := trace_length, ram_K := 2 ^ Nat.clog 2 (max (touched + 1) image_end) }

-- Rust only proves a run in which every spoil assert that runs has equal sides. A
-- spoil assert is a VirtualAssertEQ with a nonzero immediate; when its sides differ,
-- Rust warns "proof will be unsatisfiable" and keeps going, so no proof exists.
-- In practice our understanding is: spoil asserts come only from a guest calling
-- jolt::spoil_proof() (directly or through unwrap_or_spoil_proof), which compares 0
-- with 1 and so always fails. Rust's expansions emit only asserts with immediate 0,
-- and those always pass (assert_eq_holds in execution_facts.lean). A guest reaches
-- spoil_proof() only when values the prover supplied fail its checks, e.g. the
-- curve points in Jolt's P-256 ECDSA check: a cheating prover then gets no proof
-- at all. An honest prover never reaches it, so this condition is very mild.
-- See : jolt/tracer/src/instruction/virtual_assert_eq.rs:18-32
--       jolt/jolt-platform/src/spoil.rs:1-26
--       jolt/crates/jolt-program/src/expand/memory/scw.rs:54-59 (and scd.rs: immediate 0)
--       jolt/jolt-inlines/p256/src/sdk.rs:768-787, 853-858 (ECDSA advice checks)
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
  trimTrailingZeros finalState.jolt_device.outputs = trimTrailingZeros joltInstance.outputs ∧
    finalState.jolt_device.panic = joltInstance.panic
