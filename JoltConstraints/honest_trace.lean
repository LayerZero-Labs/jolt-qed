/-
An honest trace is the general data from `trace.lean` with certificates for
instruction execution, initialization, row linkage and termination. The program
and input assumptions below are the existing conditions on Rust-accepted runs.
-/
import JoltConstraints.trace
import JoltBytecode.InstructionEquivalence.Instructions.ALUAdviceFamily.Divw_math
import JoltBytecode.InstructionEquivalence.Instructions.ALUAdviceFamily.Divuw_math

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

-- A run of the instance's program on these private inputs: it starts at the entry
-- from the initial state, every row runs a row of the expanded bytecode, and each
-- row follows the previous one as in Rust's tracer. It says nothing about when the
-- run stops or which runtime advice it uses; `HonestTrace` adds both.
structure ValidRun (joltInstance : JoltInstance SourceInstruction)
    (privateInputs : JoltPrivateInputs) extends Trace where
  expands : expand_program joltInstance.program = some bytecode
  -- Every row retires.
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

-- No run of the program changes its own code: whenever an instruction starts, the
-- bytes at its address are the ones the program was loaded with. Rust's tracer reads
-- and decodes each instruction from memory as it starts (cpu.rs:631-637, 695-717;
-- stores clear its decode cache, mmu.rs:646, 689, 710, 731), while the proof checks
-- the bytecode, so the two run the same instructions exactly when this holds.
-- Assumed: a16z told us on 2026-10-07 that Jolt can assume a program does not change
-- its own code (a16z/jolt#1952; model_review.md, Assumptions).
def JoltInstance.CodeUnchanged (joltInstance : JoltInstance SourceInstruction) : Prop :=
  ∀ (privateInputs : JoltPrivateInputs) (run : ValidRun joltInstance privateInputs),
    ∀ row ∈ run.rows, run.bytecode[row.rowIndex].starts_source →
      ∀ offset < (if source_is_compressed run.bytecode row.rowIndex then 2 else 4),
        row.preState.sail.mem.get? (run.bytecode[row.rowIndex].address.toNat + offset) =
          run.initialState.sail.mem.get? (run.bytecode[row.rowIndex].address.toNat + offset)

-- The value written by a VirtualAdvice instruction; none for any other instruction.
def JoltISA.Instr.adviceValue? : JoltISA.Instr → Option (BitVec 64)
  | .VirtualAdvice _ value _ => some value
  | _ => none

-- The value a trace row's VirtualAdvice instruction writes: the one recorded in the
-- row (`runtimeAdvice`). None if the row runs any other instruction. The row comes
-- from some tracer, honest or not, so the value may be wrong.
def TraceRow.someTracerAdvice? {bytecode : Array JoltInstructionRow} (row : TraceRow bytecode) :
    Option (BitVec 64) :=
  (bytecode[row.rowIndex].instruction.withRuntimeAdvice row.runtimeAdvice).adviceValue?

section
variable {bytecode : Array JoltInstructionRow}

-- Whether step `n` of the trace runs the first row of an expandable instruction's
-- expansion. Step `n` is `rows[n]`; false if the trace has no step `n`.
def stepNOfTraceIsStartOfNewExpansion (rows : Array (TraceRow bytecode)) (n : Nat) : Bool :=
  (rows[n]?.map fun row => bytecode[row.rowIndex].starts_source).getD false

-- `n` counts steps of the whole trace: step `n` is `rows[n]`. The trace runs one
-- expansion after another, so step `n` falls inside one of them. This returns the
-- step where that expansion began. For example, if steps 10 to 19 of the trace run a
-- DIV's expansion, this is 10 for every n from 10 to 19.
def startOfExpansionContainingStepN (rows : Array (TraceRow bytecode)) : Nat → Nat
  | 0 => 0
  | n + 1 =>
    if stepNOfTraceIsStartOfNewExpansion rows (n + 1) then n + 1
    else startOfExpansionContainingStepN rows n

-- Whether step `n` of the trace runs a VirtualAdvice instruction. Step `n` is
-- `rows[n]`; false if the trace has no step `n`.
def stepNOfTraceIsAdvice (rows : Array (TraceRow bytecode)) (n : Nat) : Bool :=
  (rows[n]?.bind fun row => bytecode[row.rowIndex].instruction.adviceValue?).isSome

-- Step `n` is `rows[n]`. This counts the VirtualAdvice steps of step `n`'s expansion
-- that come before step `n`. For example, say an expansion takes steps 10 to 19 of the
-- trace, and steps 12 and 15 run VirtualAdvice. For n = 15: the expansion began at
-- step 10, the steps before 15 are 10 to 14, and of those only 12 runs VirtualAdvice,
-- so this is 1. For n = 10, there are no earlier steps, so this is 0.
def adviceStepsBeforeStepN (rows : Array (TraceRow bytecode)) (n : Nat) : Nat :=
  let start := startOfExpansionContainingStepN rows n
  ((List.range' start (n - start)).filter (stepNOfTraceIsAdvice rows)).length

end

-- Given the guest program and an address `addr`, this returns the instruction in the
-- guest program that has address `addr`. If no instruction in the guest program has
-- address `addr`, it returns none. The type allows two instructions with the same
-- address (a real ELF never has them); then this returns the first. Jolt's
-- preprocessing rejects such a program (`pc_map_ok`).
def Rv64ProgramImage.instructionAt (program : Rv64ProgramImage SourceInstruction)
    (addr : BitVec 64) : Option SourceInstruction :=
  (program.instructions.find? (·.address == addr)).map (·.instruction)

-- The advice values the honest tracer (Jolt's tracer) patches into the VirtualAdvice
-- rows of one expandable instruction, in order. It computes them from the state just
-- before the instruction's rows run. The division values are the ones the bytecode
-- project's equivalence proofs use for that expansion; they agree with the honest
-- tracer's formulas, including division by zero and the signed overflow cases. Other
-- instructions are not patched.
-- See : jolt/tracer/src/instruction/div.rs, divu.rs, rem.rs, remu.rs, divw.rs,
--       divuw.rs, remw.rs, remuw.rs (trace)
-- SC.W and SC.D have no runtime advice after PR #2039 (2a924239).
def SourceInstruction.honestTracerAdvice (source : SourceInstruction) (state : SailJoltState) :
    List (BitVec 64) :=
  let value (register : regidx) := JoltISA.sourceValue (.xreg register) state
  match source with
  | .riscv (.DIV _ rs1 rs2 _) => [sail_div_value (value rs1) (value rs2) false]
  | .riscv (.DIVU _ rs1 rs2 _) => [sail_div_value (value rs1) (value rs2) true]
  | .riscv (.REM _ rs1 rs2 _) => [rem_advice_value (value rs1) (value rs2)]
  | .riscv (.REMU _ rs1 rs2 _) => [sail_div_value (value rs1) (value rs2) true]
  | .riscv (.DIVW _ rs1 rs2 _) => [divw_advice_value (value rs1) (value rs2)]
  | .riscv (.DIVUW _ rs1 rs2 _) => [sail_divuw_advice (value rs1) (value rs2)]
  | .riscv (.REMW _ rs1 rs2 _) => [remw_advice_value (value rs1) (value rs2)]
  | .riscv (.REMUW _ rs1 rs2 _) => [sail_divuw_advice (value rs1) (value rs2)]
  | _ => []

-- The value the honest tracer gives the VirtualAdvice at step `n`, where step `n` is
-- `rows[n]`; none if step `n` does not run a VirtualAdvice.
-- When the honest tracer starts an expansion, it computes the list of all advice
-- values the expansion needs (`honestTracerAdvice`), from the state at that moment.
-- Each VirtualAdvice of the expansion then takes the next value from the list: the
-- first VirtualAdvice takes the first value, the second takes the second, and so on.
-- For example, a DIV's expansion has one VirtualAdvice, and the list holds one value:
-- the quotient of the DIV's two source registers, as they were just before the
-- expansion began.
-- See : jolt/tracer/src/instruction/mod.rs:207-233 (trace_inline_sequence_with_advice)
def honestTracerAdviceAtStepN (program : Rv64ProgramImage SourceInstruction)
    {bytecode : Array JoltInstructionRow} (rows : Array (TraceRow bytecode)) (n : Nat) :
    Option (BitVec 64) := do
  let row ← rows[n]?
  -- none unless step `n` runs a VirtualAdvice
  let bytecodeValue ← bytecode[row.rowIndex].instruction.adviceValue?
  -- the first step of step `n`'s expansion
  let first ← rows[startOfExpansionContainingStepN rows n]?
  -- the instruction step `n`'s expansion came from
  let instruction ← program.instructionAt bytecode[first.rowIndex].address
  -- the honest tracer's advice values for it, from the state before its expansion began
  let values := instruction.honestTracerAdvice first.preState
  pure (values[adviceStepsBeforeStepN rows n]?.getD bytecodeValue)

-- The rows Rust's tracer records when it runs the instance's program on these
-- private inputs: a valid run that uses Rust's runtime advice and stops where
-- Rust's tracer stops. Whether the code in memory stays the bytecode is not a
-- field; it follows from the instance assumption `CodeUnchanged`
-- (`HonestTrace.code_unchanged`).
-- See : jolt/tracer/src/lib.rs:74-131 (trace)
structure HonestTrace (joltInstance : JoltInstance SourceInstruction)
    (privateInputs : JoltPrivateInputs) extends ValidRun joltInstance privateInputs where
  -- Rust only proves programs it accepts: the PC map checks and the entry check
  -- pass during preprocessing, before any tracing.
  -- See : jolt/crates/jolt-prover/src/preprocessing.rs:43-50
  accepted : joltInstance.bytecode.isSome
  -- Rust's verifier rejects an instance whose inputs or layout fail its checks.
  -- See : jolt/crates/jolt-verifier/src/verifier.rs:356-383
  valid_inputs : joltInstance.validate_inputs = true
  -- At every step of the trace, the advice value recorded (`someTracerAdvice?`) is
  -- the value the honest tracer gives it (`honestTracerAdviceAtStepN`).
  advice_from_honest_tracer : ∀ n : Fin rows.size,
    rows[n].someTracerAdvice? = honestTracerAdviceAtStepN joltInstance.program rows n
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
    CoeOut (HonestTrace joltInstance privateInputs) Trace :=
  ⟨fun trace => trace.toValidRun.toTrace⟩

-- An honest trace never runs changed code, given the instance assumption.
theorem HonestTrace.code_unchanged {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (codeUnchanged : joltInstance.CodeUnchanged) :
    ∀ row ∈ trace.rows, trace.bytecode[row.rowIndex].starts_source →
      ∀ offset < (if source_is_compressed trace.bytecode row.rowIndex then 2 else 4),
        row.preState.sail.mem.get? (trace.bytecode[row.rowIndex].address.toNat + offset) =
          trace.initialState.sail.mem.get? (trace.bytecode[row.rowIndex].address.toNat + offset) :=
  codeUnchanged privateInputs trace.toValidRun

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

-- The instance claims an output, `joltInstance.outputs` (a list of bytes), and a panic
-- flag, `joltInstance.panic`. The honest tracer's run writes its output and panic flag
-- into the device in its state. This says the two agree: the bytes in the device after
-- the last step equal the claimed bytes once trailing zero bytes are dropped from
-- both, and the device's panic flag equals the claimed one. The termination word is
-- not compared yet (model_review.md).
-- See : jolt/crates/jolt-program/src/preprocess/public_io.rs:21-61
--       jolt/crates/jolt-verifier/src/verifier.rs:436-443
def HonestTrace.matches_outputs {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs) : Prop :=
  let finalState := (trace.rows.back?.map (·.postState)).getD trace.initialState
  trimTrailingZeros finalState.jolt_device.outputs = trimTrailingZeros joltInstance.outputs ∧
    finalState.jolt_device.panic = joltInstance.panic
