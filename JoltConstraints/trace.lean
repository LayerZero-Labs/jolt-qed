/-
Trace data, without assumptions about execution, initialization or row linkage.
The corresponding honesty certificates live in `honest_trace.lean`.

At public pin 8bbb2357, Rust uses `jolt_riscv::JoltTraceRow` for execution and
proof rows. This is a state-based abstraction of completed modeled cycles, not a
translation of its packed storage or every row accepted by its checked constructor.
Rust stores optional captures separately from encoded operands; missing captures
have zero values. Lean derives observations from pre/post states. Constructor
checks are producer checks, not additional verifier constraints or theorem premises.
-/
import JoltConstraints.program

open LeanRV64D

set_option autoImplicit false

-- In the bytecode, a VirtualAdvice instruction's value is a placeholder. The tracer
-- supplies the real value when it runs the instruction, and the trace row records it.
-- Jolt tracer: [runtime advice patching](https://github.com/a16z/jolt/blob/5def437f21a0006e13c063a03f0b5a7c9b93cd6f/tracer/src/instruction/mod.rs#L215-L241).
-- The unified Rust row retains the result through its captured destination value.
def JoltISA.Instr.RuntimeAdvice : JoltISA.Instr → Type
  | .VirtualAdvice .. => BitVec 64
  | _ => Unit

-- The instruction with the recorded value in place of the bytecode's placeholder.
-- Only VirtualAdvice changes.
def JoltISA.Instr.withRuntimeAdvice (instruction : JoltISA.Instr)
    (advice : instruction.RuntimeAdvice) : JoltISA.Instr :=
  match instruction with
  | .VirtualAdvice dst _ imm => .VirtualAdvice dst advice imm
  | instruction => instruction

-- One step of a trace: the bytecode row it runs, the advice value it recorded, and
-- the states before and after. The trace comes from some tracer, honest or not; all
-- we know is that it type-checks. `ValidRun` and `HonestTrace` say what an honest
-- tracer records.
structure TraceRow (bytecode : Array JoltInstructionRow) where
  rowIndex : Fin bytecode.size
  runtimeAdvice : bytecode[rowIndex].instruction.RuntimeAdvice
  preState : SailJoltState
  postState : SailJoltState

/-- The recorded byte address of a memory row, as a natural number.
LD/SD record `ea = base + imm` wrapping at 64 bits; floor rows subtract
`ea &&& mask`, with B/H/W masks 7/6/4, and other rows return `none`.
For example, a word floor row at `ea = 12` records `some 8`.
Jolt's tracer: `tracer/src/instruction/floor_access.rs` (`addresses`) and
`crates/jolt-riscv/src/trace_row.rs` (`ram_address`);
Jolt's prover: `crates/jolt-program/src/execution/trace.rs`
(`ExecutionDimensions::from_rows`) at `c6703570`. -/
def TraceRow.ram_address {bytecode : Array JoltInstructionRow}
    (row : TraceRow bytecode) : Option Nat :=
  match bytecode[row.rowIndex].instruction with
  | .LD _ _ base imm | .SD base _ imm =>
      some (JoltISA.sourceValue base row.preState + imm).toNat
  | .VirtualLoadB _ _ base imm _ | .VirtualStoreB base _ imm _ =>
      let ea := JoltISA.sourceValue base row.preState + imm
      some (ea - (ea &&& 7)).toNat
  | .VirtualLoadH _ _ base imm _ | .VirtualStoreH base _ imm _ =>
      let ea := JoltISA.sourceValue base row.preState + imm
      some (ea - (ea &&& 6)).toNat
  | .VirtualLoadW _ _ base imm _ | .VirtualStoreW base _ imm _ =>
      let ea := JoltISA.sourceValue base row.preState + imm
      some (ea - (ea &&& 4)).toNat
  | _ => none

-- A candidate execution: its bytecode, recorded transitions and initial state.
-- Rows represent actual modeled cycles. Canonical trailing padding is implicit,
-- matching Rust TraceData::proof_rows(); witness helpers supply default padding.
-- This does not represent arbitrary interior or noncanonical Rust NoOp rows.
structure Trace where
  bytecode : Array JoltInstructionRow
  rows : Array (TraceRow bytecode)
  initialState : SailJoltState
