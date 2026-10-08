/-
Trace data, without assumptions about execution, initialization or row linkage.
The corresponding honesty certificates live in `honest_trace.lean`.
-/
import JoltConstraints.program

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

-- A recorded transition. These data do not assert that the instruction executed.
structure TraceRow (bytecode : Array JoltInstructionRow) where
  rowIndex : Fin bytecode.size
  runtimeAdvice : bytecode[rowIndex].instruction.RuntimeAdvice
  preState : SailJoltState
  postState : SailJoltState

-- The memory address one Jolt row reads or writes. For an LD or SD row it is the
-- value in the base register before the row runs, plus the immediate (wrapping at
-- 64 bits). Any other row does not read or write memory: none. After expansion,
-- LD and SD are the only rows that touch memory (LB, SB, ... become sequences
-- around them).
-- See : jolt/crates/jolt-prover/src/config.rs:91-98 (derive_compact)
--       jolt/tracer/src/instruction/ld.rs:16-30 (wrapping_add)
--       jolt/crates/jolt-program/src/expand/memory/shared.rs:36-58, 481-518
def TraceRow.ram_address {bytecode : Array JoltInstructionRow}
    (row : TraceRow bytecode) : Option Nat :=
  match bytecode[row.rowIndex].instruction with
  | .LD _ _ base imm | .SD base _ imm =>
      some (JoltISA.sourceValue base row.preState + imm).toNat
  | _ => none

-- A candidate execution: its bytecode, recorded transitions and initial state.
structure Trace where
  bytecode : Array JoltInstructionRow
  rows : Array (TraceRow bytecode)
  initialState : SailJoltState
