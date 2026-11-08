/-
Step f: the objects of the whole-run theorem.

An honest Jolt trace runs one source instruction after another. Sail's emulator
loop runs `try_step` once per instruction. This file fixes how the two are
compared: the Sail loop (`sailRun`) and the decomposition of a trace into one
block per source instruction (`Block`, `Block.Runs`). The relation between a
Jolt state and a Sail state is in `Relation.lean`; `Run.lean` chains blocks into
a run; `docs/riscv-alignment.md` section 9 says which assumptions remain.
-/
import JoltConstraints.honest_trace
import JoltBytecode.Step.Instructions

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail LeanRV64D LeanRV64D.Functions

set_option autoImplicit false

noncomputable section

namespace WholeRun

/-- `k` iterations of the body of Sail's emulator loop (`loop` in
`LeanRV64D/Step.lean`) on an active hart: `try_step`, stopping at the first
error. The step number only selects log output, which is off. -/
def sailRun : Nat → SailState → EStateM.Result (Error exception) SailState Unit
  | 0, s => .ok () s
  | k + 1, s =>
    match try_step 0 false s with
    | .ok _ s' => sailRun k s'
    | .error e s' => .error e s'

/-- The registers that no Jolt row reads or writes: the CSRs and reservation
registers that Jolt keeps in virtual registers (`System.systemProject` reads
them from there), and Sail's instruction-retirement bookkeeping. -/
def Untouched : Register → Prop
  | .mtvec | .mscratch | .mepc | .mcause | .mtval | .mstatus
  | .reservation_valid | .reservation_addr | .reservation_width
  | .minstret | .minstret_increment | .pma_regions => True
  | _ => False

/-- The final state of a result, mapped. -/
def mapState {ε σ τ α : Type} (f : σ → τ) : EStateM.Result ε σ α → EStateM.Result ε τ α
  | .ok a s => .ok a (f s)
  | .error e s => .error e (f s)

/-- A Jolt state with one embedded Sail register replaced. -/
def withReg (js : SailJoltState) (r : Register) (v : RegisterType r) : SailJoltState :=
  { js with sail := Step.setReg js.sail r v }

/-- Patch advice values into the VirtualAdvice instructions of a list, in
order; a VirtualAdvice with no value left keeps its placeholder. This is what
Jolt's tracer does with the values of `SourceInstruction.honestTracerAdvice`
(`honestTracerAdviceAtStepN`). -/
def patchAdvice : List (BitVec 64) → List JoltISA.Instr → List JoltISA.Instr
  | _, [] => []
  | values, .VirtualAdvice dst placeholder imm :: rest =>
      .VirtualAdvice dst (values.headD placeholder) imm :: patchAdvice values.tail rest
  | values, instruction :: rest => instruction :: patchAdvice values rest

/-- The source row of the image at an address: the first one, as
`Rv64ProgramImage.instructionAt`. -/
def rowAt (program : Rv64ProgramImage SourceInstruction) (address : BitVec 64) :
    Option (SourceInstructionRow SourceInstruction) :=
  program.instructions.find? (·.address == address)

/-- The rows Jolt runs for a source row, with the honest advice for the state
`js` they start from; none where the expansion fails. -/
def blockInstrs (row : SourceInstructionRow SourceInstruction) (js : SailJoltState) :
    Option (List JoltISA.Instr) :=
  (expand_instruction row).map fun rows =>
    patchAdvice (row.instruction.honestTracerAdvice js) (rows.map (·.instruction))

/-- One source instruction's part of a trace: the state `pre` the previous
instruction left (`nextPC` at this instruction), the source row it runs, and
the state `post` its last row leaves. -/
structure Block where
  row : SourceInstructionRow SourceInstruction
  pre : SailJoltState
  post : SailJoltState

/-- The state a block's rows start from: Rust has moved the PC to the
instruction and `nextPC` past it (`advance_pc`). -/
def Block.start (b : Block) : SailJoltState :=
  advance_pc b.row.address b.row.is_compressed b.pre

/-- What every block of an honest trace satisfies: the row is the image's row
at the address `pre` continues at, and its rows, run in order with the honest
advice, retire and leave `post`. -/
structure Block.Runs (program : Rv64ProgramImage SourceInstruction) (b : Block) : Prop where
  at_row : rowAt program b.row.address = some b.row
  continues : b.pre.sail.regs.get? Register.nextPC = some b.row.address
  executes : ∃ instrs, blockInstrs b.row b.start = some instrs ∧
    JoltISA.execProgram (JoltISA.Program.seq instrs) b.start = .ok RETIRE_SUCCESS b.post

end WholeRun
