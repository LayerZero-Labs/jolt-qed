import JoltConstraints.trace
import JoltBytecode.JoltISA.HostIO

set_option autoImplicit false
set_option maxRecDepth 4096

namespace HostIOChecks

open Sail PreSail LeanRV64D.Functions JoltISA

def device : JoltDevice :=
  { memory_layout :=
      { program_size := 0
        max_trusted_advice_size := 0
        trusted_advice_start := 0x5000
        trusted_advice_end := 0x5000
        max_untrusted_advice_size := 0
        untrusted_advice_start := 0x5000
        untrusted_advice_end := 0x5000
        max_input_size := 8
        max_output_size := 8
        input_start := 0x4000
        input_end := 0x4008
        output_start := 0x6000
        output_end := 0x6008
        stack_size := 0
        stack_end := 0
        heap_size := 0
        heap_end := 0
        panic := 0x7000
        termination := 0x7008
        io_end := 0x7010 }
    inputs := #[0xde, 0xad, 0xbe, 0xef]
    trusted_advice := #[], untrusted_advice := #[], outputs := #[], panic := false }

def state (callId pointer count event : BitVec 64)
    (config : JoltHostIOConfig := {}) : SailJoltState :=
  { sail :=
      { regs := let regs : Std.ExtDHashMap Register RegisterType := {}
                (((regs.insert Register.x10 callId).insert Register.x11 pointer).insert
                  Register.x12 count).insert Register.x13 event
        mem := {}, choiceState := (), tags := (), cycleCount := 0, sailOutput := #[] }
    jolt_device := device
    adviceTape := { bytes := #[9, 8], readPosition := 1 }
    hostIO := config }

-- Encoded operands are intentionally unrelated to the architectural ABI.
def instruction : Instr := .VirtualHostIO (.vreg 40) (.vreg 41) 999

def tapeResult (result : EStateM.Result (Error exception) SailJoltState ExecutionResult) :
    Option (Array (BitVec 8) × Nat) :=
  match result with
  | .ok _ s => some (s.adviceTape.bytes, s.adviceTape.readPosition)
  | .error _ _ => none

-- Unfold execution in two stages so the extensional register map is read
-- using its proved lookup rules; the remaining closed computation uses decide.
set_option linter.unusedSimpArgs false
macro "host_io_check" : tactic => `(tactic| (
  dsimp only [instruction, execInstr, execHostIO, execHostIOWith]
  simp only [state, readSrc, rX_bits, rX, Sail.readReg, PreSail.readReg,
    Sail.BitVec.toNatInt, regval_from_reg, bind, pure, get, getThe,
    MonadStateOf.get, EStateM.bind, EStateM.get]
  simp [hostAdviceWriteCall, hostCycleTrackCall, hostPrintCall, liftSail,
    EStateM.bind, EStateM.pure, EStateM.get, Std.ExtDHashMap.get?_insert]
  all_goals decide))

-- Actual instruction/device path: append in order; preserve existing bytes/cursor.
theorem live_append :
    tapeResult (execInstr instruction (state 0xADBABE 0x4000 4 0)) =
      some (#[9, 8, 0xde, 0xad, 0xbe, 0xef], 1) := by host_io_check

theorem replay_unchanged :
    tapeResult (execInstr instruction
      (state 0xADBABE 0x1020 4 0 { mode := .replay })) = some (#[9, 8], 1) := by host_io_check

-- Only the call ID is truncated for advice writes. Zero length does not read.
example : tapeResult (execInstr instruction (state 0x100ADBABE 0x4000 4 0)) =
    some (#[9, 8, 0xde, 0xad, 0xbe, 0xef], 1) := by host_io_check

example : tapeResult (execInstr instruction (state 0xADBABE 0x1020 0 0)) =
    some (#[9, 8], 1) := by host_io_check

example : tapeResult (execInstr instruction (state 0x123456 0x1020 4 99)) =
    some (#[9, 8], 1) := by host_io_check

-- Fatal device failures must not be swallowed as returned translation traps.
example : tapeResult (execInstr instruction (state 0xADBABE 0x1020 1 0)) = none := by host_io_check

-- Print arguments are truncated to 32 bits, including length and event.
example : tapeResult (execInstr instruction
    (state 0x505249 0x100004000 0x100000004 0x100000001)) =
    some (#[9, 8], 1) := by host_io_check

example : tapeResult (execInstr instruction (state 0x505249 0x4000 4 3)) = none := by host_io_check

example : tapeResult (execInstr instruction
    (state 0x505249 0x1020 4 3 { mode := .replay })) = some (#[9, 8], 1) := by host_io_check

-- Cycle end does not read a label; cycle start does. Invalid events are fatal.
example : tapeResult (execInstr instruction (state 0xC7C1E 0x1020 4 2)) =
    some (#[9, 8], 1) := by host_io_check
example : tapeResult (execInstr instruction (state 0xC7C1E 0x1020 4 1)) = none := by host_io_check
example : tapeResult (execInstr instruction (state 0xC7C1E 0x4000 4 3)) = none := by host_io_check

-- Isolate handler error behavior from the memory implementation: the second
-- load returns a trap, after one byte was collected. Nothing is appended.
def trapAfterFirst (address : BitVec 64) : JoltMonad (Result (BitVec 8) ExecutionResult) :=
  if address = 0x4000 then pure (.Ok 42)
  else pure (.Err (.Memory_Exception (.Virtaddr address, .E_Load_Page_Fault ())))

theorem returned_trap_is_ignored_without_partial_append :
    tapeResult (execHostIOWith trapAfterFirst (state 0xADBABE 0x4000 4 0)) =
      some (#[9, 8], 1) := by host_io_check

-- Rust validates a print event only after successfully reading the string.
example : tapeResult (execHostIOWith trapAfterFirst (state 0x505249 0x4000 4 3)) =
    some (#[9, 8], 1) := by host_io_check

def lowByte (address : BitVec 64) : JoltMonad (Result (BitVec 8) ExecutionResult) :=
  pure (.Ok (address.setWidth 8))

-- Advice pointers retain all 64 bits, and release arithmetic wraps.
example : tapeResult (execHostIOWith lowByte (state 0xADBABE 0xffffffffffffffff 2 0)) =
    some (#[9, 8, 255, 0], 1) := by host_io_check

-- Checked profiles abort before appending on pointer overflow.
example : tapeResult (execHostIOWith lowByte
    (state 0xADBABE 0xffffffffffffffff 2 0 { overflowChecks := true })) = none := by host_io_check

-- Advice does not increment past its last byte; read_string does.
example : tapeResult (execHostIOWith lowByte
    (state 0xADBABE 0xffffffffffffffff 1 0 { overflowChecks := true })) =
    some (#[9, 8, 255], 1) := by host_io_check
example : tapeResult (execHostIOWith lowByte
    (state 0x505249 0xffffffff 1 1 { overflowChecks := true })) = none := by host_io_check

-- Observe the appended tape through both downstream advice instructions.
noncomputable def appendThenRead : JoltMonad ExecutionResult := do
  let _ ← execInstr instruction
  let _ ← execInstr (.VirtualAdviceLen (.vreg 40) (.vreg 41) 0)
  execInstr (.VirtualAdviceLoad (.vreg 41) 2)

def adviceResult (result : EStateM.Result (Error exception) SailJoltState ExecutionResult) :
    Option (BitVec 64 × BitVec 64 × Nat) :=
  match result with
  | .ok _ s => some (s.vregs 40, s.vregs 41, s.adviceTape.readPosition)
  | .error _ _ => none

example : adviceResult (appendThenRead (state 0xADBABE 0x4000 4 0)) =
    some (5, 0xde08, 3) := by
  unfold appendThenRead
  host_io_check

-- Initialization carries the selected host execution configuration.
example : (init_state 0x80000000 #[] device { bytes := #[], readPosition := 0 }
    { mode := .replay }).hostIO.mode = .replay := rfl

#print axioms live_append
#print axioms replay_unchanged
#print axioms returned_trap_is_ignored_without_partial_append

end HostIOChecks
