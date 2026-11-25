import JoltBytecode.JoltISA.RegisterAccess
import JoltBytecode.JoltISA.DeviceMemory

/-!
# Total host calls at Jolt `ff6fc6568`

Jolt's tracer logs and ignores rejected host calls.
Only advice writes change guest-visible state: they append a complete readable
range to the advice tape, including during replay, without moving its cursor.
Print and cycle-marker handlers skip replay and reject unknown events before
reading memory.
Their stdout, lossy UTF-8 conversion, marker bookkeeping and logs are outside
Sail state, as are the tracer's memory-access bookkeeping and host I/O failures.
We model host allocation (`try_reserve`, including string/marker allocation) as
succeeding; allocation depends on the host machine rather than the guest.

Readability means that the model's guest byte load succeeds at every address of
the requested range.
The pure load query checks the entire range before collecting any bytes.
For example, a two-byte advice write whose second address is unreadable appends
no bytes, and a zero-length write at `u64::MAX` succeeds without loading.

Sources at `ff6fc6568`: `tracer/src/instruction/virtual_host_io.rs`
(`VirtualHostIO::exec`, lines 19–38), `tracer/src/emulator/host_io.rs`
(`read_host_bytes`, lines 51–87; `print_terminator`),
`tracer/src/emulator/cpu.rs` (`handle_jolt_cycle_marker`, `handle_jolt_print`,
`handle_advice_write`, `read_host_string`, `read_host_message`, lines 1116–1230),
and `tracer/src/emulator/mmu.rs` (`HostMemory for Mmu`, lines 1076–1096).
-/

open LeanRV64D

set_option autoImplicit false

namespace JoltISA

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail LeanRV64D LeanRV64D.Functions

/-- Advice-write call ID, truncated from x10 to 32 bits; for example,
`0xADBABE` selects `Cpu::handle_advice_write` in `VirtualHostIO::exec`.
See `jolt-platform/src/advice.rs` at `ff6fc6568`. -/
def hostAdviceWriteCall : BitVec 32 := 0xADBABE
/-- Cycle-marker call ID; for example, event 1 starts a named marker.
See `jolt-platform/src/cycle_tracking.rs` at `ff6fc6568`. -/
def hostCycleTrackCall : BitVec 32 := 0xC7C1E
/-- Print call ID; for example, event 2 prints a message followed by a newline.
See `jolt-platform/src/print.rs` at `ff6fc6568`. -/
def hostPrintCall : BitVec 32 := 0x505249

/-- Read `[pointer, pointer + count)` using the pure guest-load query `loadByte`
and append it to `bytes`, or return `none` without an appended prefix.
The exclusive end must fit in a u64 and be at most `addressLimit`, even when
`count = 0`; for example, an end of `2^32` is allowed for a print message.
For a nonempty range, check every address before collecting any byte.
Allocation is assumed to succeed.
See `tracer/src/emulator/host_io.rs` (`read_host_bytes`) at `ff6fc6568`. -/
def readHostBytes (loadByte : Nat → Option (BitVec 8))
    (pointer count addressLimit : Nat) (bytes : Array (BitVec 8)) :
    Option (Array (BitVec 8)) :=
  if pointer + count ≤ 2 ^ 64 - 1 ∧ pointer + count ≤ addressLimit then
    if count = 0 then some bytes
    else if (List.range count).all (fun offset => (loadByte (pointer + offset)).isSome) then do
      let loaded ← (List.range count).mapM (fun offset => loadByte (pointer + offset))
      pure (bytes ++ loaded.toArray)
    else none
  else none

/-- Run the host-call ABI with a pure byte-load query on the initial state.
`loadByte` supplies both the whole-range readability check and the loaded bytes.
Only advice writes append to the tape; for example, replay still appends an
accepted advice range but suppresses print and marker reads.
Architectural x10..x13 supply the arguments, independently of encoded operands.
`sourceValue` reads the CPU's register array through the Sail map and defaults
absent map entries to zero, making the handler total even on partial Sail maps.
See `tracer/src/instruction/virtual_host_io.rs` (`VirtualHostIO::exec`) and
`tracer/src/emulator/cpu.rs` (the three handlers) at `ff6fc6568`. -/
noncomputable def execHostIOWith
    (loadByte : SailJoltState → Nat → Option (BitVec 8)) :
    JoltMonad ExecutionResult := do
  let state ← get
  let callId := (sourceValue (.xreg (.Regidx 10)) state).setWidth 32
  if callId = hostAdviceWriteCall then
    let pointer := sourceValue (.xreg (.Regidx 11)) state
    let count := sourceValue (.xreg (.Regidx 12)) state
    match readHostBytes (loadByte state) pointer.toNat count.toNat (2 ^ 64 - 1) #[] with
    | none => pure ()
    | some bytes => modify fun current =>
        { current with adviceTape :=
            { current.adviceTape with bytes := current.adviceTape.bytes ++ bytes } }
  else if state.hostIO.mode != .replay then
    let pointer := (sourceValue (.xreg (.Regidx 11)) state).setWidth 32
    let count := (sourceValue (.xreg (.Regidx 12)) state).setWidth 32
    let event := (sourceValue (.xreg (.Regidx 13)) state).setWidth 32
    -- Both handlers reject unknown events before reading. Their accepted events
    -- are 1 and 2; their output and marker effects are outside the guest state.
    if (callId = hostCycleTrackCall || callId = hostPrintCall) && (event = 1 || event = 2) then
      let _ := readHostBytes (loadByte state) pointer.toNat count.toNat (2 ^ 32) #[]
      pure ()
  pure RETIRE_SUCCESS

/-- Execute host calls using exactly the model's guest byte-load acceptance.
For example, an unreadable advice range retires successfully without appending.
See `tracer/src/emulator/mmu.rs` (`is_host_readable`, `load_host_byte`) at `ff6fc6568`. -/
noncomputable def execHostIO : JoltMonad ExecutionResult :=
  execHostIOWith Mmu.load?

/-- Every host call retires successfully, and its only state change is an
append to the advice tape.
For example, a rejected advice write or any print returns the state unchanged,
and an accepted advice write appends its bytes without moving the read cursor. -/
theorem execHostIO_result (state : SailJoltState) :
    execHostIO state = .ok RETIRE_SUCCESS state ∨
      ∃ bytes, execHostIO state = .ok RETIRE_SUCCESS
        { state with adviceTape :=
            { state.adviceTape with bytes := state.adviceTape.bytes ++ bytes } } := by
  simp only [execHostIO, execHostIOWith, get, getThe, MonadStateOf.get, EStateM.get,
    bind, EStateM.bind, pure, modify, modifyGet, MonadStateOf.modifyGet]
  by_cases hadvice : (sourceValue (.xreg (.Regidx 10)) state).setWidth 32 = hostAdviceWriteCall
  · rw [ite_eq_left hadvice]
    cases readHostBytes (Mmu.load? state) (sourceValue (.xreg (.Regidx 11)) state).toNat
        (sourceValue (.xreg (.Regidx 12)) state).toNat (2 ^ 64 - 1) #[] with
    | none => exact .inl rfl
    | some bytes => exact .inr ⟨bytes, rfl⟩
  · rw [ite_eq_right hadvice]
    simp only [ite_self]
    exact .inl rfl

/-- Every host call retires successfully from every state, including rejected
calls and partial register maps.
For example, a whole-run proof can use the resulting post-state for an arbitrary
next `VirtualHostIO` row without a host-call-success restriction. -/
theorem execHostIO_succeeds (state : SailJoltState) :
    ∃ post, execHostIO state = .ok RETIRE_SUCCESS post := by
  rcases execHostIO_result state with h | ⟨_, h⟩ <;> exact ⟨_, h⟩

end JoltISA
