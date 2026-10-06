import JoltConstraints.witness_helpers.ram_ra_chunk

set_option autoImplicit false

namespace HonestWitness

-- The final snapshot is the last actual post-state, regardless of witness
-- padding. An empty execution retains the program's initial state.
noncomputable def finalTraceState {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (trace : HonestTrace joltInstance privateInputs) : SailJoltState :=
  if nonempty : 0 < trace.rows.size then
    (getElem trace.rows (trace.rows.size - 1) (Nat.sub_lt nonempty (by decide))).postState
  else trace.initialState

-- Rust: [populate_ram_bytes](/Users/ari.biswas/Work-with-A16z/jolt/crates/jolt-witness/src/backend/trace/ram.rs:289).
-- Pack a witness memory image in little-endian order. Missing image bytes are
-- intentionally zero: Rust starts with a zero array and zero-pads partial words.
-- This is image encoding, not an ISA read of possibly missing execution memory.
def ramImageWord (byte : Nat → BitVec 8) (start : Nat) : BitVec 64 :=
  byte (start + 7) ++ byte (start + 6) ++ byte (start + 5) ++ byte (start + 4) ++
    byte (start + 3) ++ byte (start + 2) ++ byte (start + 1) ++ byte start

-- Rust layouts place the device regions at aligned byte addresses. A buffer
-- overlays whole remapped words, with zero-padding in its final partial word.
def overlayRamBytes (layout : MemoryLayout) (start : BitVec 64)
    (bytes : Array (BitVec 8)) (address : Nat) (previous : BitVec 64) : BitVec 64 :=
  match remapRamAddress layout start with
  | none => previous
  | some firstWord =>
      if firstWord ≤ address ∧ (address - firstWord) * 8 < bytes.size then
        ramImageWord (fun i => bytes[i]?.getD 0) ((address - firstWord) * 8)
      else previous

-- Rust: [initial_ram_state](/Users/ari.biswas/Work-with-A16z/jolt/crates/jolt-witness/src/backend/trace/ram.rs:81)
-- and [RAM preprocessing](/Users/ari.biswas/Work-with-A16z/jolt/crates/jolt-program/src/preprocess/ram.rs:40).
-- The loaded program bytes are already in initialState.sail.mem. Allocated RAM
-- beyond that image is zero. Overlay trusted advice, untrusted advice, then input
-- in Rust's order; output, panic, and termination start at zero in this witness.
noncomputable def initialRamWord {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (address : Nat) : BitVec 64 :=
  let state := trace.initialState
  let layout := state.jolt_device.memory_layout
  let absolute := min layout.trusted_advice_start.toNat layout.untrusted_advice_start.toNat + 8 * address
  let ram := if JoltISA.RAM_START_ADDRESS ≤ absolute then
      ramImageWord (fun i => (state.sail.mem.get? i).getD 0) absolute
    else 0
  let trusted := overlayRamBytes layout layout.trusted_advice_start state.jolt_device.trusted_advice address ram
  let untrusted := overlayRamBytes layout layout.untrusted_advice_start state.jolt_device.untrusted_advice address trusted
  overlayRamBytes layout layout.input_start state.jolt_device.inputs address untrusted

-- Rust: [final_ram_state](/Users/ari.biswas/Work-with-A16z/jolt/crates/jolt-witness/src/backend/trace/ram.rs:132).
-- Use the final ISA RAM snapshot and device buffers. In particular, termination
-- is an explicit witness word (1 unless panicked), even though device loads from
-- the termination region return zero. Panic occupies one word, not eight 1 bytes.
noncomputable def finalRamWord {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (trace : HonestTrace joltInstance privateInputs) (address : Nat) : BitVec 64 :=
  let state := finalTraceState trace
  let layout := trace.initialState.jolt_device.memory_layout
  let absolute := min layout.trusted_advice_start.toNat layout.untrusted_advice_start.toNat + 8 * address
  let ram := if JoltISA.RAM_START_ADDRESS ≤ absolute then
      ramImageWord (fun i => (state.sail.mem.get? i).getD 0) absolute
    else 0
  let trusted := overlayRamBytes layout state.jolt_device.memory_layout.trusted_advice_start state.jolt_device.trusted_advice address ram
  let untrusted := overlayRamBytes layout state.jolt_device.memory_layout.untrusted_advice_start state.jolt_device.untrusted_advice address trusted
  let input := overlayRamBytes layout state.jolt_device.memory_layout.input_start state.jolt_device.inputs address untrusted
  let output := overlayRamBytes layout state.jolt_device.memory_layout.output_start state.jolt_device.outputs address input
  let panic := if remapRamAddress layout state.jolt_device.memory_layout.panic = some address then
      (if state.jolt_device.panic then 1 else 0)
    else output
  if !state.jolt_device.panic && remapRamAddress layout state.jolt_device.memory_layout.termination == some address then 1
  else panic

end HonestWitness
