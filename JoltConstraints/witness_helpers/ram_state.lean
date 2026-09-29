import JoltConstraints.witness_helpers.ram_ra_chunk

set_option autoImplicit false

namespace HonestWitness

-- The final snapshot is the last actual post-state, regardless of witness
-- padding. An empty execution retains the program's initial state.
noncomputable def finalTraceState {program : JoltProgram}
    (trace : JoltTrace program) : SailJoltState :=
  if nonempty : 0 < trace.rows.size then
    (getElem trace.rows (trace.rows.size - 1) (Nat.sub_lt nonempty (by decide))).postState
  else program.initialState

-- Rust: [populate_ram_bytes](/Users/ari.biswas/Work-with-A16z/jolt/crates/jolt-witness/src/backend/trace/ram.rs:289).
-- Pack a witness memory image in little-endian order. Missing image bytes are
-- intentionally zero: Rust starts with a zero array and zero-pads partial words.
-- This is image encoding, not an ISA read of possibly missing execution memory.
def ramImageWord (byte : Nat → BitVec 8) (start : Nat) : BitVec 64 :=
  byte (start + 7) ++ byte (start + 6) ++ byte (start + 5) ++ byte (start + 4) ++
    byte (start + 3) ++ byte (start + 2) ++ byte (start + 1) ++ byte start

-- Rust layouts place the device regions at aligned byte addresses. A buffer
-- overlays whole remapped words, with zero-padding in its final partial word.
def overlayRamBytes (layout : JoltIOLayout) (start : BitVec 64)
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
noncomputable def initialRamWord (program : JoltProgram) (address : Nat) : BitVec 64 :=
  let state := program.initialState
  let layout := state.io.layout
  let absolute := min layout.trustedAdvice.1.toNat layout.untrustedAdvice.1.toNat + 8 * address
  let ram := if JoltISA.ramStartAddress ≤ absolute then
      ramImageWord (fun i => (state.sail.mem.get? i).getD 0) absolute
    else 0
  let trusted := overlayRamBytes layout layout.trustedAdvice.1 state.io.trustedAdvice address ram
  let untrusted := overlayRamBytes layout layout.untrustedAdvice.1 state.io.untrustedAdvice address trusted
  overlayRamBytes layout layout.input.1 state.io.inputs address untrusted

-- Rust: [final_ram_state](/Users/ari.biswas/Work-with-A16z/jolt/crates/jolt-witness/src/backend/trace/ram.rs:132).
-- Use the final ISA RAM snapshot and device buffers. In particular, termination
-- is an explicit witness word (1 unless panicked), even though device loads from
-- the termination region return zero. Panic occupies one word, not eight 1 bytes.
noncomputable def finalRamWord {program : JoltProgram}
    (trace : JoltTrace program) (address : Nat) : BitVec 64 :=
  let state := finalTraceState trace
  let layout := program.initialState.io.layout
  let absolute := min layout.trustedAdvice.1.toNat layout.untrustedAdvice.1.toNat + 8 * address
  let ram := if JoltISA.ramStartAddress ≤ absolute then
      ramImageWord (fun i => (state.sail.mem.get? i).getD 0) absolute
    else 0
  let trusted := overlayRamBytes layout state.io.layout.trustedAdvice.1 state.io.trustedAdvice address ram
  let untrusted := overlayRamBytes layout state.io.layout.untrustedAdvice.1 state.io.untrustedAdvice address trusted
  let input := overlayRamBytes layout state.io.layout.input.1 state.io.inputs address untrusted
  let output := overlayRamBytes layout state.io.layout.output.1 state.io.outputs address input
  let panic := if remapRamAddress layout state.io.layout.panic.1 = some address then
      (if state.io.panic then 1 else 0)
    else output
  if !state.io.panic && remapRamAddress layout state.io.layout.termination.1 == some address then 1
  else panic

end HonestWitness
