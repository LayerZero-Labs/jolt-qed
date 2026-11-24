import JoltConstraints.translation.witness_helpers.ram_ra_chunk

open LeanRV64D

set_option autoImplicit false

namespace TraceWitness

-- The final snapshot is the last actual post-state, regardless of witness
-- padding. An empty execution retains the program's initial state.
noncomputable def finalTraceState (trace : Trace) : SailJoltState :=
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

/-- Byte index `k` is counted from the low end of the packed word, and `bit`
is the bit index within that byte. -/
private theorem ramImageWord_getLsbD (byte : Nat → BitVec 8) (start : Nat)
    (k : Fin 8) (bit : Nat) (inByte : bit < 8) :
    (ramImageWord byte start).getLsbD (8 * k.val + bit) =
      (byte (start + k.val)).getLsbD bit := by
  fin_cases k <;> simp only [ramImageWord, Nat.reduceMul,
    Nat.zero_add, Nat.add_zero]
  all_goals repeat' (rw [BitVec.getLsbD_append]; split_ifs <;> try omega)
  all_goals congr 1
  all_goals omega

/-- Equal packed words have equal bytes at every offset from zero through seven. -/
theorem ramImageWord_injective_byte (f g : Nat → BitVec 8) (start : Nat)
    (same : ramImageWord f start = ramImageWord g start) :
    ∀ offset < 8, f (start + offset) = g (start + offset) := by
  intro offset offsetLt
  let k : Fin 8 := ⟨offset, offsetLt⟩
  apply BitVec.eq_of_getLsbD_eq
  intro bit bitLt
  have bits := congrArg (fun word : BitVec 64 => word.getLsbD (8 * k.val + bit)) same
  simpa only [ramImageWord_getLsbD f start k bit bitLt,
    ramImageWord_getLsbD g start k bit bitLt] using bits

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

/-- Read a remapped word from the shared initial memory.
For example, index zero reads the first advice/I/O word at the layout's lowest address.
Jolt at `ff6fc6568`: `crates/jolt-witness/src/backend/trace/ram.rs`
(`initial_ram_state`). -/
noncomputable def initialRamWordFromState (state : SailJoltState)
    (address : Nat) : BitVec 64 :=
  let layout := state.jolt_device.memory_layout
  ramImageWord (fun i => (state.sail.mem.get? i).getD 0)
    (layout.get_lowest_address.toNat + 8 * address)

/-- The initial shared-memory image of a trace; for example, before its first load. -/
noncomputable def initialRamWord (trace : Trace) : Nat → BitVec 64 :=
  initialRamWordFromState trace.initialState

/-- Read a remapped word from the final shared memory, without synthetic flag words.
For example, a store in the I/O gap remains in that word of the final snapshot.
Jolt at `ff6fc6568`: `crates/jolt-witness/src/backend/trace/ram.rs`
(`final_ram_state`). -/
noncomputable def finalRamWord (trace : Trace) (address : Nat) : BitVec 64 :=
  let state := finalTraceState trace
  ramImageWord (fun i => (state.sail.mem.get? i).getD 0)
    (trace.initialState.jolt_device.memory_layout.get_lowest_address.toNat + 8 * address)

end TraceWitness
