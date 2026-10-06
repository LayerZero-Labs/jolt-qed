import JoltConstraints.witness_helpers.address_chunk
import JoltConstraints.witness_helpers.ram_address
import JoltConstraints.witness
import JoltConstraints.honest_trace

set_option autoImplicit false

namespace HonestWitness

-- Rust: [remap_word_address](/Users/ari.biswas/Work-with-A16z/jolt/common/src/jolt_device.rs:496).
-- RAM and device I/O share one word-address domain, starting at the lower
-- advice-region address. Address 0 and addresses below that start have no hot
-- entry, matching RemappedRamAddress's treatment of Rust remapping errors.
def remapRamAddress (layout : MemoryLayout) (address : BitVec 64) : Option Nat :=
  let lowest := min layout.trusted_advice_start.toNat layout.untrusted_advice_start.toNat
  if address.toNat = 0 ∨ address.toNat < lowest then none
  else some ((address.toNat - lowest) / 8)

-- Preprocessing uses the program's initial layout for every execution step.
-- Padding and instructions without a RAM access have no remapped address.
noncomputable def remappedRamAddress {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (trace : HonestTrace joltInstance privateInputs) (t : Nat) : Option Nat :=
  if inBounds : t < trace.rows.size then
    let row := getElem trace.rows t inBounds
    let instruction :=
      (getElem trace.bytecode row.rowIndex.val row.rowIndex.isLt).instruction
    (ramAccessAddress instruction row.preState).bind
      (remapRamAddress trace.initialState.jolt_device.memory_layout)
  else none

-- Rust: [RamRaChunk](/Users/ari.biswas/Work-with-A16z/jolt/crates/jolt-witness/src/witnesses/one_hot.rs:134).
-- Each actual remapped access selects one entry per chunk. All other cycles
-- are entirely zero, unlike instruction and bytecode padding.
noncomputable def RamRaChunk {F : Type} [Field F] (p : WitnessParams)
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs) :
    Fin p.ramChunks → Fin (2 ^ p.chunkBits) → Fin p.traceLength → F :=
  fun chunk entry t =>
    addressChunkEntry p.chunkBits chunk (remappedRamAddress trace t.val) entry

end HonestWitness
