import JoltConstraints.witness_helpers.address_chunk
import JoltConstraints.witness_helpers.ram_address
import JoltConstraints.witness
import JoltConstraints.trace

set_option autoImplicit false

namespace HonestWitness

-- Rust: [remap_word_address](/Users/ari.biswas/Work-with-A16z/jolt/common/src/jolt_device.rs:496).
-- RAM and device I/O share one word-address domain, starting at the lower
-- advice-region address. Address 0 and addresses below that start have no hot
-- entry, matching RemappedRamAddress's treatment of Rust remapping errors.
def remapRamAddress (layout : JoltIOLayout) (address : BitVec 64) : Option Nat :=
  let lowest := min layout.trustedAdvice.1.toNat layout.untrustedAdvice.1.toNat
  if address.toNat = 0 ∨ address.toNat < lowest then none
  else some ((address.toNat - lowest) / 8)

-- Preprocessing uses the program's initial layout for every execution step.
-- Padding and instructions without a RAM access have no remapped address.
noncomputable def remappedRamAddress {program : JoltProgram}
    (trace : JoltTrace program) (t : Nat) : Option Nat :=
  if inBounds : t < trace.rows.size then
    let row := getElem trace.rows t inBounds
    let instruction :=
      (getElem program.expandedBytecode row.rowIndex.val row.rowIndex.isLt).instruction
    (ramAccessAddress instruction row.preState).bind
      (remapRamAddress program.initialState.io.layout)
  else none

-- Rust: [RamRaChunk](/Users/ari.biswas/Work-with-A16z/jolt/crates/jolt-witness/src/witnesses/one_hot.rs:134).
-- Each actual remapped access selects one entry per chunk. All other cycles
-- are entirely zero, unlike instruction and bytecode padding.
noncomputable def RamRaChunk {F : Type} [Field F] (p : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program) :
    Fin p.ramChunks → Fin (2 ^ p.chunkBits) → Fin p.traceLength → F :=
  fun chunk entry t =>
    addressChunkEntry p.chunkBits chunk (remappedRamAddress trace t.val) entry

end HonestWitness
