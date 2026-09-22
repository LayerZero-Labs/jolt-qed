import Mathlib.Algebra.Field.Defs

set_option autoImplicit false

namespace HonestWitness

-- Rust: [RaChunkSelector](/Users/ari.biswas/Work-with-A16z/jolt/crates/jolt-witness/src/witnesses/one_hot.rs:19).
-- Split an unsigned address into equally wide chunks, most significant first.
-- For example, with three 4-bit chunks, 0x123 gives chunks 1, 2, 3.
-- Leading bits in a partially used first chunk are zero.
def addressChunk (bits : Nat) {chunks : Nat} (chunk : Fin chunks)
    (address : Nat) : Nat :=
  (address / 2 ^ ((chunks - 1 - chunk.val) * bits)) % 2 ^ bits

-- Rust: [materialize_one_hot](/Users/ari.biswas/Work-with-A16z/jolt/crates/jolt-witness/src/backend/trace/cycle.rs:73).
-- A present address selects exactly one entry in this chunk. None selects no
-- entry; RAM uses this for padding and cycles without a remappable access.
def addressChunkEntry {F : Type} [Zero F] [One F] (bits : Nat)
    {chunks : Nat} (chunk : Fin chunks) (address : Option Nat)
    (entry : Fin (2 ^ bits)) : F :=
  match address with
  | some address => if entry.val = addressChunk bits chunk address then 1 else 0
  | none => 0

end HonestWitness
