import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Fintype.Basic

set_option autoImplicit false

namespace HonestWitness

open scoped BigOperators

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

theorem sum_addressChunkEntry_some {F : Type} [Field F] (bits : Nat)
    {chunks : Nat} (chunk : Fin chunks) (address : Nat) :
    (∑ entry : Fin (2 ^ bits), addressChunkEntry (F := F) bits chunk
      (some address) entry) = 1 := by
  let selected : Fin (2 ^ bits) :=
    ⟨addressChunk bits chunk address, Nat.mod_lt _ (Nat.pow_pos (by decide))⟩
  have h : ∀ entry : Fin (2 ^ bits),
      (entry.val = addressChunk bits chunk address) ↔ entry = selected := by
    intro entry
    simp [selected, Fin.ext_iff]
  simp only [addressChunkEntry]
  simp_rw [h]
  simp [Finset.sum_ite_eq']

end HonestWitness
