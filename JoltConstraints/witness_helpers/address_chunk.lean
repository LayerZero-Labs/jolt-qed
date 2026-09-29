import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

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

private theorem eq_of_baseDigits (base n a b : Nat) (basePos : 0 < base)
    (ha : a < base ^ n) (hb : b < base ^ n)
    (digits : ∀ i : Nat, i < n →
      a / base ^ i % base = b / base ^ i % base) : a = b := by
  induction n generalizing a b with
  | zero =>
      simp at ha hb
      omega
  | succ n ih =>
      have ha' : a / base < base ^ n := by
        apply (Nat.div_lt_iff_lt_mul basePos).2
        simpa [pow_succ, mul_comm] using ha
      have hb' : b / base < base ^ n := by
        apply (Nat.div_lt_iff_lt_mul basePos).2
        simpa [pow_succ, mul_comm] using hb
      have hd : ∀ i : Nat, i < n →
          (a / base) / base ^ i % base = (b / base) / base ^ i % base := by
        intro i hi
        have h := digits (i + 1) (by omega)
        simpa [pow_succ, Nat.div_div_eq_div_mul, mul_comm] using h
      have hquot := ih (a / base) (b / base) ha' hb' hd
      have hrem := digits 0 (by omega)
      simp only [pow_zero, Nat.div_one] at hrem
      calc
        a = a % base + base * (a / base) := (Nat.mod_add_div a base).symm
        _ = b % base + base * (b / base) := by rw [hrem, hquot]
        _ = b := Nat.mod_add_div b base

/-- Two addresses in the represented range are equal if all of their
most-significant-first chunks agree. -/
theorem addressChunk_injective (bits chunks a b : Nat)
    (ha : a < 2 ^ (chunks * bits)) (hb : b < 2 ^ (chunks * bits))
    (digits : ∀ chunk : Fin chunks,
      addressChunk bits chunk a = addressChunk bits chunk b) : a = b := by
  apply eq_of_baseDigits (2 ^ bits) chunks a b (Nat.pow_pos (by decide))
  · simpa only [mul_comm chunks bits, pow_mul] using ha
  · simpa only [mul_comm chunks bits, pow_mul] using hb
  · intro i hi
    let chunk : Fin chunks := ⟨chunks - 1 - i, by omega⟩
    have h := digits chunk
    dsimp [addressChunk, chunk] at h
    have hindex : chunks - 1 - (chunks - 1 - i) = i := by omega
    simpa only [hindex, mul_comm i bits, pow_mul] using h

end HonestWitness
