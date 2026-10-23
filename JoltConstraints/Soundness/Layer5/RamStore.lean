import JoltBytecode.InstructionEquivalence.ProofSupport.Memory.Write

/-! The byte-map effect of Jolt's ordinary-RAM doubleword store, expressed as
an update to one aligned word. Reuse the existing byte hit/frame proofs.
At public pin 8bbb2357:
See : jolt/tracer/src/emulator/mmu.rs:721-740 -/

set_option autoImplicit false

namespace JoltConstraints.Soundness

open Sail PreSail LeanRV64D.Functions JoltISA

/-- Reading byte `offset < 8` after a doubleword store returns that byte of
the stored word, counting from its least significant byte.
For example, offset zero of word 257 is byte 1.
See `jolt/tracer/src/emulator/mmu.rs` (`Mmu::store_doubleword_raw`) at 5def437f. -/
theorem ram_store_byte (state : SailState) (base value : BitVec 64)
    (offset : Nat) (within : offset < 8) :
    (Mmu.write_ram_doubleword state.mem base.toNat value).get? (base.toNat + offset) =
      some (value.extractLsb' (8 * offset) 8) := by
  change ({ state with mem := Mmu.write_ram_doubleword state.mem base.toNat value } : SailState).mem.get?
    (base.toNat + offset) = _
  rw [Mmu.write_ram_doubleword_eq]
  exact stored_dword_get?_hit state base value offset within

/-- Reading the eight bytes written by a doubleword store reconstructs its word.
For example, writing 257 and reading the same word gives 257 independently of
the old memory contents.
See `jolt/tracer/src/emulator/mmu.rs` (`Mmu::store_doubleword_raw`) at 5def437f. -/
theorem ram_store_word (state : SailState) (base value : BitVec 64) :
    Mmu.ram_doubleword (Mmu.write_ram_doubleword state.mem base.toNat value) base.toNat = value := by
  have first := ram_store_byte state base value 0 (by decide)
  simp only [Nat.add_zero] at first
  simp only [Mmu.ram_doubleword, Mmu.ram_byte, first,
    ram_store_byte state base value 1 (by decide),
    ram_store_byte state base value 2 (by decide),
    ram_store_byte state base value 3 (by decide),
    ram_store_byte state base value 4 (by decide),
    ram_store_byte state base value 5 (by decide),
    ram_store_byte state base value 6 (by decide),
    ram_store_byte state base value 7 (by decide), Option.getD_some, Nat.reduceMul]
  repeat rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide)]
  exact BitVec.extractLsb'_eq_self

private theorem ram_store_other (state : SailState) (base value : BitVec 64)
    (address : Nat) (separate : address + 8 ≤ base.toNat ∨ base.toNat + 8 ≤ address) :
    Mmu.ram_doubleword (Mmu.write_ram_doubleword state.mem base.toNat value) address =
      Mmu.ram_doubleword state.mem address := by
  have byte (offset : Nat) (within : offset < 8) :
      (Mmu.write_ram_doubleword state.mem base.toNat value).get? (address + offset) =
        state.mem.get? (address + offset) := by
    change ({ state with mem := Mmu.write_ram_doubleword state.mem base.toNat value } : SailState).mem.get?
      (address + offset) = _
    rw [Mmu.write_ram_doubleword_eq]
    exact stored_dword_untouched state base base value (address + offset) (by omega)
  have first := byte 0 (by decide)
  simp only [Nat.add_zero] at first
  simp only [Mmu.ram_doubleword, Mmu.ram_byte, first,
    byte 1 (by decide), byte 2 (by decide), byte 3 (by decide), byte 4 (by decide),
    byte 5 (by decide), byte 6 (by decide), byte 7 (by decide)]

/-- A byte-map store at the selected word updates exactly that word when the
map is observed on the RAM table's eight-byte grid. No prior memory contents
or byte-presence assumptions are needed: missing RAM bytes read as zero. -/
theorem ram_store_index (state : SailState) (base value : BitVec 64)
    (lowest chosen index : Nat) (addressIs : base.toNat = lowest + 8 * chosen) :
    Mmu.ram_doubleword (Mmu.write_ram_doubleword state.mem base.toNat value) (lowest + 8 * index) =
      if index = chosen then value else Mmu.ram_doubleword state.mem (lowest + 8 * index) := by
  by_cases same : index = chosen
  · rw [if_pos same, same, ← addressIs]
    exact ram_store_word state base value
  · rw [if_neg same]
    exact ram_store_other state base value _ (by omega)

end JoltConstraints.Soundness
