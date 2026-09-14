import JoltBytecode.Assumptions
import Mathlib.Tactic

/-!
# Exact flat-memory model

This file contains the direct memory predicates and byte-assembly functions used
by instruction-equivalence memory proofs. It has no Sail pipeline collapse
lemmas and no instruction-family assumptions.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option mvcgen.warning false

open Sail PreSail LeanRV64D.Functions
open Std.Do
open virtaddr MemoryAccessType mem_payload

set_option autoImplicit true

noncomputable section

/-!
# Memory utilities: direct hash-map byte assembly from `SailState.mem`.

-/

abbrev MemBytePresentAt (s : SailState) (addr : Nat) : Prop :=
  ∃ b : BitVec 8, s.mem.get? addr = some b

abbrev MemBytesPresentAt (s : SailState) (addr : BitVec 64) (width : Nat) : Prop :=
  ∀ k : Nat, k < width → MemBytePresentAt s (addr.toNat + k)

/-- Convert a concrete byte lookup into the `isSome` proof required by
`Option.get`. This is derived evidence, not an assumption. -/
theorem memBytePresent_isSome {s : SailState} {addr : Nat}
    (hpresent : MemBytePresentAt s addr) :
    (s.mem.get? addr).isSome = true := by
  rcases hpresent with ⟨b, hb⟩
  rw [hb]
  rfl

theorem ofNat64_toNat_lt_pow64 (k : Nat) (hk : k < 2 ^ 64) :
    (BitVec.ofNat 64 k).toNat = k := by
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt hk

theorem toNat_add_small_of_no_ovf (base : BitVec 64) (k : Nat)
    (h_no_ovf : base.toNat + k < 2 ^ 64) :
    (base + BitVec.ofNat 64 k).toNat = base.toNat + k := by
  have hk64 : k < 2 ^ 64 := by omega
  have hk_toNat := ofNat64_toNat_lt_pow64 k hk64
  have hadd := BitVec.toNat_add_of_lt
    (x := base) (y := BitVec.ofNat 64 k) (by simpa [hk_toNat] using h_no_ovf)
  simpa [hk_toNat] using hadd

theorem MemBytesPresentAt.byte_addr
    {s : SailState} {base : BitVec 64} {width k : Nat}
    (hbytes : MemBytesPresentAt s base width)
    (hk : k < width)
    (h_no_ovf : base.toNat + k < 2 ^ 64) :
    MemBytePresentAt s (base + BitVec.ofNat 64 k).toNat := by
  simpa [toNat_add_small_of_no_ovf base k h_no_ovf] using hbytes k hk

/-- A one-byte memory window contains the byte at its base address. -/
theorem MemBytesPresentAt.single_byte
    {s : SailState} {addr : BitVec 64}
    (hbytes : MemBytesPresentAt s addr 1) :
    MemBytePresentAt s addr.toNat := by
  simpa only [Nat.add_zero] using hbytes 0 (by omega)

namespace Assumptions.DwordPresent

theorem memBytesPresentAt
    {addr : BitVec 64} {s : SailState}
    (h : Assumptions.DwordPresent addr s) :
    MemBytesPresentAt s addr 8 := by
  intro k hk
  rcases h.bytes with ⟨bytes, hbytes⟩
  exact ⟨bytes ⟨k, hk⟩, hbytes ⟨k, hk⟩⟩

end Assumptions.DwordPresent

def loaded_byte_at_nat (s : SailState) (addr : Nat)
    (hpresent : MemBytePresentAt s addr) : BitVec 8 :=
  (s.mem.get? addr).get (memBytePresent_isSome hpresent)

-- The 8-bit byte at a given vaddr. Direct hash-map lookup on `s.mem`.
-- This has no missing-memory default: callers must pass byte-populatedness
-- derived from the public top-level memory assumption.
def loaded_byte_at (s : SailState) (vaddr : BitVec 64)
    (hpresent : MemBytePresentAt s vaddr.toNat) : BitVec 8 :=
  loaded_byte_at_nat s vaddr.toNat hpresent

-- Explicit little-endian byte-assembly at standard RISC-V load widths.
-- Byte at `vaddr` occupies the low 8 bits; each successive byte stacks above.
-- No recursion, no dependent-type gymnastics — each definition is a plain
-- chain of `BitVec.append` (`++`) of `loaded_byte_at` calls.

def loaded_halfword_at (s : SailState) (vaddr : BitVec 64)
    (hbytes : MemBytesPresentAt s vaddr 2)
    (h_no_ovf : vaddr.toNat + 1 < 2 ^ 64) : BitVec 16 :=
  loaded_byte_at s (vaddr + 1)
      (hbytes.byte_addr (k := 1) (by omega) h_no_ovf) ++
  loaded_byte_at s vaddr
      (by simpa using hbytes 0 (by omega))

def loaded_word_at (s : SailState) (vaddr : BitVec 64)
    (hbytes : MemBytesPresentAt s vaddr 4)
    (h_no_ovf : vaddr.toNat + 3 < 2 ^ 64) : BitVec 32 :=
  loaded_byte_at s (vaddr + 3)
      (hbytes.byte_addr (k := 3) (by omega) (by omega)) ++
  loaded_byte_at s (vaddr + 2)
      (hbytes.byte_addr (k := 2) (by omega) (by omega)) ++
  loaded_byte_at s (vaddr + 1)
      (hbytes.byte_addr (k := 1) (by omega) (by omega)) ++
  loaded_byte_at s vaddr
      (by simpa using hbytes 0 (by omega))

def loaded_dword_at (s : SailState) (vaddr : BitVec 64)
    (hbytes : MemBytesPresentAt s vaddr 8)
    (h_no_ovf : vaddr.toNat + 7 < 2 ^ 64) : BitVec 64 :=
  loaded_byte_at s (vaddr + 7)
      (hbytes.byte_addr (k := 7) (by omega) (by omega)) ++
  loaded_byte_at s (vaddr + 6)
      (hbytes.byte_addr (k := 6) (by omega) (by omega)) ++
  loaded_byte_at s (vaddr + 5)
      (hbytes.byte_addr (k := 5) (by omega) (by omega)) ++
  loaded_byte_at s (vaddr + 4)
      (hbytes.byte_addr (k := 4) (by omega) (by omega)) ++
  loaded_byte_at s (vaddr + 3)
      (hbytes.byte_addr (k := 3) (by omega) (by omega)) ++
  loaded_byte_at s (vaddr + 2)
      (hbytes.byte_addr (k := 2) (by omega) (by omega)) ++
  loaded_byte_at s (vaddr + 1)
      (hbytes.byte_addr (k := 1) (by omega) (by omega)) ++
  loaded_byte_at s vaddr
      (by simpa using hbytes 0 (by omega))

theorem loaded_byte_at_eq_of_addr_eq {s : SailState} {a b : BitVec 64}
    (haddr : a = b)
    (ha : MemBytePresentAt s a.toNat)
    (hb : MemBytePresentAt s b.toNat) :
    loaded_byte_at s a ha = loaded_byte_at s b hb := by
  subst b
  unfold loaded_byte_at loaded_byte_at_nat
  congr

theorem loaded_halfword_at_eq_of_addr_eq {s : SailState} {a b : BitVec 64}
    (haddr : a = b)
    (ha : MemBytesPresentAt s a 2)
    (ha_no_ovf : a.toNat + 1 < 2 ^ 64)
    (hb : MemBytesPresentAt s b 2)
    (hb_no_ovf : b.toNat + 1 < 2 ^ 64) :
    loaded_halfword_at s a ha ha_no_ovf =
      loaded_halfword_at s b hb hb_no_ovf := by
  subst b
  unfold loaded_halfword_at
  congr

theorem loaded_word_at_eq_of_addr_eq {s : SailState} {a b : BitVec 64}
    (haddr : a = b)
    (ha : MemBytesPresentAt s a 4)
    (ha_no_ovf : a.toNat + 3 < 2 ^ 64)
    (hb : MemBytesPresentAt s b 4)
    (hb_no_ovf : b.toNat + 3 < 2 ^ 64) :
    loaded_word_at s a ha ha_no_ovf =
      loaded_word_at s b hb hb_no_ovf := by
  subst b
  unfold loaded_word_at
  congr

-- ============================================================================
-- Reusable EStateM / Sail plumbing lemmas
-- ============================================================================


theorem readReg_eq (r : Register) (s : SailState) (v : RegisterType r)
    (h : s.regs.get? r = some v) :
    (Sail.readReg r : SailM (RegisterType r)) s = .ok v s := by
  unfold Sail.readReg PreSail.readReg
  simp only [bind, EStateM.bind, pure, EStateM.pure,
             MonadStateOf.get, EStateM.get, getThe, get, h]


end
