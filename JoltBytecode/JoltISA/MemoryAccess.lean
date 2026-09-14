/-
Copyright (c) 2026 Ari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ari 
-/


import LeanRV64D.Prelude

/-!
# Jolt ISA memory address vocabulary

These are small helper abbreviations or definitions that make memory
addressing more readable.
-/

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace Memory

/-- Effective address for base-plus-12-bit-immediate memory instructions. -/
abbrev effectiveAddr12 (base : BitVec 64) (imm : BitVec 12) : BitVec 64 :=
  base + sign_extend (m := 64) imm

/-- Align an address down to the enclosing 8-byte dword. -/
abbrev dwordBase (addr : BitVec 64) : BitVec 64 :=
  addr &&& (-8 : BitVec 64)

/-- Enclosing dword base for base-plus-12-bit-immediate memory instructions. -/
abbrev effectiveDwordBase12 (base : BitVec 64) (imm : BitVec 12) : BitVec 64 :=
  dwordBase (effectiveAddr12 base imm)

end Memory


/-- The double word aligned address -/
abbrev aligned_dword_addr (v : BitVec 64) (imm : BitVec 12) : BitVec 64 :=
  (v + sign_extend (m := 64) imm) &&& sign_extend (m := 64) (-8 : BitVec 12)

/-- Generic effective address for memory instructions with a sign-extended
12-bit immediate. -/
abbrev load_effective_address (val : BitVec 64) (imm : BitVec 12) : BitVec 64 :=
  Memory.effectiveAddr12 val imm

/-- Generic aligned dword base address used by the Jolt inline memory sequences
after computing the effective address. -/
abbrev compute_aligned_dword_base_address
    (val : BitVec 64) (imm : BitVec 12) : BitVec 64 :=
  load_effective_address val imm &&& (-8 : BitVec 64)

end
