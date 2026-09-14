import JoltBytecode.InstructionEquivalence.ProofSupport.Memory.Basic
import Mathlib.Tactic

/-!
# Memory window derivations

This file contains generic consequences of primitive memory-window assumptions.
It does not define proof-facing memory bundles: bytes, PMP, and MMIO facts are
projected directly from the top-level assumption bundles.
-/

set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions
open virtaddr MemoryAccessType mem_payload

set_option autoImplicit true

noncomputable section

/-- Byte-present facts are monotone over explicit subwindows. -/
theorem memBytesPresentAt_subaccess
    {s : SailState} {base : BitVec 64} {baseWidth offset accessWidth : Nat}
    (hbytes : MemBytesPresentAt s base baseWidth)
    (hfits : offset + accessWidth ≤ baseWidth)
    (h_no_ovf : base.toNat + offset < 2 ^ 64) :
    MemBytesPresentAt s (base + BitVec.ofNat 64 offset) accessWidth := by
  intro k hk
  have haddr_toNat :
      (base + BitVec.ofNat 64 offset).toNat = base.toNat + offset :=
    toNat_add_small_of_no_ovf base offset h_no_ovf
  simpa [haddr_toNat, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    using hbytes (offset + k) (by omega)

namespace Assumptions.LoadPmpOkWindow

theorem subaccess
    {base : BitVec 64} {baseWidth offset accessWidth : Nat} {s : SailState}
    (h : Assumptions.LoadPmpOkWindow base baseWidth s)
    (hfits : offset + accessWidth ≤ baseWidth) :
    Assumptions.LoadPmpOk (base + BitVec.ofNat 64 offset) accessWidth s :=
  h.ok offset accessWidth hfits

end Assumptions.LoadPmpOkWindow

namespace Assumptions.StorePmpOkWindow

theorem subaccess
    {base : BitVec 64} {baseWidth offset accessWidth : Nat} {s : SailState}
    (h : Assumptions.StorePmpOkWindow base baseWidth s)
    (hfits : offset + accessWidth ≤ baseWidth) :
    Assumptions.StorePmpOk (base + BitVec.ofNat 64 offset) accessWidth s :=
  h.ok offset accessWidth hfits

end Assumptions.StorePmpOkWindow

namespace Assumptions.AtomicPmpOkWindow

theorem subaccess
    {op : amoop} {base : BitVec 64} {baseWidth offset accessWidth : Nat}
    {s : SailState}
    (h : Assumptions.AtomicPmpOkWindow op base baseWidth s)
    (hfits : offset + accessWidth ≤ baseWidth) :
    Assumptions.AtomicPmpOk op (base + BitVec.ofNat 64 offset) accessWidth s :=
  h.ok offset accessWidth hfits

end Assumptions.AtomicPmpOkWindow

namespace Assumptions.NotReadableMmioWindow

theorem subaccess
    {base : BitVec 64} {baseWidth offset accessWidth : Nat} {s : SailState}
    (h : Assumptions.NotReadableMmioWindow base baseWidth s)
    (hfits : offset + accessWidth ≤ baseWidth) :
    Assumptions.NotReadableMmio (base + BitVec.ofNat 64 offset) accessWidth s :=
  h.ok offset accessWidth hfits

end Assumptions.NotReadableMmioWindow

namespace Assumptions.NotWritableMmioWindow

theorem subaccess
    {base : BitVec 64} {baseWidth offset accessWidth : Nat} {s : SailState}
    (h : Assumptions.NotWritableMmioWindow base baseWidth s)
    (hfits : offset + accessWidth ≤ baseWidth) :
    Assumptions.NotWritableMmio (base + BitVec.ofNat 64 offset) accessWidth s :=
  h.ok offset accessWidth hfits

end Assumptions.NotWritableMmioWindow

end
