import JoltBytecode.InstructionEquivalence.ProofSupport.Lemmas

/-!
# LD instruction semantics

Run lemmas for the Jolt ISA `LD` instruction.
-/

open Sail PreSail LeanRV64D.Functions
open virtaddr MemoryAccessType mem_payload

set_option autoImplicit true

noncomputable section

namespace JoltISA

/-- Successful `LD`: if Sail's dword read pipeline returns `value`, then the
Jolt-ISA `LD` writes that dword to the destination virtual register and
continues with `RETIRE_SUCCESS`. -/
theorem ld_run_vreg_vreg_from_memory_read {faultClass : LoadFaultClass}
    (vd base : VReg) (imm : BitVec 12)
    (js : SailJoltState) (value : BitVec 64)
    (h_align :
      (js.vregs base + sign_extend (m := 64) imm) &&& (7 : BitVec 64) = 0)
    (h :
      vmem_read_addr (Virtaddr (js.vregs base + sign_extend (m := 64) imm)) 0 8
        (Load Data) false false false js.sail =
        .ok (Ok value) js.sail)
    (hvd : WritableVReg vd)
    (h_ram : ramStartAddress ≤ (js.vregs base + sign_extend (m := 64) imm).toNat) :
    (execInstr (.LD faultClass (.vreg vd) (.vreg base) imm)).run js =
      .ok RETIRE_SUCCESS
        { js with
          vregs := fun r => if r = vd then value else js.vregs r } := by
  unfold WritableVReg at hvd
  unfold execInstr readSrc writeDst readVReg liftSail
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get]
  rw [if_pos h_align]
  rw [readMemoryWord_ram _ h_ram]
  unfold liftSail
  simp only [EStateM.bind, h, sideEffectingDst, writeVReg, hvd, ↓reduceIte,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, EStateM.pure]

/-- Successful `LD` from an architectural-register base into a virtual
register. -/
theorem ld_run_vreg_xreg_from_memory_read {faultClass : LoadFaultClass}
    (vd : VReg) (base : regidx)
    (imm : BitVec 12) (js : SailJoltState) (baseValue value : BitVec 64)
    (hbase : rX_bits base js.sail = .ok baseValue js.sail)
    (h_align :
      (baseValue + sign_extend (m := 64) imm) &&& (7 : BitVec 64) = 0)
    (hread :
      vmem_read_addr (Virtaddr (baseValue + sign_extend (m := 64) imm)) 0 8
        (Load Data) false false false js.sail =
        .ok (Ok value) js.sail)
    (hvd : WritableVReg vd)
    (h_ram : ramStartAddress ≤ (baseValue + sign_extend (m := 64) imm).toNat) :
    (execInstr (.LD faultClass (.vreg vd) (.xreg base) imm)).run js =
      .ok RETIRE_SUCCESS
        { js with
          vregs := fun r => if r = vd then value else js.vregs r } := by
  unfold WritableVReg at hvd
  unfold execInstr readSrc writeDst liftSail
  simp only [bind, EStateM.bind, pure, EStateM.run]
  rw [hbase]
  dsimp only
  rw [if_pos h_align]
  rw [readMemoryWord_ram _ h_ram]
  unfold liftSail
  simp only [EStateM.bind, hread, sideEffectingDst, writeVReg, hvd, ↓reduceIte,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, EStateM.pure]

end JoltISA

end
