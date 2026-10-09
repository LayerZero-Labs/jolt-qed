import JoltBytecode.InstructionEquivalence.ProofSupport.Lemmas
import JoltBytecode.InstructionEquivalence.ProofSupport.Memory.MmuJolt

/-!
# LD instruction semantics

Run lemmas for the Jolt ISA `LD` instruction.
-/

open Sail PreSail LeanRV64D.Functions
open virtaddr MemoryAccessType mem_payload

set_option autoImplicit true

noncomputable section

namespace JoltISA

-- When Rust's checks pass, LD writes the 64 bits read directly from RAM.
theorem ld_run_vreg_vreg {faultClass : LoadFaultClass}
    (vd base : VReg) (imm : BitVec 12) (js : SailJoltState)
    (h_align :
      (js.vregs base + sign_extend (m := 64) imm) &&& (7 : BitVec 64) = 0)
    (hvd : WritableVReg vd)
    (h_ram : RAM_START_ADDRESS ≤ (js.vregs base + sign_extend (m := 64) imm).toNat)
    (h_legal : Mmu.effective_address_ok js.jolt_device
      (js.vregs base + sign_extend (m := 64) imm).toNat false = true) :
    (execInstr (JoltISA.Encoded.LD faultClass (.vreg vd) (.vreg base) imm)).run js =
      .ok RETIRE_SUCCESS
        { js with
          vregs := fun r =>
            if r = vd then
              Mmu.ram_doubleword js.sail.mem (js.vregs base + sign_extend (m := 64) imm).toNat
            else js.vregs r } := by
  unfold WritableVReg at hvd
  unfold execInstr readSrc writeDst readVReg
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get]
  rw [if_pos h_align]
  simp only [EStateM.bind, Mmu.load_doubleword_ram _ _ h_align h_ram h_legal]
  simp only [writeVReg, hvd, ↓reduceIte,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, EStateM.pure]

-- The same, from an architectural-register base.
theorem ld_run_vreg_xreg {faultClass : LoadFaultClass}
    (vd : VReg) (base : regidx)
    (imm : BitVec 12) (js : SailJoltState) (baseValue : BitVec 64)
    (hbase : rX_bits base js.sail = .ok baseValue js.sail)
    (h_align :
      (baseValue + sign_extend (m := 64) imm) &&& (7 : BitVec 64) = 0)
    (hvd : WritableVReg vd)
    (h_ram : RAM_START_ADDRESS ≤ (baseValue + sign_extend (m := 64) imm).toNat)
    (h_legal : Mmu.effective_address_ok js.jolt_device
      (baseValue + sign_extend (m := 64) imm).toNat false = true) :
    (execInstr (JoltISA.Encoded.LD faultClass (.vreg vd) (.xreg base) imm)).run js =
      .ok RETIRE_SUCCESS
        { js with
          vregs := fun r =>
            if r = vd then
              Mmu.ram_doubleword js.sail.mem (baseValue + sign_extend (m := 64) imm).toNat
            else js.vregs r } := by
  unfold WritableVReg at hvd
  unfold execInstr readSrc writeDst liftSail
  simp only [bind, EStateM.bind, pure, EStateM.run]
  rw [hbase]
  dsimp only
  rw [if_pos h_align]
  simp only [EStateM.bind, Mmu.load_doubleword_ram _ _ h_align h_ram h_legal]
  simp only [writeVReg, hvd, ↓reduceIte,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, EStateM.pure]

end JoltISA

end
