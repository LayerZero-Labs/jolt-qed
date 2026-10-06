import JoltBytecode.InstructionEquivalence.ProofSupport.Lemmas
import JoltBytecode.InstructionEquivalence.ProofSupport.Memory.MmuJolt

/-!
# SD instruction semantics

Run lemmas for the Jolt ISA `SD` instruction.
-/

open Sail PreSail LeanRV64D.Functions
open virtaddr MemoryAccessType mem_payload

set_option autoImplicit true

noncomputable section

namespace JoltISA

-- When Rust's checks pass, SD writes the 64 bits directly to RAM.
theorem execInstr_sd_vreg_run (base value : VReg) (imm : BitVec 12)
    (js : SailJoltState)
    (h_align :
      (js.vregs base + sign_extend (m := 64) imm) &&& (7 : BitVec 64) = 0)
    (h_ram : RAM_START_ADDRESS ≤ (js.vregs base + sign_extend (m := 64) imm).toNat)
    (h_legal : Mmu.effective_address_ok js.jolt_device
      (js.vregs base + sign_extend (m := 64) imm).toNat true = true) :
    (execInstr (JoltISA.Encoded.SD (.vreg base) (.vreg value) imm)).run js =
      .ok RETIRE_SUCCESS
        { js with
          sail := { js.sail with
            mem := Mmu.write_ram_doubleword js.sail.mem
              (js.vregs base + sign_extend (m := 64) imm).toNat (js.vregs value) } } := by
  unfold execInstr readSrc readVReg
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get]
  rw [if_pos h_align]
  simp only [EStateM.bind, Mmu.store_doubleword_ram _ _ _ h_align h_ram h_legal, EStateM.pure]

-- The same, from architectural-register base and value sources.
theorem execInstr_sd_xreg_xreg_run
    (base value : regidx) (imm : BitVec 12)
    (js : SailJoltState) (baseValue stored : BitVec 64)
    (hbase : rX_bits base js.sail = .ok baseValue js.sail)
    (hvalue : rX_bits value js.sail = .ok stored js.sail)
    (h_align :
      (baseValue + sign_extend (m := 64) imm) &&& (7 : BitVec 64) = 0)
    (h_ram : RAM_START_ADDRESS ≤ (baseValue + sign_extend (m := 64) imm).toNat)
    (h_legal : Mmu.effective_address_ok js.jolt_device
      (baseValue + sign_extend (m := 64) imm).toNat true = true) :
    (execInstr (JoltISA.Encoded.SD (.xreg base) (.xreg value) imm)).run js =
      .ok RETIRE_SUCCESS
        { js with
          sail := { js.sail with
            mem := Mmu.write_ram_doubleword js.sail.mem
              (baseValue + sign_extend (m := 64) imm).toNat stored } } := by
  unfold execInstr readSrc liftSail
  simp only [bind, EStateM.bind, pure, EStateM.run]
  rw [hbase]
  dsimp only
  rw [hvalue]
  dsimp only
  rw [if_pos h_align]
  simp only [EStateM.bind, Mmu.store_doubleword_ram _ _ _ h_align h_ram h_legal, EStateM.pure]

end JoltISA

end
