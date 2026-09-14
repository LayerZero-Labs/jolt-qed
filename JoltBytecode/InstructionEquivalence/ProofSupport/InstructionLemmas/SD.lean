import JoltBytecode.InstructionEquivalence.ProofSupport.Lemmas

/-!
# SD instruction semantics

Run lemmas for the Jolt ISA `SD` instruction.
-/

open Sail PreSail LeanRV64D.Functions
open virtaddr MemoryAccessType mem_payload

set_option autoImplicit true

noncomputable section

namespace JoltISA

/-- Successful `SD`: if Sail's dword write pipeline returns success, then the
Jolt-ISA `SD` retires with the produced Sail state and preserves virtual
registers. -/
theorem execInstr_sd_vreg_run_of_write (base value : VReg) (imm : BitVec 12)
    (js : SailJoltState) (s' : SailState)
    (h_align :
      (js.vregs base + sign_extend (m := 64) imm) &&& (7 : BitVec 64) = 0)
    (h :
      vmem_write_addr (Virtaddr (js.vregs base + sign_extend (m := 64) imm)) 8
        (js.vregs value) (Store Data) false false false js.sail =
        .ok (Ok true) s') :
    (execInstr (.SD (.vreg base) (.vreg value) imm)).run js =
      .ok RETIRE_SUCCESS { sail := s', vregs := js.vregs } := by
  unfold execInstr readSrc readVReg liftSail
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get]
  rw [if_pos h_align]
  simp [EStateM.bind, h]
  rfl

/-- Successful `SD` from architectural-register base and value sources. -/
theorem execInstr_sd_xreg_xreg_run_of_write
    (base value : regidx) (imm : BitVec 12)
    (js : SailJoltState) (baseValue stored : BitVec 64) (s' : SailState)
    (hbase : rX_bits base js.sail = .ok baseValue js.sail)
    (hvalue : rX_bits value js.sail = .ok stored js.sail)
    (h_align :
      (baseValue + sign_extend (m := 64) imm) &&& (7 : BitVec 64) = 0)
    (hwrite :
      vmem_write_addr (Virtaddr (baseValue + sign_extend (m := 64) imm)) 8
        stored (Store Data) false false false js.sail =
        .ok (Ok true) s') :
    (execInstr (.SD (.xreg base) (.xreg value) imm)).run js =
      .ok RETIRE_SUCCESS { sail := s', vregs := js.vregs } := by
  unfold execInstr readSrc liftSail
  simp only [bind, EStateM.bind, pure, EStateM.run]
  rw [hbase]
  dsimp only
  rw [hvalue]
  dsimp only
  rw [if_pos h_align]
  simp [EStateM.bind, hwrite]
  rfl

end JoltISA

end
