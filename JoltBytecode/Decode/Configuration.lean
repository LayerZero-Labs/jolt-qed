import JoltBytecode.Step.Instructions

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail
  LeanRV64D LeanRV64D.Functions

namespace Decode

/-- The value of misa after `sail_model_init` and `reset_misa`: RV64, I, M, A and C.
For example, bit 12 enables multiplication and division. Jolt never writes misa. -/
def resetMisa : BitVec 64 := 0x8000000000001105

/-- M and A are enabled when misa has its reset value.
Sail tests these bits in `currentlyEnabled` (`Types.lean`), for example before decoding DIV. -/
theorem enabledMA_reset (e : extension) (he : e = .Ext_M ∨ e = .Ext_A)
    (s : SailState) (hm : s.regs.get? Register.misa = some resetMisa) :
    currentlyEnabled e s = .ok true s := by
  have hr := readReg_eq_of_get? Register.misa s resetMisa hm
  rcases he with rfl | rfl <;> unfold currentlyEnabled <;>
    simp [hartSupports, andM, toBool, bind, EStateM.bind, pure, EStateM.pure, hr,
      resetMisa, _get_Misa_M, _get_Misa_A, Sail.BitVec.extractLsb]

/-- Zmmul and Zalrsc are enabled through M and A, respectively, at reset.
For example, the LR decoder tests Zalrsc although only the aggregate A extension is configured. -/
theorem enabledSub_reset (e : extension) (he : e = .Ext_Zmmul ∨ e = .Ext_Zalrsc)
    (s : SailState) (hm : s.regs.get? Register.misa = some resetMisa) :
    currentlyEnabled e s = .ok true s := by
  have hM := enabledMA_reset .Ext_M (Or.inl rfl) s hm
  have hA := enabledMA_reset .Ext_A (Or.inr rfl) s hm
  rcases he with rfl | rfl <;> unfold currentlyEnabled <;>
    simp [hartSupports, orM, toBool, bind, EStateM.bind, pure, EStateM.pure, hM, hA]

/-- AMOs are enabled through A at reset; for example, AMOADD tests Zaamo. -/
theorem enabledAMO_reset (s : SailState)
    (hm : s.regs.get? Register.misa = some resetMisa) :
    currentlyEnabled .Ext_Zaamo s = .ok true s := by
  have hA := enabledMA_reset .Ext_A (Or.inr rfl) s hm
  unfold currentlyEnabled
  simp [hartSupports, orM, toBool, bind, EStateM.bind, pure, EStateM.pure, hA]

/-- PAUSE hints are disabled by the fixed hart configuration; FENCE 0x0100000f stays FENCE. -/
theorem pause_disabled : currentlyEnabled .Ext_Zihintpause = pure false := by
  unfold currentlyEnabled
  simp only [hartSupports, pure]

/-- Landing-pad instructions are disabled; AUIPC words retain their ordinary decoding. -/
theorem landingPad_disabled : currentlyEnabled .Ext_Zicfilp = pure false := by
  funext s
  exact HartConfig.currentlyEnabled_Zicfilp_run s

/-- CSR decoding is always enabled, for example for CSRRW mstatus. -/
theorem csr_enabled : currentlyEnabled .Ext_Zicsr = pure true := by
  funext s
  exact HartConfig.currentlyEnabled_Zicsr_run s

end Decode
