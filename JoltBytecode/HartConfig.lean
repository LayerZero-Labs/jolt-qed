import JoltBytecode.JoltISA.Core

/-!
# Facts fixed by the hart configuration

The Sail model is generated from `sail-import/rv64d_jolt.json`, which describes
Jolt's hart: RV64IMAC with Zca and Zicsr, M-mode only, no PMP entries (see
`docs/riscv-alignment.md`, sections 1 and 2). Several properties that earlier
versions of the instruction theorems took as hypotheses on the Sail state are
consequences of that configuration and hold in every state. This file proves
them.
-/

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail LeanRV64D LeanRV64D.Functions

namespace HartConfig

/-- The hart has no U-mode. -/
theorem hartSupports_U : hartSupports extension.Ext_U = false := by
  simp [hartSupports]

/-- The hart has no S-mode. -/
theorem hartSupports_S : hartSupports extension.Ext_S = false := by
  simp [hartSupports]

/-- The hart has no Zicfilp. -/
theorem hartSupports_Zicfilp : hartSupports extension.Ext_Zicfilp = false := by
  simp [hartSupports]

/-- The hart has Zicsr. -/
theorem hartSupports_Zicsr : hartSupports extension.Ext_Zicsr = true := by
  simp [hartSupports]

/-- Zicsr is always enabled. -/
theorem currentlyEnabled_Zicsr_run (s : SailState) :
    currentlyEnabled extension.Ext_Zicsr s = .ok true s := by
  unfold currentlyEnabled
  simp only [hartSupports_Zicsr, pure, EStateM.pure]

/-- U-mode is never enabled, whatever `misa` holds. -/
theorem currentlyEnabled_U_run (s : SailState) :
    currentlyEnabled extension.Ext_U s = .ok false s := by
  unfold currentlyEnabled
  simp only [hartSupports_U, andM, toBool, bind, EStateM.bind, pure, EStateM.pure]

/-- S-mode is never enabled, whatever `misa` holds. -/
theorem currentlyEnabled_S_run (s : SailState) :
    currentlyEnabled extension.Ext_S s = .ok false s := by
  unfold currentlyEnabled
  simp only [hartSupports_S, andM, toBool, bind, EStateM.bind, pure, EStateM.pure]

/-- The Zicfilp landing-pad extension is never enabled. -/
theorem currentlyEnabled_Zicfilp_run (s : SailState) :
    currentlyEnabled extension.Ext_Zicfilp s = .ok false s := by
  unfold currentlyEnabled
  simp only [hartSupports_Zicfilp, currentlyEnabled_Zicsr_run, andM, toBool, bind, EStateM.bind,
    pure, EStateM.pure]

/-- The lowest supported privilege level is M. -/
theorem lowest_supported_privLevel_run (s : SailState) :
    lowest_supported_privLevel () s = .ok Privilege.Machine s := by
  unfold lowest_supported_privLevel
  simp only [bind, EStateM.bind, currentlyEnabled_U_run]
  rfl

/-- The hart has no PMP entries, so the PMP check never faults. -/
theorem pmpCheck_run (addr : physaddr) (width : Nat)
    (access : MemoryAccessType mem_payload) (priv : Privilege) (s : SailState) :
    pmpCheck addr width access priv s = .ok none s := by
  unfold pmpCheck
  rfl

end HartConfig
