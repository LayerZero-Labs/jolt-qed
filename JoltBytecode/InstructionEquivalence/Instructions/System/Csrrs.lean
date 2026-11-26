import JoltBytecode.Bundles
import JoltBytecode.InstructionEquivalence.Instructions.System.CsrReg

open LeanRV64D

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail LeanRV64D LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace System

/-! ## Main theorem -/

def csrrsProgramEqSailStatement
    (js : SailJoltState) (csr : JoltISA.SystemCSR) (rs1 rd : regidx)
    (_h_sys : CsrrsSystemAssumptions js csr rs1 rd) : Prop :=
  systemProjectResult
      ((JoltISA.execProgram (JoltISA.csrrsProgramAuto csr rd rs1)).run js) =
    (execute_CSRReg (JoltISA.SystemCSR.address csr) rs1 rd csrop.CSRRS).run
      (systemProject js)

theorem csrrsProgram_eq_sail_projected
    (js : SailJoltState) (csr : JoltISA.SystemCSR) (rs1 rd : regidx)
    (h_sys : CsrrsSystemAssumptions js csr rs1 rd) :
    csrrsProgramEqSailStatement js csr rs1 rd h_sys := by
  unfold csrrsProgramEqSailStatement
  obtain ⟨hpriv, halign⟩ :=
    SystemProofs.csr_bundle_facts js csr h_sys.cur_privilege_machine h_sys.mepc_read_aligned
  rw [JoltISA.csrrsProgramAuto_eq]
  exact SystemProofs.csrBitUpdateProgram_eq_execute false csr rs1 rd js h_sys.rs1_val hpriv
    halign h_sys.linked_csrs h_sys.rs1_read h_sys.mstatus_legal.mstatus_bits h_sys.mtvec_legal.mtvec_mode
    h_sys.mepc_legal.mepc_align

end System

end
