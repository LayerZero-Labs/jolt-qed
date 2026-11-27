import JoltBytecode.Bundles
import JoltBytecode.InstructionEquivalence.Instructions.System.CsrReg

open LeanRV64D

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail LeanRV64D LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace System

/-! ## Main theorems

CSRRWI, CSRRSI and CSRRCI use the hand-written programs in
`JoltISA/ExpansionsHandwritten.lean`, which the generator cannot yet translate.
-/

def csrrwiProgramEqSailStatement
    (js : SailJoltState) (csr : JoltISA.SystemCSR) (uimm : BitVec 5) (rd : regidx)
    (_h_sys : CsrImmSystemAssumptions js csr) : Prop :=
  systemProjectResult
      ((JoltISA.execProgram (JoltISA.csrrwiProgram csr uimm rd)).run js) =
    (execute_CSRImm (JoltISA.SystemCSR.address csr) uimm rd csrop.CSRRW).run
      (systemProject js)

theorem csrrwiProgram_eq_sail_projected
    (js : SailJoltState) (csr : JoltISA.SystemCSR) (uimm : BitVec 5) (rd : regidx)
    (h_sys : CsrImmSystemAssumptions js csr) :
    csrrwiProgramEqSailStatement js csr uimm rd h_sys := by
  unfold csrrwiProgramEqSailStatement
  obtain ⟨hpriv, halign⟩ :=
    SystemProofs.csr_bundle_facts js csr h_sys.cur_privilege_machine h_sys.mepc_read_aligned
  exact SystemProofs.csrrwiProgram_eq_execute csr uimm rd js hpriv halign
    h_sys.mstatus_legal.mstatus_bits h_sys.mtvec_legal.mtvec_mode h_sys.mepc_legal.mepc_align

def csrrsiProgramEqSailStatement
    (js : SailJoltState) (csr : JoltISA.SystemCSR) (uimm : BitVec 5) (rd : regidx)
    (_h_sys : CsrImmSystemAssumptions js csr) : Prop :=
  systemProjectResult
      ((JoltISA.execProgram (JoltISA.csrrsiProgram csr uimm rd)).run js) =
    (execute_CSRImm (JoltISA.SystemCSR.address csr) uimm rd csrop.CSRRS).run
      (systemProject js)

theorem csrrsiProgram_eq_sail_projected
    (js : SailJoltState) (csr : JoltISA.SystemCSR) (uimm : BitVec 5) (rd : regidx)
    (h_sys : CsrImmSystemAssumptions js csr) :
    csrrsiProgramEqSailStatement js csr uimm rd h_sys := by
  unfold csrrsiProgramEqSailStatement JoltISA.csrrsiProgram
  obtain ⟨hpriv, halign⟩ :=
    SystemProofs.csr_bundle_facts js csr h_sys.cur_privilege_machine h_sys.mepc_read_aligned
  exact SystemProofs.csrImmediateBitUpdateProgram_eq_execute false csr uimm rd js hpriv halign
    h_sys.mstatus_legal.mstatus_bits h_sys.mtvec_legal.mtvec_mode h_sys.mepc_legal.mepc_align

def csrrciProgramEqSailStatement
    (js : SailJoltState) (csr : JoltISA.SystemCSR) (uimm : BitVec 5) (rd : regidx)
    (_h_sys : CsrImmSystemAssumptions js csr) : Prop :=
  systemProjectResult
      ((JoltISA.execProgram (JoltISA.csrrciProgram csr uimm rd)).run js) =
    (execute_CSRImm (JoltISA.SystemCSR.address csr) uimm rd csrop.CSRRC).run
      (systemProject js)

theorem csrrciProgram_eq_sail_projected
    (js : SailJoltState) (csr : JoltISA.SystemCSR) (uimm : BitVec 5) (rd : regidx)
    (h_sys : CsrImmSystemAssumptions js csr) :
    csrrciProgramEqSailStatement js csr uimm rd h_sys := by
  unfold csrrciProgramEqSailStatement JoltISA.csrrciProgram
  obtain ⟨hpriv, halign⟩ :=
    SystemProofs.csr_bundle_facts js csr h_sys.cur_privilege_machine h_sys.mepc_read_aligned
  exact SystemProofs.csrImmediateBitUpdateProgram_eq_execute true csr uimm rd js hpriv halign
    h_sys.mstatus_legal.mstatus_bits h_sys.mtvec_legal.mtvec_mode h_sys.mepc_legal.mepc_align

end System

end
