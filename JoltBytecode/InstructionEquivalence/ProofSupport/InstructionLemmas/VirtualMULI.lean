import JoltBytecode.InstructionEquivalence.ProofSupport.Lemmas
import JoltBytecode.InstructionEquivalence.ProofSupport.RegisterAccess

/-!
# VirtualMULI instruction semantics

Run lemmas for the Jolt ISA `VirtualMULI` instruction.
-/

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace JoltISA

/-- `VirtualMULI` from a real source to a real destination multiplies the
source by the encoded immediate and writes the result through Sail. -/
theorem virtual_muli_run_xreg_xreg (rd rs1 : regidx)
    (imm : BitVec 64) (js : SailJoltState) (x : BitVec 64) (s' : SailState)
    (h : rX_bits rs1 js.sail = .ok x js.sail)
    (hw : wX_bits rd (jolt_virtual_muli_value x imm) js.sail = .ok () s') :
    (execInstr (.VirtualMULI (.xreg rd) (.xreg rs1) imm)).run js =
      .ok RETIRE_SUCCESS { sail := s', vregs := js.vregs } := by
  unfold execInstr readSrc writeDst liftSail
  simp only [h, hw, bind, EStateM.bind, pure, EStateM.pure, EStateM.run]

/-- `VirtualMULI` from a real source to a real destination, with the output
state chosen by the instruction lemma. -/
theorem exists_sail_state_after_virtual_muli_run_xreg_xreg (rd rs1 : regidx)
    (imm : BitVec 64) (js : SailJoltState) (x : BitVec 64)
    (h : rX_bits rs1 js.sail = .ok x js.sail) :
    ∃ s',
      (execInstr (.VirtualMULI (.xreg rd) (.xreg rs1) imm)).run js =
        .ok RETIRE_SUCCESS { sail := s', vregs := js.vregs } ∧
      wX_bits rd (jolt_virtual_muli_value x imm) js.sail = .ok () s' := by
  obtain ⟨s', hw⟩ := wX_shape rd (jolt_virtual_muli_value x imm) js.sail
  exact ⟨s', virtual_muli_run_xreg_xreg rd rs1 imm js x s' h hw, hw⟩

/-- `VirtualMULI` from a real source to a real destination, exposing the full
checkpoint state produced by the architectural write. -/
theorem exists_state_after_virtual_muli_run_xreg_xreg (rd rs1 : regidx)
    (imm : BitVec 64) (js : SailJoltState) (x : BitVec 64)
    (h : rX_bits rs1 js.sail = .ok x js.sail) :
    ∃ js',
      rX_bits rs1 js.sail = .ok x js.sail ∧
      js'.sail = stateAfterWrite js.sail rd (jolt_virtual_muli_value x imm) ∧
      (execInstr (.VirtualMULI (.xreg rd) (.xreg rs1) imm)).run js =
        .ok RETIRE_SUCCESS js' := by
  obtain ⟨s', h_run, h_write⟩ :=
    exists_sail_state_after_virtual_muli_run_xreg_xreg rd rs1 imm js x h
  have h_sail_after_muli :
      s' = stateAfterWrite js.sail rd (jolt_virtual_muli_value x imm) :=
    wX_bits_eq_stateAfterWrite rd (jolt_virtual_muli_value x imm) js.sail s' h_write
  exact ⟨{ sail := s', vregs := js.vregs }, h, h_sail_after_muli, h_run⟩

/-- `VirtualMULI` from a virtual source to a virtual destination writes the
wrapped product with the encoded immediate and leaves Sail unchanged. -/
theorem virtual_muli_run_vreg_vreg (vd vs : VReg)
    (imm : BitVec 64) (js : SailJoltState) (hvd : WritableVReg vd) :
    (execInstr (.VirtualMULI (.vreg vd) (.vreg vs) imm)).run js =
      .ok RETIRE_SUCCESS
        { sail := js.sail
          vregs := fun r =>
            if r = vd then jolt_virtual_muli_value (js.vregs vs) imm else js.vregs r } := by
  unfold execInstr readSrc writeDst readVReg
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get]
  exact writeVReg_retire_run_of_writable vd
    (jolt_virtual_muli_value (js.vregs vs) imm) js hvd

end JoltISA

end
