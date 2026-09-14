import JoltBytecode.InstructionEquivalence.ProofSupport.Lemmas
import JoltBytecode.InstructionEquivalence.ProofSupport.RegisterAccess

/-!
# VirtualSRLI instruction semantics

Run lemmas for the Jolt ISA `VirtualSRLI` instruction.
-/

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace JoltISA

/-- `VirtualSRLI` from a real source to a real destination writes the logical
right shift selected by the encoded immediate bitmask. -/
theorem virtual_srli_run_xreg_xreg (rd rs : regidx)
    (bitmask : Nat) (js : SailJoltState) (x : BitVec 64) (s' : SailState)
    (h : rX_bits rs js.sail = .ok x js.sail)
    (hw : wX_bits rd (jolt_virtual_srli_value x bitmask) js.sail = .ok () s') :
    (execInstr (.VirtualSRLI (.xreg rd) (.xreg rs) bitmask)).run js =
      .ok RETIRE_SUCCESS { sail := s', vregs := js.vregs } := by
  unfold execInstr readSrc writeDst liftSail
  simp only [h, hw, bind, EStateM.bind, pure, EStateM.pure, EStateM.run]

/-- `VirtualSRLI` from a real source to a real destination, with the output
state chosen by the instruction lemma. -/
theorem exists_sail_state_after_virtual_srli_run_xreg_xreg (rd rs : regidx)
    (bitmask : Nat) (js : SailJoltState) (x : BitVec 64)
    (h : rX_bits rs js.sail = .ok x js.sail) :
    ∃ s',
      (execInstr (.VirtualSRLI (.xreg rd) (.xreg rs) bitmask)).run js =
        .ok RETIRE_SUCCESS { sail := s', vregs := js.vregs } ∧
      wX_bits rd (jolt_virtual_srli_value x bitmask) js.sail = .ok () s' := by
  obtain ⟨s', hw⟩ := wX_shape rd (jolt_virtual_srli_value x bitmask) js.sail
  exact ⟨s', virtual_srli_run_xreg_xreg rd rs bitmask js x s' h hw, hw⟩

/-- `VirtualSRLI` from a real source to a real destination, exposing the full
checkpoint state produced by the architectural write. -/
theorem exists_state_after_virtual_srli_run_xreg_xreg (rd rs : regidx)
    (bitmask : Nat) (js : SailJoltState) (x : BitVec 64)
    (h : rX_bits rs js.sail = .ok x js.sail) :
    ∃ js',
      rX_bits rs js.sail = .ok x js.sail ∧
      js'.sail = stateAfterWrite js.sail rd (jolt_virtual_srli_value x bitmask) ∧
      (execInstr (.VirtualSRLI (.xreg rd) (.xreg rs) bitmask)).run js =
        .ok RETIRE_SUCCESS js' := by
  obtain ⟨s', h_run, h_write⟩ :=
    exists_sail_state_after_virtual_srli_run_xreg_xreg rd rs bitmask js x h
  have h_sail_after_srli :
      s' = stateAfterWrite js.sail rd (jolt_virtual_srli_value x bitmask) :=
    wX_bits_eq_stateAfterWrite rd (jolt_virtual_srli_value x bitmask) js.sail s' h_write
  exact ⟨{ sail := s', vregs := js.vregs }, h, h_sail_after_srli, h_run⟩

/-- `VirtualSRLI` can consume a value from a virtual register and write the
logical shift result to a real destination. -/
theorem virtual_srli_run_xreg_vreg (rd : regidx) (vs : VReg)
    (bitmask : Nat) (js : SailJoltState) (s' : SailState)
    (hw : wX_bits rd (jolt_virtual_srli_value (js.vregs vs) bitmask) js.sail = .ok () s') :
    (execInstr (.VirtualSRLI (.xreg rd) (.vreg vs) bitmask)).run js =
      .ok RETIRE_SUCCESS { sail := s', vregs := js.vregs } := by
  unfold execInstr readSrc writeDst readVReg liftSail
  simp only [hw, bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get]

/-- `VirtualSRLI` from a virtual source to a real destination, with the output
state chosen by the instruction lemma. -/
theorem exists_sail_state_after_virtual_srli_run_xreg_vreg (rd : regidx) (vs : VReg)
    (bitmask : Nat) (js : SailJoltState) :
    ∃ s',
      (execInstr (.VirtualSRLI (.xreg rd) (.vreg vs) bitmask)).run js =
        .ok RETIRE_SUCCESS { sail := s', vregs := js.vregs } ∧
      wX_bits rd (jolt_virtual_srli_value (js.vregs vs) bitmask) js.sail = .ok () s' := by
  obtain ⟨s', hw⟩ := wX_shape rd (jolt_virtual_srli_value (js.vregs vs) bitmask) js.sail
  exact ⟨s', virtual_srli_run_xreg_vreg rd vs bitmask js s' hw, hw⟩

/-- `VirtualSRLI` from a virtual source to a real destination, exposing the
full checkpoint state produced by the architectural write. -/
theorem exists_state_after_virtual_srli_run_xreg_vreg (rd : regidx) (vs : VReg)
    (bitmask : Nat) (js : SailJoltState) :
    ∃ js',
      js'.sail = stateAfterWrite js.sail rd (jolt_virtual_srli_value (js.vregs vs) bitmask) ∧
      (execInstr (.VirtualSRLI (.xreg rd) (.vreg vs) bitmask)).run js =
        .ok RETIRE_SUCCESS js' := by
  obtain ⟨s', h_run, h_write⟩ :=
    exists_sail_state_after_virtual_srli_run_xreg_vreg rd vs bitmask js
  have h_sail_after_srli :
      s' = stateAfterWrite js.sail rd (jolt_virtual_srli_value (js.vregs vs) bitmask) :=
    wX_bits_eq_stateAfterWrite rd (jolt_virtual_srli_value (js.vregs vs) bitmask)
      js.sail s' h_write
  exact ⟨{ sail := s', vregs := js.vregs }, h_sail_after_srli, h_run⟩

/-- `VirtualSRLI` from a virtual source to a real destination, packaged from
the known virtual-register value and base Sail state. -/
theorem exists_state_after_virtual_srli_run_xreg_vreg_of_value
    (rd : regidx) (vs : VReg) (bitmask : Nat) (js : SailJoltState)
    (s : SailState) (x : BitVec 64)
    (h_sail : js.sail = s)
    (h_value : js.vregs vs = x) :
    ∃ js',
      js'.sail = stateAfterWrite s rd (jolt_virtual_srli_value x bitmask) ∧
      (execInstr (.VirtualSRLI (.xreg rd) (.vreg vs) bitmask)).run js =
        .ok RETIRE_SUCCESS js' := by
  obtain ⟨js', h_sail_after_srli, h_srli_succeeds⟩ :=
    exists_state_after_virtual_srli_run_xreg_vreg rd vs bitmask js
  refine ⟨js', ?_, h_srli_succeeds⟩
  rw [h_sail_after_srli, h_sail, h_value]

/-- `VirtualSRLI` from a virtual source to a virtual destination writes the
logical right shift selected by the encoded bitmask and leaves Sail unchanged. -/
theorem virtual_srli_run_vreg_vreg (vd vs : VReg)
    (bitmask : Nat) (js : SailJoltState) (hvd : WritableVReg vd) :
    (execInstr (.VirtualSRLI (.vreg vd) (.vreg vs) bitmask)).run js =
      .ok RETIRE_SUCCESS
        { sail := js.sail
          vregs := fun r =>
            if r = vd then jolt_virtual_srli_value (js.vregs vs) bitmask else js.vregs r } := by
  unfold execInstr readSrc writeDst readVReg
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get]
  exact writeVReg_retire_run_of_writable vd
    (jolt_virtual_srli_value (js.vregs vs) bitmask) js hvd

end JoltISA

end
