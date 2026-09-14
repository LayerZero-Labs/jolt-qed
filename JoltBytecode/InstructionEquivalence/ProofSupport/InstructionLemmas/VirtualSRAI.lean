import JoltBytecode.InstructionEquivalence.ProofSupport.Lemmas
import JoltBytecode.InstructionEquivalence.ProofSupport.RegisterAccess

/-!
# VirtualSRAI instruction semantics

Run lemmas for the Jolt ISA `VirtualSRAI` instruction.
-/

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace JoltISA

/-- `VirtualSRAI` from a real source to a real destination writes the arithmetic
right shift selected by the encoded immediate bitmask. -/
theorem virtual_srai_run_xreg_xreg (rd rs : regidx)
    (bitmask : Nat) (js : SailJoltState) (x : BitVec 64) (s' : SailState)
    (h : rX_bits rs js.sail = .ok x js.sail)
    (hw : wX_bits rd (jolt_virtual_srai_value x bitmask) js.sail = .ok () s') :
    (execInstr (.VirtualSRAI (.xreg rd) (.xreg rs) bitmask)).run js =
      .ok RETIRE_SUCCESS { sail := s', vregs := js.vregs } := by
  unfold execInstr readSrc writeDst liftSail
  simp only [h, hw, bind, EStateM.bind, pure, EStateM.pure, EStateM.run]

/-- `VirtualSRAI` from a real source to a real destination, with the output
state chosen by the instruction lemma. -/
theorem exists_sail_state_after_virtual_srai_run_xreg_xreg (rd rs : regidx)
    (bitmask : Nat) (js : SailJoltState) (x : BitVec 64)
    (h : rX_bits rs js.sail = .ok x js.sail) :
    ∃ s',
      (execInstr (.VirtualSRAI (.xreg rd) (.xreg rs) bitmask)).run js =
        .ok RETIRE_SUCCESS { sail := s', vregs := js.vregs } ∧
      wX_bits rd (jolt_virtual_srai_value x bitmask) js.sail = .ok () s' := by
  obtain ⟨s', hw⟩ := wX_shape rd (jolt_virtual_srai_value x bitmask) js.sail
  exact ⟨s', virtual_srai_run_xreg_xreg rd rs bitmask js x s' h hw, hw⟩

/-- `VirtualSRAI` from a real source to a real destination, exposing the full
checkpoint state produced by the architectural write. -/
theorem exists_state_after_virtual_srai_run_xreg_xreg (rd rs : regidx)
    (bitmask : Nat) (js : SailJoltState) (x : BitVec 64)
    (h : rX_bits rs js.sail = .ok x js.sail) :
    ∃ js',
      rX_bits rs js.sail = .ok x js.sail ∧
      js'.sail = stateAfterWrite js.sail rd (jolt_virtual_srai_value x bitmask) ∧
      (execInstr (.VirtualSRAI (.xreg rd) (.xreg rs) bitmask)).run js =
        .ok RETIRE_SUCCESS js' := by
  obtain ⟨s', h_run, h_write⟩ :=
    exists_sail_state_after_virtual_srai_run_xreg_xreg rd rs bitmask js x h
  have h_sail_after_srai :
      s' = stateAfterWrite js.sail rd (jolt_virtual_srai_value x bitmask) :=
    wX_bits_eq_stateAfterWrite rd (jolt_virtual_srai_value x bitmask) js.sail s' h_write
  exact ⟨{ sail := s', vregs := js.vregs }, h, h_sail_after_srai, h_run⟩

/-- `VirtualSRAI` can consume a value from a virtual register and write the
arithmetic shift result to a real destination. -/
theorem virtual_srai_run_xreg_vreg (rd : regidx) (vs : VReg)
    (bitmask : Nat) (js : SailJoltState) (s' : SailState)
    (hw : wX_bits rd (jolt_virtual_srai_value (js.vregs vs) bitmask) js.sail = .ok () s') :
    (execInstr (.VirtualSRAI (.xreg rd) (.vreg vs) bitmask)).run js =
      .ok RETIRE_SUCCESS { sail := s', vregs := js.vregs } := by
  unfold execInstr readSrc writeDst readVReg liftSail
  simp only [hw, bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get]

/-- `VirtualSRAI` from a virtual source to a real destination, with the output
state chosen by the instruction lemma. -/
theorem exists_sail_state_after_virtual_srai_run_xreg_vreg (rd : regidx) (vs : VReg)
    (bitmask : Nat) (js : SailJoltState) :
    ∃ s',
      (execInstr (.VirtualSRAI (.xreg rd) (.vreg vs) bitmask)).run js =
        .ok RETIRE_SUCCESS { sail := s', vregs := js.vregs } ∧
      wX_bits rd (jolt_virtual_srai_value (js.vregs vs) bitmask) js.sail = .ok () s' := by
  obtain ⟨s', hw⟩ := wX_shape rd (jolt_virtual_srai_value (js.vregs vs) bitmask) js.sail
  exact ⟨s', virtual_srai_run_xreg_vreg rd vs bitmask js s' hw, hw⟩

/-- `VirtualSRAI` from a virtual source to a real destination, exposing the
full checkpoint state produced by the architectural write. -/
theorem exists_state_after_virtual_srai_run_xreg_vreg (rd : regidx) (vs : VReg)
    (bitmask : Nat) (js : SailJoltState) :
    ∃ js',
      js'.sail = stateAfterWrite js.sail rd (jolt_virtual_srai_value (js.vregs vs) bitmask) ∧
      (execInstr (.VirtualSRAI (.xreg rd) (.vreg vs) bitmask)).run js =
        .ok RETIRE_SUCCESS js' := by
  obtain ⟨s', h_run, h_write⟩ :=
    exists_sail_state_after_virtual_srai_run_xreg_vreg rd vs bitmask js
  have h_sail_after_srai :
      s' = stateAfterWrite js.sail rd (jolt_virtual_srai_value (js.vregs vs) bitmask) :=
    wX_bits_eq_stateAfterWrite rd (jolt_virtual_srai_value (js.vregs vs) bitmask)
      js.sail s' h_write
  exact ⟨{ sail := s', vregs := js.vregs }, h_sail_after_srai, h_run⟩

/-- `VirtualSRAI` from a virtual source to a real destination, packaged from
the known virtual-register value and base Sail state. -/
theorem exists_state_after_virtual_srai_run_xreg_vreg_of_value
    (rd : regidx) (vs : VReg) (bitmask : Nat) (js : SailJoltState)
    (s : SailState) (x : BitVec 64)
    (h_sail : js.sail = s)
    (h_value : js.vregs vs = x) :
    ∃ js',
      js'.sail = stateAfterWrite s rd (jolt_virtual_srai_value x bitmask) ∧
      (execInstr (.VirtualSRAI (.xreg rd) (.vreg vs) bitmask)).run js =
        .ok RETIRE_SUCCESS js' := by
  obtain ⟨js', h_sail_after_srai, h_srai_succeeds⟩ :=
    exists_state_after_virtual_srai_run_xreg_vreg rd vs bitmask js
  refine ⟨js', ?_, h_srai_succeeds⟩
  rw [h_sail_after_srai, h_sail, h_value]

end JoltISA

end
