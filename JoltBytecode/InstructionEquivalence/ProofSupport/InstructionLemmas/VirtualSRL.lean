import JoltBytecode.InstructionEquivalence.ProofSupport.Lemmas
import JoltBytecode.InstructionEquivalence.ProofSupport.RegisterAccess

/-!
# VirtualSRL instruction semantics

Run lemmas for the Jolt ISA `VirtualSRL` instruction.
-/

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace JoltISA

/-- `VirtualSRL` from a real value and a virtual bitmask to a real destination
is the two-instruction `SRL` program's final write. -/
theorem virtual_srl_run_xreg_xreg_vreg (rd rs : regidx) (vbitmask : VReg)
    (js : SailJoltState) (x : BitVec 64) (s' : SailState)
    (h : rX_bits rs js.sail = .ok x js.sail)
    (hw : wX_bits rd (jolt_virtual_srl_value x (js.vregs vbitmask)) js.sail = .ok () s') :
    (execInstr (.VirtualSRL (.xreg rd) (.xreg rs) (.vreg vbitmask))).run js =
      .ok RETIRE_SUCCESS { js with sail := s' } := by
  unfold execInstr readSrc writeDst readVReg liftSail
  simp only [h, hw, bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get]

/-- `VirtualSRL` from a real value and a virtual bitmask to a real destination,
with the output state chosen by the instruction lemma. -/
theorem exists_sail_state_after_virtual_srl_run_xreg_xreg_vreg
    (rd rs : regidx) (vbitmask : VReg) (js : SailJoltState) (x : BitVec 64)
    (h : rX_bits rs js.sail = .ok x js.sail) :
    ∃ s',
      (execInstr (.VirtualSRL (.xreg rd) (.xreg rs) (.vreg vbitmask))).run js =
        .ok RETIRE_SUCCESS { js with sail := s' } ∧
      wX_bits rd (jolt_virtual_srl_value x (js.vregs vbitmask)) js.sail = .ok () s' := by
  obtain ⟨s', hw⟩ := wX_shape rd (jolt_virtual_srl_value x (js.vregs vbitmask)) js.sail
  exact ⟨s', virtual_srl_run_xreg_xreg_vreg rd rs vbitmask js x s' h hw, hw⟩

/-- `VirtualSRL` from a real source and a virtual bitmask to a real destination,
with the output Sail state exposed as the architectural write performed by the
instruction. -/
theorem exists_state_after_virtual_srl_run_xreg_xreg_vreg
    (rd rs : regidx) (vbitmask : VReg) (js : SailJoltState) (x : BitVec 64)
    (h : rX_bits rs js.sail = .ok x js.sail) :
    ∃ js',
      rX_bits rs js.sail = .ok x js.sail ∧
      js'.sail = stateAfterWrite js.sail rd (jolt_virtual_srl_value x (js.vregs vbitmask)) ∧
      (execInstr (.VirtualSRL (.xreg rd) (.xreg rs) (.vreg vbitmask))).run js =
        .ok RETIRE_SUCCESS js' := by
  obtain ⟨s', h_run, h_write⟩ :=
    exists_sail_state_after_virtual_srl_run_xreg_xreg_vreg rd rs vbitmask js x h
  have h_sail_after_srl :
      s' = stateAfterWrite js.sail rd (jolt_virtual_srl_value x (js.vregs vbitmask)) :=
    wX_bits_eq_stateAfterWrite rd (jolt_virtual_srl_value x (js.vregs vbitmask))
      js.sail s' h_write
  exact ⟨{ js with sail := s' }, h, h_sail_after_srl, h_run⟩

/-- `VirtualSRL` from a real source and a virtual bitmask to a real
destination, packaged from the known bitmask value and base Sail state. -/
theorem exists_state_after_virtual_srl_run_xreg_xreg_vreg_of_value
    (rd rs : regidx) (vbitmask : VReg) (js : SailJoltState)
    (s : SailState) (x bitmask : BitVec 64)
    (h_sail : js.sail = s)
    (h_read : rX_bits rs s = .ok x s)
    (h_bitmask : js.vregs vbitmask = bitmask) :
    ∃ js',
      rX_bits rs js.sail = .ok x js.sail ∧
      js'.sail = stateAfterWrite s rd (jolt_virtual_srl_value x bitmask) ∧
      (execInstr (.VirtualSRL (.xreg rd) (.xreg rs) (.vreg vbitmask))).run js =
        .ok RETIRE_SUCCESS js' := by
  have h_read_current : rX_bits rs js.sail = .ok x js.sail := by
    simpa only [h_sail] using h_read
  obtain ⟨js', h_read_again, h_sail_after_srl, h_srl_succeeds⟩ :=
    exists_state_after_virtual_srl_run_xreg_xreg_vreg rd rs vbitmask js x
      h_read_current
  refine ⟨js', h_read_again, ?_, h_srl_succeeds⟩
  rw [h_sail_after_srl, h_sail, h_bitmask]


/-- `VirtualSRL` from virtual value and bitmask sources to a virtual
destination writes the logical-right-shift result and leaves Sail unchanged. -/
theorem virtual_srl_run_vreg_vreg_vreg (vd vvalue vbitmask : VReg)
    (js : SailJoltState) (hvd : WritableVReg vd) :
    (execInstr (.VirtualSRL (.vreg vd) (.vreg vvalue) (.vreg vbitmask))).run js =
      .ok RETIRE_SUCCESS
        { js with
          vregs := fun r =>
            if r = vd then jolt_virtual_srl_value (js.vregs vvalue) (js.vregs vbitmask)
            else js.vregs r } := by
  unfold execInstr readSrc writeDst readVReg
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get]
  exact writeVReg_retire_run_of_writable vd
    (jolt_virtual_srl_value (js.vregs vvalue) (js.vregs vbitmask)) js hvd

end JoltISA

end
