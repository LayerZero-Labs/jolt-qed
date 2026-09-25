import JoltBytecode.InstructionEquivalence.ProofSupport.Lemmas

/-!
# ANDI instruction semantics

Run lemmas for the Jolt ISA `ANDI` instruction.
-/

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace JoltISA

/-- `ANDI` on virtual registers reads the virtual source, writes the masked
value to the virtual destination, and leaves the Sail state unchanged. -/
theorem andi_run_vreg_vreg (vd vs : VReg) (imm : BitVec 12)
    (js : SailJoltState) (hvd : WritableVReg vd) :
    (execInstr (JoltISA.Encoded.ANDI (.vreg vd) (.vreg vs) imm)).run js =
      .ok RETIRE_SUCCESS
        { js with
          vregs := fun r => if r = vd then js.vregs vs &&& sign_extend (m := 64) imm else js.vregs r } := by
  unfold execInstr readSrc writeDst readVReg
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get]
  exact writeVReg_retire_run_of_writable vd
    (js.vregs vs &&& sign_extend (m := 64) imm) js hvd

/-- `ANDI` from a virtual source to a virtual destination, packaged as an
instruction step from a known virtual-source value. -/
theorem exists_state_after_andi_run_vreg_vreg
    (vd vs : VReg) (imm : BitVec 12) (js : SailJoltState) (x : BitVec 64)
    (hvd : WritableVReg vd)
    (h_value : js.vregs vs = x) :
    ∃ js',
      js'.sail = js.sail ∧
      js'.vregs vd = x &&& sign_extend (m := 64) imm ∧
      (∀ r, r ≠ vd → js'.vregs r = js.vregs r) ∧
      (execInstr (JoltISA.Encoded.ANDI (.vreg vd) (.vreg vs) imm)).run js =
        .ok RETIRE_SUCCESS js' := by
  let js' : SailJoltState :=
    { js with
      vregs := fun r => if r = vd then js.vregs vs &&& sign_extend (m := 64) imm
        else js.vregs r }
  refine ⟨js', rfl, ?_, ?_, ?_⟩
  · simp [js', h_value]
  · intro r hne
    simp [js', hne]
  · simpa only [js'] using andi_run_vreg_vreg vd vs imm js hvd

/-- `ANDI` from a real source to a virtual destination masks the source value
and leaves Sail unchanged. -/
theorem andi_run_vreg_xreg (vd : VReg) (rs : regidx) (imm : BitVec 12)
    (js : SailJoltState) (x : BitVec 64)
    (h : rX_bits rs js.sail = .ok x js.sail)
    (hvd : WritableVReg vd) :
    (execInstr (JoltISA.Encoded.ANDI (.vreg vd) (.xreg rs) imm)).run js =
      .ok RETIRE_SUCCESS
        { js with
          vregs := fun r => if r = vd then x &&& sign_extend (m := 64) imm else js.vregs r } := by
  unfold execInstr readSrc writeDst liftSail
  simp only [h, bind, EStateM.bind, EStateM.run]
  exact writeVReg_retire_run_of_writable vd
    (x &&& sign_extend (m := 64) imm) js hvd

/-- `ANDI` from a real source to a virtual destination, packaged as an
instruction step. The source read may be supplied from a known unchanged Sail
state, which is the common shape after earlier virtual-register writes. -/
theorem exists_state_after_andi_run_vreg_xreg_of_sail_eq
    (vd : VReg) (rs : regidx) (imm : BitVec 12)
    (js : SailJoltState) (s : SailState) (x : BitVec 64)
    (h_sail : js.sail = s)
    (h_read : rX_bits rs s = .ok x s)
    (hvd : WritableVReg vd) :
    ∃ js',
      rX_bits rs js.sail = .ok x js.sail ∧
      js'.sail = js.sail ∧
      js'.vregs vd = x &&& sign_extend (m := 64) imm ∧
      (∀ r, r ≠ vd → js'.vregs r = js.vregs r) ∧
      (execInstr (JoltISA.Encoded.ANDI (.vreg vd) (.xreg rs) imm)).run js =
        .ok RETIRE_SUCCESS js' := by
  have h_read_current : rX_bits rs js.sail = .ok x js.sail := by
    simpa only [h_sail] using h_read
  let js' : SailJoltState :=
    { js with
      vregs := fun r =>
        if r = vd then x &&& sign_extend (m := 64) imm else js.vregs r }
  refine ⟨js', h_read_current, rfl, ?_, ?_, ?_⟩
  · simp [js']
  · intro r hne
    simp [js', hne]
  · simpa only [js'] using andi_run_vreg_xreg vd rs imm js x h_read_current hvd


end JoltISA

end
