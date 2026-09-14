import JoltBytecode.InstructionEquivalence.ProofSupport.Lemmas
import JoltBytecode.InstructionEquivalence.ProofSupport.RegisterAccess
import JoltBytecode.InstructionEquivalence.ProofSupport.StateLemmas

/-!
# MUL instruction semantics

Run lemmas for the Jolt ISA `MUL` instruction.
-/

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace JoltISA

/-- `MUL` on virtual registers writes the low 64 bits of the product. -/
theorem mul_run_vreg_vreg_vreg (vd lhs rhs : VReg) (js : SailJoltState)
    (hvd : WritableVReg vd) :
    (execInstr (.MUL (.vreg vd) (.vreg lhs) (.vreg rhs))).run js =
      .ok RETIRE_SUCCESS
        { sail := js.sail
          vregs := fun r => if r = vd then js.vregs lhs * js.vregs rhs
            else js.vregs r } := by
  unfold execInstr readSrc writeDst readVReg
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get]
  exact writeVReg_retire_run_of_writable vd (js.vregs lhs * js.vregs rhs) js hvd


/-- `MUL` from a virtual source and a real source to a virtual destination reads
the real source through Sail, writes the low product to the virtual destination,
and leaves the Sail state unchanged when the real read is state-preserving. -/
theorem mul_run_vreg_vreg_xreg (vd lhs : VReg) (rhs : regidx)
    (js : SailJoltState) (y : BitVec 64)
    (h : rX_bits rhs js.sail = .ok y js.sail)
    (hvd : WritableVReg vd) :
    (execInstr (.MUL (.vreg vd) (.vreg lhs) (.xreg rhs))).run js =
      .ok RETIRE_SUCCESS
        { sail := js.sail
          vregs := fun r => if r = vd then js.vregs lhs * y else js.vregs r } := by
  unfold execInstr readSrc writeDst readVReg liftSail
  simp only [h, bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get]
  exact writeVReg_retire_run_of_writable vd (js.vregs lhs * y) js hvd

/-- `MUL` from a real source and a virtual source to a virtual destination
reads the real source through Sail, writes the low product to the virtual
destination, and leaves Sail unchanged when the real read is state-preserving. -/
theorem mul_run_vreg_xreg_vreg (vd : VReg) (lhs : regidx) (rhs : VReg)
    (js : SailJoltState) (x : BitVec 64)
    (h : rX_bits lhs js.sail = .ok x js.sail)
    (hvd : WritableVReg vd) :
    (execInstr (.MUL (.vreg vd) (.xreg lhs) (.vreg rhs))).run js =
      .ok RETIRE_SUCCESS
        { sail := js.sail
          vregs := fun r => if r = vd then x * js.vregs rhs else js.vregs r } := by
  unfold execInstr readSrc writeDst readVReg liftSail
  simp only [h, bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get]
  exact writeVReg_retire_run_of_writable vd (x * js.vregs rhs) js hvd

/-- `MUL` from a virtual source and a real source to a virtual destination,
packaged from a known virtual-source value and a known base Sail state. -/
theorem exists_state_after_mul_run_vreg_vreg_xreg
    (vd lhs : VReg) (rhs : regidx) (js : SailJoltState)
    (s : SailState) (x y : BitVec 64)
    (h_sail : js.sail = s)
    (h_lhs : js.vregs lhs = x)
    (h_read : rX_bits rhs s = .ok y s)
    (hvd : WritableVReg vd) :
    ∃ js',
      rX_bits rhs js.sail = .ok y js.sail ∧
      js'.sail = s ∧
      js'.vregs vd = x * y ∧
      (∀ r, r ≠ vd → js'.vregs r = js.vregs r) ∧
      (execInstr (.MUL (.vreg vd) (.vreg lhs) (.xreg rhs))).run js =
        .ok RETIRE_SUCCESS js' := by
  have h_read_current : rX_bits rhs js.sail = .ok y js.sail := by
    simpa only [h_sail] using h_read
  let js' : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = vd then js.vregs lhs * y else js.vregs r }
  refine ⟨js', h_read_current, ?_, ?_, ?_, ?_⟩
  · exact h_sail
  · simp [js', h_lhs]
  · intro r hne
    simp [js', hne]
  · simpa only [js'] using mul_run_vreg_vreg_xreg vd lhs rhs js y h_read_current hvd

/-- `MUL` from a real source and a virtual source to a real destination
consumes a scratch virtual register and writes the product through Sail. -/
theorem mul_run_xreg_xreg_vreg (rd rs1 : regidx) (vs2 : VReg)
    (js : SailJoltState) (x : BitVec 64) (s' : SailState)
    (h : rX_bits rs1 js.sail = .ok x js.sail)
    (hw : wX_bits rd (x * js.vregs vs2) js.sail = .ok () s') :
    (execInstr (.MUL (.xreg rd) (.xreg rs1) (.vreg vs2))).run js =
      .ok RETIRE_SUCCESS { sail := s', vregs := js.vregs } := by
  unfold execInstr readSrc writeDst readVReg liftSail
  simp only [h, hw, bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get]

/-- `MUL` from a real source and a virtual source to a real destination, with
the output state chosen by the instruction lemma. -/
theorem exists_sail_state_after_mul_run_xreg_xreg_vreg (rd rs1 : regidx) (vs2 : VReg)
    (js : SailJoltState) (x : BitVec 64)
    (h : rX_bits rs1 js.sail = .ok x js.sail) :
    ∃ s',
      (execInstr (.MUL (.xreg rd) (.xreg rs1) (.vreg vs2))).run js =
        .ok RETIRE_SUCCESS { sail := s', vregs := js.vregs } ∧
      wX_bits rd (x * js.vregs vs2) js.sail = .ok () s' := by
  obtain ⟨s', hw⟩ := wX_shape rd (x * js.vregs vs2) js.sail
  exact ⟨s', mul_run_xreg_xreg_vreg rd rs1 vs2 js x s' h hw, hw⟩

/-- `MUL` from a real source and a virtual source to a real destination, with
the output Sail state exposed as the architectural write performed by the
instruction. -/
theorem exists_state_after_mul_run_xreg_xreg_vreg (rd rs1 : regidx) (vs2 : VReg)
    (js : SailJoltState) (x : BitVec 64)
    (h : rX_bits rs1 js.sail = .ok x js.sail) :
    ∃ js',
      rX_bits rs1 js.sail = .ok x js.sail ∧
      js'.sail = stateAfterWrite js.sail rd (x * js.vregs vs2) ∧
      (execInstr (.MUL (.xreg rd) (.xreg rs1) (.vreg vs2))).run js =
        .ok RETIRE_SUCCESS js' := by
  obtain ⟨s', h_run, h_write⟩ :=
    exists_sail_state_after_mul_run_xreg_xreg_vreg rd rs1 vs2 js x h
  have h_sail_after_mul :
      s' = stateAfterWrite js.sail rd (x * js.vregs vs2) :=
    wX_bits_eq_stateAfterWrite rd (x * js.vregs vs2) js.sail s' h_write
  exact ⟨{ sail := s', vregs := js.vregs }, h, h_sail_after_mul, h_run⟩

/-- `MUL` from a real source and a virtual source to a real destination,
packaged from the known virtual-register value and base Sail state. -/
theorem exists_state_after_mul_run_xreg_xreg_vreg_of_value
    (rd rs1 : regidx) (vs2 : VReg) (js : SailJoltState)
    (s : SailState) (x y : BitVec 64)
    (h_sail : js.sail = s)
    (h_read : rX_bits rs1 s = .ok x s)
    (h_value : js.vregs vs2 = y) :
    ∃ js',
      rX_bits rs1 js.sail = .ok x js.sail ∧
      js'.sail = stateAfterWrite s rd (x * y) ∧
      (execInstr (.MUL (.xreg rd) (.xreg rs1) (.vreg vs2))).run js =
        .ok RETIRE_SUCCESS js' := by
  have h_read_current : rX_bits rs1 js.sail = .ok x js.sail := by
    simpa only [h_sail] using h_read
  obtain ⟨js', h_read_again, h_sail_after_mul, h_mul_succeeds⟩ :=
    exists_state_after_mul_run_xreg_xreg_vreg rd rs1 vs2 js x h_read_current
  refine ⟨js', h_read_again, ?_, h_mul_succeeds⟩
  rw [h_sail_after_mul, h_sail, h_value]

/-- Existential single-write post-state for `MUL` on virtual registers. -/
theorem mul_run_vreg_vreg_vreg_ex (vd vs1 vs2 : VReg) (js : SailJoltState)
    (hvd : WritableVReg vd) :
    ∃ js',
      (execInstr (.MUL (.vreg vd) (.vreg vs1) (.vreg vs2))).run js =
        .ok RETIRE_SUCCESS js' ∧
      js'.vregs vd = js.vregs vs1 * js.vregs vs2 ∧
      (∀ k, k ≠ vd → js'.vregs k = js.vregs k) ∧
      js'.sail = js.sail :=
  writeSingleVReg_ex (mul_run_vreg_vreg_vreg vd vs1 vs2 js hvd)

end JoltISA

end
