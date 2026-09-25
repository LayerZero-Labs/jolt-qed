import JoltBytecode.InstructionEquivalence.ProofSupport.Lemmas
import JoltBytecode.InstructionEquivalence.ProofSupport.RegisterAccess

/-!
# VirtualSignExtendWord instruction semantics

Run lemmas for the Jolt ISA `VirtualSignExtendWord` instruction.
-/

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace JoltISA

-- execInstr now calls the shared pure value. Relate it to the unchanged Sail
-- expression in the existing run lemmas; their statements and assumptions stay
-- the same.
private theorem shared_sign_extend_word_eq_sail (x : BitVec 64) :
    jolt_virtual_sign_extend_word_value x =
      sign_extend (m := 64) (Sail.BitVec.extractLsb x 31 0) := by
  unfold jolt_virtual_sign_extend_word_value sign_extend Sail.BitVec.signExtend
  congr 1

def jolt_virtual_sign_extend_word (rd : regidx) : JoltMonad Unit := do
  let v ← liftSail (rX_bits rd)
  liftSail (wX_bits rd (sign_extend (m := 64) (Sail.BitVec.extractLsb v 31 0)))


/-- `VirtualSignExtendWord` from a real source to a virtual destination computes
the word-sign-extended scratch value used by word operations. -/
theorem virtual_sign_extend_word_run_vreg_xreg (vd : VReg) (rs : regidx)
    (js : SailJoltState) (x : BitVec 64)
    (h : rX_bits rs js.sail = .ok x js.sail)
    (hvd : WritableVReg vd) :
    (execInstr (.VirtualSignExtendWord (.vreg vd) (.xreg rs))).run js =
      .ok RETIRE_SUCCESS
        { js with
          vregs := fun r =>
            if r = vd then sign_extend (m := 64) (Sail.BitVec.extractLsb x 31 0)
            else js.vregs r } := by
  unfold WritableVReg at hvd
  unfold execInstr readSrc writeDst liftSail writeVReg
  simp only [shared_sign_extend_word_eq_sail]
  simp only [h, bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    hvd, ↓reduceIte, modify, modifyGet, MonadStateOf.modifyGet,
    EStateM.modifyGet]

/-- `VirtualSignExtendWord` from a virtual source to a virtual destination. -/
theorem virtual_sign_extend_word_run_vreg_vreg (vd vs : VReg) (js : SailJoltState)
    (hvd : WritableVReg vd) :
    (execInstr (.VirtualSignExtendWord (.vreg vd) (.vreg vs))).run js =
      .ok RETIRE_SUCCESS
        { js with
          vregs := fun r =>
            if r = vd then sign_extend (m := 64) (Sail.BitVec.extractLsb (js.vregs vs) 31 0)
            else js.vregs r } := by
  unfold WritableVReg at hvd
  unfold execInstr readSrc writeDst readVReg writeVReg
  simp only [shared_sign_extend_word_eq_sail]
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get,
    hvd, ↓reduceIte, modify, modifyGet, MonadStateOf.modifyGet,
    EStateM.modifyGet]

/-- `VirtualSignExtendWord` from a virtual source to a real destination. -/
theorem virtual_sign_extend_word_run_xreg_vreg (rd : regidx) (vs : VReg)
    (js : SailJoltState) (s' : SailState)
    (hw : wX_bits rd
      (sign_extend (m := 64) (Sail.BitVec.extractLsb (js.vregs vs) 31 0))
      js.sail = .ok () s') :
    (execInstr (.VirtualSignExtendWord (.xreg rd) (.vreg vs))).run js =
      .ok RETIRE_SUCCESS { js with sail := s' } := by
  unfold execInstr readSrc writeDst readVReg liftSail
  simp only [shared_sign_extend_word_eq_sail]
  simp only [hw, bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get]

/-- `VirtualSignExtendWord` from a real source to a virtual destination,
packaged as an instruction step. It exposes the read, the virtual-register
write, the unchanged Sail state, and the successful run. -/
theorem exists_state_after_virtual_sign_extend_word_run_vreg_xreg
    (vd : VReg) (rs : regidx) (js : SailJoltState) (x : BitVec 64)
    (h : rX_bits rs js.sail = .ok x js.sail)
    (hvd : WritableVReg vd) :
    ∃ js',
      rX_bits rs js.sail = .ok x js.sail ∧
      js'.sail = js.sail ∧
      js'.vregs vd = sign_extend (m := 64) (Sail.BitVec.extractLsb x 31 0) ∧
      (∀ r, r ≠ vd → js'.vregs r = js.vregs r) ∧
      (execInstr (.VirtualSignExtendWord (.vreg vd) (.xreg rs))).run js =
        .ok RETIRE_SUCCESS js' := by
  let js' : SailJoltState :=
    { js with
      vregs := fun r =>
        if r = vd then sign_extend (m := 64) (Sail.BitVec.extractLsb x 31 0)
        else js.vregs r }
  refine ⟨js', h, rfl, ?_, ?_, ?_⟩
  · simp [js']
  · intro r hne
    simp [js', hne]
  · simpa only [js'] using virtual_sign_extend_word_run_vreg_xreg vd rs js x h hvd

/-- `VirtualSignExtendWord` from a real source to a virtual destination, in the
standard single-vreg-write shape used by program-block proofs. -/
theorem virtual_sign_extend_word_run_vreg_xreg_ex
    (vd : VReg) (rs : regidx) (js : SailJoltState) (x : BitVec 64)
    (hread : rX_bits rs js.sail = .ok x js.sail)
    (hvd : WritableVReg vd) :
    ∃ js',
      (execInstr (.VirtualSignExtendWord (.vreg vd) (.xreg rs))).run js =
        .ok RETIRE_SUCCESS js' ∧
      js'.vregs vd =
        sign_extend (m := 64) (Sail.BitVec.extractLsb x 31 0) ∧
      (∀ r, r ≠ vd → js'.vregs r = js.vregs r) ∧
      js'.sail = js.sail := by
  obtain ⟨js', _, hsail, hvalue, hpreserved, hrun⟩ :=
    exists_state_after_virtual_sign_extend_word_run_vreg_xreg
      vd rs js x hread hvd
  exact ⟨js', hrun, hvalue, hpreserved, hsail⟩

end JoltISA

end
