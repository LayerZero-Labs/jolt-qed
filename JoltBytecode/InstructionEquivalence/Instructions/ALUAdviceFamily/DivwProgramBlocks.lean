import JoltBytecode.InstructionEquivalence.ProofSupport.Basic
import JoltBytecode.InstructionEquivalence.Instructions.ALUAdviceFamily.Primitives

set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# Shared word-extension execution helpers

Only the helpers still consumed by the unchanged DIVUW and REMUW proofs remain
here. The old DIVW phase decomposition described an expansion Rust no longer
emits.
-/

theorem vreg_sign_extend_word_run
    (vd vs1 : BitVec 7)
    (js : SailJoltState)
    (hvd : WritableVReg vd) :
    (JoltISA.execInstr
      (.VirtualSignExtendWord (.vreg vd) (.vreg vs1))).run js =
      .ok RETIRE_SUCCESS
      { js with
        vregs := fun r =>
          if r = vd then
            sign_extend (m := 64)
              (Sail.BitVec.extractLsb (js.vregs vs1) 31 0)
          else js.vregs r } :=
  JoltISA.virtual_sign_extend_word_run_vreg_vreg vd vs1 js hvd

theorem vreg_sign_extend_word_run_ex
    (vd vs1 : BitVec 7)
    (js : SailJoltState)
    (hvd : WritableVReg vd) :
    ∃ js',
      (JoltISA.execInstr
        (.VirtualSignExtendWord (.vreg vd) (.vreg vs1))).run js =
          .ok RETIRE_SUCCESS js' ∧
      js'.vregs vd =
        sign_extend (m := 64)
          (Sail.BitVec.extractLsb (js.vregs vs1) 31 0) ∧
      (∀ k, k ≠ vd → js'.vregs k = js.vregs k) ∧
      js'.sail = js.sail := by
  let js' : SailJoltState :=
    { js with
      vregs := fun r =>
        if r = vd then
          sign_extend (m := 64)
            (Sail.BitVec.extractLsb (js.vregs vs1) 31 0)
        else js.vregs r }
  refine ⟨js', ?_, ?_, ?_, rfl⟩
  · simpa only [js'] using vreg_sign_extend_word_run vd vs1 js hvd
  · show (if vd = vd then _ else js.vregs vd) = _
    rw [if_pos rfl]
  · intro k h
    show (if k = vd then _ else js.vregs k) = _
    rw [if_neg h]

theorem vreg_sign_extend_word_to_real_run
    (rd : regidx)
    (vs1 : BitVec 7)
    (js : SailJoltState)
    (s' : SailState)
    (hwrite :
      wX_bits rd
        (sign_extend (m := 64)
          (Sail.BitVec.extractLsb (js.vregs vs1) 31 0))
        js.sail = .ok () s') :
    (JoltISA.execInstr
      (.VirtualSignExtendWord (.xreg rd) (.vreg vs1))).run js =
      .ok RETIRE_SUCCESS { js with sail := s' } :=
  JoltISA.virtual_sign_extend_word_run_xreg_vreg rd vs1 js s' hwrite

end
