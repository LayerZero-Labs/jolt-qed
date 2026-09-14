import JoltBytecode.InstructionEquivalence.ProofSupport.Lemmas

/-!
# Virtual alignment assertion semantics

Run lemmas for the Jolt ISA `VirtualAssertHalfwordAlignment` and
`VirtualAssertWordAlignment` rows.
-/

open Sail PreSail LeanRV64D.Functions
open virtaddr

set_option autoImplicit true

noncomputable section

namespace JoltISA

/-- A halfword-alignment assertion retires successfully when the effective
address has its low bit clear. -/
theorem virtual_assert_halfword_alignment_run_aligned
    (base : regidx) (imm : BitVec 12) (fault : ExceptionType)
    (js : SailJoltState) (baseValue : BitVec 64)
    (h_read : rX_bits base js.sail = .ok baseValue js.sail)
    (h_aligned : (baseValue + sign_extend (m := 64) imm) &&& (1 : BitVec 64) = 0) :
    (execInstr (.VirtualAssertHalfwordAlignment base imm fault)).run js =
      .ok RETIRE_SUCCESS js := by
  have h_condition :
      (baseValue + sign_extend (m := 64) imm) &&& (1#64) = 0#64 := by
    simpa using h_aligned
  cases js
  unfold execInstr liftSail
  simp [h_read, h_condition, EStateM.run, bind, EStateM.bind, pure, EStateM.pure]

/-- A halfword-alignment assertion returns the supplied memory exception when
the effective address has its low bit set. -/
theorem virtual_assert_halfword_alignment_run_misaligned
    (base : regidx) (imm : BitVec 12) (fault : ExceptionType)
    (js : SailJoltState) (baseValue : BitVec 64)
    (h_read : rX_bits base js.sail = .ok baseValue js.sail)
    (h_misaligned : (baseValue + sign_extend (m := 64) imm) &&& (1 : BitVec 64) ≠ 0) :
    (execInstr (.VirtualAssertHalfwordAlignment base imm fault)).run js =
      .ok (ExecutionResult.Memory_Exception
        (Virtaddr (baseValue + sign_extend (m := 64) imm), fault)) js := by
  have h_condition :
      (baseValue + sign_extend (m := 64) imm) &&& (1#64) ≠ 0#64 := by
    simpa using h_misaligned
  cases js
  unfold execInstr liftSail
  simp [h_read, h_condition, EStateM.run, bind, EStateM.bind, pure, EStateM.pure]

/-- A word-alignment assertion retires successfully when the effective address
has its low two bits clear. -/
theorem virtual_assert_word_alignment_run_aligned
    (base : regidx) (imm : BitVec 12) (fault : ExceptionType)
    (js : SailJoltState) (baseValue : BitVec 64)
    (h_read : rX_bits base js.sail = .ok baseValue js.sail)
    (h_aligned : (baseValue + sign_extend (m := 64) imm) &&& (3 : BitVec 64) = 0) :
    (execInstr (.VirtualAssertWordAlignment base imm fault)).run js =
      .ok RETIRE_SUCCESS js := by
  have h_condition :
      (baseValue + sign_extend (m := 64) imm) &&& (3#64) = 0#64 := by
    simpa using h_aligned
  cases js
  unfold execInstr liftSail
  simp [h_read, h_condition, EStateM.run, bind, EStateM.bind, pure, EStateM.pure]

/-- A word-alignment assertion returns the supplied memory exception when the
effective address has one of its low two bits set. -/
theorem virtual_assert_word_alignment_run_misaligned
    (base : regidx) (imm : BitVec 12) (fault : ExceptionType)
    (js : SailJoltState) (baseValue : BitVec 64)
    (h_read : rX_bits base js.sail = .ok baseValue js.sail)
    (h_misaligned : (baseValue + sign_extend (m := 64) imm) &&& (3 : BitVec 64) ≠ 0) :
    (execInstr (.VirtualAssertWordAlignment base imm fault)).run js =
      .ok (ExecutionResult.Memory_Exception
        (Virtaddr (baseValue + sign_extend (m := 64) imm), fault)) js := by
  have h_condition :
      (baseValue + sign_extend (m := 64) imm) &&& (3#64) ≠ 0#64 := by
    simpa using h_misaligned
  cases js
  unfold execInstr liftSail
  simp [h_read, h_condition, EStateM.run, bind, EStateM.bind, pure, EStateM.pure]

end JoltISA

end
