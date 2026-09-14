import JoltBytecode.InstructionEquivalence.ProofSupport.Lemmas

/-!
TODO: Consolidate these tactics.
# Program composition lemmas

`Program.append` is the proof-facing API for composing bytecode fragments.  A
phase proof should establish that one fragment retires successfully from an
input state to an output state; these lemmas compose those phase proofs without
unfolding the whole program into one long instruction chain.
-/


open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace JoltISA

/-- If the first program retires successfully, running `first.append second`
is the same as running `second` from the state produced by `first`. -/
theorem execProgram_append_of_first_succeeds (first second : Program)
    (js js_afterFirst : SailJoltState)
    (h_first : (execProgram first).run js = .ok RETIRE_SUCCESS js_afterFirst) :
    (execProgram (first.append second)).run js =
      (execProgram second).run js_afterFirst := by
  induction first generalizing js js_afterFirst with
  | done result =>
      cases result <;>
        simp only [Program.append, execProgram_done, EStateM.run, pure, EStateM.pure]
          at h_first ⊢
      · cases h_first
        rfl
      all_goals cases h_first
  | instr instr rest ih =>
      obtain ⟨js_afterInstr, h_instr_succeeds, h_rest_succeeds⟩ :=
        execProgram_instr_run_retire_inv instr rest js js_afterFirst h_first
      change (execProgram (.instr instr (rest.append second))).run js =
        (execProgram second).run js_afterFirst
      rw [execProgram_instr_run_retire instr (rest.append second) js js_afterInstr
        h_instr_succeeds]
      exact ih js_afterInstr js_afterFirst h_rest_succeeds

/-- Compose two successful program-fragment runs into one successful appended
program run. -/
theorem execProgram_append_succeeds_of_both_succeed (first second : Program)
    (js js_afterFirst js_afterSecond : SailJoltState)
    (h_first : (execProgram first).run js = .ok RETIRE_SUCCESS js_afterFirst)
    (h_second : (execProgram second).run js_afterFirst =
      .ok RETIRE_SUCCESS js_afterSecond) :
    (execProgram (first.append second)).run js =
      .ok RETIRE_SUCCESS js_afterSecond := by
  rw [execProgram_append_of_first_succeeds first second js js_afterFirst h_first]
  exact h_second

/-- If an appended program retires successfully, then the first fragment
retired successfully and the second fragment retired successfully from the
intermediate state. -/
theorem execProgram_append_succeeds_inv (first second : Program)
    (js js_afterSecond : SailJoltState)
    (h_append : (execProgram (first.append second)).run js =
      .ok RETIRE_SUCCESS js_afterSecond) :
    ∃ js_afterFirst,
      (execProgram first).run js = .ok RETIRE_SUCCESS js_afterFirst ∧
      (execProgram second).run js_afterFirst = .ok RETIRE_SUCCESS js_afterSecond := by
  induction first generalizing js js_afterSecond with
  | done result =>
      cases result <;>
        simp only [Program.append, execProgram_done, EStateM.run, pure, EStateM.pure]
          at h_append ⊢
      · exact ⟨js, rfl, h_append⟩
      all_goals cases h_append
  | instr instr rest ih =>
      change (execProgram (.instr instr (rest.append second))).run js =
        .ok RETIRE_SUCCESS js_afterSecond at h_append
      obtain ⟨js_afterInstr, h_instr_succeeds, h_rest_append_succeeds⟩ :=
        execProgram_instr_run_retire_inv instr (rest.append second) js js_afterSecond h_append
      obtain ⟨js_afterFirst, h_rest_succeeds, h_second_succeeds⟩ :=
        ih js_afterInstr js_afterSecond h_rest_append_succeeds
      refine ⟨js_afterFirst, ?_, h_second_succeeds⟩
      rw [execProgram_instr_run_retire instr rest js js_afterInstr h_instr_succeeds]
      exact h_rest_succeeds

namespace Program

/-- `program` retires successfully from `js` to `js'`. This is the
proof-facing form used by phase-composition proofs. -/
def Run (program : Program) (js js' : SailJoltState) : Prop :=
  (execProgram program).run js = .ok RETIRE_SUCCESS js'

namespace Run

/-- Compose two successful program-fragment runs. -/
theorem append {first second : Program}
    {js js_afterFirst js_afterSecond : SailJoltState}
    (h_first : Run first js js_afterFirst)
    (h_second : Run second js_afterFirst js_afterSecond) :
    Run (first.append second) js js_afterSecond :=
  execProgram_append_succeeds_of_both_succeed first second
    js js_afterFirst js_afterSecond h_first h_second

/-- Decompose a successful appended-program run into the first fragment, an
intermediate state, and the second fragment. -/
theorem append_inv {first second : Program}
    {js js_afterSecond : SailJoltState}
    (h_append : Run (first.append second) js js_afterSecond) :
    ∃ js_afterFirst,
      Run first js js_afterFirst ∧
      Run second js_afterFirst js_afterSecond :=
  execProgram_append_succeeds_inv first second js js_afterSecond h_append

end Run

end Program

end JoltISA

end
