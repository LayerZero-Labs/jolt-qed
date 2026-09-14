import JoltBytecode.JoltISA.Semantics
import JoltBytecode.InstructionEquivalence.ProofSupport.RegisterAccess

/-!
# Basic Jolt ISA semantic lemmas

Instruction-specific proof files should import this module when they need
facts about the generic interpreter rather than unfolding it ad hoc.
-/


open Sail PreSail LeanRV64D.Functions
open virtaddr MemoryAccessType mem_payload

set_option autoImplicit true

noncomputable section

namespace JoltISA

-- TODO: Not sure if we need this as simp lemmas to clean up proof but to be seen.

/-- Executing a terminal Jolt program returns its terminal result without
changing the state. -/
-- True by literally how we write execProgram
@[simp] theorem execProgram_done (result : ExecutionResult) :
    execProgram (.done result) = (pure result : JoltMonad ExecutionResult) := rfl

/-- Executing a non-empty Jolt program means executing the head instruction and,
only if it retires successfully, continuing with the tail. -/
@[simp] theorem execProgram_instr (instr : Instr) (rest : Program) :
    execProgram (.instr instr rest) =
      (execInstr instr >>= fun
        | .Retire_Success () => execProgram rest
        | result => pure result) := rfl 

/-- If the head instruction retires successfully, running a program continues
from the state produced by that instruction and executes the tail. -/
theorem execProgram_instr_run_retire (instr : Instr) (rest : Program)
    (js js' : SailJoltState)
    (h : (execInstr instr).run js = .ok RETIRE_SUCCESS js') :
    (execProgram (.instr instr rest)).run js = (execProgram rest).run js' := by
  change execInstr instr js = .ok RETIRE_SUCCESS js' at h
  simp only [execProgram_instr, EStateM.run, bind, EStateM.bind]
  rw [h]
  rfl

/-- Successful execution of a non-empty program can be peeled into a successful
head-instruction run and a successful tail-program run. -/
theorem execProgram_instr_run_retire_inv (instr : Instr) (rest : Program)
    (js js' : SailJoltState)
    (h : (execProgram (.instr instr rest)).run js = .ok RETIRE_SUCCESS js') :
    ∃ js₁,
      (execInstr instr).run js = .ok RETIRE_SUCCESS js₁ ∧
      (execProgram rest).run js₁ = .ok RETIRE_SUCCESS js' := by
  simp only [execProgram_instr, EStateM.run, bind, EStateM.bind] at h
  cases hinstr : execInstr instr js with
  | ok result js₁ =>
      simp only [hinstr] at h
      cases result <;> simp only [pure, EStateM.pure] at h
      case Retire_Success u =>
        cases u
        exact ⟨js₁, by simpa [EStateM.run] using hinstr, h⟩
      all_goals cases h
  | error e js₁ =>
      simp only [hinstr] at h
      cases h

/-- If the head instruction throws an error, running a program throws the same
error and does not execute the tail. -/
theorem execProgram_instr_run_error (instr : Instr) (rest : Program)
    (js js' : SailJoltState) (e : Error exception)
    (h : (execInstr instr).run js = .error e js') :
    (execProgram (.instr instr rest)).run js = .error e js' := by
  change execInstr instr js = .error e js' at h
  simp only [execProgram_instr, EStateM.run, bind, EStateM.bind]
  rw [h]

/-- If the head instruction returns a memory exception as an ordinary
`ExecutionResult`, the structured program returns that exception immediately
and does not execute the tail. -/
theorem execProgram_instr_run_memory_exception (instr : Instr) (rest : Program)
    (js js' : SailJoltState) (e : virtaddr × ExceptionType)
    (h : (execInstr instr).run js = .ok (ExecutionResult.Memory_Exception e) js') :
    (execProgram (.instr instr rest)).run js =
      .ok (ExecutionResult.Memory_Exception e) js' := by
  change execInstr instr js = .ok (ExecutionResult.Memory_Exception e) js' at h
  simp only [execProgram_instr, EStateM.run, bind, EStateM.bind]
  rw [h]
  rfl

/-- If a Jolt computation can only return `RETIRE_SUCCESS` on success, then
binding it into `pure RETIRE_SUCCESS` does not change its run result. -/
theorem bind_pure_retire_of_onlyRetire
    (m : JoltMonad ExecutionResult) (js : SailJoltState)
    (hret : ∀ js r js', m.run js = .ok r js' → r = RETIRE_SUCCESS) :
    (do
      let _ ← m
      pure RETIRE_SUCCESS).run js = m.run js := by
  simp only [bind, EStateM.bind, EStateM.run]
  cases h : m js with
  | ok r js' =>
      have hr := hret js r js' (by simpa [EStateM.run] using h)
      cases hr
      rfl
  | error e js' =>
      rfl

/-- Function-extensional form of `bind_pure_retire_of_onlyRetire`. -/
theorem bind_pure_retire_of_onlyRetire_eq
    (m : JoltMonad ExecutionResult)
    (hret : ∀ js r js', m.run js = .ok r js' → r = RETIRE_SUCCESS) :
    (do
      let _ ← m
      pure RETIRE_SUCCESS) = m := by
  funext js
  exact bind_pure_retire_of_onlyRetire m js hret

theorem writeVReg_retire_run
    (vd : VReg) (value : BitVec 64) (js : SailJoltState) :
    (do
      writeVReg vd value
      pure RETIRE_SUCCESS : JoltMonad ExecutionResult).run js =
      if vd.toNat < 32 then
        .error (Error.Assertion "writeVReg: architectural xreg address") js
      else
        .ok RETIRE_SUCCESS
          { js with vregs := fun r => if r = vd then value else js.vregs r } := by
  simp only [EStateM.run, bind, EStateM.bind]
  have hwrite :
      writeVReg vd value js =
        if vd.toNat < 32 then
          EStateM.Result.error (Error.Assertion "writeVReg: architectural xreg address") js
        else
          EStateM.Result.ok ()
            { js with vregs := fun r => if r = vd then value else js.vregs r } := by
    simpa only [EStateM.run] using writeVReg_run vd value js
  rw [hwrite]
  by_cases h : vd.toNat < 32
  · simp only [h, ↓reduceIte]
  · simp only [h, ↓reduceIte, pure, EStateM.pure]

theorem writeVReg_retire_run_of_writable
    (vd : VReg) (value : BitVec 64) (js : SailJoltState)
    (hvd : WritableVReg vd) :
    (do
      writeVReg vd value
      pure RETIRE_SUCCESS : JoltMonad ExecutionResult).run js =
      .ok RETIRE_SUCCESS
        { js with vregs := fun r => if r = vd then value else js.vregs r } := by
  unfold WritableVReg at hvd
  rw [writeVReg_retire_run]
  simp only [hvd, ↓reduceIte]

end JoltISA

end
