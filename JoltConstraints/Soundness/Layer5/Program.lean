import JoltConstraints.Soundness.Layer5.TapeSemantics

/-! Execute a generated expansion using the same per-row answer rule as
UntrustedAnswerRun. Row indices here are local to the expansion. Answers on
non-tape rows are ignored, and a failed or non-retiring row stops execution. -/

set_option autoImplicit false

namespace JoltConstraints.Soundness

open Sail PreSail LeanRV64D.Functions JoltISA

/-- Run a straight-line expansion, supplying one independent answer per row. -/
noncomputable def execProgramWithTapeAnswers :
    Program → (Nat → BitVec 64) → JoltMonad ExecutionResult
  | .done result, _ => pure result
  | .instr instruction rest, answers => do
      match ← execWithTapeAnswer instruction (answers 0) with
      | .Retire_Success () => execProgramWithTapeAnswers rest (fun n => answers (n + 1))
      | result => pure result

/-- A successful row continues with the next row's answer and its exact
post-state, as required by expansion linkage. -/
theorem execProgramWithTapeAnswers_cons (instruction : Instr) (rest : Program)
    (answers : Nat → BitVec 64) (pre post : SailJoltState)
    (step : execWithTapeAnswer instruction (answers 0) pre = .ok RETIRE_SUCCESS post) :
    execProgramWithTapeAnswers (.instr instruction rest) answers pre =
      execProgramWithTapeAnswers rest (fun n => answers (n + 1)) post := by
  simp only [execProgramWithTapeAnswers, bind, EStateM.bind, step, RETIRE_SUCCESS]

end JoltConstraints.Soundness
