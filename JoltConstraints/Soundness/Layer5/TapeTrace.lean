import JoltConstraints.Soundness.Layer5.TapeSemantics
import JoltConstraints.Soundness.soundness

/-! A separate execution language for independent tape answers. Existing
ValidRun, HonestTrace and the main soundness statement are unchanged.
The fixed-tape inclusion below preserves the entire Trace, including all states,
so it preserves registers, RAM, outputs, runtime advice and stopping behavior.
The shared run and trace requirements are currently duplicated. Changes to
ValidRun or HonestTrace, especially their stopping rules, must be reviewed here
too; the inclusion proof alone does not ensure that both specifications change
in the same way. -/

set_option autoImplicit false

namespace JoltConstraints.Soundness

open Sail PreSail LeanRV64D.Functions

/-- A run with one independent private answer per executed row. Answers on
non-tape rows are ignored; the remaining fields retain the existing run rules. -/
structure UntrustedAnswerRun (joltInstance : JoltInstance SourceInstruction)
    (privateInputs : JoltPrivateInputs) extends Trace where
  answers : Fin rows.size → BitVec 64
  expands : expand_program joltInstance.program = some bytecode
  executes : ∀ step : Fin rows.size,
    execWithTapeAnswer
      (bytecode[rows[step].rowIndex].instruction.withRuntimeAdvice rows[step].runtimeAdvice)
      (answers step) rows[step].preState = .ok (.Retire_Success ()) rows[step].postState
  -- Jolt's tracer starts from the emulator create_emulator builds.
  -- See : jolt/tracer/src/lib.rs:89-97, 364-408 (create_emulator)
  initialized : joltInstance.initial_state privateInputs = some initialState
  -- The trace begins where the program begins: Jolt's first tick runs the
  -- instruction at the entry address, with the PC already advanced past it.
  -- See : jolt/tracer/src/lib.rs:327-337, jolt/tracer/src/emulator/cpu.rs:622-632
  starts : ∀ first ∈ rows[0]?,
    bytecode[first.rowIndex].address = joltInstance.program.entry_address ∧
    bytecode[first.rowIndex].starts_source ∧
    first.preState = advance_pc joltInstance.program.entry_address
      (source_is_compressed bytecode first.rowIndex) initialState
  -- How one row leads to the next. If the instruction still has rows left, the
  -- next row is its next row and starts from the state this row left. If this was
  -- its last row, the next row is the first row of the instruction at nextPC, and
  -- the PC is moved to that instruction before it starts.
  -- See : jolt/tracer/src/instruction/mod.rs:679-687 (rows of one instruction, in order)
  --       jolt/tracer/src/emulator/cpu.rs:622-632 (the next instruction is fetched at the PC)
  linked : ∀ (i : Nat) (current next : TraceRow bytecode),
    rows[i]? = some current → rows[i + 1]? = some next →
    if bytecode[current.rowIndex].virtual_sequence_remaining.getD 0 ≠ 0 then
      next.rowIndex.val = current.rowIndex.val + 1 ∧
      next.preState = current.postState
    else
      ∃ address, current.postState.sail.regs.get? Register.nextPC = some address ∧
        bytecode[next.rowIndex].address = address ∧
        bytecode[next.rowIndex].starts_source ∧
        next.preState = advance_pc address (source_is_compressed bytecode next.rowIndex)
          current.postState

/-- A completed untrusted-answer run with honest internal runtime advice and
the same stopping and preprocessing requirements as an honest fixed-tape trace. -/
structure UntrustedAnswerTrace (joltInstance : JoltInstance SourceInstruction)
    (privateInputs : JoltPrivateInputs) extends UntrustedAnswerRun joltInstance privateInputs where
  -- Jolt only proves programs it accepts: the PC map checks and the entry check
  -- pass during preprocessing, before any tracing.
  -- See : jolt/crates/jolt-prover/src/preprocessing.rs:43-50
  accepted : joltInstance.bytecode.isSome
  -- Jolt's verifier rejects an instance whose inputs or layout fail its checks.
  -- See : jolt/crates/jolt-verifier/src/verifier.rs:356-383
  valid_inputs : joltInstance.validate_inputs = true
  -- At every step of the trace, the advice value recorded (`someTracerAdvice?`) is
  -- the value the honest tracer gives it (`honestTracerAdviceAtStepN`).
  advice_from_honest_tracer : ∀ n : Fin rows.size,
    rows[n].someTracerAdvice? = honestTracerAdviceAtStepN joltInstance.program rows n
  -- The run ends on the last row of an instruction that left the PC pointing at
  -- itself. Jolt's tracer stops there.
  -- See : jolt/tracer/src/lib.rs:113-120, 327-337 (trace, step_emulator)
  stops : ∀ last ∈ rows.back?,
    bytecode[last.rowIndex].virtual_sequence_remaining.getD 0 = 0 ∧
    last.postState.sail.regs.get? Register.nextPC = some bytecode[last.rowIndex].address
  -- The run does not end early: no earlier instruction left the PC pointing at itself.
  runs_until_stop : ∀ (i : Nat) (current next : TraceRow bytecode),
    rows[i]? = some current → rows[i + 1]? = some next →
    bytecode[current.rowIndex].virtual_sequence_remaining.getD 0 = 0 →
    current.postState.sail.regs.get? Register.nextPC ≠ some bytecode[current.rowIndex].address
  -- The run is empty only when the entry address is 0: Jolt compares the PC with a
  -- starting value of 0 and stops before running anything.
  nonempty : joltInstance.program.entry_address ≠ 0 → 0 < rows.size

/-- Embed a fixed-tape run by supplying its actual answers at every row. -/
noncomputable def UntrustedAnswerRun.ofFixed
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (run : ValidRun joltInstance privateInputs) : UntrustedAnswerRun joltInstance privateInputs where
  toTrace := run.toTrace
  answers step := fixedTapeAnswer
    (run.bytecode[run.rows[step].rowIndex].instruction.withRuntimeAdvice run.rows[step].runtimeAdvice)
    run.rows[step].preState
  expands := run.expands
  executes step := execWithTapeAnswer_of_fixed _ _ _
    (run.executes run.rows[step] (Array.getElem_mem step.isLt))
  initialized := run.initialized
  starts := run.starts
  linked := run.linked

/-- The embedding changes none of the run's bytecode, rows or states. -/
theorem UntrustedAnswerRun.ofFixed_toTrace
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (run : ValidRun joltInstance privateInputs) :
    (UntrustedAnswerRun.ofFixed run).toTrace = run.toTrace := rfl

/-- Embed an honest fixed-tape trace, retaining its runtime-advice and stopping facts. -/
noncomputable def UntrustedAnswerTrace.ofFixed
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (trace : HonestTrace joltInstance privateInputs) :
    UntrustedAnswerTrace joltInstance privateInputs where
  toUntrustedAnswerRun := UntrustedAnswerRun.ofFixed trace.toValidRun
  accepted := trace.accepted
  valid_inputs := trace.valid_inputs
  advice_from_honest_tracer := trace.advice_from_honest_tracer
  stops := trace.stops
  runs_until_stop := trace.runs_until_stop
  nonempty := trace.nonempty

/-- Compare the final device to the instance exactly as the fixed-tape specification does. -/
def UntrustedAnswerTrace.matches_outputs
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (trace : UntrustedAnswerTrace joltInstance privateInputs) : Prop :=
  let finalState := (trace.rows.back?.map (·.postState)).getD trace.initialState
  trimTrailingZeros finalState.jolt_device.outputs = trimTrailingZeros joltInstance.outputs ∧
    finalState.jolt_device.panic = joltInstance.panic

/-- Embedding a fixed-tape trace preserves its output and panic comparison. -/
theorem UntrustedAnswerTrace.ofFixed_matches_outputs
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (trace : HonestTrace joltInstance privateInputs) :
    (UntrustedAnswerTrace.ofFixed trace).matches_outputs ↔ trace.matches_outputs := Iff.rfl

/-- The proposed language existentially chooses private inputs and independent
per-row tape answers, retaining the output and stopping requirements. -/
def UntrustedAnswerLanguage (joltInstance : JoltInstance SourceInstruction) : Prop :=
  ∃ privateInputs, ∃ trace : UntrustedAnswerTrace joltInstance privateInputs, trace.matches_outputs

/-- Every instance in the fixed-tape language is also in the relaxed language. -/
theorem inLanguage_implies_untrustedAnswerLanguage
    {joltInstance : JoltInstance SourceInstruction} (member : joltInstance.InLanguage) :
    UntrustedAnswerLanguage joltInstance := by
  obtain ⟨privateInputs, trace, outputs⟩ := member
  exact ⟨privateInputs, UntrustedAnswerTrace.ofFixed trace, outputs⟩

end JoltConstraints.Soundness
