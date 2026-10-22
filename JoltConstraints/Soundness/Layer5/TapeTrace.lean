import JoltConstraints.Soundness.Layer5.TapeSemantics
import JoltConstraints.language

/-! A separate execution language for independent tape answers.
The fixed-tape inclusion below preserves the entire Trace, including all states,
so it preserves registers, RAM, outputs, runtime advice and stopping behavior.
The two languages use shared predicates on the plain Trace for outputs, checked
prover configuration and spoil asserts.
UntrustedAnswerRun and UntrustedAnswerTrace still repeat the run requirements
of ValidRun and HonestTrace, so changes to either trace structure must be
checked here until the reverse inclusion is proved. -/

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
  -- The tracer stops at a self-jump only when re-execution jumps there again.
  -- See : a16z/jolt PR #2109, head d2995380, `Cpu::tick`.
  stops : ∀ last ∈ rows.back?, last.StableStall
  -- No earlier row meets that stopping rule.
  runs_until_stop : ∀ (i : Nat) (current next : TraceRow bytecode),
    rows[i]? = some current → rows[i + 1]? = some next →
    ¬ current.StableStall
  -- Language membership has no empty trace because this field requires it;
  -- `prover_config` itself allows trace length zero. Soundness obtains this
  -- bound from the termination store.
  -- See : a16z/jolt PR #2109, head d2995380.
  nonempty : 0 < rows.size

instance {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} :
    CoeOut (UntrustedAnswerTrace joltInstance privateInputs) Trace :=
  ⟨fun trace => trace.toUntrustedAnswerRun.toTrace⟩

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

/-- The relaxed language existentially chooses private inputs and independent
per-row tape answers, with the same public output, prover and spoil requirements. -/
def UntrustedAnswerLanguage (joltInstance : JoltInstance SourceInstruction) : Prop :=
  ∃ privateInputs, ∃ trace : UntrustedAnswerTrace joltInstance privateInputs,
    trace.matches_outputs joltInstance ∧
    (trace.prover_config joltInstance).isSome ∧
    trace.SpoilAssertsPass

/-- Every instance in the fixed-tape language is also in the relaxed language. -/
theorem inLanguage_implies_untrustedAnswerLanguage
    {joltInstance : JoltInstance SourceInstruction} (member : joltInstance.InLanguage) :
    UntrustedAnswerLanguage joltInstance := by
  obtain ⟨privateInputs, trace, outputs, proverAccepts, spoilAsserts⟩ := member
  exact ⟨privateInputs, UntrustedAnswerTrace.ofFixed trace,
    outputs, proverAccepts, spoilAsserts⟩

end JoltConstraints.Soundness
