import JoltConstraints.Soundness.Layer6.ExecutionPrefix
import JoltConstraints.Soundness.Layer5.Registers

/-! Shared boundary and in-expansion state for execution-prefix reconstruction. -/

set_option autoImplicit false

namespace JoltInstance

open JoltConstraints.Soundness

/-- Agreement after `run.rows.size` witness cycles, at a source-instruction boundary.
`represents` compares retained row observations and RAM outside the termination word;
`real` excludes retained padding and `noEarlierStop` excludes a stall before the last row.
`honestAdvice` records the honest tracer's advice at every retained row, while
`atBoundary` says the last row, if present, completes its source instruction.
`registers` compares all non-instruction-temporary registers at the next witness cycle
with the run's final state and retains the presence of every Sail register.
`terminationWord` keeps the termination RAM word zero until a store touches it.
`ready` supplies the next selected bytecode row and its prepared execution state when
the witness has another real cycle and the run has not reached a stable stall.
For example, after `rem a0, a1, zero`, witness quotient 5 and honest quotient 0 may
differ in temporary 40, while `a0`, other persistent registers and RAM still agree.
See jolt/crates/jolt-program/src/expand/division/rem.rs:15-24 and
jolt/tracer/src/instruction/rem.rs:44-58 at 5def437f. -/
structure BoundaryState {F : Type} [Field F] {params : WitnessParams}
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (witness : WitnessType F params)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (run : UntrustedAnswerRun joltInstance privateInputs) : Prop where
  represents : RepresentsPrefix witness run.toTrace
  real : ∀ t : Fin params.traceLength,
    t.val < run.rows.size → witness.InstructionFlags .IsNoop t = 0
  noEarlierStop : ∀ (i : Nat) (current next : TraceRow run.bytecode),
    run.rows[i]? = some current → run.rows[i + 1]? = some next →
    ¬ current.StableStall
  honestAdvice : ∀ n : Fin run.rows.size,
    run.rows[n].someTracerAdvice? =
      honestTracerAdviceAtStepN joltInstance.program run.rows n
  atBoundary : ∀ last ∈ run.rows.back?,
    run.bytecode[last.rowIndex].virtual_sequence_remaining.getD 0 = 0
  registers : ∀ bound : run.rows.size < params.traceLength,
    RegisterAgreementOn (fun register => ¬ IsInstructionTemporary register)
      witness ⟨run.rows.size, bound⟩ (TraceWitness.finalTraceState run.toTrace)
  terminationWord : ∀ bound : run.rows.size < params.traceLength,
    (¬ ∃ i : Fin run.rows.size, run.StoresTerminationAt i) →
    ∀ address : Fin params.ramSize,
      address.val = (run.initialState.jolt_device.memory_layout.termination.toNat -
        JoltConstraints.ramLowestAddress run.initialState.jolt_device.memory_layout) / 8 →
      witness.RamVal address ⟨run.rows.size, bound⟩ = 0
  ready : ∀ bound : run.rows.size < params.traceLength,
    witness.InstructionFlags .IsNoop ⟨run.rows.size, bound⟩ = 0 →
    (∀ last ∈ run.rows.back?, ¬ last.StableStall) →
    ∃ (next : Fin run.bytecode.size) (pre : SailJoltState)
      (slot : Fin (2 ^ params.logBytecodeK)),
      JoltConstraints.bytecodeRa witness slot ⟨run.rows.size, bound⟩ = 1 ∧
      slot.val = next.val + 1 ∧ run.NextStep next pre

/-- The row at `first` plus the rows left in its sequence stamp.
When `first` starts a source instruction, this is that instruction's full row count;
for example, a nonzero-destination REM has nine rows and a native ADDI has one.
See jolt/crates/jolt-program/src/expand/metadata.rs (`stamp_sequence_metadata`)
at 5def437f. -/
def expansionRowCount (bytecode : Array JoltInstructionRow)
    (first : Fin bytecode.size) : Nat :=
  (bytecode[first].virtual_sequence_remaining.getD 0).toNat + 1

/-- Some row of the block beginning at `first`, within its stamped row count,
is a VirtualAdvice row. This concerns internal division advice, not tape reads.
For example, REM with a nonzero destination has advice, while AdviceLD does not.
See jolt/crates/jolt-program/src/expand/division/rem.rs (`expand_rem`) at 5def437f. -/
def ExpansionHasAdvice (bytecode : Array JoltInstructionRow)
    (first : Fin bytecode.size) : Prop :=
  ∃ offset < expansionRowCount bytecode first,
    ∃ row ∈ bytecode[first.val + offset]?, row.instruction.adviceValue? ≠ none

/-- A register is live after `done` rows if it is persistent, or if the source
is unfinished and one of its already executed rows wrote that register.
The block's ordered-row certificate in `ExpansionState` connects these bytecode
writes to executed rows. For example, temporary 40 is live after REM's advice
row but is no longer required to agree after all nine rows finish. -/
def ExpansionLive (bytecode : Array JoltInstructionRow)
    (first : Fin bytecode.size) (done : Nat) (register : Fin 128) : Prop :=
  ¬ IsInstructionTemporary register ∨
    (done < expansionRowCount bytecode first ∧
      ∃ offset < done, ∃ row ∈ bytecode[first.val + offset]?,
        ∃ destination ∈ row.instruction.destination?,
          TraceWitness.destinationRegisterAddress destination = register)

/-- `extended` retains every row of `run`, including its recorded advice and
pre/post states, after identifying their bytecode arrays.
For example, appending nine REM rows preserves the entire earlier prefix.
The step lemmas separately specify the number of appended rows; initialization
of both runs already identifies their initial states with the same instance. -/
def RunExtends {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs}
    (run extended : UntrustedAnswerRun joltInstance privateInputs) : Prop :=
  ∃ same : extended.bytecode = run.bytecode,
    (same ▸ extended.rows : Array (TraceRow run.bytecode)).extract 0 run.rows.size = run.rows

/-- Agreement after executing the first `done` rows of the source starting at
`first` in the context bytecode. `represents`, `real`, `noEarlierStop` and
`terminationWord` have the boundary invariant's meanings.
`starts`, `done_le`, `retained`, `ordered` and `priorBoundary` locate these rows
at the end of the run, following an empty prefix or a completed source.
`registers` compares the final state with the next witness column on `ExpansionLive`.
While unfinished, `next` provides a real next cycle, its consecutive selected
slot and the entry/linkage clause of `NextStep`; `notStopped` excludes a final stall.
Honest advice is deliberately separate: after REM's first row a run carrying
witness quotient 5 can satisfy this state, although the honest quotient is 0.
See jolt/crates/jolt-program/src/expand/division/rem.rs (`expand_rem`) and
jolt/tracer/src/instruction/mod.rs (`trace_inline_sequence_with_advice`) at 5def437f. -/
structure ExpansionState {F : Type} [Field F] {params : WitnessParams}
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (witness : WitnessType F params)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (run : UntrustedAnswerRun joltInstance privateInputs)
    (first : Fin context.bytecode.size) (done : Nat) : Prop where
  represents : RepresentsPrefix witness run.toTrace
  real : ∀ t : Fin params.traceLength,
    t.val < run.rows.size → witness.InstructionFlags .IsNoop t = 0
  noEarlierStop : ∀ (i : Nat) (current next : TraceRow run.bytecode),
    run.rows[i]? = some current → run.rows[i + 1]? = some next →
    ¬ current.StableStall
  terminationWord : ∀ bound : run.rows.size < params.traceLength,
    (¬ ∃ i : Fin run.rows.size, run.StoresTerminationAt i) →
    ∀ address : Fin params.ramSize,
      address.val = (run.initialState.jolt_device.memory_layout.termination.toNat -
        JoltConstraints.ramLowestAddress run.initialState.jolt_device.memory_layout) / 8 →
      witness.RamVal address ⟨run.rows.size, bound⟩ = 0
  starts : context.bytecode[first].starts_source = true
  done_le : done ≤ expansionRowCount context.bytecode first
  retained : done ≤ run.rows.size
  ordered : ∀ offset < done,
    ∃ row ∈ run.rows[run.rows.size - done + offset]?,
      row.rowIndex.val = first.val + offset
  priorBoundary : ∀ last ∈ (run.rows.extract 0 (run.rows.size - done)).back?,
    run.bytecode[last.rowIndex].virtual_sequence_remaining.getD 0 = 0
  registers : ∀ bound : run.rows.size < params.traceLength,
    RegisterAgreementOn (ExpansionLive context.bytecode first done)
      witness ⟨run.rows.size, bound⟩ (TraceWitness.finalTraceState run.toTrace)
  next : done < expansionRowCount context.bytecode first →
    ∃ bound : run.rows.size < params.traceLength,
      witness.InstructionFlags .IsNoop ⟨run.rows.size, bound⟩ = 0 ∧
      ∃ (next : Fin run.bytecode.size) (pre : SailJoltState)
        (slot : Fin (2 ^ params.logBytecodeK)),
        next.val = first.val + done ∧
        JoltConstraints.bytecodeRa witness slot ⟨run.rows.size, bound⟩ = 1 ∧
        slot.val = first.val + done + 1 ∧
        (match run.rows.back? with
        | none =>
          run.bytecode[next].address = joltInstance.program.entry_address ∧
          run.bytecode[next].starts_source ∧
          pre = advance_pc joltInstance.program.entry_address
            (source_is_compressed run.bytecode next) run.initialState
        | some last =>
          if run.bytecode[last.rowIndex].virtual_sequence_remaining.getD 0 ≠ 0 then
            next.val = last.rowIndex.val + 1 ∧ pre = last.postState
          else
            ∃ address, last.postState.sail.regs.get? Register.nextPC = some address ∧
              ¬ last.StableStall ∧
              run.bytecode[next].address = address ∧
              run.bytecode[next].starts_source ∧
              pre = advance_pc address (source_is_compressed run.bytecode next) last.postState)
  notStopped : done < expansionRowCount context.bytecode first →
    ∀ last ∈ run.rows.back?, ¬ last.StableStall

end JoltInstance
