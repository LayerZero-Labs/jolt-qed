import JoltConstraints.Soundness.Layer6.PrefixState
import JoltConstraints.Soundness.Layer6.BytecodePC
import JoltConstraints.Soundness.Layer7.TerminationStore
import JoltConstraints.Soundness.Layer3.State

/-! Staged initialization of the empty run and the next source expansion. -/

set_option autoImplicit false

namespace JoltInstance

open JoltConstraints.Soundness

/-- For an accepted nonpadding entry slot, the slot is one past the first row
of its source instruction, whose address is the program entry address.
For example, entry slot 1 identifies row 0 of an ADDI at the entry address.
See jolt/crates/jolt-program/src/preprocess/bytecode.rs (`get_first_pc`,
`BytecodePCMapper::try_new`) at 5def437f. -/
private theorem first_row_of_entry_slot
    (image : Rv64ProgramImage SourceInstruction)
    (bytecode : Array JoltInstructionRow)
    (expanded : expand_program image = some bytecode)
    (slots : Array BytecodeSlot) (preprocessed : preprocess bytecode = some slots)
    (slot : Nat) (found : get_first_pc slots image.entry_address = some slot)
    (nonzero : slot ≠ 0) :
    ∃ first : Fin bytecode.size,
      slot = first.val + 1 ∧ bytecode[first].address = image.entry_address ∧
      bytecode[first].starts_source = true := by
  sorry

/-- On an empty initialized run, the final RAM image equals the initial image
outside the synthetic termination word: the initial output buffer is empty and
the panic bit is false.
For example, an untouched input word retains its initial value at cycle zero.
See jolt/crates/jolt-witness/src/backend/trace/ram.rs (`initial_ram_state`,
`final_ram_state`) at 5def437f. -/
private theorem empty_run_ram_word
    {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs}
    (run : UntrustedAnswerRun joltInstance privateInputs)
    (empty : run.rows = #[]) (address : Nat)
    (outsideTermination : address ≠
      (run.initialState.jolt_device.memory_layout.termination.toNat -
        JoltConstraints.ramLowestAddress run.initialState.jolt_device.memory_layout) / 8) :
    TraceWitness.finalRamWord run.toTrace address =
      TraceWitness.initialRamWordFromState run.initialState address := by
  sorry

/-- The instance's initialized state admits an empty run satisfying the boundary
invariant at witness cycle zero. The run's `initialized` certificate identifies
its state with the state supplied by `context.initialized`.
For example, before an entry ADDI, registers and nontermination RAM agree with
their initial tables, and the selected entry row supplies `ready` if it is real. -/
theorem boundaryState_empty {F : Type} [Field F] (joltField : JoltField F)
    {joltInstance : JoltInstance SourceInstruction} {params : WitnessParams}
    {privateInputs : JoltPrivateInputs} (witness : WitnessType F params)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (equations : JoltConstraints.ConstraintEquations context.bytecode context.initialRam
      context.io context.entry witness) :
    ∃ run : UntrustedAnswerRun joltInstance privateInputs,
      run.rows = #[] ∧ BoundaryState witness context run := by
  obtain ⟨state, initialized, _⟩ := context.initialized
  let run : UntrustedAnswerRun joltInstance privateInputs := {
    toTrace := { bytecode := context.bytecode, rows := #[], initialState := state }
    answers := by intro step; exact False.elim (by simpa using step.isLt)
    expands := context.expands
    executes := by intro step; exact False.elim (by simpa using step.isLt)
    initialized := initialized
    starts := by intro first member; simp at member
    linked := by intro i current next currentIs _; simp at currentIs
  }
  have char : 2 ^ 127 < ringChar F := by
    dsimp [JoltField] at joltField
    omega
  refine ⟨run, rfl, {
    represents := ?_
    real := by intro t inRun; simp [run] at inRun
    noEarlierStop := by intro i current next currentIs _; simp [run] at currentIs
    honestAdvice := by intro n; exact False.elim (by simpa [run] using n.isLt)
    atBoundary := by intro last member; simp [run] at member
    registers := ?_
    terminationWord := ?_
    ready := ?_
  }⟩
  · refine {
      toRepresentsRows := {
        rowsBound := by simp [run]
        pc := by intro t inRun; simp [run] at inRun
        rs1 := by intro t inRun _; simp [run] at inRun
        rs2 := by intro t inRun _; simp [run] at inRun
        ramAddress := by intro t inRun; simp [run] at inRun
      }
      cutRam := ⟨?_, ?_⟩
    }
    · intro bound address outside
      have initial := ramVal_initial_state context
        equations.ramValEqInitialPlusPrefixRamInc initialized address
      have final := empty_run_ram_word run rfl address.val outside
      simpa [run] using initial.trans (congrArg (fun word : BitVec 64 => ((word.toNat : Nat) : F)) final.symm)
    · intro full
      have floor := context.traceLengthFloor
      simp [run] at full
      omega
  · intro bound
    have initial := RegisterAgreement.initial equations.registersValEqPrefixRdInc initialized
    simpa [run, TraceWitness.finalTraceState] using
      (initial.toOn (fun register => ¬ IsInstructionTemporary register))
  · intro bound _ address termAddress
    have layout := initial_state_memory_layout context initialized
    have zero := context_initial_termination_zero context
    have initial := ramVal_zero equations.ramValEqInitialPlusPrefixRamInc address
    have sameAddress : address.val =
        (context.io.memory_layout.termination.toNat -
          JoltConstraints.ramLowestAddress context.io.memory_layout) / 8 := by
      simpa only [run, layout] using termAddress
    simpa [run, JoltConstraints.ramInitialValue, sameAddress, zero] using initial
  · intro bound real _
    have selected := equations.bytecodeRaAtEntryEqOne
    have entryNonzero : context.entry.val ≠ 0 := by
      intro zero
      have flag := instructionFlag_of_selected_bytecode char context equations
        .IsNoop ⟨0, Nat.two_pow_pos _⟩ context.entry selected
      have padding : witness.InstructionFlags .IsNoop ⟨0, Nat.two_pow_pos _⟩ = (1 : F) := by
        simpa [JoltConstraints.bytecodeInstructionFlag, JoltConstraints.bytecodeRow, zero] using flag
      have impossible : (1 : F) = 0 := by
        simpa only [run] using padding.symm.trans real
      exact one_ne_zero impossible
    obtain ⟨slots, preprocessed, found⟩ := context.entryIsRust
    obtain ⟨first, slotIs, address, starts⟩ := first_row_of_entry_slot
      joltInstance.program context.bytecode context.expands slots preprocessed
      context.entry.val found entryNonzero
    refine ⟨first, advance_pc joltInstance.program.entry_address
      (source_is_compressed context.bytecode first) state, context.entry,
      ?_, slotIs, ?_⟩
    · simpa only [run] using selected
    · refine {
        honestRuntimeAdvice := by intro n; exact False.elim (by simpa [run] using n.isLt)
        noEarlierStop := by intro i current next currentIs _; simp [run] at currentIs
        ready := by simpa [run] using And.intro address starts
      }

/-- Open the source selected by a boundary's real next cycle without adding a
row. `done = 0` leaves all instruction temporaries dead and preserves the run.
For example, before a two-row SLL, the selected first row is VirtualPow2 and
the next clause prepares that row's pre-state using the source compression flag. -/
theorem expansion_start {F : Type} [Field F] {params : WitnessParams}
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (witness : WitnessType F params)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (run : UntrustedAnswerRun joltInstance privateInputs)
    (boundary : BoundaryState witness context run)
    (bound : run.rows.size < params.traceLength)
    (real : witness.InstructionFlags .IsNoop ⟨run.rows.size, bound⟩ = 0)
    (notStopped : ∀ last ∈ run.rows.back?, ¬ last.StableStall) :
    ∃ first : Fin context.bytecode.size, ExpansionState witness context run first 0 := by
  obtain ⟨next, pre, slot, selected, slotIs, step⟩ :=
    boundary.ready bound real notStopped
  have bytecodeIs : run.bytecode = context.bytecode :=
    Option.some.inj (run.expands.symm.trans context.expands)
  let first : Fin context.bytecode.size := ⟨next.val, by simp [← bytecodeIs, next.isLt]⟩
  have starts : context.bytecode[first].starts_source = true := by
    have atStart : run.bytecode[next].starts_source = true := by
      cases h : run.rows.back? with
      | none =>
        have ready := step.ready
        rw [h] at ready
        exact ready.2.1
      | some last =>
        have lastDone := boundary.atBoundary last h
        have ready := step.ready
        rw [h] at ready
        simp only [lastDone, ne_eq, not_true_eq_false, ↓reduceIte] at ready
        obtain ⟨_, _, _, _, starts, _⟩ := ready
        exact starts
    simpa only [first, bytecodeIs] using atStart
  refine ⟨first, {
    represents := boundary.represents
    real := boundary.real
    noEarlierStop := boundary.noEarlierStop
    terminationWord := boundary.terminationWord
    starts := starts
    done_le := Nat.zero_le _
    retained := Nat.zero_le _
    ordered := by intro offset offsetLt; omega
    priorBoundary := by
      simpa only [Nat.sub_zero, Array.extract_size] using boundary.atBoundary
    registers := by
      intro bound'
      exact (boundary.registers bound').mono (by
        intro register live
        rcases live with persistent | ⟨_, offset, offsetLt, _⟩
        · exact persistent
        · omega)
    next := by
      intro _
      refine ⟨bound, real, next, pre, slot, rfl, selected, ?_, ?_⟩
      · simpa only [first] using slotIs
      · simpa only [first] using step.ready
    notStopped := by intro _; exact notStopped
  }⟩

end JoltInstance
