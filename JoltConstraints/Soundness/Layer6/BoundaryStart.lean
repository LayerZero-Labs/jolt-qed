import JoltConstraints.Soundness.Layer6.PrefixState
import JoltConstraints.Soundness.Layer6.BytecodePC
import JoltConstraints.Soundness.Layer7.TerminationStore
import JoltConstraints.Soundness.Layer3.State

/-! Staged initialization of the empty run and the next source expansion. -/

set_option autoImplicit false

namespace JoltInstance

open JoltConstraints.Soundness

/-- In expanded bytecode, a row with no earlier row at its address begins its
source instruction.
For example, the first row at an ADDI address starts that ADDI's expansion. -/
private theorem first_address_row_starts
    (bytecode : Array JoltInstructionRow)
    (expanded : ∃ image : Rv64ProgramImage SourceInstruction,
      expand_program image = some bytecode)
    (first : Fin bytecode.size)
    (earlier : ∀ position : Fin bytecode.size, position.val < first.val →
      bytecode[position].address ≠ bytecode[first].address) :
    bytecode[first].starts_source = true := by
  obtain ⟨image, expanded⟩ := expanded
  obtain ⟨groups, flattened, valid⟩ := expand_program_flatten image bytecode expanded
  by_cases zero : first.val = 0
  · have bytecodeNonempty : 0 < bytecode.size := by omega
    have nonempty : 0 < groups.flatten.length := by
      simpa only [flattened, List.size_toArray] using bytecodeNonempty
    have firstStarts := rows_first_starts groups valid nonempty
    have firstStartsBytecode : bytecode[0].starts_source = true := by
      simpa only [flattened, List.getElem_toArray] using firstStarts
    simpa only [Fin.getElem_fin, zero] using firstStartsBytecode
  · let previous : Fin bytecode.size := ⟨first.val - 1, by omega⟩
    have previousVal : previous.val = first.val - 1 := rfl
    have different : bytecode[previous].address ≠ bytecode[first].address :=
      earlier previous (by omega)
    have previousLast : bytecode[previous].virtual_sequence_remaining.getD 0 = 0 := by
      by_contra continues
      have following := (expand_program_layout image bytecode expanded).next
        previous first (by omega) (by simpa [JoltInstructionRow.continues] using continues)
      exact different following.1.symm
    have prevInList : previous.val < groups.flatten.length := by
      simpa only [flattened, List.size_toArray] using previous.isLt
    have previousLastList :
        (groups.flatten[previous.val]'prevInList).virtual_sequence_remaining.getD 0 = 0 := by
      simpa only [flattened, Fin.getElem_fin, List.getElem_toArray] using previousLast
    have nextIs : previous.val + 1 = first.val := by omega
    have nextInRange : previous.val + 1 < groups.flatten.length := by
      rw [nextIs]
      simpa only [flattened, List.size_toArray] using first.isLt
    have nextStarts := rows_after_last groups valid previous.val nextInRange previousLastList
    have nextStartsBytecode : bytecode[first].starts_source = true := by
      simpa only [flattened, Fin.getElem_fin, List.getElem_toArray, nextIs] using nextStarts
    exact nextStartsBytecode

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
  have addressNonzero : image.entry_address ≠ 0 := by
    intro zero
    rw [zero] at found
    simp only [get_first_pc, ↓reduceIte, Option.some.injEq] at found
    exact nonzero found.symm
  obtain ⟨noopSlot, rowSlots, paddingSlots, _⟩ :=
    preprocess_slots bytecode slots preprocessed
  unfold get_first_pc at found
  rw [if_neg addressNonzero, Array.findIdx?_eq_some_iff_getElem] at found
  obtain ⟨inSlots, slotMatches, noEarlierSlot⟩ := found
  have inRows : slot - 1 < bytecode.size := by
    by_contra outside
    have after : bytecode.size < slot := by omega
    have noop := paddingSlots slot after inSlots
    have noopElem := (Array.getElem?_eq_some_iff.mp noop).2
    rw [noopElem] at slotMatches
    exact Bool.false_ne_true slotMatches
  have slotIs : slot = (slot - 1) + 1 := by omega
  have rowSlot := rowSlots (slot - 1) inRows
  rw [← slotIs] at rowSlot
  have rowElem := (Array.getElem?_eq_some_iff.mp rowSlot).2
  rw [rowElem] at slotMatches
  simp only [beq_iff_eq] at slotMatches
  let first : Fin bytecode.size := ⟨slot - 1, inRows⟩
  have firstVal : first.val = slot - 1 := rfl
  have earlier : ∀ position : Fin bytecode.size, position.val < first.val →
      bytecode[position].address ≠ image.entry_address := by
    intro position before same
    have previousSlot := rowSlots position.val position.isLt
    have slotBefore : position.val + 1 < slot := by rw [firstVal] at before; omega
    have previousNotMatch := noEarlierSlot (position.val + 1) slotBefore
    have previousElem := (Array.getElem?_eq_some_iff.mp previousSlot).2
    rw [previousElem] at previousNotMatch
    simp only [beq_iff_eq] at previousNotMatch
    exact previousNotMatch same
  have starts : bytecode[first].starts_source = true := by
    apply first_address_row_starts bytecode ⟨image, expanded⟩ first
    intro position before same
    exact earlier position before (same.trans slotMatches)
  exact ⟨first, slotIs, slotMatches, starts⟩

/-- The initialized device has no output or panic yet, and the supplied input
bytes fit their configured maximum.
For example, before an entry ADDI the output buffer is empty and panic is false.
See jolt/tracer/src/lib.rs (`create_emulator`) and
jolt/common/src/jolt_device.rs (`JoltDevice::new`) at 5def437f. -/
private theorem initial_state_empty_outputs_and_input_bound {Source : Type}
    (joltInstance : JoltInstance Source) (privateInputs : JoltPrivateInputs)
    (state : SailJoltState)
    (built : joltInstance.initial_state privateInputs = some state) :
    state.jolt_device.outputs = #[] ∧ state.jolt_device.panic = false ∧
      joltInstance.inputs.size ≤ joltInstance.memory_config.max_input_size.toNat := by
  unfold JoltInstance.initial_state at built
  rw [bind_some_iff] at built
  obtain ⟨initialLayout, _, built⟩ := built
  dsimp only at built
  split at built
  · cases built
  rw [bind_some_iff] at built
  obtain ⟨_, _, built⟩ := built
  split at built
  · cases built
  rw [bind_some_iff] at built
  obtain ⟨_, _, built⟩ := built
  split at built
  · cases built
  rename_i inputTooLong
  rw [bind_some_iff] at built
  obtain ⟨_, _, built⟩ := built
  cases built
  rw [init_state_jolt_device]
  exact ⟨rfl, rfl, Nat.le_of_not_lt inputTooLong⟩

/-- Initialization leaves output empty and panic false, and its initial RAM
image has zero at the panic word.
For example, before the first ADDI the panic word has not been written.
See jolt/tracer/src/lib.rs (`create_emulator`) and
jolt/common/src/jolt_device.rs (`JoltDevice::new`, `MemoryLayout::try_new`)
at 5def437f. -/
private theorem initialized_device_words {Source : Type}
    (joltInstance : JoltInstance Source) (privateInputs : JoltPrivateInputs)
    (state : SailJoltState)
    (built : joltInstance.initial_state privateInputs = some state) :
    state.jolt_device.outputs = #[] ∧ state.jolt_device.panic = false ∧
      TraceWitness.initialRamWordFromState state
        ((state.jolt_device.memory_layout.panic.toNat -
          JoltConstraints.ramLowestAddress state.jolt_device.memory_layout) / 8) = 0 := by
  let layout := state.jolt_device.memory_layout
  have layoutBuilt : MemoryLayout.new
      {joltInstance.memory_config with program_size := some joltInstance.program.program_size} =
      some layout :=
    (initial_state_device joltInstance privateInputs state built).1
  have adviceFacts := initial_state_advice_below_input joltInstance privateInputs state built
  rw [MemoryLayout.get_lowest_address_toNat] at adviceFacts
  have adviceBelow : state.jolt_device.AdviceBelowInput :=
    ⟨adviceFacts.1, adviceFacts.2.1, adviceFacts.2.2⟩
  obtain ⟨outputsEmpty, panicFalse, inputBound⟩ :=
    initial_state_empty_outputs_and_input_bound joltInstance privateInputs state built
  have inputFits : state.jolt_device.inputs.size ≤ layout.max_input_size.toNat := by
    rw [initial_state_inputs joltInstance privateInputs state built]
    exact inputBound.trans (new_input_size_bound
      {joltInstance.memory_config with program_size := some joltInstance.program.program_size}
      layout layoutBuilt)
  obtain ⟨lowLeInput, _, outputLePanic, _, _⟩ := new_io_ordered _ layout layoutBuilt
  rw [MemoryLayout.get_lowest_address_toNat] at lowLeInput
  change JoltConstraints.ramLowestAddress layout ≤ layout.input_start.toNat at lowLeInput
  have inputAligned := new_input_word_aligned _ layout layoutBuilt
  rw [MemoryLayout.get_lowest_address_toNat] at inputAligned
  change (layout.input_start.toNat - JoltConstraints.ramLowestAddress layout) % 8 = 0
    at inputAligned
  obtain ⟨outputStart, inputMultiple⟩ := new_outputs_after_inputs _ layout layoutBuilt
  obtain ⟨panicStart, outputMultiple, terminationStart, ioEndStart, ioEndBound⟩ :=
    new_io_geometry _ layout layoutBuilt
  have panicOffset : layout.panic.toNat - JoltConstraints.ramLowestAddress layout =
      (layout.input_start.toNat - JoltConstraints.ramLowestAddress layout) +
        layout.max_input_size.toNat + layout.max_output_size.toNat := by
    omega
  have panicAligned :
      (layout.panic.toNat - JoltConstraints.ramLowestAddress layout) % 8 = 0 := by
    rw [panicOffset]
    omega
  have panicAbsolute : JoltConstraints.ramLowestAddress layout +
      8 * ((layout.panic.toNat - JoltConstraints.ramLowestAddress layout) / 8) =
      layout.panic.toNat := by omega
  have afterOutput : layout.output_start.toNat ≤ JoltConstraints.ramLowestAddress layout +
      8 * ((layout.panic.toNat - JoltConstraints.ramLowestAddress layout) / 8) := by
    rw [panicAbsolute]
    exact outputLePanic
  have beforeRam : JoltConstraints.ramLowestAddress layout +
      8 * ((layout.panic.toNat - JoltConstraints.ramLowestAddress layout) / 8) <
      JoltISA.RAM_START_ADDRESS := by
    rw [panicAbsolute]
    omega
  refine ⟨outputsEmpty, panicFalse, ?_⟩
  exact initialRamWord_after_output_zero _ layout layoutBuilt state rfl adviceBelow inputFits
    _ afterOutput beforeRam

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
  obtain ⟨outputsEmpty, panicFalse, panicZero⟩ :=
    initialized_device_words joltInstance privateInputs run.initialState run.initialized
  let layout := run.initialState.jolt_device.memory_layout
  have finalState : TraceWitness.finalTraceState run.toTrace = run.initialState := by
    simp [TraceWitness.finalTraceState, empty]
  have outputOverlay (previous : BitVec 64) :
      TraceWitness.overlayRamBytes layout layout.output_start #[] address previous = previous := by
    unfold TraceWitness.overlayRamBytes
    cases TraceWitness.remapRamAddress layout layout.output_start <;> simp
  have noTermination :
      TraceWitness.remapRamAddress layout layout.termination ≠ some address := by
    intro remapped
    change (if layout.termination.toNat = 0 ∨
        layout.termination.toNat < JoltConstraints.ramLowestAddress layout then none
      else some ((layout.termination.toNat - JoltConstraints.ramLowestAddress layout) / 8)) =
        some address at remapped
    by_cases bad : layout.termination.toNat = 0 ∨
        layout.termination.toNat < JoltConstraints.ramLowestAddress layout
    · simp [bad] at remapped
    · simp only [bad, ↓reduceIte, Option.some.injEq] at remapped
      exact outsideTermination (by simpa [layout] using remapped.symm)
  unfold TraceWitness.finalRamWord
  rw [finalState]
  simp only [outputsEmpty, panicFalse]
  rw [outputOverlay]
  dsimp only [layout] at noTermination
  simp only [Bool.not_false, Bool.true_and, beq_iff_eq]
  rw [if_neg noTermination]
  by_cases atPanic : TraceWitness.remapRamAddress layout layout.panic = some address
  · have initialZero : TraceWitness.initialRamWordFromState run.initialState address = 0 := by
      change (if layout.panic.toNat = 0 ∨
          layout.panic.toNat < JoltConstraints.ramLowestAddress layout then none
        else some ((layout.panic.toNat - JoltConstraints.ramLowestAddress layout) / 8)) =
          some address at atPanic
      by_cases bad : layout.panic.toNat = 0 ∨
          layout.panic.toNat < JoltConstraints.ramLowestAddress layout
      · simp [bad] at atPanic
      · simp only [bad, ↓reduceIte, Option.some.injEq] at atPanic
        simpa [layout, ← atPanic] using panicZero
    dsimp only [layout] at atPanic
    rw [if_pos atPanic]
    exact initialZero.symm
  · dsimp only [layout] at atPanic
    rw [if_neg atPanic]
    rfl

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
