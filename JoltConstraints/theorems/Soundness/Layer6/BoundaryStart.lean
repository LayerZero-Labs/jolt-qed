import JoltConstraints.theorems.Soundness.Layer6.PrefixState
import JoltConstraints.theorems.Soundness.Layer6.BytecodePC
import JoltConstraints.theorems.Soundness.Layer6.PlainRow
import JoltConstraints.theorems.Soundness.Layer3.State

open LeanRV64D

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
`BytecodePCMapper::try_new`) at ff6fc6568. -/
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
  rw [ite_eq_right addressNonzero, Array.findIdx?_eq_some_iff_getElem] at found
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

/-- The instance's initialized state admits an empty run satisfying the boundary
invariant at witness cycle zero. The run's `initialized` certificate identifies
its state with the state supplied by `context.initialized`.
For example, before an entry ADDI, registers and shared RAM agree with
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
    · intro bound address
      have initial := ramVal_initial_state context
        equations.ramValEqInitialPlusPrefixRamInc initialized address
      have final : TraceWitness.finalRamWord run.toTrace address.val =
          TraceWitness.initialRamWordFromState state address.val := by
        simp only [TraceWitness.finalRamWord, TraceWitness.initialRamWordFromState,
          TraceWitness.finalTraceState, run, Array.size_empty, Nat.not_lt_zero, ↓reduceDIte]
      simpa [run] using initial.trans (congrArg (fun word : BitVec 64 => ((word.toNat : Nat) : F)) final.symm)
    · intro full
      have floor := context.traceLengthFloor
      simp [run] at full
      omega
  · intro bound
    have initial := RegisterAgreement.initial equations.registersValEqPrefixRdInc initialized
    simpa [run, TraceWitness.finalTraceState] using
      (initial.toOn (fun register => ¬ IsInstructionTemporary register))
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
    · simpa only [run] using! selected
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
    (notStopped : ∀ last ∈ run.rows.back?, ¬ last.Halts) :
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
    simpa only [first, bytecodeIs] using! atStart
  refine ⟨first, {
    represents := boundary.represents
    real := boundary.real
    noEarlierStop := boundary.noEarlierStop
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
      · simpa only [first] using! step.ready
    notStopped := by intro _; exact notStopped
  }⟩

end JoltInstance
