import JoltConstraints.Soundness.Layer6.RowStepKinds
import JoltConstraints.Soundness.Layer7.TerminationStore

open LeanRV64D

/-! Staged execution of one row in a source expansion without built-in internal advice. -/

set_option autoImplicit false

namespace JoltInstance

open JoltConstraints JoltConstraints.Soundness
open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail LeanRV64D LeanRV64D.Functions JoltISA

/-- A VirtualAdvice row appended inside an inline expansion is an inline advice step:
the expansion's first row, `done` rows back, belongs to a registered inline.
For example, the first VirtualAdvice row of a SECP256K1_MULQ call is an inline advice
step, so `BuiltinAdviceHonest` leaves its word unconstrained.
See jolt/tracer/src/instruction/inline.rs (`INLINE::trace_sequence`) at a6b6dc717. -/
theorem inline_expansion_step_flag (program : Rv64ProgramImage SourceInstruction)
    {bytecode : Array JoltInstructionRow} (rows : Array (TraceRow bytecode))
    (step : TraceRow bytecode) (first done : Nat) (retained : done ≤ rows.size)
    (ordered : ∀ offset < done,
      ∃ row ∈ rows[rows.size - done + offset]?, row.rowIndex.val = first + offset)
    (indexIs : step.rowIndex.val = first + done)
    (starts : ∀ row ∈ bytecode[first]?, row.starts_source = true)
    (later : ∀ k, 0 < k → k ≤ done → ∀ row ∈ bytecode[first + k]?, row.starts_source = false)
    (inline : ∀ row ∈ bytecode[first]?, ∃ key rs1 rs2 rs3,
      program.instructionAt row.address = some (.inline key rs1 rs2 rs3))
    (advice : bytecode[step.rowIndex].instruction.adviceValue? ≠ none) :
    stepNOfTraceIsInlineAdvice program (rows.push step) rows.size = true := by
  have pushed : ∀ k ≤ done, ∃ row ∈ (rows.push step)[rows.size - done + k]?,
      row.rowIndex.val = first + k := by
    intro k within
    by_cases old : k < done
    · obtain ⟨row, atRow, index⟩ := ordered k old
      refine ⟨row, ?_, index⟩
      rw [Array.getElem?_push, ite_eq_right (by omega)]
      exact atRow
    · have same : k = done := by omega
      subst k
      refine ⟨step, ?_, indexIs⟩
      rw [show rows.size - done + done = rows.size by omega]
      exact Array.getElem?_push_size
  have bytecodeAt : ∀ (row : TraceRow bytecode) (k : Nat), row.rowIndex.val = first + k →
      bytecode[first + k]? = some bytecode[row.rowIndex] := by
    intro row k index
    rw [← index]
    exact Array.getElem?_eq_getElem row.rowIndex.isLt
  have startFlag : ∀ k ≤ done, stepNOfTraceIsStartOfNewExpansion (rows.push step)
      (rows.size - done + k) = bytecode[first + k]?.any (·.starts_source) := by
    intro k within
    obtain ⟨row, atRow, index⟩ := pushed k within
    unfold stepNOfTraceIsStartOfNewExpansion
    rw [Option.mem_def.mp atRow, bytecodeAt row k index]
    rfl
  have startEq : startOfExpansionContainingStepN (rows.push step) rows.size =
      rows.size - done := by
    have segment := expansion_start_of_segment (rows.push step) (rows.size - done) done
      (by
        rw [← Nat.add_zero (rows.size - done), startFlag 0 (Nat.zero_le _)]
        cases atFirst : bytecode[first + 0]? with
        | none => exact absurd atFirst (by
            obtain ⟨row, _, index⟩ := pushed 0 (Nat.zero_le _)
            rw [bytecodeAt row 0 index]
            simp)
        | some row => simpa using starts row (by simpa using atFirst))
      (by
        intro k positive within
        rw [startFlag k within]
        cases atK : bytecode[first + k]? with
        | none => rfl
        | some row => simpa using later k positive within row atK)
    rwa [show rows.size - done + done = rows.size by omega] at segment
  obtain ⟨firstRow, firstAt, firstIndex⟩ := pushed 0 (Nat.zero_le _)
  rw [Nat.add_zero] at firstAt firstIndex
  obtain ⟨key, rs1, rs2, rs3, source⟩ := inline bytecode[firstRow.rowIndex]
    (by simpa using bytecodeAt firstRow 0 (by simpa using firstIndex))
  unfold stepNOfTraceIsInlineAdvice stepNOfTraceIsAdvice
  rw [startEq, Option.mem_def.mp firstAt, Array.getElem?_push_size]
  simp only [Option.bind_some, source, Bool.and_true]
  exact Option.isSome_iff_ne_none.mpr advice

private theorem row_extension {F : Type} [Field F] (joltField : JoltField F)
    {inst : JoltInstance SourceInstruction} {params : WitnessParams} {inputs : JoltPrivateInputs}
    (assumptions : inst.SoundnessAssumptions) (restrictions : inst.TemporaryRestrictions)
    (witness : WitnessType F params) (context : ConstraintContext inst inputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
    (run : UntrustedAnswerRun inst inputs) (first : Fin context.bytecode.size) (done : Nat)
    (state : ExpansionState witness context run first done)
    (unfinished : done < expansionRowCount context.bytecode first)
    (honest : BuiltinAdviceHonest inst.program run.rows)
    (bound : run.rows.size < params.traceLength) :
    PlainRowExtension witness context run first done bound := by
  have bytecodeEq : run.bytecode = context.bytecode :=
    Option.some.inj (run.expands.symm.trans context.expands)
  obtain ⟨_, _, next, pre, slot, indexIs, _, _, entry⟩ := state.next unfinished
  have ready : RawRowEntry run next pre := entry
  have registers := (rawEntry_prepared ready (state.registers bound)).1
  obtain ⟨pc, nextPC⟩ := ready.prepared_pc
  have atRow : context.bytecode[first.val + done]? = some run.bytecode[next] := by
    rw [← indexIs, ← bytecodeEq]
    exact Array.getElem?_eq_getElem next.isLt
  have terminal (nonordinary : ExpansionFacts.ordinary run.bytecode[next].instruction = false) :=
    expansion_nonordinary_terminal inst.program context.bytecode context.expands first state.starts
      done unfinished _ atRow nonordinary
  rcases row_kind run.bytecode[next].instruction with
    plain | ⟨width, destination, base, imm, kind⟩ | ⟨width, base, source, imm, kind⟩ |
      kind | ⟨destination, imm, kind⟩ | ⟨destination, base, imm, kind⟩
  · apply plain_row_step joltField witness context equations run first done state unfinished bound
    intro row member
    have same := Option.some.inj (atRow.symm.trans member)
    simpa only [← same] using plain
  · exact append_load_row joltField assumptions restrictions witness context equations run first done
      state unfinished honest bound next pre indexIs ready registers kind
  · exact append_store_row joltField assumptions restrictions witness context equations run first done
      state unfinished honest bound next pre indexIs ready registers kind
  · exact host_row_step joltField assumptions restrictions witness context equations run first done
      state unfinished honest bound next pre indexIs ready registers kind
      (terminal (by rw [kind]; rfl))
  · exact jal_row_step joltField assumptions restrictions witness context equations run first done
      state unfinished honest bound next pre indexIs ready registers pc nextPC kind
      (terminal (by rw [kind]; rfl))
  · exact jalr_row_step joltField assumptions restrictions witness context equations run first done
      state unfinished honest bound next pre indexIs ready registers pc nextPC kind
      (terminal (by rw [kind]; rfl))

/-- Append one row of an unfinished source that is a registered inline or has no
VirtualAdvice, preserving the expansion invariant and built-in advice honesty.
For example, SLL's first row writes temporary 40, which becomes live for its
second row; no hypothesis equates that temporary before its first write. An inline's
VirtualAdvice row records the witness's word, which `BuiltinAdviceHonest` leaves free. -/
theorem row_step {F : Type} [Field F] (joltField : JoltField F)
    (joltInstance : JoltInstance SourceInstruction)
    (assumptions : joltInstance.SoundnessAssumptions)
    (restrictions : joltInstance.TemporaryRestrictions)
    {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (equations : JoltConstraints.ConstraintEquations context.bytecode context.initialRam
      context.io context.entry witness)
    (run : UntrustedAnswerRun joltInstance privateInputs)
    (first : Fin context.bytecode.size) (done : Nat)
    (state : ExpansionState witness context run first done)
    (unfinished : done < expansionRowCount context.bytecode first)
    (honestAdvice : BuiltinAdviceHonest joltInstance.program run.rows)
    (adviceFree : ¬ ExpansionHasAdvice context.bytecode first ∨
      ExpansionIsInline joltInstance.program context.bytecode first) :
    ∃ run' : UntrustedAnswerRun joltInstance privateInputs,
      RunExtends run run' ∧ run'.rows.size = run.rows.size + 1 ∧
      ExpansionState witness context run' first (done + 1) ∧
      BuiltinAdviceHonest joltInstance.program run'.rows := by
  obtain ⟨bound, _⟩ := state.next unfinished
  obtain ⟨step, answer, candidate, indexIs, _, _, traceEq, _, _, _, _, extendsRun, size, after⟩ :=
    row_extension joltField assumptions restrictions witness context equations run first done
      state unfinished honestAdvice bound
  have bytecodeEq : run.bytecode = context.bytecode :=
    Option.some.inj (run.expands.symm.trans context.expands)
  refine ⟨candidate, extendsRun, size, after, ?_⟩
  change (fun trace : Trace => BuiltinAdviceHonest joltInstance.program trace.rows) candidate.toTrace
  rw [traceEq]
  by_cases absent : run.bytecode[step.rowIndex].instruction.adviceValue? = none
  · exact BuiltinAdviceHonest.push_noAdvice joltInstance.program run.rows step honestAdvice absent
  have bytecodeAt : context.bytecode[first.val + done]? = some run.bytecode[step.rowIndex] := by
    rw [← indexIs, ← bytecodeEq]
    exact Array.getElem?_eq_getElem step.rowIndex.isLt
  have inline : ExpansionIsInline joltInstance.program context.bytecode first := by
    rcases adviceFree with noAdvice | inline
    · exact absurd ⟨done, unfinished, run.bytecode[step.rowIndex], bytecodeAt, absent⟩ noAdvice
    · exact inline
  obtain ⟨key, rs1, rs2, rs3, source⟩ := inline
  apply BuiltinAdviceHonest.push joltInstance.program run.rows step honestAdvice
  intro notInline
  rw [inline_expansion_step_flag joltInstance.program run.rows step first.val done
    state.retained state.ordered indexIs] at notInline
  · cases notInline
  · rw [bytecodeEq, Array.getElem?_eq_getElem first.isLt]
    intro row member
    rw [← Option.some.inj member]
    exact state.starts
  · rw [bytecodeEq]
    intro k positive within row atRow
    exact expansion_later_not_start joltInstance.program context.bytecode context.expands
      first state.starts k positive (by omega) row atRow
  · rw [bytecodeEq, Array.getElem?_eq_getElem first.isLt]
    intro row member
    rw [← Option.some.inj member]
    exact ⟨key, rs1, rs2, rs3, source⟩
  · exact absent

end JoltInstance
