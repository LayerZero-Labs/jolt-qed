import JoltConstraints.Soundness.Layer6.RowStepKinds
import JoltConstraints.Soundness.Layer7.TerminationStore

/-! Staged execution of one row in a source expansion without internal advice. -/

set_option autoImplicit false

namespace JoltInstance

open JoltConstraints JoltConstraints.Soundness
open Sail PreSail LeanRV64D.Functions JoltISA

/-- Appending a row without runtime advice preserves honest advice at every
position: old advice depends only on its prefix and the new value is none.
For example, adding an AND after a DIV does not change the DIV's honest quotient.
See jolt/tracer/src/instruction/mod.rs (`trace_inline_sequence_with_advice`)
at 5def437f. -/
theorem honestAdvice_push (program : Rv64ProgramImage SourceInstruction)
    {bytecode : Array JoltInstructionRow} (rows : Array (TraceRow bytecode))
    (step : TraceRow bytecode)
    (honest : ∀ n : Fin rows.size, rows[n].someTracerAdvice? =
      honestTracerAdviceAtStepN program rows n)
    (absent : bytecode[step.rowIndex].instruction.adviceValue? = none) :
    ∀ n : Fin (rows.push step).size, (rows.push step)[n].someTracerAdvice? =
      honestTracerAdviceAtStepN program (rows.push step) n := by
  intro n
  by_cases old : n.val < rows.size
  · have unchanged := honestTracerAdviceAtStepN_extract program (rows.push step) rows.size n.val
      (by simp) old
    rw [Array.extract_push_of_le (Nat.le_refl _), Array.extract_size] at unchanged
    rw [show (rows.push step)[n] = rows[n.val] from Array.getElem_push_lt old]
    exact (honest ⟨n.val, old⟩).trans unchanged
  · have last : n.val = rows.size := by have inside := n.isLt; simp only [Array.size_push] at inside; omega
    apply runtimeAdvice_agrees_of_noAdvice
    simpa only [Fin.getElem_fin, last, Array.getElem_push_eq] using absent

private theorem row_extension {F : Type} [Field F] (joltField : JoltField F)
    {inst : JoltInstance SourceInstruction} {params : WitnessParams} {inputs : JoltPrivateInputs}
    (assumptions : inst.SoundnessAssumptions) (restrictions : inst.TemporaryRestrictions)
    (witness : WitnessType F params) (context : ConstraintContext inst inputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
    (run : UntrustedAnswerRun inst inputs) (first : Fin context.bytecode.size) (done : Nat)
    (state : ExpansionState witness context run first done)
    (unfinished : done < expansionRowCount context.bytecode first)
    (honest : ∀ n : Fin run.rows.size, run.rows[n].someTracerAdvice? =
      honestTracerAdviceAtStepN inst.program run.rows n)
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
    plain | ⟨fault, destination, base, imm, kind⟩ | ⟨base, source, imm, kind⟩ |
      kind | ⟨destination, imm, kind⟩ | ⟨destination, base, imm, kind⟩
  · apply plain_row_step joltField witness context equations run first done state unfinished bound
    intro row member
    have same := Option.some.inj (atRow.symm.trans member)
    simpa only [← same] using plain
  · by_cases inRam : RAM_START_ADDRESS ≤ (sourceValue base pre + imm).toNat
    · exact ld_ram_row_step joltField assumptions restrictions witness context equations run first done
        state unfinished honest bound next pre indexIs ready registers kind inRam
    · exact ld_device_row_step joltField assumptions restrictions witness context equations run first done
        state unfinished honest bound next pre indexIs ready registers kind (by omega)
  · by_cases inRam : RAM_START_ADDRESS ≤ (sourceValue base pre + imm).toNat
    · exact sd_ram_row_step joltField assumptions restrictions witness context equations run first done
        state unfinished honest bound next pre indexIs ready registers kind inRam
    · exact sd_device_row_step joltField assumptions restrictions witness context equations run first done
        state unfinished honest bound next pre indexIs ready registers kind (by omega)
  · exact host_row_step joltField assumptions restrictions witness context equations run first done
      state unfinished honest bound next pre indexIs ready registers kind
      (terminal (by rw [kind]; rfl))
  · exact jal_row_step joltField assumptions restrictions witness context equations run first done
      state unfinished honest bound next pre indexIs ready registers pc nextPC kind
      (terminal (by rw [kind]; rfl))
  · exact jalr_row_step joltField assumptions restrictions witness context equations run first done
      state unfinished honest bound next pre indexIs ready registers pc nextPC kind
      (terminal (by rw [kind]; rfl))

/-- Append one row of an unfinished source with no VirtualAdvice, preserving
the expansion invariant and honest advice throughout the extended run.
For example, SLL's first row writes temporary 40, which becomes live for its
second row; no hypothesis equates that temporary before its first write. -/
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
    (honestAdvice : ∀ n : Fin run.rows.size, run.rows[n].someTracerAdvice? =
      honestTracerAdviceAtStepN joltInstance.program run.rows n)
    (noAdvice : ¬ ExpansionHasAdvice context.bytecode first) :
    ∃ run' : UntrustedAnswerRun joltInstance privateInputs,
      RunExtends run run' ∧ run'.rows.size = run.rows.size + 1 ∧
      ExpansionState witness context run' first (done + 1) ∧
      (∀ n : Fin run'.rows.size, run'.rows[n].someTracerAdvice? =
        honestTracerAdviceAtStepN joltInstance.program run'.rows n) := by
  obtain ⟨bound, _⟩ := state.next unfinished
  obtain ⟨step, answer, candidate, indexIs, _, _, traceEq, _, _, _, _, extendsRun, size, after⟩ :=
    row_extension joltField assumptions restrictions witness context equations run first done
      state unfinished honestAdvice bound
  have bytecodeEq : run.bytecode = context.bytecode :=
    Option.some.inj (run.expands.symm.trans context.expands)
  have absent : run.bytecode[step.rowIndex].instruction.adviceValue? = none := by
    by_contra advice
    apply noAdvice
    refine ⟨done, unfinished, run.bytecode[step.rowIndex], ?_, advice⟩
    rw [← indexIs, ← bytecodeEq]
    exact Array.getElem?_eq_getElem step.rowIndex.isLt
  refine ⟨candidate, extendsRun, size, after, ?_⟩
  change (fun trace : Trace => ∀ n : Fin trace.rows.size, trace.rows[n].someTracerAdvice? =
    honestTracerAdviceAtStepN joltInstance.program trace.rows n) candidate.toTrace
  rw [traceEq]
  exact honestAdvice_push joltInstance.program run.rows step honestAdvice absent

end JoltInstance
