import JoltConstraints.Soundness.Layer6.ExecutionPrefix
import JoltConstraints.Soundness.Layer6.BytecodePC
import JoltConstraints.Soundness.Layer3.History
import JoltConstraints.Soundness.Layer3.Access

set_option autoImplicit false

open Sail PreSail LeanRV64D.Functions JoltISA

namespace JoltInstance

/-- Every witness cycle after a nonempty cut at a stable stall has
`RamRa address t * RamInc t = 0` at every RAM word and cycle. Constraint 38
sums this term into `RamValFinal`. The proof tracks the stall's source rows and the values
of their read registers through repeated source executions, then uses the
register and bytecode lookup constraints to exclude stores. Padding also has
zero RAM update. This includes ECALL and MRET, whose expansions have multiple
rows but no stores. -/
theorem soundness_stall_suffix_zero_ram_effects
    {F : Type} [Field F] (joltField : JoltField F)
    (joltInstance : JoltInstance SourceInstruction)
    {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (equations : JoltConstraints.ConstraintEquations context.bytecode context.initialRam
      context.io context.entry witness)
    (run : JoltConstraints.Soundness.UntrustedAnswerRun joltInstance privateInputs)
    (bytecodeEq : run.bytecode = context.bytecode)
    (represented : RepresentsRows witness run.toTrace)
    (nonempty : 0 < run.rows.size)
    (stops : ∀ last ∈ run.rows.back?, last.StableStall) :
    ∀ t : Fin params.traceLength, run.rows.size ≤ t.val →
      ∀ address : Fin params.ramSize,
        witness.RamRa address t * witness.RamInc t = 0 := by
  intro t afterCut address
  have charAbove2pow127 : 2 ^ 127 < ringChar F := by
    have large := joltField
    unfold JoltField at large
    omega
  have lastInBounds : run.rows.size - 1 < run.rows.size := by omega
  let last := run.rows[run.rows.size - 1]'lastInBounds
  have lastIsBack : run.rows.back? = some last := by
    rw [Array.back?_eq_getElem?, Array.getElem?_eq_getElem (by omega)]
  have lastStable : last.StableStall := stops last lastIsBack
  have lastCycleBound : run.rows.size - 1 < params.traceLength := by
    have sizeBound := represented.rowsBound
    omega
  let lastCycle : Fin params.traceLength := ⟨run.rows.size - 1, lastCycleBound⟩
  have lastPC : witness.PC lastCycle = ((last.rowIndex.val + 1 : Nat) : F) := by
    have agrees := represented.pc lastCycle (by dsimp [lastCycle]; omega)
    simpa [TraceWitness.PC, TraceWitness.bytecodePc, lastCycle, last,
      lastInBounds, nonempty] using agrees
  obtain ⟨lastSlot, lastSelected, _⟩ :=
    JoltConstraints.Soundness.bytecodeRa_unique charAbove2pow127 context equations lastCycle
  have lastSlotEq : lastSlot.val = last.rowIndex.val + 1 := by
    have selectedPC := JoltConstraints.Soundness.pc_of_selected_bytecode
      charAbove2pow127 context equations lastCycle lastSlot lastSelected
    have same : (lastSlot.val : F) = ((last.rowIndex.val + 1 : Nat) : F) :=
      selectedPC.symm.trans lastPC
    have slotDomain : 2 ^ params.logBytecodeK ≤ 2 ^ 64 :=
      Nat.pow_le_pow_right (by decide : 0 < 2) params.logBytecodeK_lt_usizeBits.le
    have leftBound : lastSlot.val < ringChar F := by omega
    have rightBound : last.rowIndex.val + 1 < ringChar F := by
      have bytecodeBound := context.bytecodeDomain.rowsFit
      have inBytecode := last.rowIndex.isLt
      have sameSize : run.bytecode.size = context.bytecode.size :=
        congrArg Array.size bytecodeEq
      omega
    exact JoltConstraints.Soundness.natCast_injective_below_char leftBound rightBound same
  have zeroEffectOfNoStore (cycle : Fin params.traceLength)
      (notStore : witness.OpFlags .Store cycle = 0) (word : Fin params.ramSize) :
      witness.RamRa word cycle * witness.RamInc cycle = 0 := by
    by_cases load : witness.OpFlags .Load cycle = 1
    · exact JoltConstraints.Soundness.ram_write_effect_zero_of_load
        charAbove2pow127 context equations cycle load word
    · obtain ⟨slot, selected, _⟩ :=
        JoltConstraints.Soundness.bytecodeRa_unique charAbove2pow127 context equations cycle
      have value := JoltConstraints.Soundness.opFlag_of_selected_bytecode charAbove2pow127
        context equations .Load cycle slot selected
      have binary : witness.OpFlags .Load cycle = 0 := by
        cases present : JoltConstraints.bytecodeRow context.bytecode slot.val with
        | none => simpa [JoltConstraints.bytecodeCircuitFlag, present] using value
        | some row =>
          by_cases active : JoltMetadata.circuitFlag row .Load = true
          · have one : witness.OpFlags .Load cycle = 1 := by
              simpa [JoltConstraints.bytecodeCircuitFlag, present, active] using value
            exact False.elim (load one)
          · simpa [JoltConstraints.bytecodeCircuitFlag, present, active] using value
      exact (JoltConstraints.Soundness.ram_zero_effects charAbove2pow127 context equations
        cycle (JoltConstraints.Soundness.ramAddress_zero_of_not_load_store
          equations.ramAddrEqZeroIfNotLoadStore cycle binary notStore)).2.2 word
  by_cases padding : witness.InstructionFlags .IsNoop t = 1
  · exact (JoltConstraints.Soundness.ram_zero_effects charAbove2pow127 context equations t
      (JoltConstraints.Soundness.ramAddress_zero_of_padding charAbove2pow127
        context equations t padding)).2.2 address
  · apply zeroEffectOfNoStore t _ address
    sorry

/-- The cut prefix is nonempty and ends at a stable stall, including when its
last row is the witness's last cycle. Later witness rows have zero RAM updates,
so final RAM agrees outside the termination word. -/
theorem soundness_stopping {F : Type} [Field F] (joltField : JoltField F)
    (joltInstance : JoltInstance SourceInstruction)
    (assumptions : joltInstance.SoundnessAssumptions)
    (restrictions : joltInstance.TemporaryRestrictions)
    {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (equations : JoltConstraints.ConstraintEquations context.bytecode context.initialRam
      context.io context.entry witness)
    (run : JoltConstraints.Soundness.UntrustedAnswerRun joltInstance privateInputs)
    (bytecodeEq : run.bytecode = context.bytecode)
    (represented : RepresentsPrefix witness run.toTrace)
    (realRows : ∀ t : Fin params.traceLength,
      t.val < run.rows.size → witness.InstructionFlags .IsNoop t = 0)
    (noEarlierStop : ∀ (i : Nat) (current next : TraceRow run.bytecode),
      run.rows[i]? = some current → run.rows[i + 1]? = some next →
      ¬ current.StableStall)
    (cut : run.rows.size = params.traceLength ∨
      ∃ bound : run.rows.size < params.traceLength,
        witness.InstructionFlags .IsNoop ⟨run.rows.size, bound⟩ = 1 ∨
        ∃ last ∈ run.rows.back?, last.StableStall)
    (advice : ∀ n : Fin run.rows.size,
      run.rows[n].someTracerAdvice? =
        honestTracerAdviceAtStepN joltInstance.program run.rows n) :
    (∀ last ∈ run.rows.back?, last.StableStall) ∧
    0 < run.rows.size ∧
    (∀ address : Fin params.ramSize,
      address.val ≠ (run.initialState.jolt_device.memory_layout.termination.toNat -
        JoltConstraints.ramLowestAddress run.initialState.jolt_device.memory_layout) / 8 →
      witness.RamValFinal address =
        ((TraceWitness.finalRamWord run.toTrace address.val).toNat : F)) := by
  have suffixZero (stops : ∀ last ∈ run.rows.back?, last.StableStall)
      (nonempty : 0 < run.rows.size) :
      ∀ t : Fin params.traceLength, run.rows.size ≤ t.val →
        ∀ address : Fin params.ramSize,
          witness.RamRa address t * witness.RamInc t = 0 :=
    soundness_stall_suffix_zero_ram_effects joltField joltInstance privateInputs
      witness context equations run bytecodeEq represented.toRepresentsRows nonempty stops
  have finalFromCut (stops : ∀ last ∈ run.rows.back?, last.StableStall)
      (nonempty : 0 < run.rows.size) :
      ∀ address : Fin params.ramSize,
        address.val ≠ (run.initialState.jolt_device.memory_layout.termination.toNat -
          JoltConstraints.ramLowestAddress run.initialState.jolt_device.memory_layout) / 8 →
        witness.RamValFinal address =
          ((TraceWitness.finalRamWord run.toTrace address.val).toNat : F) := by
    intro address nonTermination
    by_cases below : run.rows.size < params.traceLength
    · have atCut := represented.cutRam.1 below address nonTermination
      have sameFinal := JoltConstraints.Soundness.ramVal_eq_final_of_suffix_zero
        equations.ramValEqInitialPlusPrefixRamInc
        equations.ramValFinalEqInitialPlusRamInc address ⟨run.rows.size, below⟩
        (fun cycle later => suffixZero stops nonempty cycle later address)
      exact sameFinal.symm.trans atCut
    · have equal : run.rows.size = params.traceLength := by
        exact Nat.le_antisymm represented.rowsBound (Nat.le_of_not_gt below)
      exact represented.cutRam.2 equal address nonTermination
  sorry

end JoltInstance
