import JoltConstraints.translation.Constraints.RamAccessCount
import JoltConstraints.theorems.Completeness.Helpers.RamReadSelection
import JoltConstraints.theorems.MemoryRowExecution
import JoltConstraints.translation.honest_witness

open LeanRV64D JoltISA
open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail LeanRV64D.Functions
set_option autoImplicit false
namespace JoltConstraints
open Soundness
open scoped BigOperators

/-- Every memory-flagged instruction records an address.
For example, a floor halfword load records its containing-word address. -/
private theorem memory_flag_has_address (instruction : Instr) (pre : SailJoltState)
    (memory : JoltMetadata.opcodeFlag instruction .Load = true ∨
      JoltMetadata.opcodeFlag instruction .Store = true) :
    ∃ address, TraceWitness.ramAccessAddress instruction pre = some address := by
  have access : ∃ width base imm, AccessRow instruction width base imm := by
    rcases memory with load | store
    · obtain ⟨width, dst, base, imm, row⟩ := loadRow_of_flag instruction load
      exact ⟨width, base, imm, row.access⟩
    · obtain ⟨width, base, value, imm, row⟩ := storeRow_of_flag instruction store
      exact ⟨width, base, imm, row.access⟩
  obtain ⟨width, base, imm, row⟩ := access
  exact ⟨_, row.ramAccessAddress pre⟩

/-- No retired memory row records zero after Jolt's shared-memory guard checks.
For example, a floor load whose containing word is zero fails its MMU read. -/
theorem _root_.HonestTrace.ram_access_nonzero
    {inst : JoltInstance SourceInstruction} {inputs : JoltPrivateInputs}
    (trace : HonestTrace inst inputs) (n : Nat) (inside : n < trace.rows.size)
    (raw : BitVec 64)
    (recorded : TraceWitness.ramAccessAddress trace.bytecode[(trace.rows[n]'inside).rowIndex].instruction
      (trace.rows[n]'inside).preState = some raw) : raw ≠ 0 := by
  intro zero
  subst raw
  obtain ⟨width, base, imm, access⟩ := accessRow_of_address _ _ 0 recorded
  have atZero : width.recorded (sourceValue base (trace.rows[n]'inside).preState + imm) = 0 :=
    Option.some.inj ((access.ramAccessAddress _).symm.trans recorded)
  have aligned : (width.recorded (sourceValue base (trace.rows[n]'inside).preState + imm)).toNat % 8 = 0 := by
    rw [atZero]
    rfl
  have accessed : width.accessed (sourceValue base (trace.rows[n]'inside).preState + imm) = 0 :=
    (width.recorded_eq_accessed _ (width.aligned_of_recorded _ aligned)).symm.trans atZero
  obtain ⟨config, built, aboveEight⟩ := trace.preState_layout n inside
  have runs := (trace.row n inside).executes
  rcases access with ⟨dst, load⟩ | ⟨value, store⟩
  · obtain ⟨result, middle, loaded⟩ := load.load_of_run _ _ _ runs
    rw [accessed, Mmu.load_doubleword_zero _ config built aboveEight] at loaded
    cases loaded
  · have tapeRuns : execWithTapeAnswer
        (trace.bytecode[(trace.rows[n]'inside).rowIndex].instruction.withRuntimeAdvice
          (trace.rows[n]'inside).runtimeAdvice) 0 (trace.rows[n]'inside).preState =
        .ok RETIRE_SUCCESS (trace.rows[n]'inside).postState := by
      rw [withRuntimeAdvice_eq_of_noAdvice _ (trace.rows[n]'inside).runtimeAdvice store.metadata.noAdvice,
        execWithTapeAnswer_of_ne _ 0 store.access.not_tape]
      rw [withRuntimeAdvice_eq_of_noAdvice _ (trace.rows[n]'inside).runtimeAdvice store.metadata.noAdvice] at runs
      exact runs
    obtain ⟨result, stored⟩ := store.store_of_run 0 _ _ _ tapeRuns
    obtain ⟨failure, failed⟩ := Mmu.store_doubleword_zero _ config built aboveEight
      (sourceValue value (trace.rows[n]'inside).preState)
    rw [accessed, failed] at stored
    cases stored

/-- The honest selector sum is exactly one on a load or store and zero otherwise.
For example, a protected same-value store selects its word even with increment zero.
Jolt at `ff6fc6568`: RAM `unbatched_relation`, fourth claim. -/
theorem honestWitness_ramAccessCount {F : Type} [Field F] (params : WitnessParams)
    {inst : JoltInstance SourceInstruction} {inputs : JoltPrivateInputs}
    (trace : HonestTrace inst inputs) (fits : params.RamFits trace) :
    ramAccessCount (HonestTrace.honestWitness (F := F) params trace) := by
  intro t
  change TraceWitness.OpFlags params trace .Load t + TraceWitness.OpFlags params trace .Store t =
    ∑ k : Fin params.ramSize, TraceWitness.RamRa params trace k t
  by_cases inside : t.val < trace.rows.size
  · cases recorded : TraceWitness.ramAccessAddress
      trace.bytecode[(trace.rows[t.val]'inside).rowIndex].instruction (trace.rows[t.val]'inside).preState with
    | none =>
      have noMemory := mt (memory_flag_has_address
        trace.bytecode[(trace.rows[t.val]'inside).rowIndex].instruction
        (trace.rows[t.val]'inside).preState) (by
        rintro ⟨address, atAddress⟩
        rw [recorded] at atAddress
        cases atAddress)
      have notLoad : JoltMetadata.opcodeFlag trace.bytecode[(trace.rows[t.val]'inside).rowIndex].instruction .Load = false :=
        Bool.eq_false_iff.mpr (fun load => noMemory (Or.inl load))
      have notStore : JoltMetadata.opcodeFlag trace.bytecode[(trace.rows[t.val]'inside).rowIndex].instruction .Store = false :=
        Bool.eq_false_iff.mpr (fun store => noMemory (Or.inr store))
      simp only [Fin.getElem_fin] at recorded notLoad notStore
      have remapped : TraceWitness.remappedRamAddress trace t.val = none := by
        simp only [TraceWitness.remappedRamAddress, dite_eq_left inside, recorded, Option.bind_none]
      simp [TraceWitness.OpFlags, JoltMetadata.circuitFlag, inside, notLoad, notStore,
        TraceWitness.RamRa, remapped]
    | some raw =>
      obtain ⟨chosen, selected⟩ := ramAccess_remapped_some params trace fits t inside raw recorded
        (trace.ram_access_nonzero _ inside raw recorded)
      have sum := ramRa_sum_some (F := F) params trace fits t chosen selected (fun _ => 1)
      simp only [mul_one] at sum
      rw [sum]
      obtain ⟨width, base, imm, access⟩ := accessRow_of_address _ _ raw recorded
      rcases access.metadata.1 with ⟨load, store⟩ | ⟨load, store⟩ <;>
        simp only [Fin.getElem_fin] at load store <;>
        simp [TraceWitness.OpFlags, JoltMetadata.circuitFlag, inside, load, store]
  · simp [TraceWitness.OpFlags, inside, TraceWitness.RamRa, TraceWitness.remappedRamAddress]

end JoltConstraints
