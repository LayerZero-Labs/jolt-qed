import JoltConstraints.theorems.MemoryRowExecution
import JoltConstraints.theorems.Completeness.Helpers.RamReadSelection
import JoltConstraints.theorems.Soundness.Layer5.RamStore
import JoltConstraints.theorems.Completeness.Helpers.MemoryValueFacts

open LeanRV64D JoltISA
open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail

set_option autoImplicit false

namespace JoltConstraints

open Soundness

/-- An aligned remapped address is its exact byte address on the witness grid.
For example, remapped index three denotes the lowest address plus 24 bytes. -/
private theorem remapped_aligned_address (layout : MemoryLayout) (raw : BitVec 64)
    (index : Nat) (remapped : TraceWitness.remapRamAddress layout raw = some index)
    (aligned : (raw.toNat - ramLowestAddress layout) % 8 = 0) :
    raw.toNat = ramLowestAddress layout + 8 * index := by
  simp only [TraceWitness.remapRamAddress] at remapped
  split at remapped
  · cases remapped
  · rename_i admitted
    have above : ramLowestAddress layout ≤ raw.toNat := by
      unfold ramLowestAddress
      omega
    have indexIs := Option.some.inj remapped
    change (raw.toNat - ramLowestAddress layout) / 8 = index at indexIs
    omega

/-- The accessed doubleword of a selected memory row has the selector's exact
byte address, in both I/O and RAM.
For example, a halfword floor row at effective address ten selects the word at eight. -/
theorem ram_history_accessed_address
    {inst : JoltInstance SourceInstruction} {inputs : JoltPrivateInputs}
    (trace : HonestTrace inst inputs) (valid : ramAccessesValid trace)
    (n : Nat) (inside : n < trace.rows.size) (index : Nat)
    {width : MemoryWidth} {base : Src} {imm : BitVec 64}
    (access : AccessRow trace.bytecode[(trace.rows[n]'inside).rowIndex].instruction
      width base imm)
    (selected : TraceWitness.remappedRamAddress trace n = some index) :
    (width.accessed (sourceValue base (trace.rows[n]'inside).preState + imm)).toNat =
      ramLowestAddress trace.initialState.jolt_device.memory_layout + 8 * index := by
  let row := trace.rows[n]'inside
  let layout := trace.initialState.jolt_device.memory_layout
  let ea := sourceValue base row.preState + imm
  have recorded : TraceWitness.ramAccessAddress trace.bytecode[row.rowIndex].instruction
      row.preState = some (width.recorded ea) := access.ramAccessAddress row.preState
  simp only [row, ea, Fin.getElem_fin] at recorded
  have remapped : TraceWitness.remapRamAddress layout (width.recorded ea) = some index := by
    simpa only [TraceWitness.remappedRamAddress, dite_eq_left inside,
      recorded, Option.bind_some] using selected
  have aligned := valid ⟨n, inside⟩
  change (match TraceWitness.ramAccessAddress trace.bytecode[row.rowIndex].instruction
      row.preState with
    | none => True
    | some address => (address.toNat - ramLowestAddress layout) % 8 = 0) at aligned
  simp only [row, Fin.getElem_fin] at aligned
  rw [recorded] at aligned
  have addressIs := remapped_aligned_address layout (width.recorded ea) index remapped aligned
  have lowAligned : ramLowestAddress layout % 8 = 0 := by
    obtain ⟨built, _⟩ := initial_state_device inst inputs trace.initialState trace.initialized
    simpa only [MemoryLayout.get_lowest_address_toNat, layout, ramLowestAddress] using
      new_lowest_address_aligned _ _ built
  have natural : (width.recorded ea).toNat % 8 = 0 := by omega
  rw [width.recorded_eq_accessed ea (width.aligned_of_recorded ea natural)] at addressIs
  exact addressIs

/-- Every load emitted by a checked expansion has a writable destination.
For example, an architectural load into x0 uses a temporary capture register. -/
private theorem load_destination_writable
    {inst : JoltInstance SourceInstruction} {inputs : JoltPrivateInputs}
    (trace : HonestTrace inst inputs) (slot : Fin trace.bytecode.size)
    {width : MemoryWidth} {destination : Dst} {base : Src} {imm : BitVec 64}
    (load : LoadRow trace.bytecode[slot].instruction width destination base imm) :
    destination.NotX0 := by
  cases destination with
  | vreg register => trivial
  | xreg register =>
    change isX0 register = false
    cases zero : isX0 register with
    | false => rfl
    | true =>
      have noOp := (trace.rowValid slot).x0DestinationIsNoOp register
        load.metadata.destinationIs zero
      obtain ⟨faultClass, fault, same⟩ := load
      rw [same] at noOp
      cases width <;> cases noOp

/-- A selected load's captured read is the pre-state word at its selected index.
For example, loading a gap word uses the same table image as loading a RAM word. -/
theorem ram_history_load_read
    {F : Type} [Field F] (params : WitnessParams)
    {inst : JoltInstance SourceInstruction} {inputs : JoltPrivateInputs}
    (trace : HonestTrace inst inputs) (valid : ramAccessesValid trace)
    (cycle : Fin params.traceLength) (inside : cycle.val < trace.rows.size) (index : Nat)
    {width : MemoryWidth} {destination : Dst} {base : Src} {imm : BitVec 64}
    (load : LoadRow trace.bytecode[(trace.rows[cycle.val]'inside).rowIndex].instruction
      width destination base imm)
    (selected : TraceWitness.remappedRamAddress trace cycle.val = some index) :
    HonestWitness.RamReadValue (F := F) params trace cycle =
      ((Mmu.ram_doubleword (trace.rows[cycle.val]'inside).preState.sail.mem
        (ramLowestAddress trace.initialState.jolt_device.memory_layout + 8 * index)).toNat : F) := by
  let row := trace.rows[cycle.val]'inside
  have captured := load.capture_of_run (load_destination_writable trace row.rowIndex load)
    row.runtimeAdvice row.preState row.postState (trace.row cycle.val inside).executes
  rw [ram_history_accessed_address trace valid cycle.val inside index load.access selected] at captured
  rw [ramReadValue_of_load params trace cycle inside load.metadata.load]
  simp only [TraceWitness.RdWriteValue, dite_eq_left inside]
  change TraceWitness.rdValue (F := F) trace.bytecode[row.rowIndex].instruction row.postState = _
  rw [register42_rdValue_eq_destination, load.metadata.destinationIs]
  simp only
  rw [← register42_capturedDestinationValue, captured]

/-- A captured store read uses the existing pre-state word, without an I/O overlay.
For example, a same-value protected store records the word it leaves unchanged. -/
private theorem ram_history_store_read_value
    {F : Type} [Field F] (params : WitnessParams)
    {inst : JoltInstance SourceInstruction} {inputs : JoltPrivateInputs}
    (trace : HonestTrace inst inputs)
    (cycle : Fin params.traceLength) (inside : cycle.val < trace.rows.size)
    {width : MemoryWidth} {base value : Src} {imm : BitVec 64}
    (store : StoreRow trace.bytecode[(trace.rows[cycle.val]'inside).rowIndex].instruction
      width base value imm) :
    HonestWitness.RamReadValue (F := F) params trace cycle =
      ((Mmu.ram_doubleword (trace.rows[cycle.val]'inside).preState.sail.mem
        (width.accessed (sourceValue base (trace.rows[cycle.val]'inside).preState + imm)).toNat).toNat : F) := by
  have getValue (address : BitVec 64) (present : (trace_doubleword?
        (trace.rows[cycle.val]'inside).preState address).isSome) :
      (trace_doubleword? (trace.rows[cycle.val]'inside).preState address).get present =
        Mmu.ram_doubleword (trace.rows[cycle.val]'inside).preState.sail.mem address.toNat :=
    trace_doubleword_value _ address _ (Option.some_get present).symm
  obtain ⟨fault, same⟩ := store
  simp only [Fin.getElem_fin] at same
  cases width <;>
    simp only [MemoryWidth.store] at same <;>
    simp only [HonestWitness.RamReadValue, dite_eq_left inside, HonestTrace.row,
      same, MemoryWidth.accessed, getValue]
  all_goals split <;> simp_all [getValue]
  all_goals
    rename_i excluded
    exact False.elim (excluded _ _ _ _ rfl rfl rfl rfl)

/-- A selected store's captured read is the old word at its selected index.
For example, an output store records the same old bytes as the shared RAM table. -/
theorem ram_history_store_read
    {F : Type} [Field F] (params : WitnessParams)
    {inst : JoltInstance SourceInstruction} {inputs : JoltPrivateInputs}
    (trace : HonestTrace inst inputs) (valid : ramAccessesValid trace)
    (cycle : Fin params.traceLength) (inside : cycle.val < trace.rows.size) (index : Nat)
    {width : MemoryWidth} {base value : Src} {imm : BitVec 64}
    (store : StoreRow trace.bytecode[(trace.rows[cycle.val]'inside).rowIndex].instruction
      width base value imm)
    (selected : TraceWitness.remappedRamAddress trace cycle.val = some index) :
    HonestWitness.RamReadValue (F := F) params trace cycle =
      ((Mmu.ram_doubleword (trace.rows[cycle.val]'inside).preState.sail.mem
        (ramLowestAddress trace.initialState.jolt_device.memory_layout + 8 * index)).toNat : F) := by
  rw [ram_history_store_read_value params trace cycle inside store,
    ram_history_accessed_address trace valid cycle.val inside index store.access selected]

/-- A selected retired store updates just its selected witness word.
For example, a gap store at index three preserves word four and replaces word three. -/
theorem ram_history_store_word
    {inst : JoltInstance SourceInstruction} {inputs : JoltPrivateInputs}
    (trace : HonestTrace inst inputs) (valid : ramAccessesValid trace)
    (n : Nat) (inside : n < trace.rows.size) (chosen index : Nat)
    {width : MemoryWidth} {base value : Src} {imm : BitVec 64}
    (store : StoreRow trace.bytecode[(trace.rows[n]'inside).rowIndex].instruction
      width base value imm)
    (selected : TraceWitness.remappedRamAddress trace n = some chosen) :
    Mmu.ram_doubleword (trace.rows[n]'inside).postState.sail.mem
        (ramLowestAddress trace.initialState.jolt_device.memory_layout + 8 * index) =
      if index = chosen then sourceValue value (trace.rows[n]'inside).preState
      else Mmu.ram_doubleword (trace.rows[n]'inside).preState.sail.mem
        (ramLowestAddress trace.initialState.jolt_device.memory_layout + 8 * index) := by
  let row := trace.rows[n]'inside
  have runs := (trace.row n inside).executes
  rw [withRuntimeAdvice_eq_of_noAdvice _ row.runtimeAdvice store.metadata.noAdvice] at runs
  have tapeRuns : execWithTapeAnswer
      (trace.bytecode[row.rowIndex].instruction.withRuntimeAdvice row.runtimeAdvice) 0
        row.preState = .ok (.Retire_Success ()) row.postState := by
    rw [withRuntimeAdvice_eq_of_noAdvice _ row.runtimeAdvice store.metadata.noAdvice,
      execWithTapeAnswer_of_ne _ 0 store.access.not_tape]
    exact runs
  rw [store.memory_of_run 0 row.runtimeAdvice row.preState row.postState tapeRuns]
  exact ram_store_index row.preState.sail _ _ _ chosen index
    (ram_history_accessed_address trace valid n inside chosen store.access selected)

/-- A selected row reads the old shared-memory word at its witness index.
For example, a selected load and a selected store use the same pre-state image. -/
theorem ram_history_read_word
    {F : Type} [Field F] (params : WitnessParams)
    {inst : JoltInstance SourceInstruction} {inputs : JoltPrivateInputs}
    (trace : HonestTrace inst inputs) (valid : ramAccessesValid trace)
    (cycle : Fin params.traceLength) (inside : cycle.val < trace.rows.size) (index : Nat)
    (selected : TraceWitness.remappedRamAddress trace cycle.val = some index) :
    HonestWitness.RamReadValue (F := F) params trace cycle =
      ((Mmu.ram_doubleword (trace.rows[cycle.val]'inside).preState.sail.mem
        (ramLowestAddress trace.initialState.jolt_device.memory_layout + 8 * index)).toNat : F) := by
  have selected' := selected
  simp only [TraceWitness.remappedRamAddress, dite_eq_left inside] at selected'
  obtain ⟨address, recorded, _⟩ := Option.bind_eq_some_iff.mp selected'
  obtain ⟨width, base, imm, access⟩ := accessRow_of_address _ _ address recorded
  rcases access with ⟨destination, load⟩ | ⟨value, store⟩
  · exact ram_history_load_read params trace valid cycle inside index load selected
  · exact ram_history_store_read params trace valid cycle inside index store selected

/-- Every retired store selects a RAM witness word; its address cannot be zero.
For example, a floor store at a protected word is selected even if its value is unchanged. -/
private theorem ram_history_store_selected (params : WitnessParams)
    {inst : JoltInstance SourceInstruction} {inputs : JoltPrivateInputs}
    (trace : HonestTrace inst inputs) (fits : params.RamFits trace)
    (cycle : Fin params.traceLength) (inside : cycle.val < trace.rows.size)
    {width : MemoryWidth} {base value : Src} {imm : BitVec 64}
    (store : StoreRow trace.bytecode[(trace.rows[cycle.val]'inside).rowIndex].instruction
      width base value imm) :
    ∃ chosen, TraceWitness.remappedRamAddress trace cycle.val = some chosen := by
  have nonzero : width.recorded
      (sourceValue base (trace.rows[cycle.val]'inside).preState + imm) ≠ 0 := by
    obtain ⟨fault, same⟩ := store
    cases width
    · simpa [MemoryWidth.recorded, MemoryWidth.offsetMask]
        using trace.store_nonzero cycle.val inside base value imm same
    · exact (trace.floor_store_properties cycle.val inside base value imm 0 7 fault
        (by decide) (Or.inl ⟨same, rfl⟩)).2.1
    · exact (trace.floor_store_properties cycle.val inside base value imm 1 6 fault
        (by decide) (Or.inr (Or.inl ⟨same, rfl⟩))).2.1
    · exact (trace.floor_store_properties cycle.val inside base value imm 3 4 fault
        (by decide) (Or.inr (Or.inr ⟨same, rfl⟩))).2.1
  exact ramAccess_remapped_some params trace fits cycle inside _
    (store.access.ramAccessAddress _) nonzero

/-- A store's recorded new word is its pre-state value source.
For example, a floor byte store records the full merged doubleword. -/
private theorem ram_history_store_write
    {F : Type} [Field F] (params : WitnessParams)
    {inst : JoltInstance SourceInstruction} {inputs : JoltPrivateInputs}
    (trace : HonestTrace inst inputs)
    (cycle : Fin params.traceLength) (inside : cycle.val < trace.rows.size)
    {width : MemoryWidth} {base value : Src} {imm : BitVec 64}
    (store : StoreRow trace.bytecode[(trace.rows[cycle.val]'inside).rowIndex].instruction
      width base value imm) :
    TraceWitness.RamWriteValue (F := F) params trace cycle =
      ((sourceValue value (trace.rows[cycle.val]'inside).preState).toNat : F) := by
  obtain ⟨fault, same⟩ := store
  simp only [Fin.getElem_fin] at same
  cases width <;> simp only [MemoryWidth.store] at same <;>
    simp only [TraceWitness.RamWriteValue, dite_eq_left inside, same]

/-- Each executed row changes a shared witness word by its selected RAM increment.
For example, a same-value protected store has zero increment, while a load
preserves every word.
Jolt at `ff6fc6568`: `crates/jolt-witness/src/witnesses/increments.rs` (`RamInc`). -/
theorem ram_history_word_step
    {F : Type} [Field F] (params : WitnessParams)
    {inst : JoltInstance SourceInstruction} {inputs : JoltPrivateInputs}
    (trace : HonestTrace inst inputs) (fits : params.RamFits trace)
    (valid : ramAccessesValid trace) (cycle : Fin params.traceLength)
    (inside : cycle.val < trace.rows.size) (index : Fin params.ramSize) :
    ((Mmu.ram_doubleword (trace.rows[cycle.val]'inside).postState.sail.mem
        (ramLowestAddress trace.initialState.jolt_device.memory_layout + 8 * index.val)).toNat : F) =
      ((Mmu.ram_doubleword (trace.rows[cycle.val]'inside).preState.sail.mem
        (ramLowestAddress trace.initialState.jolt_device.memory_layout + 8 * index.val)).toNat : F) +
        TraceWitness.RamRa params trace index cycle * HonestWitness.RamInc params trace cycle := by
  let row := trace.rows[cycle.val]'inside
  cases storeFlag : JoltMetadata.opcodeFlag trace.bytecode[row.rowIndex].instruction .Store with
  | false =>
    simp only [row, Fin.getElem_fin] at storeFlag
    have patched : JoltMetadata.opcodeFlag
        (trace.bytecode[row.rowIndex].instruction.withRuntimeAdvice row.runtimeAdvice) .Store = false := by
      unfold Instr.withRuntimeAdvice
      split
      · rfl
      · exact storeFlag
    have memory := nonstore_memory _ patched row.preState row.postState _ (trace.row cycle.val inside).executes
    have increment : HonestWitness.RamInc (F := F) params trace cycle = 0 := by
      simp only [HonestWitness.RamInc, dite_eq_left inside,
        JoltMetadata.circuitFlag, Fin.getElem_fin, storeFlag, Bool.false_eq_true, ↓reduceIte]
    rw [memory, increment, mul_zero, add_zero]
  | true =>
    simp only [row, Fin.getElem_fin] at storeFlag
    obtain ⟨width, base, value, imm, store⟩ := storeRow_of_flag _ storeFlag
    obtain ⟨chosen, selected⟩ := ram_history_store_selected params trace fits cycle inside store
    have memory := ram_history_store_word trace valid cycle.val inside chosen index.val store selected
    have read := ram_history_store_read (F := F) params trace valid cycle inside chosen store selected
    have write := ram_history_store_write (F := F) params trace cycle inside store
    have increment : HonestWitness.RamInc (F := F) params trace cycle =
        TraceWitness.RamWriteValue params trace cycle - HonestWitness.RamReadValue params trace cycle := by
      simp only [HonestWitness.RamInc, dite_eq_left inside,
        JoltMetadata.circuitFlag, Fin.getElem_fin, storeFlag, ↓reduceIte]
    rw [memory, increment, write, read]
    by_cases same : index.val = chosen
    · simp only [same, ite_true, TraceWitness.RamRa, selected, ↓reduceIte, one_mul]
      ring
    · simp only [ite_eq_right same, TraceWitness.RamRa, selected,
        show ¬ some chosen = some index.val from fun equal => same (Option.some.inj equal).symm,
        ↓reduceIte, zero_mul, add_zero]

end JoltConstraints
