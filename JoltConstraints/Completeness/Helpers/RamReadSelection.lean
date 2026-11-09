import JoltConstraints.Constraints.RamReadData
import JoltConstraints.Completeness.Helpers.RamAccesses
import JoltConstraints.Completeness.Helpers.IOSetupFrame
import JoltConstraints.Completeness.Helpers.LookupWriteProofHelpers
import JoltConstraints.Completeness.Helpers.FloorMemory
import JoltConstraints.Completeness.Helpers.MemoryValueFacts

open LeanRV64D

set_option autoImplicit false

open JoltConstraints

-- Every recorded pre-state has a layout Rust's MemoryLayout::new built, with the
-- lowest address above 8 (validate_inputs).
theorem HonestTrace.preState_layout {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (i : Nat) (inTrace : i < trace.rows.size) :
    ∃ config, MemoryLayout.new config =
        some (getElem trace.rows i inTrace).preState.jolt_device.memory_layout ∧
      8 < (getElem trace.rows i inTrace).preState.jolt_device.memory_layout.get_lowest_address.toNat := by
  have sameLayout := (trace_preState_ioSame trace i inTrace).1
  obtain ⟨initialLayout, _⟩ :=
    initial_state_device joltInstance privateInputs trace.initialState trace.initialized
  have valid := trace.valid_inputs
  unfold JoltInstance.validate_inputs at valid
  rw [initialLayout] at valid
  simp only [Bool.and_eq_true, decide_eq_true_eq] at valid
  rw [sameLayout]
  exact ⟨_, initialLayout, valid.1.1⟩

/-- Retiring after a write of zero captures zero even for x0, which always
reads zero; for example, a load from the zero address captures zero in x0.
Jolt's tracer: `tracer/src/instruction/floor_access.rs` (`load`) at `c6703570`. -/
private theorem captured_zero_retire (dst : JoltISA.Dst) (pre post : SailJoltState)
    (runs : (do JoltISA.writeDst dst 0; pure LeanRV64D.Functions.RETIRE_SUCCESS) pre =
      .ok (.Retire_Success ()) post) :
    TraceWitness.capturedDestinationValue dst post = 0 := by
  cases dst with
  | vreg register => exact lookup_write_retire (.vreg register) 0 pre post trivial runs
  | xreg register =>
    by_cases zeroRegister : JoltISA.isX0 register = true
    · obtain ⟨bits⟩ := register
      unfold JoltISA.isX0 at zeroRegister
      simp only [decide_eq_true_eq] at zeroRegister
      unfold TraceWitness.capturedDestinationValue TraceWitness.capturedDestination
        JoltISA.sourceValue
      dsimp only
      rw [zeroRegister]
      rfl
    · exact lookup_write_retire (.xreg register) 0 pre post (by simpa using! zeroRegister) runs

/-- An LD row at address zero captures zero, including when its destination is x0.
For example, LD from base zero with immediate zero reads the special zero word.
Jolt's tracer: `tracer/src/instruction/ld.rs` (`LD::exec`) at `c6703570`. -/
theorem HonestTrace.load_zero_captured {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (i : Nat) (inTrace : i < trace.rows.size) (faultClass : JoltISA.LoadFaultClass)
    (dst : JoltISA.Dst) (base : JoltISA.Src) (imm : BitVec 64)
    (isLoad : trace.bytecode[(getElem trace.rows i inTrace).rowIndex].instruction =
      .LD faultClass dst base imm)
    (atZero : JoltISA.sourceValue base (getElem trace.rows i inTrace).preState + imm = 0) :
    TraceWitness.capturedDestinationValue dst (getElem trace.rows i inTrace).postState = 0 := by
  obtain ⟨config, built, aboveEight⟩ := trace.preState_layout i inTrace
  have runs := (trace.row i inTrace).executes
  rw [withRuntimeAdvice_load _ faultClass dst base imm isLoad] at runs
  have written := execInstr_load_zero faultClass dst base imm _ _ config built aboveEight atZero runs
  apply captured_zero_retire dst (trace.rows[i].preState) (trace.rows[i].postState)
  simp only [bind, EStateM.bind]
  rw [written]
  rfl

-- No SD row stores at address 0.
theorem HonestTrace.store_nonzero {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (i : Nat) (inTrace : i < trace.rows.size) (base value : JoltISA.Src) (imm : BitVec 64)
    (isStore : trace.bytecode[(getElem trace.rows i inTrace).rowIndex].instruction =
      .SD base value imm) :
    JoltISA.sourceValue base (getElem trace.rows i inTrace).preState + imm ≠ 0 := by
  obtain ⟨config, built, aboveEight⟩ := trace.preState_layout i inTrace
  have runs := (trace.row i inTrace).executes
  rw [withRuntimeAdvice_store _ base value imm isStore] at runs
  exact execInstr_store_nonzero base value imm _ _ config built aboveEight runs

/-- A computation that returns ran its first step without an error: if `first >>= next`
returns from state `pre`, so does `first`.
For example, a retired floor load ran its doubleword load without an error. -/
theorem bind_ok_first {ε σ α β : Type} (first : EStateM ε σ α) (next : α → EStateM ε σ β)
    (pre post : σ) (value : β) (ran : (first >>= next) pre = .ok value post) :
    ∃ result middle, first pre = .ok result middle := by
  cases firstRan : first pre with
  | ok result middle => exact ⟨result, middle, rfl⟩
  | error failure middle =>
    simp only [bind, EStateM.bind, firstRan] at ran
    cases ran

/-- A doubleword load that returns at an address `address` at or above `RAM_START_ADDRESS`
read below the layout's `heap_end`: Jolt's tracer asserts that the start address is below
it.
For example, a load at `heap_end` itself fails the assertion.
See jolt/tracer/src/emulator/mmu.rs (`Mmu::load_doubleword`, `assert_effective_address`)
at c6703570. -/
theorem JoltISA.Mmu.load_doubleword_below_heap_end (address : BitVec 64) (state : SailJoltState)
    (inRam : JoltISA.RAM_START_ADDRESS ≤ address.toNat)
    (loaded : ∃ result after, JoltISA.Mmu.load_doubleword address state = .ok result after) :
    address.toNat < state.jolt_device.memory_layout.heap_end.toNat := by
  obtain ⟨result, after, loaded⟩ := loaded
  unfold JoltISA.Mmu.load_doubleword at loaded
  simp only [if_pos inRam] at loaded
  split at loaded
  · cases loaded
  · split at loaded
    · rename_i valid
      simpa only [JoltISA.Mmu.effective_address_ok, if_neg (Nat.not_lt.mpr inRam),
        Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq] using valid
    · cases loaded

/-- A doubleword store that returns at an address `address` at or above
`RAM_START_ADDRESS` wrote below the layout's `heap_end`: Jolt's tracer asserts that the
start address is below it.
For example, a store at `heap_end` itself fails the assertion.
See jolt/tracer/src/emulator/mmu.rs (`Mmu::store_doubleword`, `assert_effective_address`)
at c6703570. -/
theorem JoltISA.Mmu.store_doubleword_below_heap_end (address value : BitVec 64)
    (state : SailJoltState) (inRam : JoltISA.RAM_START_ADDRESS ≤ address.toNat)
    (stored : ∃ result after, JoltISA.Mmu.store_doubleword address value state = .ok result after) :
    address.toNat < state.jolt_device.memory_layout.heap_end.toNat := by
  obtain ⟨result, after, stored⟩ := stored
  unfold JoltISA.Mmu.store_doubleword at stored
  simp only [if_pos inRam] at stored
  split at stored
  · cases stored
  · split at stored
    · rename_i valid
      simp only [JoltISA.Mmu.effective_address_ok, if_neg (Nat.not_lt.mpr inRam),
        ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at valid
      exact valid.2
    · cases stored

/-- An LD that retires ran its doubleword load at `base + imm` without an error.
For example, `LD x5, 8(x6)` with `x6 = 0x80000000` ran the load at `0x80000008`.
See jolt/tracer/src/instruction/ld.rs (`LD::exec`) at c6703570. -/
theorem execInstr_load_access (faultClass : JoltISA.LoadFaultClass) (dst : JoltISA.Dst)
    (base : JoltISA.Src) (imm : BitVec 64) (state after : SailJoltState)
    (runs : JoltISA.execInstr (.LD faultClass dst base imm) state =
      .ok (.Retire_Success ()) after) :
    ∃ result middle,
      JoltISA.Mmu.load_doubleword (JoltISA.sourceValue base state + imm) state = .ok result middle := by
  simp only [JoltISA.execInstr] at runs
  have step := lookup_read_bind base _ state after _ runs
  split at step
  · exact bind_ok_first _ _ _ _ _ step
  · cases step

/-- An SD that retires ran its doubleword store at `base + imm` without an error.
For example, `SD x5, 8(x6)` with `x6 = 0x80000000` ran the store at `0x80000008`.
See jolt/tracer/src/instruction/sd.rs (`SD::exec`) at c6703570. -/
theorem execInstr_store_access (base value : JoltISA.Src) (imm : BitVec 64)
    (state after : SailJoltState)
    (runs : JoltISA.execInstr (.SD base value imm) state = .ok (.Retire_Success ()) after) :
    ∃ result middle,
      JoltISA.Mmu.store_doubleword (JoltISA.sourceValue base state + imm)
        (JoltISA.sourceValue value state) state = .ok result middle := by
  simp only [JoltISA.execInstr] at runs
  have step := lookup_read_bind base _ state after _ runs
  have stored := lookup_read_bind value _ state after _ step
  split at stored
  · exact bind_ok_first _ _ _ _ _ stored
  · cases stored

/-- A retired floor load records an aligned doubleword, captures zero when that recorded
address is zero, and reads below `heap_end` when the recorded address is in RAM (at or
above `RAM_START_ADDRESS`); for example, LoadH at ea 2 reads word zero.
Jolt's tracer: `tracer/src/instruction/floor_access.rs` (`load`, `addresses`)
at `c6703570`. -/
theorem HonestTrace.floor_load_properties {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (i : Nat) (ht : i < trace.rows.size) (faultClass : JoltISA.LoadFaultClass)
    (dst : JoltISA.Dst) (base : JoltISA.Src) (imm mask offset : BitVec 64) (fault : ExceptionType)
    (partition : mask ||| offset = 7)
    (selected : (trace.bytecode[(trace.rows[i]'ht).rowIndex].instruction =
        .VirtualLoadB faultClass dst base imm fault ∧ mask = 0) ∨
      (trace.bytecode[(trace.rows[i]'ht).rowIndex].instruction =
        .VirtualLoadH faultClass dst base imm fault ∧ mask = 1) ∨
      (trace.bytecode[(trace.rows[i]'ht).rowIndex].instruction =
        .VirtualLoadW faultClass dst base imm fault ∧ mask = 3)) :
    let ea := JoltISA.sourceValue base (trace.rows[i]'ht).preState + imm
    (ea - (ea &&& offset)).toNat % 8 = 0 ∧
      (ea - (ea &&& offset) = 0 →
        TraceWitness.capturedDestinationValue dst (trace.rows[i]'ht).postState = 0) ∧
      (JoltISA.RAM_START_ADDRESS ≤ (ea - (ea &&& offset)).toNat →
        (ea - (ea &&& offset)).toNat <
          (trace.rows[i]'ht).preState.jolt_device.memory_layout.heap_end.toNat) := by
  obtain ⟨config, built, aboveEight⟩ := trace.preState_layout i ht
  have facts := floor_load_access _ faultClass dst base imm mask fault selected
    (trace.row i ht).runtimeAdvice _ _ (trace.row i ht).executes
  dsimp only [HonestTrace.row] at facts
  have recorded := floor_recorded_address _ mask offset partition facts.1
  refine ⟨?_, ?_, ?_⟩
  · rw [recorded]
    exact toNat_mod_eight _ (align_down_8_and_7_eq_zero _)
  · intro zero
    rw [recorded] at zero
    have access := facts.2
    rw [zero] at access
    simp only [bind, EStateM.bind,
      JoltISA.Mmu.load_doubleword_zero _ config built aboveEight] at access
    exact captured_zero_retire dst _ _ access
  · intro inRam
    rw [recorded] at inRam ⊢
    exact JoltISA.Mmu.load_doubleword_below_heap_end _ _ inRam
      (bind_ok_first _ _ _ _ _ facts.2)

/-- A retired floor store records a nonzero aligned doubleword, and writes below
`heap_end` when the recorded address is in RAM (at or above `RAM_START_ADDRESS`); for
example, StoreB at ea 9 records 8, while a store into word zero cannot retire.
Jolt's tracer: `tracer/src/instruction/floor_access.rs` (`store`, `addresses`)
at `c6703570`. -/
theorem HonestTrace.floor_store_properties {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (i : Nat) (ht : i < trace.rows.size) (base value : JoltISA.Src)
    (imm mask offset : BitVec 64) (fault : ExceptionType) (partition : mask ||| offset = 7)
    (selected : (trace.bytecode[(trace.rows[i]'ht).rowIndex].instruction =
        .VirtualStoreB base value imm fault ∧ mask = 0) ∨
      (trace.bytecode[(trace.rows[i]'ht).rowIndex].instruction =
        .VirtualStoreH base value imm fault ∧ mask = 1) ∨
      (trace.bytecode[(trace.rows[i]'ht).rowIndex].instruction =
        .VirtualStoreW base value imm fault ∧ mask = 3)) :
    let ea := JoltISA.sourceValue base (trace.rows[i]'ht).preState + imm
    (ea - (ea &&& offset)).toNat % 8 = 0 ∧ ea - (ea &&& offset) ≠ 0 ∧
      (JoltISA.RAM_START_ADDRESS ≤ (ea - (ea &&& offset)).toNat →
        (ea - (ea &&& offset)).toNat <
          (trace.rows[i]'ht).preState.jolt_device.memory_layout.heap_end.toNat) := by
  obtain ⟨config, built, aboveEight⟩ := trace.preState_layout i ht
  have facts := floor_store_access _ base value imm mask fault selected
    (trace.row i ht).runtimeAdvice _ _ (trace.row i ht).executes
  dsimp only [HonestTrace.row] at facts
  have recorded := floor_recorded_address _ mask offset partition facts.1
  refine ⟨?_, ?_, ?_⟩
  · rw [recorded]
    exact toNat_mod_eight _ (align_down_8_and_7_eq_zero _)
  · intro zero
    rw [recorded] at zero
    have access := facts.2
    obtain ⟨failure, fails⟩ := JoltISA.Mmu.store_doubleword_zero
      (trace.rows[i]'ht).preState config built aboveEight (JoltISA.sourceValue value (trace.rows[i].preState))
    rw [zero] at access
    simp only [bind, EStateM.bind] at access
    rw [fails] at access
    cases access
  · intro inRam
    rw [recorded] at inRam ⊢
    exact JoltISA.Mmu.store_doubleword_below_heap_end _ _ _ inRam
      (bind_ok_first _ _ _ _ _ facts.2)

/-- Each recorded RAM address lies on the doubleword grid used by the RAM witness.
Native rows retire at multiples of eight; floor rows record their containing word,
for example LoadH at effective address ten records eight.
Jolt's tracer: `tracer/src/instruction/floor_access.rs` (`addresses`) at `c6703570`. -/
theorem HonestTrace.ram_accesses_valid {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs) :
    ramAccessesValid trace := by
  intro i
  have lowestAligned := initial_state_lowest_address_aligned joltInstance privateInputs
    trace.initialState trace.initialized
  rw [MemoryLayout.get_lowest_address_toNat] at lowestAligned
  dsimp only
  split
  · trivial
  · rename_i address accesses
    unfold TraceWitness.ramAccessAddress at accesses
    split at accesses
    · -- LD
      rename_i faultClass dst base imm isLoad
      have aligned := (trace.row i.val i.isLt).load_aligned faultClass dst base imm isLoad
      dsimp only [HonestTrace.row] at aligned
      cases accesses
      unfold ramLowestAddress
      omega
    · -- SD
      rename_i base value imm isStore
      have aligned := (trace.row i.val i.isLt).store_aligned base value imm isStore
      dsimp only [HonestTrace.row] at aligned
      cases accesses
      unfold ramLowestAddress
      omega
    · rename_i faultClass dst base imm fault selected
      have aligned := (trace.floor_load_properties i.val i.isLt faultClass dst base imm
        0 7 fault rfl (Or.inl ⟨selected, rfl⟩)).1
      cases accesses
      unfold ramLowestAddress
      omega
    · rename_i base value imm fault selected
      have aligned := (trace.floor_store_properties i.val i.isLt base value imm
        0 7 fault rfl (Or.inl ⟨selected, rfl⟩)).1
      cases accesses
      unfold ramLowestAddress
      omega
    · rename_i faultClass dst base imm fault selected
      have aligned := (trace.floor_load_properties i.val i.isLt faultClass dst base imm
        1 6 fault rfl (Or.inr (Or.inl ⟨selected, rfl⟩))).1
      cases accesses
      unfold ramLowestAddress
      omega
    · rename_i base value imm fault selected
      have aligned := (trace.floor_store_properties i.val i.isLt base value imm
        1 6 fault rfl (Or.inr (Or.inl ⟨selected, rfl⟩))).1
      cases accesses
      unfold ramLowestAddress
      omega
    · rename_i faultClass dst base imm fault selected
      have aligned := (trace.floor_load_properties i.val i.isLt faultClass dst base imm
        3 4 fault rfl (Or.inr (Or.inr ⟨selected, rfl⟩))).1
      cases accesses
      unfold ramLowestAddress
      omega
    · rename_i base value imm fault selected
      have aligned := (trace.floor_store_properties i.val i.isLt base value imm
        3 4 fault rfl (Or.inr (Or.inr ⟨selected, rfl⟩))).1
      cases accesses
      unfold ramLowestAddress
      omega
    · cases accesses

/-- Every RAM address the honest trace records (`TraceRow.ram_address`) at or above
`RAM_START_ADDRESS` is below the starting layout's `heap_end`: each LD, SD and floor row
retired its doubleword access, and Jolt's tracer asserts that an access in RAM starts
below `heap_end`.
For example, an SD at `heap_end - 8` can be recorded, but no row records `heap_end`.
See jolt/tracer/src/emulator/mmu.rs (`assert_effective_address`) and
jolt/tracer/src/instruction/floor_access.rs (`addresses`) at c6703570. -/
theorem HonestTrace.ram_address_below_heap_end {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (i : Nat) (inTrace : i < trace.rows.size) (address : Nat)
    (touches : (trace.rows[i]'inTrace).ram_address = some address)
    (inRam : JoltISA.RAM_START_ADDRESS ≤ address) :
    address < trace.initialState.jolt_device.memory_layout.heap_end.toNat := by
  rw [← (trace_preState_ioSame trace i inTrace).1]
  have runs := (trace.row i inTrace).executes
  dsimp only [HonestTrace.row] at runs
  unfold TraceRow.ram_address at touches
  split at touches
  · rename_i faultClass dst base imm isLoad
    cases touches
    rw [withRuntimeAdvice_load _ faultClass dst base imm isLoad] at runs
    exact JoltISA.Mmu.load_doubleword_below_heap_end _ _ inRam
      (execInstr_load_access faultClass dst base imm _ _ runs)
  · rename_i base value imm isStore
    cases touches
    rw [withRuntimeAdvice_store _ base value imm isStore] at runs
    exact JoltISA.Mmu.store_doubleword_below_heap_end _ _ _ inRam
      (execInstr_store_access base value imm _ _ runs)
  · rename_i faultClass dst base imm fault selected
    cases touches
    exact (trace.floor_load_properties i inTrace faultClass dst base imm 0 7 fault rfl
      (Or.inl ⟨selected, rfl⟩)).2.2 inRam
  · rename_i base value imm fault selected
    cases touches
    exact (trace.floor_store_properties i inTrace base value imm 0 7 fault rfl
      (Or.inl ⟨selected, rfl⟩)).2.2 inRam
  · rename_i faultClass dst base imm fault selected
    cases touches
    exact (trace.floor_load_properties i inTrace faultClass dst base imm 1 6 fault rfl
      (Or.inr (Or.inl ⟨selected, rfl⟩))).2.2 inRam
  · rename_i base value imm fault selected
    cases touches
    exact (trace.floor_store_properties i inTrace base value imm 1 6 fault rfl
      (Or.inr (Or.inl ⟨selected, rfl⟩))).2.2 inRam
  · rename_i faultClass dst base imm fault selected
    cases touches
    exact (trace.floor_load_properties i inTrace faultClass dst base imm 3 4 fault rfl
      (Or.inr (Or.inr ⟨selected, rfl⟩))).2.2 inRam
  · rename_i base value imm fault selected
    cases touches
    exact (trace.floor_store_properties i inTrace base value imm 3 4 fault rfl
      (Or.inr (Or.inr ⟨selected, rfl⟩))).2.2 inRam
  · cases touches

namespace JoltConstraints

open scoped BigOperators

/-- A missing RAM address has no hot selector. -/
theorem ramRa_sum_none {F : Type} [Field F] (params : WitnessParams)
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (ramFits : params.RamFits trace)
    (t : Fin params.traceLength)
    (hnone : TraceWitness.remappedRamAddress trace t.val = none)
    (value : Fin params.ramSize → F) :
    (∑ address : Fin params.ramSize,
      TraceWitness.RamRa params trace address t * value address) = 0 := by
  simp [TraceWitness.RamRa, hnone]

/-- A present RAM address selects precisely its remapped word. -/
theorem ramRa_sum_some {F : Type} [Field F] (params : WitnessParams)
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (ramFits : params.RamFits trace)
    (t : Fin params.traceLength) (b : Nat)
    (hsome : TraceWitness.remappedRamAddress trace t.val = some b)
    (value : Fin params.ramSize → F) :
    (∑ address : Fin params.ramSize,
      TraceWitness.RamRa params trace address t * value address) =
      value ⟨b, params.remappedRamAddress_lt trace ramFits t b hsome⟩ := by
  let selected : Fin params.ramSize :=
    ⟨b, params.remappedRamAddress_lt trace ramFits t b hsome⟩
  have hsel : ∀ address : Fin params.ramSize,
      (some b = some address.val) ↔ address = selected := by
    intro address
    simp [selected, Fin.ext_iff, eq_comm]
  simp_rw [TraceWitness.RamRa, hsome, hsel]
  simp [Finset.sum_ite_eq', selected]

/-- A recorded memory access at a nonzero address has a hot RAM selector. -/
theorem ramAccess_remapped_some (params : WitnessParams)
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (ramFits : params.RamFits trace)
    (t : Fin params.traceLength) (ht : t.val < trace.rows.size)
    (raw : BitVec 64)
    (hraw : TraceWitness.ramAccessAddress
      (getElem trace.bytecode (getElem trace.rows t.val ht).rowIndex.val
        (getElem trace.rows t.val ht).rowIndex.isLt).instruction
      (getElem trace.rows t.val ht).preState = some raw)
    (nonzero : raw ≠ 0) :
    ∃ b, TraceWitness.remappedRamAddress trace t.val = some b := by
  have hf := ramFits ⟨t.val, ht⟩
  have hf' : raw = 0 ∨ ∃ b : Nat,
      TraceWitness.remapRamAddress trace.initialState.jolt_device.memory_layout raw = some b ∧
      b < params.ramSize := by
    simpa only [hraw] using hf
  rcases hf' with hz | ⟨b, hremap, _⟩
  · exact False.elim (nonzero hz)
  · refine ⟨b, ?_⟩
    simp [TraceWitness.remappedRamAddress, ht, hraw, hremap]

/-- A memory row recording address zero has zero RAM read and write cells.
Stores cannot retire there; for example, LoadH at effective address two reads
the special zero doubleword and leaves it unchanged.
Jolt's tracer: `tracer/src/instruction/floor_access.rs` (`load`, `store`) at `c6703570`. -/
theorem ramValues_zero_at_zero {F : Type} [Field F]
    (params : WitnessParams) {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (trace : HonestTrace joltInstance privateInputs) (t : Fin params.traceLength)
    (ht : t.val < trace.rows.size)
    (atZero : TraceWitness.ramAccessAddress
      (getElem trace.bytecode (getElem trace.rows t.val ht).rowIndex.val
        (getElem trace.rows t.val ht).rowIndex.isLt).instruction
      (getElem trace.rows t.val ht).preState = some 0) :
    HonestWitness.RamReadValue (F := F) params trace t = 0 ∧
      TraceWitness.RamWriteValue (F := F) params trace t = 0 := by
  have loadZero
      (load : JoltMetadata.opcodeFlag trace.bytecode[(trace.rows[t.val]'ht).rowIndex].instruction
        .Load = true) (rd : TraceWitness.RdWriteValue (F := F) params trace t = 0) :
      HonestWitness.RamReadValue (F := F) params trace t = 0 ∧
        TraceWitness.RamWriteValue (F := F) params trace t = 0 :=
    ⟨(ramReadValue_of_load params trace t ht load).trans rd,
      (ramWriteValue_of_load params trace t ht load).trans rd⟩
  unfold TraceWitness.ramAccessAddress at atZero
  split at atZero
  · rename_i faultClass dst base imm selected
    have loaded := trace.load_zero_captured t.val ht faultClass dst base imm selected
      (Option.some.inj atZero)
    apply loadZero
    · simp [selected, JoltMetadata.opcodeFlag]
    · simp [TraceWitness.RdWriteValue, TraceWitness.rdValue, ht, selected, loaded]
  · rename_i base value imm selected
    exact False.elim ((trace.store_nonzero t.val ht base value imm selected)
      (Option.some.inj atZero))
  · rename_i faultClass dst base imm fault selected
    have property := (trace.floor_load_properties t.val ht faultClass dst base imm
      0 7 fault rfl (Or.inl ⟨selected, rfl⟩)).2.1
    have loaded := property (Option.some.inj atZero)
    apply loadZero
    · simp [selected, JoltMetadata.opcodeFlag]
    · simp [TraceWitness.RdWriteValue, TraceWitness.rdValue, ht, selected, loaded]
  · rename_i base value imm fault selected
    have property := (trace.floor_store_properties t.val ht base value imm
      0 7 fault rfl (Or.inl ⟨selected, rfl⟩)).2.1
    exact False.elim (property (Option.some.inj atZero))
  · rename_i faultClass dst base imm fault selected
    have property := (trace.floor_load_properties t.val ht faultClass dst base imm
      1 6 fault rfl (Or.inr (Or.inl ⟨selected, rfl⟩))).2.1
    have loaded := property (Option.some.inj atZero)
    apply loadZero
    · simp [selected, JoltMetadata.opcodeFlag]
    · simp [TraceWitness.RdWriteValue, TraceWitness.rdValue, ht, selected, loaded]
  · rename_i base value imm fault selected
    have property := (trace.floor_store_properties t.val ht base value imm
      1 6 fault rfl (Or.inr (Or.inl ⟨selected, rfl⟩))).2.1
    exact False.elim (property (Option.some.inj atZero))
  · rename_i faultClass dst base imm fault selected
    have property := (trace.floor_load_properties t.val ht faultClass dst base imm
      3 4 fault rfl (Or.inr (Or.inr ⟨selected, rfl⟩))).2.1
    have loaded := property (Option.some.inj atZero)
    apply loadZero
    · simp [selected, JoltMetadata.opcodeFlag]
    · simp [TraceWitness.RdWriteValue, TraceWitness.rdValue, ht, selected, loaded]
  · rename_i base value imm fault selected
    have property := (trace.floor_store_properties t.val ht base value imm
      3 4 fault rfl (Or.inr (Or.inr ⟨selected, rfl⟩))).2.1
    exact False.elim (property (Option.some.inj atZero))
  · cases atZero

theorem ramReadValue_zero_of_noaccess {F : Type} [Field F]
    (params : WitnessParams) {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (trace : HonestTrace joltInstance privateInputs) (t : Fin params.traceLength)
    (ht : t.val < trace.rows.size)
    (hnoaccess : TraceWitness.ramAccessAddress
      (getElem trace.bytecode (getElem trace.rows t.val ht).rowIndex.val
        (getElem trace.rows t.val ht).rowIndex.isLt).instruction
      (getElem trace.rows t.val ht).preState = none) :
    HonestWitness.RamReadValue (F := F) params trace t = 0 := by
  cases hi : (getElem trace.bytecode (getElem trace.rows t.val ht).rowIndex.val
    (getElem trace.rows t.val ht).rowIndex.isLt).instruction <;>
    simp [TraceWitness.ramAccessAddress, hi] at hnoaccess
  all_goals simp [HonestWitness.RamReadValue, ht, hi]

theorem ramWriteValue_zero_of_noaccess {F : Type} [Field F]
    (params : WitnessParams) {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (trace : HonestTrace joltInstance privateInputs) (t : Fin params.traceLength)
    (ht : t.val < trace.rows.size)
    (hnoaccess : TraceWitness.ramAccessAddress
      (getElem trace.bytecode (getElem trace.rows t.val ht).rowIndex.val
        (getElem trace.rows t.val ht).rowIndex.isLt).instruction
      (getElem trace.rows t.val ht).preState = none) :
    TraceWitness.RamWriteValue (F := F) params trace t = 0 := by
  cases hi : (getElem trace.bytecode (getElem trace.rows t.val ht).rowIndex.val
    (getElem trace.rows t.val ht).rowIndex.isLt).instruction <;>
    simp [TraceWitness.ramAccessAddress, hi] at hnoaccess
  all_goals simp [TraceWitness.RamWriteValue, ht, hi]

theorem ramReadValue_zero_of_remapped_none {F : Type} [Field F]
    (params : WitnessParams) {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (trace : HonestTrace joltInstance privateInputs) (ramFits : params.RamFits trace)
    (t : Fin params.traceLength)
    (hnone : TraceWitness.remappedRamAddress trace t.val = none) :
    HonestWitness.RamReadValue (F := F) params trace t = 0 := by
  by_cases ht : t.val < trace.rows.size
  · cases ha : TraceWitness.ramAccessAddress
      (getElem trace.bytecode (getElem trace.rows t.val ht).rowIndex.val
        (getElem trace.rows t.val ht).rowIndex.isLt).instruction
      (getElem trace.rows t.val ht).preState with
    | none => exact ramReadValue_zero_of_noaccess params trace t ht ha
    | some raw =>
        by_cases zero : raw = 0
        · -- address 0: a load of 0
          subst zero
          exact (ramValues_zero_at_zero params trace t ht ha).1
        · -- any other address has a hot selector
          obtain ⟨b, hb⟩ := ramAccess_remapped_some params trace ramFits t ht raw ha zero
          rw [hnone] at hb
          contradiction
  · simp [HonestWitness.RamReadValue, ht]

theorem ramWriteValue_zero_of_remapped_none {F : Type} [Field F]
    (params : WitnessParams) {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (trace : HonestTrace joltInstance privateInputs) (ramFits : params.RamFits trace)
    (t : Fin params.traceLength)
    (hnone : TraceWitness.remappedRamAddress trace t.val = none) :
    TraceWitness.RamWriteValue (F := F) params trace t = 0 := by
  by_cases ht : t.val < trace.rows.size
  · cases ha : TraceWitness.ramAccessAddress
      (getElem trace.bytecode (getElem trace.rows t.val ht).rowIndex.val
        (getElem trace.rows t.val ht).rowIndex.isLt).instruction
      (getElem trace.rows t.val ht).preState with
    | none => exact ramWriteValue_zero_of_noaccess params trace t ht ha
    | some raw =>
        by_cases zero : raw = 0
        · -- address 0: a load of 0
          subst zero
          exact (ramValues_zero_at_zero params trace t ht ha).2
        · -- any other address has a hot selector
          obtain ⟨b, hb⟩ := ramAccess_remapped_some params trace ramFits t ht raw ha zero
          rw [hnone] at hb
          contradiction
  · simp [TraceWitness.RamWriteValue, ht]

/-- A RAM write cell equals its read cell plus the store increment.
For example, replacing word three by five gives increment two; loads give zero.
Jolt's prover: `crates/jolt-witness/src/witnesses/increments.rs` (`RamInc`) at `c6703570`. -/
theorem ramWriteValue_eq_read_add_inc {F : Type} [Field F]
    (params : WitnessParams) {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (trace : HonestTrace joltInstance privateInputs) (t : Fin params.traceLength) :
    TraceWitness.RamWriteValue (F := F) params trace t =
      HonestWitness.RamReadValue params trace t +
        HonestWitness.RamInc params trace t := by
  by_cases ht : t.val < trace.rows.size
  · cases hi : (getElem trace.bytecode (getElem trace.rows t.val ht).rowIndex.val
      (getElem trace.rows t.val ht).rowIndex.isLt).instruction
    all_goals simp [TraceWitness.RamWriteValue, HonestWitness.RamReadValue,
      HonestWitness.RamInc, JoltMetadata.circuitFlag, hi, ht]
    all_goals split <;> simp_all [JoltMetadata.opcodeFlag]
    all_goals
      rename_i excluded
      first
      | exact False.elim (excluded _ _ _ _ rfl rfl rfl rfl)
      | exact False.elim (excluded _ _ _ _ _ rfl rfl rfl rfl rfl)
  · simp [TraceWitness.RamWriteValue, HonestWitness.RamReadValue,
      HonestWitness.RamInc, ht]

end JoltConstraints
