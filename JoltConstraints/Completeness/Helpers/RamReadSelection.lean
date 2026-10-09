import JoltConstraints.Constraints.RamReadData
import JoltConstraints.Completeness.Helpers.RamAccesses
import JoltConstraints.Completeness.Helpers.IOSetupFrame
import JoltConstraints.Completeness.Helpers.JumpReturnProofHelpers

set_option autoImplicit false

namespace JoltConstraints

open scoped BigOperators

-- Every recorded pre-state has a layout Rust's MemoryLayout::new built, with the
-- lowest address above 8 (validate_inputs).
theorem _root_.HonestTrace.preState_layout {joltInstance : JoltInstance SourceInstruction}
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

-- An LD row at address 0 captures 0 as the value it loads.
theorem _root_.HonestTrace.load_zero_captured {joltInstance : JoltInstance SourceInstruction}
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
  cases dst with
  | vreg register => exact jump_write_capture (.vreg register) 0 _ _ trivial written
  | xreg register =>
    by_cases zeroRegister : JoltISA.isX0 register = true
    · -- x0 always reads 0
      obtain ⟨bits⟩ := register
      unfold JoltISA.isX0 at zeroRegister
      simp only [decide_eq_true_eq] at zeroRegister
      unfold TraceWitness.capturedDestinationValue TraceWitness.capturedDestination
        JoltISA.sourceValue
      dsimp only
      rw [zeroRegister]
    · exact jump_write_capture (.xreg register) 0 _ _ (by simpa using zeroRegister) written

-- No SD row stores at address 0.
theorem _root_.HonestTrace.store_nonzero {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (i : Nat) (inTrace : i < trace.rows.size) (base value : JoltISA.Src) (imm : BitVec 64)
    (isStore : trace.bytecode[(getElem trace.rows i inTrace).rowIndex].instruction =
      .SD base value imm) :
    JoltISA.sourceValue base (getElem trace.rows i inTrace).preState + imm ≠ 0 := by
  obtain ⟨config, built, aboveEight⟩ := trace.preState_layout i inTrace
  have runs := (trace.row i inTrace).executes
  rw [withRuntimeAdvice_store _ base value imm isStore] at runs
  exact execInstr_store_nonzero base value imm _ _ config built aboveEight runs

-- Every memory access in an honest trace is a whole number of 64-bit words above the
-- lowest address: LD and SD retire only at multiples of 8, and the lowest address is one.
theorem _root_.HonestTrace.ram_accesses_valid {joltInstance : JoltInstance SourceInstruction}
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
    · cases accesses

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

-- A row that accesses address 0 is a load of 0, since no SD row stores there, so its
-- read and write values are 0.
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
  unfold TraceWitness.ramAccessAddress at atZero
  split at atZero
  · -- an LD loads 0
    rename_i faultClass dst base imm isLoad
    have loaded := trace.load_zero_captured t.val ht faultClass dst base imm isLoad
      (Option.some.inj atZero)
    -- the read and write values are both the loaded value
    have readZero : HonestWitness.RamReadValue (F := F) params trace t = 0 := by
      unfold HonestWitness.RamReadValue
      rw [dif_pos ht]
      dsimp only
      split
      · rw [isLoad]
        simp [TraceWitness.rdValue, loaded]
      · rename_i storeIs
        rw [isLoad] at storeIs
        cases storeIs
      · rfl
    have writeZero : TraceWitness.RamWriteValue (F := F) params trace t = 0 := by
      unfold TraceWitness.RamWriteValue
      rw [dif_pos ht]
      dsimp only
      rw [isLoad]
      simp [TraceWitness.rdValue, loaded]
    exact ⟨readZero, writeZero⟩
  · -- no SD stores at address 0
    rename_i base value imm isStore
    exact absurd (Option.some.inj atZero) (trace.store_nonzero t.val ht base value imm isStore)
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

/-- The captured write value differs from the read value only on stores. -/
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
    case h_3 =>
      rename_i bad
      exact False.elim (bad _ _ _ _ rfl rfl rfl rfl)
  · simp [TraceWitness.RamWriteValue, HonestWitness.RamReadValue,
      HonestWitness.RamInc, ht]

end JoltConstraints
