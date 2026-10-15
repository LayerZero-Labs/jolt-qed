import JoltConstraints.prover_config
import JoltConstraints.witness_params

set_option autoImplicit false

namespace ExecutionDimensions

private def BoundsFor (addresses : List Nat) : Option (Nat × Nat) → Prop
  | none => ∀ address ∈ addresses, address = 0
  | some (lo, hi) => lo ∈ addresses ∧ hi ∈ addresses ∧ lo ≠ 0 ∧ hi ≠ 0 ∧
      ∀ address ∈ addresses, address = 0 ∨ (lo ≤ address ∧ address ≤ hi)

private theorem boundsFor_observe (addresses : List Nat) (bounds : Option (Nat × Nat))
    (valid : BoundsFor addresses bounds) (address : Nat) :
    BoundsFor (addresses ++ [address]) (observe bounds address) := by
  by_cases zero : address = 0
  · subst address
    cases bounds with
    | none =>
      simp only [observe, BoundsFor, List.mem_append, List.mem_singleton]
      intro a member
      exact member.elim (valid a) id
    | some pair =>
      rcases pair with ⟨lo, hi⟩
      obtain ⟨loMem, hiMem, loNonzero, hiNonzero, bounded⟩ := valid
      simp only [observe, BoundsFor, List.mem_append, List.mem_singleton]
      refine ⟨Or.inl loMem, Or.inl hiMem, loNonzero, hiNonzero, ?_⟩
      intro a member
      exact member.elim (bounded a) Or.inl
  · cases bounds with
    | none =>
      simp only [BoundsFor] at valid
      simp only [observe, if_neg zero, BoundsFor, List.mem_append, List.mem_singleton]
      refine ⟨Or.inr trivial, Or.inr trivial, zero, zero, ?_⟩
      intro a member
      rcases member with member | rfl
      · exact Or.inl (valid a member)
      · exact Or.inr ⟨le_rfl, le_rfl⟩
    | some pair =>
      rcases pair with ⟨lo, hi⟩
      obtain ⟨loMem, hiMem, loNonzero, hiNonzero, bounded⟩ := valid
      simp only [observe, if_neg zero, BoundsFor, List.mem_append, List.mem_singleton]
      refine ⟨?_, ?_, by omega, by omega, ?_⟩
      · by_cases h : lo ≤ address
        · exact Or.inl (by simpa [min_eq_left h] using loMem)
        · exact Or.inr (min_eq_right (by omega))
      · by_cases h : hi ≤ address
        · exact Or.inr (max_eq_right h)
        · exact Or.inl (by simpa [max_eq_left (by omega : address ≤ hi)] using hiMem)
      · intro a member
        rcases member with member | rfl
        · rcases bounded a member with rfl | bounds
          · exact Or.inl rfl
          · exact Or.inr ⟨by omega, by omega⟩
        · exact Or.inr ⟨by omega, by omega⟩

private theorem boundsFor_fold (addresses : List Nat) :
    BoundsFor addresses (addresses.foldl observe none) := by
  induction addresses using List.reverseRecOn with
  | nil => simp [BoundsFor]
  | append_singleton addresses address ih =>
    simpa only [List.foldl_append, List.foldl_cons, List.foldl_nil] using
      boundsFor_observe addresses _ ih address

/-- The streaming bounds and the old address scan agree after checked remapping. -/
theorem checkedTouched_fold (addresses : List Nat) (layout : MemoryLayout) (touched : Nat)
    (checked : ProverConfig.checkedTouched (addresses.foldl observe none) layout = some touched) :
    (∀ address ∈ addresses, address = 0 ∨ layout.get_lowest_address.toNat ≤ address) ∧
    (addresses.filterMap (remap_address layout)).max?.getD 0 = touched := by
  have valid := boundsFor_fold addresses
  cases bounds : addresses.foldl observe none with
  | none =>
    rw [bounds] at valid checked
    simp only [BoundsFor] at valid
    cases checked
    refine ⟨fun a member => Or.inl (valid a member), ?_⟩
    have empty : addresses.filterMap (remap_address layout) = [] := by
      apply List.filterMap_eq_nil_iff.mpr
      intro a member
      simp [remap_address, valid a member]
    simp [empty]
  | some pair =>
    rcases pair with ⟨lo, hi⟩
    rw [bounds] at valid checked
    obtain ⟨_, hiMem, _, hiNonzero, bounded⟩ := valid
    simp only [ProverConfig.checkedTouched, bind_some_iff] at checked
    obtain ⟨loOffset, loChecked, hiOffset, hiChecked, result⟩ := checked
    obtain ⟨_, loAbove⟩ := checkedSub_some loChecked
    obtain ⟨rfl, _⟩ := checkedSub_some hiChecked
    cases result
    refine ⟨?_, ?_⟩
    · intro a member
      rcases bounded a member with rfl | bounds
      · exact Or.inl rfl
      · exact Or.inr (by omega)
    · have largest : (addresses.filterMap (remap_address layout)).max? =
          some ((hi - layout.get_lowest_address.toNat) / 8) := by
        apply List.max?_eq_some_iff.mpr
        refine ⟨?_, ?_⟩
        · exact List.mem_filterMap.mpr ⟨hi, hiMem, by simp [remap_address, hiNonzero]⟩
        · intro slot member
          obtain ⟨a, aMem, remapped⟩ := List.mem_filterMap.mp member
          unfold remap_address at remapped
          split at remapped
          · cases remapped
          · cases remapped
            have aBound := bounded a aMem
            apply Nat.div_le_div_right
            omega
      simp [largest]

end ExecutionDimensions

namespace ProverConfig

/-- Successful checked Rust padding equals the previous mathematical formula. -/
theorem checkedTraceLength_eq_padded (rows padded : Nat)
    (accepted : checkedTraceLength rows = some padded) :
    padded = padded_trace_length rows := by
  rw [checkedTraceLength_eq rows padded accepted]
  unfold padded_trace_length
  split
  · have exponent : Nat.clog 2 (rows + 1) ≤ 8 :=
      Nat.clog_le_of_le_pow (by omega)
    have rounded : 2 ^ Nat.clog 2 (rows + 1) ≤ 256 :=
      Nat.pow_le_pow_right (by decide) exponent
    exact max_eq_right rounded
  · have roundedUp := Nat.le_pow_clog (by decide : 1 < 2) (rows + 1)
    exact max_eq_left (by omega)

end ProverConfig

/-- Largest remapped slot actually touched by the physical trace; zero when
there is no nonzero memory access. This is the scan used by the corrected policy. -/
def HonestTrace.highest_touched_slot {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs) : Nat :=
  (((trace.rows.toList.filterMap (·.ram_address)).filterMap
    (remap_address trace.initialState.jolt_device.memory_layout)).max?).getD 0

private theorem remapWordAddress_eq (layout : MemoryLayout) (address : Nat)
    (slot : Option Nat)
    (checked : JoltConstraints.VerifierSizes.remapWordAddress layout address = some slot) :
    slot = remap_address layout address := by
  unfold JoltConstraints.VerifierSizes.remapWordAddress at checked
  by_cases zero : address = 0
  · subst address
    simpa [remap_address] using checked.symm
  · simp only [if_neg zero, pure_bind] at checked
    rw [bind_some_iff] at checked
    obtain ⟨offset, subtracted, result⟩ := checked
    obtain ⟨rfl, _⟩ := checkedSub_some subtracted
    cases result
    simp [remap_address, zero]

private theorem HonestTrace.prover_config_ram_shape
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (trace : HonestTrace joltInstance privateInputs) (config : ProverConfig)
    (accepted : trace.prover_config = some config) :
    (∀ address ∈ trace.rows.toList.filterMap (·.ram_address), address = 0 ∨
      trace.initialState.jolt_device.memory_layout.get_lowest_address.toNat ≤ address) ∧
    config.ram_K = 2 ^ Nat.clog 2 (max trace.highest_touched_slot
      ((remap_address trace.initialState.jolt_device.memory_layout
        (min_bytecode_address joltInstance.program.memory_init)).getD 0 +
        program_image_len_words joltInstance.program.memory_init + 1)) := by
  have checked := (ProverConfig.deriveFromDimensions_sizes _ _ _ _ _ config accepted).2.2.1
  unfold ProverConfig.checkedRamSize at checked
  simp only [bind_some_iff] at checked
  obtain ⟨touched, touchChecked, start, startChecked, imageEnd, imageAdded,
    imageEnd', extraAdded, rounded⟩ := checked
  obtain ⟨addressesOk, touchedIs⟩ := ExecutionDimensions.checkedTouched_fold
    (trace.rows.toList.filterMap (fun (row : TraceRow trace.bytecode) => row.ram_address))
      trace.initialState.jolt_device.memory_layout touched touchChecked
  obtain ⟨rfl, _⟩ := checkedAdd_some imageAdded
  obtain ⟨rfl, _⟩ := checkedAdd_some extraAdded
  have startIs := remapWordAddress_eq _ _ _ startChecked
  dsimp only [JoltConstraints.VerifierSizes.checkedNextPowerOfTwo] at rounded
  split at rounded
  · refine ⟨addressesOk, ?_⟩
    have formula := Option.some.inj rounded
    rw [← formula, startIs, ← touchedIs]
    rfl
  · cases rounded

private theorem corrected_rounding (touched imageEnd ramK : Nat)
    (rust : ramK = 2 ^ Nat.clog 2 (max touched imageEnd)) (fits : touched < ramK) :
    2 ^ Nat.clog 2 (max (touched + 1) imageEnd) = ramK := by
  have roundedUp := Nat.le_pow_clog (by decide : 1 < 2) (max touched imageEnd)
  have upper : max (touched + 1) imageEnd ≤ 2 ^ Nat.clog 2 (max touched imageEnd) := by
    omega
  apply Nat.le_antisymm
  · rw [rust]
    exact Nat.pow_le_pow_right (by decide) (Nat.clog_le_of_le_pow upper)
  · rw [rust]
    apply Nat.pow_le_pow_right (by decide)
    exact Nat.clog_mono_right 2 (by omega)

/-- Every accepted Rust domain reaches the highest slot. Failure of the strict
bound is therefore precisely equality with `ram_K`, not a larger missed range. -/
theorem HonestTrace.prover_config_highest_le
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (trace : HonestTrace joltInstance privateInputs) (config : ProverConfig)
    (accepted : trace.prover_config = some config) : trace.highest_touched_slot ≤ config.ram_K := by
  rw [(trace.prover_config_ram_shape config accepted).2]
  exact (Nat.le_max_left _ _).trans (Nat.le_pow_clog (by decide : 1 < 2) _)

/-- Rust acceptance agrees with the corrected policy exactly when the highest
slot is strictly inside Rust's RAM domain. The reverse direction identifies the
excluded off-by-one boundary; it adds no premise to corrected completeness. -/
theorem HonestTrace.prover_config_eq_corrected_iff
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (trace : HonestTrace joltInstance privateInputs) (config : ProverConfig)
    (accepted : trace.prover_config = some config) :
    trace.corrected_prover_config = some config ↔ trace.highest_touched_slot < config.ram_K := by
  constructor
  · intro corrected
    apply Nat.lt_of_le_of_ne (trace.prover_config_highest_le config accepted)
    unfold HonestTrace.corrected_prover_config at corrected
    simp only [bind_some_iff] at corrected
    obtain ⟨_, _, _, _, _, _, result⟩ := corrected
    cases result
    change trace.highest_touched_slot ≠ 2 ^ Nat.clog 2
      (max (trace.highest_touched_slot + 1)
        ((remap_address trace.initialState.jolt_device.memory_layout
          (min_bytecode_address joltInstance.program.memory_init)).getD 0 +
          program_image_len_words joltInstance.program.memory_init + 1))
    have roundedUp := Nat.le_pow_clog (by decide : 1 < 2)
      (max (trace.highest_touched_slot + 1)
        ((remap_address trace.initialState.jolt_device.memory_layout
          (min_bytecode_address joltInstance.program.memory_init)).getD 0 +
          program_image_len_words joltInstance.program.memory_init + 1))
    omega
  · intro fits
    obtain ⟨jump, lengthChecked, _, lengthBound⟩ :=
      ProverConfig.deriveFromDimensions_sizes _ _ _ _ _ config accepted
    have lengthIs := ProverConfig.checkedTraceLength_eq_padded _ _ lengthChecked
    change config.trace_length = padded_trace_length trace.rows.size at lengthIs
    obtain ⟨addressesOk, ramIs⟩ := trace.prover_config_ram_shape config accepted
    have correctedRam := corrected_rounding _ _ _ ramIs fits
    have lastJump : (trace.rows.back?.all fun last =>
        trace.bytecode[last.rowIndex].instruction.is_jump) = true := by
      rcases jump with empty | jump
      · change trace.rows.size = 0 at empty
        have emptyRows := Array.size_eq_zero_iff.mp empty
        rw [emptyRows]
        rfl
      · change (trace.rows.back?.any fun last =>
          trace.bytecode[last.rowIndex].instruction.is_jump) = true at jump
        cases last : trace.rows.back? with
        | none => rfl
        | some row => simpa only [last, Option.any_some, Option.all_some] using jump
    have addressCheck : (trace.rows.toList.filterMap (·.ram_address)).all
        (fun address => address == 0 ||
          trace.initialState.jolt_device.memory_layout.get_lowest_address.toNat ≤ address) = true := by
      apply List.all_eq_true.mpr
      intro a member
      simpa only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] using addressesOk a member
    have paddedBound : padded_trace_length trace.rows.size ≤
        joltInstance.max_padded_trace_length.toNat := by
      omega
    unfold HonestTrace.corrected_prover_config
    simp only [lastJump, addressCheck, guard, paddedBound, ↓reduceIte, pure_bind]
    change some {
      trace_length := padded_trace_length trace.rows.size
      ram_K := 2 ^ Nat.clog 2 (max (trace.highest_touched_slot + 1)
        ((remap_address trace.initialState.jolt_device.memory_layout
          (min_bytecode_address joltInstance.program.memory_init)).getD 0 +
          program_image_len_words joltInstance.program.memory_init + 1)) } = some config
    rw [correctedRam, ← lengthIs]

/-- Checked Rust dimensions fit the logarithm fields of `WitnessParams`. -/
theorem HonestTrace.prover_config_log_bounds
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (trace : HonestTrace joltInstance privateInputs) (config : ProverConfig)
    (accepted : trace.prover_config = some config) :
    Nat.log2 config.trace_length < 64 ∧ Nat.log2 config.ram_K < 64 := by
  obtain ⟨_, traceChecked, ramChecked, _⟩ :=
    ProverConfig.deriveFromDimensions_sizes _ _ _ _ _ config accepted
  obtain ⟨_, _, traceBound⟩ := ProverConfig.checkedTraceLength_bounds _ _ traceChecked
  obtain ⟨traceLog, tracePower⟩ := ProverConfig.checkedTraceLength_power _ _ traceChecked
  obtain ⟨⟨ramLog, ramPower⟩, ramBound⟩ := ProverConfig.checkedRamSize_power _ _ _ _ _ ramChecked
  rw [tracePower] at traceBound
  rw [ramPower] at ramBound
  rw [tracePower, ramPower, Nat.log2_two_pow, Nat.log2_two_pow]
  exact ⟨(Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp traceBound,
    (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp ramBound⟩

/-- Witness parameters from Rust's checked policy, including its actual RAM
size. Constructing these parameters does not assert that all touched slots fit. -/
noncomputable def HonestTrace.witness_params
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (trace : HonestTrace joltInstance privateInputs) (config : ProverConfig)
    (accepted : trace.prover_config = some config) : WitnessParams where
  logT := Nat.log2 config.trace_length
  logRamK := Nat.log2 config.ram_K
  logBytecodeK := max 1 (Nat.clog 2 (trace.bytecode.size + 1))
  chunkBits := if Nat.log2 config.trace_length < 25 then 4 else 8
  virtualChunkBits := if Nat.log2 config.trace_length < 25 then 16 else 32
  chunkBits_pos := by
    split
    · decide
    · decide
  virtualChunkBits_pos := by
    split
    · decide
    · decide
  chunkBits_dvd_virtual := by
    by_cases small : Nat.log2 config.trace_length < 25
    · rw [if_pos small, if_pos small]
      decide
    · rw [if_neg small, if_neg small]
      decide
  virtualChunkBits_dvd_lookup := by
    split
    · decide
    · decide
  logT_lt_usizeBits := (trace.prover_config_log_bounds config accepted).1
  logRamK_lt_usizeBits := (trace.prover_config_log_bounds config accepted).2
  logBytecodeK_lt_usizeBits := trace.log_bytecode_size_lt
