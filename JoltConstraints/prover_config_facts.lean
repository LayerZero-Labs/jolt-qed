import JoltConstraints.prover_config

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

/-- Folding the observed addresses records their nonzero minimum and maximum,
or no bounds when every address is zero.
For example, observing `[0, 16, 8]` records the bounds `(8, 16)`.
See jolt/crates/jolt-program/src/execution/trace.rs (`RamAddressBounds::observe`)
at 5def437f. -/
theorem boundsFor_fold (addresses : List Nat) :
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

-- Jolt's prover accepts only traces whose nonzero RAM addresses are at or above the
-- lowest address.
private theorem HonestTrace.prover_config_addresses_ok
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (trace : HonestTrace joltInstance privateInputs) (config : ProverConfig)
    (accepted : trace.prover_config joltInstance = some config) :
    ∀ address ∈ trace.rows.toList.filterMap (·.ram_address), address = 0 ∨
      trace.initialState.jolt_device.memory_layout.get_lowest_address.toNat ≤ address := by
  have checked := (ProverConfig.deriveFromDimensions_sizes _ _ _ _ _ config accepted).2.2.1
  unfold ProverConfig.checkedRamSize at checked
  simp only [bind_some_iff] at checked
  obtain ⟨touched, touchChecked, _⟩ := checked
  exact (ExecutionDimensions.checkedTouched_fold
    (trace.rows.toList.filterMap (fun (row : TraceRow trace.bytecode) => row.ram_address))
      trace.initialState.jolt_device.memory_layout touched touchChecked).1

/-- When Jolt's prover accepts the honest trace (`proverAccepts`), the length it pads to,
`config.trace_length`, is the run's padded length `padded_trace_length trace.rows.size`
(the power of two above the row count, at least 256), and it is at most the instance's
maximum padded length.
For example, a 300-row run pads to 512, and the instance's maximum must be at least 512.
See jolt/crates/jolt-prover/src/config.rs (`ProverConfig::derive_from_dimensions`,
`ProverConfig::from_padded_dimensions`) at c6703570. -/
theorem HonestTrace.prover_config_trace_length
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (trace : HonestTrace joltInstance privateInputs) (config : ProverConfig)
    (proverAccepts : trace.prover_config joltInstance = some config) :
    config.trace_length = padded_trace_length trace.rows.size ∧
    config.trace_length ≤ joltInstance.max_padded_trace_length.toNat := by
  obtain ⟨_, lengthChecked, _, lengthBound⟩ :=
    ProverConfig.deriveFromDimensions_sizes _ _ _ _ _ config proverAccepts
  exact ⟨ProverConfig.checkedTraceLength_eq_padded _ _ lengthChecked, lengthBound⟩

/-- When Jolt's prover accepts the honest trace (`proverAccepts`), the trace's last row,
if it has one, is a jump: its bytecode instruction is a JAL or a JALR (`is_jump`).
For example, a run whose last row is a self-jump `j .` passes; a run ending in an ADD
is rejected (a16z/jolt#1968).
See jolt/crates/jolt-prover/src/config.rs (`ProverConfig::derive_from_dimensions`,
`TraceDoesNotEndInJump`) at c6703570. -/
theorem HonestTrace.prover_config_last_jump
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (trace : HonestTrace joltInstance privateInputs) (config : ProverConfig)
    (proverAccepts : trace.prover_config joltInstance = some config) :
    (trace.rows.back?.all fun last =>
      trace.bytecode[last.rowIndex].instruction.is_jump) = true := by
  obtain ⟨jump, _⟩ := ProverConfig.deriveFromDimensions_sizes _ _ _ _ _ config proverAccepts
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

/-- The highest RAM word index a run touches: the largest word index
`(address - lowest) / 8` over the run's nonzero recorded RAM addresses
(`TraceRow.ram_address`), where `lowest` is the lowest address of the run's memory
layout; it is 0 when the run touches no nonzero address.
For example, with lowest address `0x7fff8000`, a run whose only access is an SD at
`0x80000010` touches word `0x8010 / 8 = 4098`.
This is the `touched` of Jolt's prover; since a16z/jolt#2250, the
prover rounds up `touched + 1` to pick its RAM size.
See jolt/crates/jolt-prover/src/config.rs (`ProverConfig::derive_from_dimensions`,
`checked_remap_address`) at c97e9300. -/
def Trace.highest_ram_slot (trace : Trace) : Nat :=
  ((trace.rows.toList.filterMap (·.ram_address)).filterMap
    (remap_address trace.initialState.jolt_device.memory_layout)).max?.getD 0

/-- Jolt's RAM size for the honest trace, unfolded. When Jolt's prover accepts the trace
(`proverAccepts`), it remaps the program image's lowest address to a word index
`imageStart` (none for address 0), and `config.ram_K` is the power of two that rounds up
the larger of one more than the highest touched word (`Trace.highest_ram_slot`) and the
image's end, `imageStart + program_image_len_words + 1`; both that end and `config.ram_K`
fit in 64 bits.
For example, a run touching word 1024 with an image ending at word 40 gets
`ram_K = pow2(1025) = 2048`.
See jolt/crates/jolt-prover/src/config.rs (`ProverConfig::derive_from_dimensions`,
`checked_remap_address`) at c97e9300. -/
theorem HonestTrace.prover_config_ram_K
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (trace : HonestTrace joltInstance privateInputs) (config : ProverConfig)
    (proverAccepts : trace.prover_config joltInstance = some config) :
    ∃ imageStart : Option Nat,
      JoltConstraints.VerifierSizes.remapWordAddress trace.initialState.jolt_device.memory_layout
        (min_bytecode_address joltInstance.program.memory_init) = some imageStart ∧
      imageStart.getD 0 + program_image_len_words joltInstance.program.memory_init + 1 < 2 ^ 64 ∧
      config.ram_K = 2 ^ Nat.clog 2 (max ((trace : Trace).highest_ram_slot + 1)
        (imageStart.getD 0 + program_image_len_words joltInstance.program.memory_init + 1)) ∧
      config.ram_K < 2 ^ 64 := by
  have checked := (ProverConfig.deriveFromDimensions_sizes _ _ _ _ _ config proverAccepts).2.2.1
  unfold ProverConfig.checkedRamSize at checked
  simp only [bind_some_iff] at checked
  obtain ⟨touched, touchChecked, imageStart, remapped, imageEnd, added, imageEnd', addedOne,
    rounded⟩ := checked
  have touchedIs := (ExecutionDimensions.checkedTouched_fold
    (trace.rows.toList.filterMap (fun (row : TraceRow trace.bytecode) => row.ram_address))
      trace.initialState.jolt_device.memory_layout touched touchChecked).2
  obtain ⟨rfl, _⟩ := checkedAdd_some added
  obtain ⟨rfl, endFits⟩ := checkedAdd_some addedOne
  obtain ⟨sizeIs, sizeFits⟩ := ProverConfig.checkedRound_some _ _ rounded
  refine ⟨imageStart, remapped, endFits, ?_, sizeFits⟩
  rw [sizeIs, ← touchedIs]
  rfl

/-- Jolt's RAM table holds the highest RAM word the run touches: when Jolt's prover accepts
the honest trace (`proverAccepts`), the highest touched word index
`h = Trace.highest_ram_slot` is below Jolt's RAM size `K = config.ram_K`.
A table of `K` words holds indices `0` to `K - 1`, so this needs `h < K`.
Since a16z/jolt#2250, Jolt's prover picks
`K = pow2(max(h + 1, imageEnd))` (`HonestTrace.prover_config_ram_K`), which is at least
`h + 1`.
For example, `h = 1024` with an image ending at word 40 gives `K = pow2(1025) = 2048`,
which holds word 1024; the prover before #2250, with `pow2(max(h, imageEnd)) = 1024`, did not.
See jolt/crates/jolt-prover/src/config.rs (`ProverConfig::derive_from_dimensions`)
at c97e9300 and https://github.com/a16z/jolt/issues/1951 (item 4). -/
theorem HonestTrace.prover_config_holds_highest_slot
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (trace : HonestTrace joltInstance privateInputs) (config : ProverConfig)
    (proverAccepts : trace.prover_config joltInstance = some config) :
    (trace : Trace).highest_ram_slot < config.ram_K := by
  obtain ⟨_, _, _, sizeIs, _⟩ := trace.prover_config_ram_K config proverAccepts
  rw [sizeIs]
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _)
    ((Nat.le_max_left _ _).trans (Nat.le_pow_clog (by decide : 1 < 2) _))

/-- When Jolt's prover accepts the honest trace (`proverAccepts`), every memory address
a row touches (`TraceRow.ram_address`) is 0 (no access), or is at or above the layout's
lowest address and has a word index (`remap_address`) below Jolt's RAM size
`config.ram_K`.
For example, with lowest address `0x7fff8000`, an SD at `0x80000010` has word index 4098,
which must be below `config.ram_K`.
The bound on the word index uses `HonestTrace.prover_config_holds_highest_slot`, which
holds under the fix of a16z/jolt#1951 item 4.
See jolt/crates/jolt-prover/src/config.rs (`checked_remap_address`) and
jolt/crates/jolt-witness/src/backend/trace/ram.rs (`remapped_ram_address`) at c6703570. -/
theorem HonestTrace.prover_config_ram_fits
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (trace : HonestTrace joltInstance privateInputs) (config : ProverConfig)
    (proverAccepts : trace.prover_config joltInstance = some config)
    (row : TraceRow trace.bytecode) (inTrace : row ∈ trace.rows) (address : Nat)
    (touches : row.ram_address = some address) :
    address = 0 ∨
      (trace.initialState.jolt_device.memory_layout.get_lowest_address.toNat ≤ address ∧
        ∃ slot, remap_address trace.initialState.jolt_device.memory_layout address = some slot ∧
          slot < config.ram_K) := by
  -- the address is one of the run's addresses, so it passed the prover's address check
  have member : address ∈ trace.rows.toList.filterMap (·.ram_address) :=
    List.mem_filterMap.mpr ⟨row, Array.mem_toList_iff.mpr inTrace, touches⟩
  by_cases zero : address = 0
  · exact Or.inl zero
  · have above := (trace.prover_config_addresses_ok config proverAccepts address member).resolve_left zero
    -- its slot is at most the highest touched slot, which Jolt's table is taken to hold
    have slotIs : remap_address trace.initialState.jolt_device.memory_layout address =
        some ((address - trace.initialState.jolt_device.memory_layout.get_lowest_address.toNat) / 8) := by
      unfold remap_address
      rw [if_neg zero]
    have atMost := List.le_max?_getD_of_mem (k := 0)
      (List.mem_filterMap.mpr ⟨address, member, slotIs⟩)
    exact Or.inr ⟨above, _, slotIs,
      Nat.lt_of_le_of_lt atMost (trace.prover_config_holds_highest_slot config proverAccepts)⟩

/-- When Jolt's prover accepts the honest trace (`proverAccepts`), its RAM size
`config.ram_K` is at least 2: the program image's end is at least 2, since the image
spans at least one word and the prover adds one more.
So a RAM word index splits into at least one chunk.
For example, an image starting at word 0 with one word ends at 2, and `ram_K ≥ 2`.
See jolt/crates/jolt-prover/src/config.rs (`ProverConfig::derive_from_dimensions`)
at c97e9300. -/
theorem HonestTrace.prover_config_ram_K_ge_two
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (trace : HonestTrace joltInstance privateInputs) (config : ProverConfig)
    (proverAccepts : trace.prover_config joltInstance = some config) :
    2 ≤ config.ram_K := by
  obtain ⟨_, _, _, sizeIs, _⟩ := trace.prover_config_ram_K config proverAccepts
  have imageWords := program_image_len_words_pos joltInstance.program.memory_init
  rw [sizeIs]
  exact (by omega : 2 ≤ max _ _).trans (Nat.le_pow_clog (by decide : 1 < 2) _)
