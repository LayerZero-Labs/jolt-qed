import JoltConstraints.verifier_sizes
import JoltConstraints.witness_domain
import JoltConstraints.Completeness.Helpers.RamReadSelection

open LeanRV64D

set_option autoImplicit false

namespace JoltConstraints

-- A nonempty image starts in RAM, by the program image's existing certificate.
theorem min_bytecode_address_ge_ram_start {Source : Type}
    (program : Rv64ProgramImage Source) (nonempty : program.memory_init ≠ []) :
    JoltISA.RAM_START_ADDRESS ≤ min_bytecode_address program.memory_init := by
  unfold min_bytecode_address
  cases minimum : (program.memory_init.map (·.1.toNat)).min? with
  | none =>
    have := List.min?_eq_none_iff.mp minimum
    simp only [List.map_eq_nil_iff] at this
    exact False.elim (nonempty this)
  | some address =>
    obtain ⟨entry, member, isAddress⟩ := List.mem_map.mp (List.min?_mem minimum)
    simpa only [Option.getD_some, ← isAddress] using
      (program.memory_init_in_program entry member).1

-- Rounding up to even never decreases.
private theorem le_round_up_even (vars : Nat) : vars ≤ if vars % 2 = 0 then vars else vars + 1 := by
  split <;> omega

-- A longer trace never gets a narrower honest chunk width.
private theorem chunks_mono {logT maxLogT : Nat} (shorter : logT ≤ maxLogT) :
    logT + VerifierSizes.committedLogKChunk logT ≤
      maxLogT + VerifierSizes.committedLogKChunk maxLogT := by
  unfold VerifierSizes.committedLogKChunk
  split <;> split <;> omega

-- Chunks of the honest width for a trace no longer than the maximum fit the setup
-- sized for the maximum.
theorem VerifierSizes.chunks_fit_dorySetupLogN (layout : MemoryLayout) (maxLength logT : Nat)
    (shorter : logT ≤ Nat.clog 2 maxLength) :
    logT + VerifierSizes.committedLogKChunk logT ≤ VerifierSizes.dorySetupLogN layout maxLength := by
  unfold VerifierSizes.dorySetupLogN
  exact ((chunks_mono shorter).trans (le_max_left _ _)).trans (le_round_up_even _)

end JoltConstraints

open JoltConstraints

/-- Jolt's RAM size for the honest trace of a nonempty program, unfolded
(`HonestTrace.prover_config_ram_K` with the image's start computed).
The image's lowest address `min_bytecode_address` is nonzero and at or above the layout's
lowest address `lowest`, so Jolt's prover remaps it to the word index
`(min_bytecode_address - lowest) / 8`; `config.ram_K` rounds up the larger of one more
than the highest touched word (`Trace.highest_ram_slot`) and the image's end, that index
plus `program_image_len_words` plus one; that end and `config.ram_K` fit in 64 bits.
For example, an image at `0x80000000` with lowest address `0x7fff8000` starts at word 4096.
See jolt/crates/jolt-prover/src/config.rs (`ProverConfig::derive_from_dimensions`,
`checked_remap_address`) at c97e9300. -/
theorem HonestTrace.prover_config_ram_K_of_nonempty
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (trace : HonestTrace joltInstance privateInputs)
    (config : ProverConfig) (proverAccepts : trace.prover_config joltInstance = some config)
    (nonempty : joltInstance.program.memory_init ≠ []) :
    trace.initialState.jolt_device.memory_layout.get_lowest_address.toNat ≤
        min_bytecode_address joltInstance.program.memory_init ∧
      VerifierSizes.remapWordAddress trace.initialState.jolt_device.memory_layout
          (min_bytecode_address joltInstance.program.memory_init) =
        some (some ((min_bytecode_address joltInstance.program.memory_init -
          trace.initialState.jolt_device.memory_layout.get_lowest_address.toNat) / 8)) ∧
      (min_bytecode_address joltInstance.program.memory_init -
          trace.initialState.jolt_device.memory_layout.get_lowest_address.toNat) / 8 +
        program_image_len_words joltInstance.program.memory_init + 1 < 2 ^ 64 ∧
      config.ram_K = 2 ^ Nat.clog 2 (max (trace.highest_ram_slot + 1)
        ((min_bytecode_address joltInstance.program.memory_init -
          trace.initialState.jolt_device.memory_layout.get_lowest_address.toNat) / 8 +
            program_image_len_words joltInstance.program.memory_init + 1)) ∧
      config.ram_K < 2 ^ 64 := by
  have imageAbove := min_bytecode_address_ge_ram_start joltInstance.program nonempty
  have imageNonzero : min_bytecode_address joltInstance.program.memory_init ≠ 0 := by
    unfold JoltISA.RAM_START_ADDRESS at imageAbove
    omega
  obtain ⟨imageStart, remapped, endFits, sizeIs, sizeFits⟩ :=
    trace.prover_config_ram_K config proverAccepts
  have unfolded := remapped
  unfold VerifierSizes.remapWordAddress at unfolded
  simp only [if_neg imageNonzero, pure_bind] at unfolded
  rw [bind_some_iff] at unfolded
  obtain ⟨offset, subtracted, unfolded⟩ := unfolded
  obtain ⟨rfl, lowestBelow⟩ := checkedSub_some subtracted
  cases unfolded
  exact ⟨lowestBelow, remapped, endFits, sizeIs, sizeFits⟩

/-- If Jolt's verifier computes a RAM minimum for a nonempty image, Jolt's RAM size meets it.
The minimum (`VerifierSizes.minRamSize`, Jolt's `compute_min_ram_k`) rounds up the larger of
the image's end word and the word index of `RAM_START_ADDRESS`; Jolt's prover rounds up a
number at least the image's end (`HonestTrace.prover_config_ram_K`).
For example, an image whose first word index plus word count is 40 has minimum
`pow2(40) = 64`, and Jolt's prover rounds at least 41, so its `ram_K` is at least 64.
See jolt/crates/jolt-program/src/preprocess/ram.rs (`compute_min_ram_k`) and
jolt/crates/jolt-prover/src/config.rs (`ProverConfig::derive_from_dimensions`) at c97e9300. -/
theorem HonestTrace.witness_params_ram_minimum_of_nonempty
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (trace : HonestTrace joltInstance privateInputs)
    (config : ProverConfig) (proverAccepts : trace.prover_config joltInstance = some config)
    (nonempty : joltInstance.program.memory_init ≠ []) (minimum : Nat)
    (computed : VerifierSizes.minRamSize joltInstance.program
      trace.initialState.jolt_device.memory_layout = some minimum) :
    minimum ≤ (trace.witness_params config proverAccepts).ramSize := by
  have imageAbove := min_bytecode_address_ge_ram_start joltInstance.program nonempty
  obtain ⟨_, proverRemapped, _, sizeIs, _⟩ :=
    trace.prover_config_ram_K_of_nonempty config proverAccepts nonempty
  unfold VerifierSizes.minRamSize at computed
  rw [bind_some_iff] at computed
  obtain ⟨imageStart, remappedImage, computed⟩ := computed
  rw [bind_some_iff] at computed
  obtain ⟨imageEnd, imageAdded, computed⟩ := computed
  rw [bind_some_iff] at computed
  obtain ⟨ioEnd, remappedIo, computed⟩ := computed
  rw [proverRemapped] at remappedImage
  cases remappedImage
  unfold VerifierSizes.remapWordAddress at remappedIo
  have ramNonzero : JoltISA.RAM_START_ADDRESS ≠ 0 := by decide
  simp only [if_neg ramNonzero, pure_bind] at remappedIo
  rw [bind_some_iff] at remappedIo
  obtain ⟨ioOffset, ioSubtracted, remappedIo⟩ := remappedIo
  cases remappedIo
  obtain ⟨ioOffsetIs, _⟩ := checkedSub_some ioSubtracted
  obtain ⟨imageEndIs, _⟩ := checkedAdd_some imageAdded
  have ioBelow : ioOffset / 8 ≤ (min_bytecode_address joltInstance.program.memory_init -
      trace.initialState.jolt_device.memory_layout.get_lowest_address.toNat) / 8 := by
    apply Nat.div_le_div_right
    omega
  have imageEndAbove : ioOffset / 8 ≤ imageEnd := by
    simp only [Option.getD_some] at imageEndIs
    omega
  dsimp only at computed
  rw [Nat.max_eq_left imageEndAbove] at computed
  obtain ⟨minimumIs, _⟩ := ProverConfig.checkedRound_some _ _ computed
  rw [minimumIs, trace.witness_params_ram_size config proverAccepts, sizeIs]
  apply Nat.pow_le_pow_right (by decide : 0 < 2)
  apply Nat.clog_mono_right
  simp only [Option.getD_some] at imageEndIs ⊢
  omega

/-- A successful layout (`MemoryLayout.new`) puts `heap_end` at least
`STACK_CANARY_SIZE = 128` bytes past the end of the program region,
`RAM_START_ADDRESS + programSize`, where `programSize` is the configured program size:
the stack canary, the stack and the heap follow the program.
For example, a 4096-byte program gives `heap_end ≥ 0x80000000 + 4096 + 128`.
See jolt/common/src/jolt_device.rs (`MemoryLayout::try_new`) at c6703570. -/
theorem new_heap_end_ge (config : MemoryConfig) (layout : MemoryLayout)
    (built : MemoryLayout.new config = some layout) :
    ∃ programSize, config.program_size = some programSize ∧
      JoltISA.RAM_START_ADDRESS + programSize.toNat + JoltISA.STACK_CANARY_SIZE ≤
        layout.heap_end.toNat := by
  unfold MemoryLayout.new at built
  rw [bind_some_iff] at built
  obtain ⟨programSize, programSizeIs, built⟩ := built
  -- the six sizes, the two power-of-two checks and the size of the I/O region
  iterate 10 (rw [bind_some_iff] at built; obtain ⟨_, _, built⟩ := built)
  -- the advice regions
  rw [bind_some_iff] at built
  obtain ⟨⟨_, _, _, _⟩, _, built⟩ := built
  -- input end, output end, termination, I/O end
  iterate 4 (rw [bind_some_iff] at built; obtain ⟨_, _, built⟩ := built)
  -- stack end, stack start, heap end
  rw [bind_some_iff] at built
  obtain ⟨stackEnd, stackEndAdded, built⟩ := built
  rw [bind_some_iff] at built
  obtain ⟨stackStart, stackStartAdded, built⟩ := built
  rw [bind_some_iff] at built
  obtain ⟨heapEnd, heapEndAdded, built⟩ := built
  cases built
  rw [bind_some_iff] at stackStartAdded
  obtain ⟨withCanary, canaryAdded, stackStartAdded⟩ := stackStartAdded
  obtain ⟨stackEndIs, _⟩ := checkedAdd_some stackEndAdded
  obtain ⟨withCanaryIs, _⟩ := checkedAdd_some canaryAdded
  obtain ⟨stackStartIs, _⟩ := checkedAdd_some stackStartAdded
  obtain ⟨heapEndIs, heapEndFits⟩ := checkedAdd_some heapEndAdded
  refine ⟨programSize, programSizeIs, ?_⟩
  dsimp only
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

/-- In the instance's starting layout, `heap_end` lies at least `STACK_CANARY_SIZE = 128`
bytes past the program image's end `program_end`: the host sets the program size to
`program_end - RAM_START_ADDRESS` (`Rv64ProgramImage.program_size`).
For example, an image ending at `0x80001000` gives `heap_end ≥ 0x80001080`.
See jolt/common/src/jolt_device.rs (`MemoryLayout::try_new`) at c6703570. -/
theorem HonestTrace.program_end_below_heap_end {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs) :
    joltInstance.program.program_end.toNat + JoltISA.STACK_CANARY_SIZE ≤
      trace.initialState.jolt_device.memory_layout.heap_end.toNat := by
  have layoutBuilt :=
    (initial_state_device joltInstance privateInputs trace.initialState trace.initialized).1
  unfold JoltInstance.memory_layout at layoutBuilt
  obtain ⟨programSize, sizeIs, bound⟩ := new_heap_end_ge _ _ layoutBuilt
  cases sizeIs
  have aboveStart := joltInstance.program.program_end_ge_ram_start
  have sizeValue : joltInstance.program.program_size.toNat =
      joltInstance.program.program_end.toNat - JoltISA.RAM_START_ADDRESS := by
    unfold Rv64ProgramImage.program_size
    have startValue : (BitVec.ofNat 64 JoltISA.RAM_START_ADDRESS).toNat =
        JoltISA.RAM_START_ADDRESS := rfl
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, startValue]; exact aboveStart), startValue]
  omega

/-- The lowest address of the instance's starting layout is at most `RAM_START_ADDRESS`:
the advice and I/O regions lie below RAM.
For example, a layout whose larger advice region starts at `0x7fff8000` has that as its
lowest address. -/
theorem HonestTrace.lowest_address_le_ram_start {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs) :
    trace.initialState.jolt_device.memory_layout.get_lowest_address.toNat ≤
      JoltISA.RAM_START_ADDRESS := by
  have layoutBuilt :=
    (initial_state_device joltInstance privateInputs trace.initialState trace.initialized).1
  unfold JoltInstance.memory_layout at layoutBuilt
  have ordered := new_io_ordered _ _ layoutBuilt
  have geometry := new_io_geometry _ _ layoutBuilt
  omega

/-- The highest RAM word index the honest trace touches (`Trace.highest_ram_slot`) is
below the number of words that start below `heap_end`,
`⌈(heap_end - lowest) / 8⌉ = (heap_end - lowest + 7) / 8`, where `lowest` is the
layout's lowest address: every recorded address in RAM is below `heap_end`
(`HonestTrace.ram_address_below_heap_end`), and every other one is below
`RAM_START_ADDRESS`, which `heap_end` follows by at least 128 bytes.
For example, with lowest address `0x7fff8000` and `heap_end = 0x80010004`, an SD at
`0x80010000` straddles `heap_end` and touches word `0x18000 / 8 = 12288`, which is below
`(0x18004 + 7) / 8 = 12289`. -/
theorem HonestTrace.highest_ram_slot_lt_heap_end {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs) :
    trace.highest_ram_slot <
      (trace.initialState.jolt_device.memory_layout.heap_end.toNat -
        trace.initialState.jolt_device.memory_layout.get_lowest_address.toNat + 7) / 8 := by
  have programBelow := trace.program_end_below_heap_end
  have aboveStart := joltInstance.program.program_end_ge_ram_start
  have lowestBelow := trace.lowest_address_le_ram_start
  have stackCanary : JoltISA.STACK_CANARY_SIZE = 128 := rfl
  unfold Trace.highest_ram_slot
  apply max?_getD_lt _ _ (by omega)
  intro slot member
  obtain ⟨address, member, remapped⟩ := List.mem_filterMap.mp member
  obtain ⟨row, inRows, touches⟩ := List.mem_filterMap.mp member
  obtain ⟨i, inTrace, isRow⟩ := Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp inRows)
  subst isRow
  have below : address < trace.initialState.jolt_device.memory_layout.heap_end.toNat := by
    by_cases inRam : JoltISA.RAM_START_ADDRESS ≤ address
    · exact trace.ram_address_below_heap_end i inTrace address touches inRam
    · omega
  have bounded := remap_address_lt trace.initialState.jolt_device.memory_layout address _
    (by omega) below
  rw [remapped] at bounded
  exact bounded

/-- When Jolt's prover accepts the honest trace (`proverAccepts`) of a nonempty program,
Jolt's verifier computes its RAM minimum (`VerifierSizes.minRamSize`, Jolt's
`compute_min_ram_k`): the image's start and end words are the ones Jolt's prover already
computed, the word index of `RAM_START_ADDRESS` exists because the lowest address is
below RAM, and rounding fits in 64 bits because Jolt's RAM size, which is at least as
large, does.
For example, an image of words 4096 to 4135 with lowest address `0x7fff8000` has minimum
`pow2(max(4136, 4096)) = 8192`.
See jolt/crates/jolt-program/src/preprocess/ram.rs (`compute_min_ram_k`) at c6703570. -/
theorem HonestTrace.verifier_ram_minimum_computes
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (trace : HonestTrace joltInstance privateInputs)
    (config : ProverConfig) (proverAccepts : trace.prover_config joltInstance = some config)
    (nonempty : joltInstance.program.memory_init ≠ []) :
    ∃ minimum, VerifierSizes.minRamSize joltInstance.program
      trace.initialState.jolt_device.memory_layout = some minimum := by
  have imageAbove := min_bytecode_address_ge_ram_start joltInstance.program nonempty
  have lowestBelow := trace.lowest_address_le_ram_start
  obtain ⟨_, remapped, endFits, sizeIs, sizeFits⟩ :=
    trace.prover_config_ram_K_of_nonempty config proverAccepts nonempty
  -- the end of the image, rounded, is at most Jolt's RAM size
  have rounded : 2 ^ Nat.clog 2 ((min_bytecode_address joltInstance.program.memory_init -
      trace.initialState.jolt_device.memory_layout.get_lowest_address.toNat) / 8 +
        program_image_len_words joltInstance.program.memory_init) < 2 ^ 64 := by
    refine Nat.lt_of_le_of_lt ?_ sizeFits
    rw [sizeIs]
    exact Nat.pow_le_pow_right (by decide) (Nat.clog_mono_right _ (by omega))
  have ioBelow : (JoltISA.RAM_START_ADDRESS -
      trace.initialState.jolt_device.memory_layout.get_lowest_address.toNat) / 8 ≤
      (min_bytecode_address joltInstance.program.memory_init -
        trace.initialState.jolt_device.memory_layout.get_lowest_address.toNat) / 8 :=
    Nat.div_le_div_right (by omega)
  have ramNonzero : JoltISA.RAM_START_ADDRESS ≠ 0 := by decide
  have endAdded : MemoryLayout.checkedAdd
      ((min_bytecode_address joltInstance.program.memory_init -
        trace.initialState.jolt_device.memory_layout.get_lowest_address.toNat) / 8)
      (program_image_len_words joltInstance.program.memory_init) =
      some ((min_bytecode_address joltInstance.program.memory_init -
        trace.initialState.jolt_device.memory_layout.get_lowest_address.toNat) / 8 +
          program_image_len_words joltInstance.program.memory_init) := by
    unfold MemoryLayout.checkedAdd
    rw [if_pos (by omega)]
  have ioRemapped : VerifierSizes.remapWordAddress trace.initialState.jolt_device.memory_layout
      JoltISA.RAM_START_ADDRESS = some (some ((JoltISA.RAM_START_ADDRESS -
        trace.initialState.jolt_device.memory_layout.get_lowest_address.toNat) / 8)) := by
    unfold VerifierSizes.remapWordAddress MemoryLayout.checkedSub
    simp only [if_neg ramNonzero, if_pos lowestBelow]
    rfl
  refine ⟨2 ^ Nat.clog 2 ((min_bytecode_address joltInstance.program.memory_init -
      trace.initialState.jolt_device.memory_layout.get_lowest_address.toNat) / 8 +
        program_image_len_words joltInstance.program.memory_init), ?_⟩
  unfold VerifierSizes.minRamSize
  rw [remapped]
  simp only [Option.getD_some, Option.bind_eq_bind, Option.bind_some, endAdded, ioRemapped]
  rw [Nat.max_eq_left (by omega)]
  simp only [VerifierSizes.checkedNextPowerOfTwo, if_pos rounded]

/-- When Jolt's prover accepts the honest trace (`proverAccepts`) of a nonempty program,
Jolt's verifier computes its RAM maximum (`VerifierSizes.maxRamSize`, Jolt's
`compute_max_ram_k` with `div_ceil(8)`), `pow2(⌈(heap_end - lowest) / 8⌉)`, and Jolt's
RAM size is at most that maximum.
Jolt's RAM size `pow2(max(h + 1, imageEnd))` (`HonestTrace.prover_config_ram_K`) rounds
up numbers at most `⌈(heap_end - lowest) / 8⌉`: one more than the highest touched word
`h`, because every access starts below `heap_end`
(`HonestTrace.highest_ram_slot_lt_heap_end`), and the image's end, because `heap_end`
lies 128 bytes past the program.
For example, with lowest address `0x7fff8000` and `heap_end = 0x80010000`, the maximum is
`pow2(12288) = 16384`, and a run touching at most word 5000 with an image of words 4096
to 4135 gets `ram_K = pow2(max(5001, 4137)) = 8192 ≤ 16384`.
See jolt/crates/jolt-program/src/preprocess/ram.rs (`compute_max_ram_k`) and
jolt/crates/jolt-prover/src/config.rs (`ProverConfig::derive_from_dimensions`)
at c97e9300. -/
theorem HonestTrace.witness_params_ram_maximum
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (trace : HonestTrace joltInstance privateInputs)
    (config : ProverConfig) (proverAccepts : trace.prover_config joltInstance = some config)
    (nonempty : joltInstance.program.memory_init ≠ []) :
    ∃ maximum, VerifierSizes.maxRamSize trace.initialState.jolt_device.memory_layout =
        some maximum ∧
      (trace.witness_params config proverAccepts).ramSize ≤ maximum := by
  have programBelow := trace.program_end_below_heap_end
  have aboveStart := joltInstance.program.program_end_ge_ram_start
  have heapFits := trace.initialState.jolt_device.memory_layout.heap_end.isLt
  have touchedBelow := trace.highest_ram_slot_lt_heap_end
  -- the image's first word plus its length is bounded by the program's end
  have ramStartPos : 0 < JoltISA.RAM_START_ADDRESS := by decide
  have imageWords := program_image_len_words_le joltInstance.program.memory_init
    joltInstance.program.program_end.toNat (by omega)
    (fun entry inImage => (joltInstance.program.memory_init_in_program entry inImage).2)
  obtain ⟨lowestBelowImage, _, _, sizeIs, _⟩ :=
    trace.prover_config_ram_K_of_nonempty config proverAccepts nonempty
  -- the verifier's maximum: the number of words below heap_end, rounded up
  have stackCanary : JoltISA.STACK_CANARY_SIZE = 128 := rfl
  have wordsBound : (trace.initialState.jolt_device.memory_layout.heap_end.toNat -
      trace.initialState.jolt_device.memory_layout.get_lowest_address.toNat + 7) / 8 ≤
        2 ^ 61 := by
    omega
  have maximumFits : 2 ^ Nat.clog 2
      ((trace.initialState.jolt_device.memory_layout.heap_end.toNat -
        trace.initialState.jolt_device.memory_layout.get_lowest_address.toNat + 7) / 8) <
          2 ^ 64 :=
    Nat.lt_of_le_of_lt (Nat.pow_le_pow_right (by decide) (Nat.clog_le_of_le_pow wordsBound))
      (by decide)
  refine ⟨2 ^ Nat.clog 2
      ((trace.initialState.jolt_device.memory_layout.heap_end.toNat -
        trace.initialState.jolt_device.memory_layout.get_lowest_address.toNat + 7) / 8),
    ?_, ?_⟩
  · unfold VerifierSizes.maxRamSize
    simp only [MemoryLayout.checkedSub, if_pos (by omega :
      trace.initialState.jolt_device.memory_layout.get_lowest_address.toNat ≤
        trace.initialState.jolt_device.memory_layout.heap_end.toNat), Option.bind_eq_bind,
      Option.bind_some, VerifierSizes.checkedNextPowerOfTwo, if_pos maximumFits]
  · -- both numbers Jolt's prover rounds are at most the number of words below heap_end
    rw [trace.witness_params_ram_size config proverAccepts, sizeIs]
    apply Nat.pow_le_pow_right (by decide : 0 < 2)
    apply Nat.clog_mono_right
    omega

/-- Jolt's RAM size passes Jolt's verifier's RAM bounds (`JoltInstance.ram_size_in_bounds`):
the verifier computes both its minimum and its maximum
(`HonestTrace.verifier_ram_minimum_computes`, `HonestTrace.witness_params_ram_maximum`),
and Jolt's RAM size `config.ram_K` lies between them
(`HonestTrace.witness_params_ram_minimum_of_nonempty`).
An empty program is excluded by the a16z-confirmed assumption `imageNonempty`.
For example, with lowest address `0x7fff8000` and `heap_end = 0x80010000`, a run
touching word 1000 with an image of words 4096 to 4135 gets
`ram_K = pow2(max(1001, 4137)) = 8192`, between the minimum 8192 and the maximum 16384. -/
theorem HonestTrace.witness_params_ram_bounds
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (trace : HonestTrace joltInstance privateInputs)
    (config : ProverConfig) (proverAccepts : trace.prover_config joltInstance = some config)
    -- Assumed: a16z told us by phone on 2026-10-08 that Jolt can assume a program
    -- is never empty, so its memory image loads at least one byte. Jolt's prover does
    -- not reject an empty ELF; only its verifier does (bug-report/verifier-ram-minimum).
    (imageNonempty : joltInstance.program.ImageNonempty) :
    joltInstance.ram_size_in_bounds (trace.witness_params config proverAccepts).ramSize = true := by
  have layoutBuilt :=
    (initial_state_device joltInstance privateInputs trace.initialState trace.initialized).1
  obtain ⟨minimum, minimumComputed⟩ :=
    trace.verifier_ram_minimum_computes config proverAccepts imageNonempty
  obtain ⟨maximum, maximumComputed, atMostMaximum⟩ :=
    trace.witness_params_ram_maximum config proverAccepts imageNonempty
  have atLeastMinimum := trace.witness_params_ram_minimum_of_nonempty config proverAccepts
    imageNonempty minimum minimumComputed
  unfold JoltInstance.ram_size_in_bounds JoltInstance.verifier_ram_bounds
  simp only [layoutBuilt, minimumComputed, maximumComputed, Option.bind_eq_bind,
    Option.bind_some, Option.pure_def, decide_eq_true_eq]
  exact ⟨atLeastMinimum, atMostMaximum⟩

/-- The honest prover's one-hot chunks fit the verifier's Dory setup
(`JoltInstance.one_hot_fits_setup`): its trace is no longer than the maximum padded
length, and its chunk width is the setup's width for that length.
For example, a run padded to `2^9` cycles with 4-bit chunks needs 13 setup variables,
and a setup sized for at least `2^9` cycles has at least that many.
See jolt/crates/jolt-prover/src/dory/preprocessing.rs (`setup_total_vars`) at c6703570. -/
theorem HonestTrace.witness_params_one_hot_fits_setup
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (trace : HonestTrace joltInstance privateInputs)
    (config : ProverConfig) (proverAccepts : trace.prover_config joltInstance = some config)
    (layout : MemoryLayout) (hasLayout : joltInstance.memory_layout = some layout) :
    joltInstance.one_hot_fits_setup (trace.witness_params config proverAccepts).logT
      (trace.witness_params config proverAccepts).chunkBits = true := by
  obtain ⟨isPadded, bounded⟩ := trace.prover_config_trace_length config proverAccepts
  have fits : 2 ^ (trace.witness_params config proverAccepts).logT ≤
      joltInstance.max_padded_trace_length.toNat := by
    have length := trace.witness_params_trace_length config proverAccepts
    unfold WitnessParams.traceLength at length
    rw [length, ← isPadded]
    exact bounded
  have shorter : (trace.witness_params config proverAccepts).logT ≤
      Nat.clog 2 joltInstance.max_padded_trace_length.toNat := by
    have := Nat.clog_mono_right 2 fits
    rwa [Nat.clog_pow 2 _ (by decide)] at this
  have chunk : (trace.witness_params config proverAccepts).chunkBits =
      VerifierSizes.committedLogKChunk (trace.witness_params config proverAccepts).logT := rfl
  unfold JoltInstance.one_hot_fits_setup
  rw [hasLayout, chunk, decide_eq_true_eq]
  exact VerifierSizes.chunks_fit_dorySetupLogN layout _ _ shorter
