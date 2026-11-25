import JoltConstraints.theorems.Completeness.Helpers.RamReadSelection

open LeanRV64D

set_option autoImplicit false

-- The largest of a list of numbers below a bound is below it; an empty list gives 0.
theorem max?_getD_lt (numbers : List Nat) (bound : Nat) (positive : 0 < bound)
    (allBelow : ∀ number ∈ numbers, number < bound) :
    numbers.max?.getD 0 < bound := by
  cases largest : numbers.max? with
  | none => exact positive
  | some number => exact allBelow number (List.max?_mem largest)

-- The smallest of a list of numbers below a bound is below it; an empty list gives 0.
theorem min?_getD_lt (numbers : List Nat) (bound : Nat) (positive : 0 < bound)
    (allBelow : ∀ number ∈ numbers, number < bound) :
    numbers.min?.getD 0 < bound := by
  cases smallest : numbers.min? with
  | none => exact positive
  | some number => exact allBelow number (List.min?_mem smallest)

/-- The word index `(address - lowest) / 8` of an address below `bound` is below the number
of words that start below `bound`, `⌈(bound - lowest) / 8⌉ = (bound - lowest + 7) / 8`,
where `lowest` is the layout's lowest address, below `bound`; address 0 (no access) and
an address below `lowest` count as index 0.
For example, with lowest address 16, an address 40 below a bound 44 has index
`3 < (44 - 16 + 7) / 8 = 4`. -/
theorem remap_address_lt (layout : MemoryLayout) (address bound : Nat)
    (lowestBelow : layout.get_lowest_address.toNat < bound) (below : address < bound) :
    (remap_address layout address).getD 0 <
      (bound - layout.get_lowest_address.toNat + 7) / 8 := by
  unfold remap_address
  split
  · dsimp only [Option.getD]
    omega
  · dsimp only [Option.getD]
    omega

/-- The program image's lowest address, `min_bytecode_address`, is below any positive
`bound` that every image address is below; an empty image gives 0.
For example, an image of bytes at `0x80000000` and `0x80000004` has lowest address
`0x80000000`, below its program end `0x80000008`. -/
theorem min_bytecode_address_lt (memory_init : List (BitVec 64 × BitVec 8)) (bound : Nat)
    (positive : 0 < bound) (allBelow : ∀ entry ∈ memory_init, entry.1.toNat < bound) :
    min_bytecode_address memory_init < bound := by
  unfold min_bytecode_address
  apply min?_getD_lt _ _ positive
  intro address member
  obtain ⟨entry, inImage, isAddress⟩ := List.mem_map.mp member
  rw [← isAddress]
  exact allBelow entry inImage

/-- When every image address is below a positive `bound`, the program image's first
word index `min_bytecode_address / 8` plus its word count `program_image_len_words`
(the span from its lowest byte's word to the word of its highest byte plus 3, the rest
of a 4-byte instruction) is at most `(bound + 9) / 8 + 1`.
For example, one byte at `0x80000000` with bound `0x80000001` gives first word
`0x10000000` and 2 words, and `0x10000002 ≤ 0x10000001 + 1`.
At `bound = 2^64` the image spans at most `2^61 + 2` words. -/
theorem program_image_len_words_le (memory_init : List (BitVec 64 × BitVec 8)) (bound : Nat)
    (positive : 0 < bound) (allBelow : ∀ entry ∈ memory_init, entry.1.toNat < bound) :
    min_bytecode_address memory_init / 8 + program_image_len_words memory_init ≤
      (bound + 9) / 8 + 1 := by
  have highestBelow : ((memory_init.map (·.1.toNat)).max?).getD 0 < bound := by
    apply max?_getD_lt _ _ positive
    intro address member
    obtain ⟨entry, inImage, isAddress⟩ := List.mem_map.mp member
    rw [← isAddress]
    exact allBelow entry inImage
  have lowestBelow := min_bytecode_address_lt memory_init bound positive allBelow
  unfold program_image_len_words
  dsimp only
  omega

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
`checked_remap_address`) at ff6fc6568. -/
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
  simp only [ite_eq_right imageNonzero] at unfolded
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
jolt/crates/jolt-prover/src/config.rs (`ProverConfig::derive_from_dimensions`) at ff6fc6568. -/
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
  simp only [ite_eq_right ramNonzero] at remappedIo
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
See jolt/common/src/jolt_device.rs (`MemoryLayout::try_new`) at ff6fc6568. -/
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
  -- input end and output end
  iterate 2 (rw [bind_some_iff] at built; obtain ⟨_, _, built⟩ := built)
  -- stack end, stack start, heap end
  rw [bind_some_iff] at built
  obtain ⟨stackEnd, stackEndAdded, built⟩ := built
  rw [bind_some_iff] at built
  obtain ⟨stackStart, stackStartAdded, built⟩ := built
  rw [bind_some_iff] at built
  obtain ⟨heapEnd, heapEndAdded, built⟩ := built
  rw [bind_some_iff] at built
  obtain ⟨_, _, built⟩ := built
  cases built
  rw [bind_some_iff] at stackStartAdded
  obtain ⟨withCanary, canaryAdded, stackStartAdded⟩ := stackStartAdded
  obtain ⟨stackEndIs, _⟩ := checkedAdd_some stackEndAdded
  obtain ⟨withCanaryIs, _⟩ := checkedAdd_some canaryAdded
  obtain ⟨stackStartIs, _⟩ := checkedAdd_some stackStartAdded
  obtain ⟨rawHeapEnd, rawHeapAdded, heapRounded⟩ := Option.bind_eq_some_iff.mp heapEndAdded
  obtain ⟨heapEndIs, heapEndFits⟩ := checkedAdd_some rawHeapAdded
  have heapGe := (alignUp8_some heapRounded).1
  have finalHeapFits : heapEnd < 2^64 := by
    unfold MemoryLayout.alignUp8 at heapRounded
    split at heapRounded
    · have same := Option.some.inj heapRounded
      omega
    · obtain ⟨same, bound⟩ := checkedAdd_some heapRounded
      omega
  refine ⟨programSize, programSizeIs, ?_⟩
  dsimp only
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt finalHeapFits]
  omega

/-- In the instance's starting layout, `heap_end` lies at least `STACK_CANARY_SIZE = 128`
bytes past the program image's end `program_end`: the host sets the program size to
`program_end - RAM_START_ADDRESS` (`Rv64ProgramImage.program_size`).
For example, an image ending at `0x80001000` gives `heap_end ≥ 0x80001080`.
See jolt/common/src/jolt_device.rs (`MemoryLayout::try_new`) at ff6fc6568. -/
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
  have ioEnd := congrArg BitVec.toNat geometry.2.2.1
  omega

private theorem highest_ram_slot_below_domain (trace : Trace) (maximum : Nat)
    (positive : 0 < maximum)
    (accesses : ∀ i (inTrace : i < trace.rows.size) address,
      (trace.rows[i]'inTrace).ram_address = some address →
      address < trace.initialState.jolt_device.memory_layout.get_lowest_address.toNat +
        8 * maximum) : trace.highest_ram_slot < maximum := by
  unfold Trace.highest_ram_slot
  apply max?_getD_lt _ _ positive
  intro slot member
  obtain ⟨address, member, remapped⟩ := List.mem_filterMap.mp member
  obtain ⟨row, inRows, touches⟩ := List.mem_filterMap.mp member
  obtain ⟨i, inTrace, isRow⟩ := Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp inRows)
  subst isRow
  have bounded := remap_address_lt trace.initialState.jolt_device.memory_layout address _
    (by omega) (accesses i inTrace address touches)
  rw [remapped] at bounded
  simp only [Option.getD_some] at bounded
  omega

private theorem backing_end_of_domain (base lowest : Nat) (domain : Option Nat)
    (maximum : Nat) (computed : domain = some maximum)
    (above : base ≤ lowest + 8 * maximum) :
    base + (domain.map fun k => lowest + 8 * k - base).getD 0 =
      lowest + 8 * maximum := by
  rw [computed]
  simp only [Option.map_some, Option.getD_some]
  omega

private theorem checked_backing_end (device : JoltDevice) (maximum : Nat)
    (computed : device.memory_layout.max_ram_k? = some maximum)
    (lowestAligned : device.memory_layout.get_lowest_address.toNat % 8 = 0)
    (heapAboveRam : JoltISA.RAM_START_ADDRESS + 128 ≤ device.memory_layout.heap_end.toNat) :
    0 < maximum ∧ JoltISA.Mmu.ram_backing_end device =
      device.memory_layout.get_lowest_address.toNat + 8 * maximum := by
  obtain ⟨heapAligned, lowestBelowHeap, maximumIs, _⟩ :=
    max_ram_k_spec device.memory_layout maximum computed
  have rounded := Nat.le_nextPowerOfTwo ((device.memory_layout.heap_end.toNat -
    device.memory_layout.get_lowest_address.toNat) / 8)
  rw [← maximumIs] at rounded
  have positive : 0 < maximum := by
    rw [maximumIs]
    obtain ⟨exponent, power⟩ := Nat.isPowerOfTwo_nextPowerOfTwo
      ((device.memory_layout.heap_end.toNat - device.memory_layout.get_lowest_address.toNat) / 8)
    rw [power]
    exact Nat.two_pow_pos _
  refine ⟨positive, ?_⟩
  exact backing_end_of_domain _ _ _ maximum computed (by omega)

/-- Every touched word lies in the checked maximum padded RAM domain.
For example, a store after `heap_end` can touch heap padding, but cannot reach
one word past the maximum admitted backing allocation.
Jolt at `ff6fc6568`: `common/src/jolt_device.rs` (`MemoryLayout::max_ram_k`)
and `tracer/src/emulator/mmu.rs` (`assert_effective_address`). -/
theorem HonestTrace.highest_ram_slot_lt_maximum {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs) :
    trace.highest_ram_slot <
      trace.initialState.jolt_device.memory_layout.max_ram_k?.getD 0 := by
  have built := (initial_state_device joltInstance privateInputs _ trace.initialized).1
  obtain ⟨maximum, computed⟩ := Option.isSome_iff_exists.mp (new_max_ram_k _ _ built)
  have programBelow := trace.program_end_below_heap_end
  have aboveStart := joltInstance.program.program_end_ge_ram_start
  have lowestBelow := trace.lowest_address_le_ram_start
  have stackCanary : JoltISA.STACK_CANARY_SIZE = 128 := rfl
  obtain ⟨positive, backing⟩ := checked_backing_end trace.initialState.jolt_device maximum computed
    (new_lowest_address_aligned _ _ built) (by omega)
  rw [computed, Option.getD_some]
  apply highest_ram_slot_below_domain trace.toTrace maximum positive
  intro i inTrace address touches
  by_cases inRam : JoltISA.RAM_START_ADDRESS ≤ address
  · rw [← backing]
    exact trace.ram_address_below_ram_backing_end i inTrace address touches inRam
  · have reachesHeap := heap_end_le_ram_backing_end trace.initialState.jolt_device _ built
    rw [backing] at reachesHeap
    omega

/-- When Jolt's prover accepts the honest trace (`proverAccepts`) of a nonempty program,
Jolt's verifier computes its RAM minimum (`VerifierSizes.minRamSize`, Jolt's
`compute_min_ram_k`): the image's start and end words are the ones Jolt's prover already
computed, the word index of `RAM_START_ADDRESS` exists because the lowest address is
below RAM, and rounding fits in 64 bits because Jolt's RAM size, which is at least as
large, does.
For example, an image of words 4096 to 4135 with lowest address `0x7fff8000` has minimum
`pow2(max(4136, 4096)) = 8192`.
See jolt/crates/jolt-program/src/preprocess/ram.rs (`compute_min_ram_k`) at ff6fc6568. -/
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
    rw [ite_eq_left (by omega)]
  have ioRemapped : VerifierSizes.remapWordAddress trace.initialState.jolt_device.memory_layout
      JoltISA.RAM_START_ADDRESS = some (some ((JoltISA.RAM_START_ADDRESS -
        trace.initialState.jolt_device.memory_layout.get_lowest_address.toNat) / 8)) := by
    unfold VerifierSizes.remapWordAddress MemoryLayout.checkedSub
    simp only [ite_eq_right ramNonzero, ite_eq_left lowestBelow]
    rfl
  refine ⟨2 ^ Nat.clog 2 ((min_bytecode_address joltInstance.program.memory_init -
      trace.initialState.jolt_device.memory_layout.get_lowest_address.toNat) / 8 +
        program_image_len_words joltInstance.program.memory_init), ?_⟩
  unfold VerifierSizes.minRamSize
  rw [remapped]
  simp only [Option.getD_some, Option.bind_eq_bind, Option.bind_some, endAdded, ioRemapped]
  rw [Nat.max_eq_left (by omega)]
  simp only [VerifierSizes.checkedNextPowerOfTwo, ite_eq_left rounded]

/-- The honest prover's RAM size is at most the checked maximum allocation.
For example, touching heap padding can enlarge the chosen domain up to that maximum.
Jolt at `ff6fc6568`: `crates/jolt-program/src/preprocess/ram.rs`
(`compute_max_ram_k`) and `crates/jolt-prover/src/config.rs`
(`ProverConfig::derive_from_dimensions`). -/
theorem HonestTrace.witness_params_ram_maximum
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (trace : HonestTrace joltInstance privateInputs)
    (config : ProverConfig) (proverAccepts : trace.prover_config joltInstance = some config)
    (nonempty : joltInstance.program.memory_init ≠ []) :
    ∃ maximum, VerifierSizes.maxRamSize trace.initialState.jolt_device.memory_layout =
        some maximum ∧
      (trace.witness_params config proverAccepts).ramSize ≤ maximum := by
  let layout := trace.initialState.jolt_device.memory_layout
  have built := (initial_state_device joltInstance privateInputs _ trace.initialized).1
  obtain ⟨maximum, computed⟩ := Option.isSome_iff_exists.mp (new_max_ram_k _ layout built)
  obtain ⟨heapAligned, lowestBelowHeap, maximumIs, _⟩ := max_ram_k_spec layout maximum computed
  have rounded := Nat.le_nextPowerOfTwo ((layout.heap_end.toNat -
    layout.get_lowest_address.toNat) / 8)
  rw [← maximumIs] at rounded
  have programBelow := trace.program_end_below_heap_end
  have aboveStart := joltInstance.program.program_end_ge_ram_start
  have touchedBelow := trace.highest_ram_slot_lt_maximum
  change trace.highest_ram_slot < layout.max_ram_k?.getD 0 at touchedBelow
  rw [computed, Option.getD_some] at touchedBelow
  have imageWords := program_image_len_words_le joltInstance.program.memory_init
    joltInstance.program.program_end.toNat (by unfold JoltISA.RAM_START_ADDRESS at aboveStart; omega)
    (fun entry inImage => (joltInstance.program.memory_init_in_program entry inImage).2)
  obtain ⟨lowestBelowImage, _, _, sizeIs, _⟩ :=
    trace.prover_config_ram_K_of_nonempty config proverAccepts nonempty
  have stackCanary : JoltISA.STACK_CANARY_SIZE = 128 := rfl
  have power : ∃ exponent, maximum = 2 ^ exponent := by
    rw [maximumIs]
    exact Nat.isPowerOfTwo_nextPowerOfTwo _
  obtain ⟨exponent, power⟩ := power
  refine ⟨maximum, computed, ?_⟩
  rw [trace.witness_params_ram_size config proverAccepts, sizeIs, power]
  apply Nat.pow_le_pow_right (by decide : 0 < 2)
  apply Nat.clog_le_of_le_pow
  rw [← power]
  dsimp only [layout] at *
  apply Nat.max_le.mpr
  constructor
  · omega
  · omega

/-- Jolt's RAM size passes Jolt's verifier's RAM bounds (`JoltInstance.ram_size_in_bounds`):
the verifier computes both its minimum and its maximum
(`HonestTrace.verifier_ram_minimum_computes`, `HonestTrace.witness_params_ram_maximum`),
and Jolt's RAM size `config.ram_K` lies between them
(`HonestTrace.witness_params_ram_minimum_of_nonempty`).
The program is not empty, because Jolt's prover accepts its run
(`HonestTrace.prover_config_image_nonempty`).
For example, with lowest address `0x7fff8000` and `heap_end = 0x80010000`, a run
touching word 1000 with an image of words 4096 to 4135 gets
`ram_K = pow2(max(1001, 4137)) = 8192`, between the minimum 8192 and the maximum 16384. -/
theorem HonestTrace.witness_params_ram_bounds
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (trace : HonestTrace joltInstance privateInputs)
    (config : ProverConfig) (proverAccepts : trace.prover_config joltInstance = some config) :
    joltInstance.ram_size_in_bounds (trace.witness_params config proverAccepts).ramSize = true := by
  have imageNonempty := trace.prover_config_image_nonempty config proverAccepts
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
See jolt/crates/jolt-prover/src/dory/preprocessing.rs (`setup_total_vars`) at ff6fc6568. -/
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
