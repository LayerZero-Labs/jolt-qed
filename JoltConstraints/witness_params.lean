/-
The witness sizes Rust's prover uses for an honest run, built from the prover config
and the bytecode instead of taken as free parameters.
-/
import JoltConstraints.trace_facts
import JoltConstraints.witness

set_option autoImplicit false

-- An accepted run's padded length is 2^logT with logT below 64: it is a power of two
-- and at most the instance's 64-bit maximum.
theorem HonestTrace.prover_config_log_trace_length_lt
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (trace : HonestTrace joltInstance privateInputs) (config : ProverConfig)
    (accepted : trace.prover_config = some config) :
    Nat.log2 config.trace_length < 64 := by
  obtain ⟨isPadded, fitsMaximum⟩ := trace.prover_config_trace_length config accepted
  obtain ⟨_, _, log, isPower⟩ := padded_trace_length_spec trace.rows.size
  rw [isPadded, isPower, Nat.log2_two_pow]
  have maximumFits := joltInstance.max_padded_trace_length.isLt
  rw [isPadded, isPower] at fitsMaximum
  exact (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp (by omega)

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

-- A row's memory address is a 64-bit value.
theorem TraceRow.ram_address_lt {bytecode : Array JoltInstructionRow}
    (row : TraceRow bytecode) (address : Nat) (touches : row.ram_address = some address) :
    address < 2 ^ 64 := by
  unfold TraceRow.ram_address at touches
  split at touches
  · -- LD
    cases touches
    exact BitVec.isLt _
  · -- SD
    cases touches
    exact BitVec.isLt _
  · -- no other instruction touches memory
    cases touches

-- The slot of an address below 2^64 is below 2^61: it counts 64-bit steps.
theorem remap_address_lt (layout : MemoryLayout) (address : Nat) (fits : address < 2 ^ 64) :
    (remap_address layout address).getD 0 < 2 ^ 61 := by
  have steps : (2 : Nat) ^ 64 = 8 * 2 ^ 61 := by norm_num
  unfold remap_address
  split
  · exact Nat.two_pow_pos 61
  · dsimp only [Option.getD]
    omega

-- The program image's lowest address is a 64-bit value.
theorem min_bytecode_address_lt (memory_init : List (BitVec 64 × BitVec 8)) :
    min_bytecode_address memory_init < 2 ^ 64 := by
  unfold min_bytecode_address
  apply min?_getD_lt _ _ (Nat.two_pow_pos 64)
  intro address member
  obtain ⟨entry, _, isAddress⟩ := List.mem_map.mp member
  rw [← isAddress]
  exact entry.1.isLt

-- The program image spans at most 2^61 + 2 slots: its bytes have 64-bit addresses.
theorem program_image_len_words_le (memory_init : List (BitVec 64 × BitVec 8)) :
    program_image_len_words memory_init ≤ 2 ^ 61 + 2 := by
  have steps : (2 : Nat) ^ 64 = 8 * 2 ^ 61 := by norm_num
  have highestFits : ((memory_init.map (·.1.toNat)).max?).getD 0 < 2 ^ 64 := by
    apply max?_getD_lt _ _ (Nat.two_pow_pos 64)
    intro address member
    obtain ⟨entry, _, isAddress⟩ := List.mem_map.mp member
    rw [← isAddress]
    exact entry.1.isLt
  unfold program_image_len_words
  dsimp only
  omega

-- An accepted run's RAM size is 2^logRamK with logRamK below 64: every touched slot
-- and the end of the program image come from 64-bit addresses, so they are at most
-- 2^63, and ram_K is the power of two that rounds them up.
-- See : jolt/crates/jolt-prover/src/config.rs:140-143
theorem HonestTrace.prover_config_log_ram_K_lt
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (trace : HonestTrace joltInstance privateInputs) (config : ProverConfig)
    (accepted : trace.prover_config = some config) :
    Nat.log2 config.ram_K < 64 := by
  unfold HonestTrace.prover_config at accepted
  -- the jump check
  rw [bind_some_iff] at accepted
  obtain ⟨_, _, accepted⟩ := accepted
  -- the length check
  rw [bind_some_iff] at accepted
  obtain ⟨_, _, accepted⟩ := accepted
  -- the address check
  rw [bind_some_iff] at accepted
  obtain ⟨_, _, accepted⟩ := accepted
  -- the config itself
  cases accepted
  dsimp only
  -- every touched slot comes from a 64-bit address, so it is below 2^61
  have touchedFits : ((trace.rows.toList.filterMap (·.ram_address)).filterMap
      (remap_address trace.initialState.jolt_device.memory_layout)).max?.getD 0 < 2 ^ 61 := by
    apply max?_getD_lt _ _ (Nat.two_pow_pos 61)
    intro slot member
    obtain ⟨address, member, remapped⟩ := List.mem_filterMap.mp member
    obtain ⟨row, _, touches⟩ := List.mem_filterMap.mp member
    have below := remap_address_lt trace.initialState.jolt_device.memory_layout address
      (row.ram_address_lt address touches)
    rw [remapped] at below
    exact below
  -- the image starts at a slot below 2^61 and spans at most 2^61 + 2 slots
  have imageStartFits := remap_address_lt trace.initialState.jolt_device.memory_layout _
    (min_bytecode_address_lt joltInstance.program.memory_init)
  have imageLength := program_image_len_words_le joltInstance.program.memory_init
  -- so both are at most 2^63, and ram_K is 2^c with c at most 63
  have quarters : (2 : Nat) ^ 63 = 4 * 2 ^ 61 := by norm_num
  rw [Nat.log2_two_pow]
  exact Nat.lt_of_le_of_lt (m := 63) (Nat.clog_le_of_le_pow (by omega)) (by decide)

-- The preprocessed bytecode has 2^logBytecodeK slots with logBytecodeK below 64: the
-- PC map accepts fewer than 2^32 rows.
theorem HonestTrace.log_bytecode_size_lt
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (trace : HonestTrace joltInstance privateInputs) :
    max 1 (Nat.clog 2 (trace.bytecode.size + 1)) < 64 := by
  have fewRows := pc_map_ok_size trace.bytecode
    (accepted_pc_map_ok joltInstance trace.bytecode trace.expands trace.accepted)
  have atMost := Nat.clog_le_of_le_pow (b := 2) (y := 32) (by omega : trace.bytecode.size + 1 ≤ 2 ^ 32)
  omega

-- The witness sizes Rust's prover uses for an accepted run: the padded length and
-- ram_K from the prover config, the bytecode size from preprocessing (preprocess_slots:
-- max 2 (2 ^ clog 2 (rows + 1)) slots), and the chunk widths Rust picks from the length:
-- 4 and 16 below 2^25 cycles, else 8 and 32.
-- See : jolt/crates/jolt-prover/src/config.rs:231-243 (one_hot_config)
--       jolt/common/src/constants.rs:13 (ONEHOT_CHUNK_THRESHOLD_LOG_T = 25)
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
  logT_lt_usizeBits := trace.prover_config_log_trace_length_lt config accepted
  logRamK_lt_usizeBits := trace.prover_config_log_ram_K_lt config accepted
  logBytecodeK_lt_usizeBits := trace.log_bytecode_size_lt

-- Rust's sizes use the chunk widths Rust's prover picks.
theorem HonestTrace.witness_params_chunk_config
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (trace : HonestTrace joltInstance privateInputs) (config : ProverConfig)
    (accepted : trace.prover_config = some config) :
    (trace.witness_params config accepted).ProverChunkConfig := by
  unfold WitnessParams.ProverChunkConfig HonestTrace.witness_params
  dsimp only
  by_cases small : Nat.log2 config.trace_length < 25
  · exact Or.inl ⟨small, if_pos small, if_pos small⟩
  · exact Or.inr ⟨by omega, if_neg small, if_neg small⟩

-- For n ≥ 1, the smallest power of two that holds n + 1 is the one just above n.
theorem clog_succ_eq_log2_succ (n : Nat) (positive : 1 ≤ n) :
    Nat.clog 2 (n + 1) = Nat.log2 n + 1 := by
  have below := (Nat.lt_log2_self (n := n))
  have above := Nat.log2_self_le (n := n) (by omega)
  apply Nat.le_antisymm
  · exact (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mpr (by omega)
  · by_contra tooSmall
    have fits := (Nat.clog_le_iff_le_pow (by decide : 1 < 2)
      (x := n + 1) (y := Nat.log2 n)).mp (by omega)
    omega

-- Rust's padded length is the witness's prover length with Rust's 256-cycle floor.
theorem padded_trace_length_eq_prover (rows : Nat) :
    padded_trace_length rows = WitnessParams.proverTraceLength 8 rows := by
  unfold padded_trace_length WitnessParams.proverTraceLength
  have below := (Nat.lt_log2_self (n := rows))
  split
  · -- a short run: the power of two above it is at most 256
    rename_i short
    have small : 2 ^ (Nat.log2 rows + 1) ≤ 2 ^ 8 := by
      apply Nat.pow_le_pow_right (by decide)
      by_cases zero : rows = 0
      · subst zero
        decide
      · have := (Nat.log2_lt zero (k := 8)).mpr (by omega)
        omega
    have floor : (2 : Nat) ^ 8 = 256 := rfl
    omega
  · -- a longer run: the power of two that holds rows + 1 is the one above rows
    rename_i long
    rw [clog_succ_eq_log2_succ rows (by omega)]
    have floor : (2 : Nat) ^ 8 = 256 := rfl
    omega

-- The witness length Rust's sizes give is the run's padded length.
theorem HonestTrace.witness_params_trace_length {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (config : ProverConfig) (accepted : trace.prover_config = some config) :
    (trace.witness_params config accepted).traceLength = padded_trace_length trace.rows.size := by
  obtain ⟨isPadded, _⟩ := trace.prover_config_trace_length config accepted
  obtain ⟨_, _, log, isPower⟩ := padded_trace_length_spec trace.rows.size
  unfold WitnessParams.traceLength HonestTrace.witness_params
  dsimp only
  rw [isPadded, isPower, Nat.log2_two_pow]

-- Rust's sizes pad the run as its prover does (the old ProverPaddedFor assumption).
theorem HonestTrace.witness_params_padded {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (config : ProverConfig) (accepted : trace.prover_config = some config) :
    (trace.witness_params config accepted).ProverPaddedFor trace.rows.size := by
  rw [WitnessParams.ProverPaddedFor, trace.witness_params_trace_length config accepted,
    padded_trace_length_eq_prover]
  exact ⟨Or.inl rfl, by
    rw [← padded_trace_length_eq_prover]
    exact (padded_trace_length_spec trace.rows.size).1⟩

-- Rust's sizes give the bytecode its preprocessed size (the old BytecodeDomainFor
-- assumption): a NoOp, the rows, and padding to a power of two, at least 2.
theorem HonestTrace.witness_params_bytecode_domain {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (config : ProverConfig) (accepted : trace.prover_config = some config) :
    (trace.witness_params config accepted).BytecodeDomainFor trace.bytecode.size := by
  unfold WitnessParams.BytecodeDomainFor WitnessParams.preprocessedBytecodeSize
    HonestTrace.witness_params
  dsimp only
  by_cases zero : Nat.clog 2 (trace.bytecode.size + 1) = 0
  · rw [zero]
    rfl
  · have atLeastOne : 1 ≤ Nat.clog 2 (trace.bytecode.size + 1) := by omega
    have big := Nat.pow_le_pow_right (by decide : 2 > 0) atLeastOne
    rw [Nat.max_eq_right atLeastOne]
    omega

-- Rust's sizes split a RAM slot number into at least one chunk: ram_K is at least 2,
-- so logRamK is at least 1.
theorem HonestTrace.witness_params_ram_chunks_pos {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (config : ProverConfig) (accepted : trace.prover_config = some config) :
    0 < (trace.witness_params config accepted).ramChunks := by
  have atLeastTwo := trace.prover_config_ram_K_ge_two config accepted
  have logPositive : 1 ≤ Nat.log2 config.ram_K := (Nat.le_log2 (by omega)).mpr atLeastTwo
  have chunkPositive := (trace.witness_params config accepted).chunkBits_pos
  unfold WitnessParams.ramChunks
  change 0 < (Nat.log2 config.ram_K + _ - 1) / _
  exact Nat.div_pos (by omega) chunkPositive
