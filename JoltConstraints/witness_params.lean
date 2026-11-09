/-
The witness sizes Jolt's prover picks, built from its config and the bytecode
instead of taken as free parameters.
-/
import JoltConstraints.trace_facts
import JoltConstraints.prover_config_facts
import JoltConstraints.witness

open LeanRV64D

set_option autoImplicit false

/-- When Jolt's prover accepts the honest trace (`proverAccepts`), the base-two logarithm
of its padded length `config.trace_length` is below 64: the length is a power of two at
most the instance's 64-bit maximum.
For example, a 300-row run pads to `512 = 2^9`, and `9 < 64`.
See jolt/crates/jolt-prover/src/config.rs (`ProverConfig::from_padded_dimensions`)
at c6703570. -/
theorem HonestTrace.prover_config_log_trace_length_lt
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (trace : HonestTrace joltInstance privateInputs) (config : ProverConfig)
    (proverAccepts : trace.prover_config joltInstance = some config) :
    Nat.log2 config.trace_length < 64 := by
  obtain ⟨isPadded, fitsMaximum⟩ := trace.prover_config_trace_length config proverAccepts
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

/-- Every recorded RAM byte address fits in 64 bits, including a floor row's
`ea - (ea &&& mask)`; for example, a byte floor row at effective address 11
records 8, which is still below `2^64`.
Jolt's tracer: `tracer/src/instruction/floor_access.rs` (`addresses`) and
`crates/jolt-riscv/src/trace_row.rs` (`ram_address`) at `c6703570`. -/
theorem TraceRow.ram_address_lt {bytecode : Array JoltInstructionRow}
    (row : TraceRow bytecode) (address : Nat) (touches : row.ram_address = some address) :
    address < 2 ^ 64 := by
  unfold TraceRow.ram_address at touches
  split at touches <;> cases touches
  all_goals exact BitVec.isLt _

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

/-- When Jolt's prover accepts the honest trace (`proverAccepts`), the base-two logarithm
of its RAM size `config.ram_K` is below 64: Jolt's prover checks that the rounded size
fits in 64 bits (`HonestTrace.prover_config_ram_K`).
For example, `ram_K = 1024 = 2^10` gives `10 < 64`.
See jolt/crates/jolt-prover/src/config.rs (`ProverConfig::derive_from_dimensions`)
at c97e9300. -/
theorem HonestTrace.prover_config_log_ram_K_lt
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (trace : HonestTrace joltInstance privateInputs) (config : ProverConfig)
    (proverAccepts : trace.prover_config joltInstance = some config) :
    Nat.log2 config.ram_K < 64 := by
  obtain ⟨_, _, _, sizeIs, sizeFits⟩ := trace.prover_config_ram_K config proverAccepts
  rw [sizeIs] at sizeFits ⊢
  rw [Nat.log2_two_pow]
  exact (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp sizeFits

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

/-- The witness sizes Jolt's prover uses for the honest trace, when it accepts the trace
with config `config` (`proverAccepts`):
`logT` and `logRamK` are the base-two logarithms of the config's padded length
`config.trace_length` and RAM size `config.ram_K`;
`logBytecodeK` is the logarithm of the preprocessed bytecode size, a NoOp plus the rows
padded to a power of two, at least 2 (`max 2 (2 ^ clog 2 (rows + 1))` slots);
the committed and virtual chunk widths are 4 and 16 bits below `2^25` cycles, else 8
and 32 (`ONEHOT_CHUNK_THRESHOLD_LOG_T = 25`).
For example, a 300-row run of a 5-row bytecode with `ram_K = 1024` gets `logT = 9`,
`logRamK = 10`, `logBytecodeK = 3`, and widths 4 and 16.
See jolt/crates/jolt-prover/src/config.rs (`ProverConfig::from_padded_dimensions`,
`one_hot_config`), jolt/crates/jolt-prover/src/dory/stages/stage0.rs (the
`validate_inputs_from_parts` call with `config.trace_length`, `config.ram_K` and
`config.one_hot_config`), jolt/crates/jolt-program/src/preprocess/bytecode.rs
(`BytecodePreprocessing::preprocess`, `code_size`) and jolt/common/src/constants.rs
(`ONEHOT_CHUNK_THRESHOLD_LOG_T`) at c6703570. -/
noncomputable def HonestTrace.witness_params
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (trace : HonestTrace joltInstance privateInputs) (config : ProverConfig)
    (proverAccepts : trace.prover_config joltInstance = some config) : WitnessParams where
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
  logT_lt_usizeBits := trace.prover_config_log_trace_length_lt config proverAccepts
  logRamK_lt_usizeBits := trace.prover_config_log_ram_K_lt config proverAccepts
  logBytecodeK_lt_usizeBits := trace.log_bytecode_size_lt

/-- Jolt's witness sizes use the chunk widths Jolt's prover picks
(`WitnessParams.ProverChunkConfig`): 4 and 16 bits below `2^25` cycles, else 8 and 32.
For example, a run padded to `2^9` cycles uses widths 4 and 16.
See jolt/crates/jolt-prover/src/config.rs (`one_hot_config`) at c6703570. -/
theorem HonestTrace.witness_params_chunk_config
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (trace : HonestTrace joltInstance privateInputs) (config : ProverConfig)
    (proverAccepts : trace.prover_config joltInstance = some config) :
    (trace.witness_params config proverAccepts).ProverChunkConfig := by
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

/-- The witness length at Jolt's sizes, `2 ^ logT`, is the run's padded length
`padded_trace_length trace.rows.size`.
For example, a 300-row run gets a 512-cycle witness. -/
theorem HonestTrace.witness_params_trace_length {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (config : ProverConfig) (proverAccepts : trace.prover_config joltInstance = some config) :
    (trace.witness_params config proverAccepts).traceLength =
      padded_trace_length trace.rows.size := by
  obtain ⟨isPadded, _⟩ := trace.prover_config_trace_length config proverAccepts
  obtain ⟨_, _, log, isPower⟩ := padded_trace_length_spec trace.rows.size
  unfold WitnessParams.traceLength HonestTrace.witness_params
  dsimp only
  rw [isPadded, isPower, Nat.log2_two_pow]

/-- Jolt's sizes pad the run as Jolt's base prover does (`WitnessParams.ProverPaddedFor`):
the witness length is the 256-cycle-floor padding of the row count, and it exceeds the
row count.
For example, a 300-row run gets 512 cycles, one of them at least padding. -/
theorem HonestTrace.witness_params_padded {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (config : ProverConfig) (proverAccepts : trace.prover_config joltInstance = some config) :
    (trace.witness_params config proverAccepts).ProverPaddedFor trace.rows.size := by
  rw [WitnessParams.ProverPaddedFor, trace.witness_params_trace_length config proverAccepts,
    padded_trace_length_eq_prover]
  exact ⟨Or.inl rfl, by
    rw [← padded_trace_length_eq_prover]
    exact (padded_trace_length_spec trace.rows.size).1⟩

/-- Jolt's sizes give the bytecode its preprocessed size (`WitnessParams.BytecodeDomainFor`):
a NoOp, the rows, and padding to a power of two, at least 2.
For example, 5 rows give `2 ^ clog 2 6 = 8` slots. -/
theorem HonestTrace.witness_params_bytecode_domain {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (config : ProverConfig) (proverAccepts : trace.prover_config joltInstance = some config) :
    (trace.witness_params config proverAccepts).BytecodeDomainFor trace.bytecode.size := by
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

/-- Jolt's sizes split a RAM word index into at least one chunk (`WitnessParams.ramChunks`):
`config.ram_K` is at least 2 (`HonestTrace.prover_config_ram_K_ge_two`), so `logRamK` is
at least 1.
For example, `ram_K = 1024` with 4-bit chunks gives `(10 + 4 - 1) / 4 = 3` chunks. -/
theorem HonestTrace.witness_params_ram_chunks_pos {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (config : ProverConfig) (proverAccepts : trace.prover_config joltInstance = some config) :
    0 < (trace.witness_params config proverAccepts).ramChunks := by
  have atLeastTwo := trace.prover_config_ram_K_ge_two config proverAccepts
  have logPositive : 1 ≤ Nat.log2 config.ram_K := (Nat.le_log2 (by omega)).mpr atLeastTwo
  have chunkPositive := (trace.witness_params config proverAccepts).chunkBits_pos
  unfold WitnessParams.ramChunks
  change 0 < (Nat.log2 config.ram_K + _ - 1) / _
  exact Nat.div_pos (by omega) chunkPositive
