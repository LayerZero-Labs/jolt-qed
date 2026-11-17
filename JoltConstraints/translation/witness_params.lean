/-
The witness sizes Jolt's prover picks, built from its config and the bytecode
instead of taken as free parameters.
-/
import JoltConstraints.theorems.trace_facts
import JoltConstraints.theorems.prover_config_facts
import JoltConstraints.translation.witness

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
    · rw [ite_eq_left small, ite_eq_left small]
      decide
    · rw [ite_eq_right small, ite_eq_right small]
      decide
  virtualChunkBits_dvd_lookup := by
    split
    · decide
    · decide
  logT_lt_usizeBits := trace.prover_config_log_trace_length_lt config proverAccepts
  logRamK_lt_usizeBits := trace.prover_config_log_ram_K_lt config proverAccepts
  logBytecodeK_lt_usizeBits := trace.log_bytecode_size_lt
