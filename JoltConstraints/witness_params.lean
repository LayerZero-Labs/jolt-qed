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

-- An accepted run's RAM size is 2^logRamK with logRamK below 64.
-- TODO: prove: every address a run touches is below heap_end (the MMU checks it), so
-- every touched slot, the program image end, and so ram_K, are at most 2^61.
theorem HonestTrace.prover_config_log_ram_K_lt
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (trace : HonestTrace joltInstance privateInputs) (config : ProverConfig)
    (accepted : trace.prover_config = some config) :
    Nat.log2 config.ram_K < 64 := by
  sorry

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
  proverChunkConfig := by
    by_cases small : Nat.log2 config.trace_length < 25
    · exact Or.inl ⟨small, if_pos small, if_pos small⟩
    · exact Or.inr ⟨by omega, if_neg small, if_neg small⟩
  logT_lt_usizeBits := trace.prover_config_log_trace_length_lt config accepted
  logRamK_lt_usizeBits := trace.prover_config_log_ram_K_lt config accepted
  logBytecodeK_lt_usizeBits := trace.log_bytecode_size_lt

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

