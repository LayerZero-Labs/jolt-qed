import JoltConstraints.verifier_sizes
import JoltConstraints.witness_domain

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

-- If the verifier computes a minimum for a nonempty image, the prover's chosen
-- RAM size meets it. No additional condition is imposed on the final theorem.
theorem _root_.HonestTrace.witness_params_ram_minimum_of_nonempty
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (trace : HonestTrace joltInstance privateInputs)
    (config : ProverConfig) (accepted : trace.prover_config = some config)
    (nonempty : joltInstance.program.memory_init ≠ []) (minimum : Nat)
    (computed : VerifierSizes.minRamSize joltInstance.program
      trace.initialState.jolt_device.memory_layout = some minimum) :
    minimum ≤ (trace.witness_params config accepted).ramSize := by
  have imageAbove := min_bytecode_address_ge_ram_start joltInstance.program nonempty
  have imageNonzero : min_bytecode_address joltInstance.program.memory_init ≠ 0 := by
    unfold JoltISA.RAM_START_ADDRESS at imageAbove
    omega
  unfold VerifierSizes.minRamSize at computed
  rw [bind_some_iff] at computed
  obtain ⟨imageStart, remappedImage, computed⟩ := computed
  rw [bind_some_iff] at computed
  obtain ⟨imageEnd, imageAdded, computed⟩ := computed
  rw [bind_some_iff] at computed
  obtain ⟨ioEnd, remappedIo, computed⟩ := computed
  unfold VerifierSizes.remapWordAddress at remappedImage remappedIo
  simp only [if_neg imageNonzero, pure_bind] at remappedImage
  rw [bind_some_iff] at remappedImage
  obtain ⟨imageOffset, imageSubtracted, remappedImage⟩ := remappedImage
  cases remappedImage
  have ramNonzero : JoltISA.RAM_START_ADDRESS ≠ 0 := by decide
  simp only [if_neg ramNonzero, pure_bind] at remappedIo
  rw [bind_some_iff] at remappedIo
  obtain ⟨ioOffset, ioSubtracted, remappedIo⟩ := remappedIo
  cases remappedIo
  obtain ⟨imageOffsetIs, _⟩ := checkedSub_some imageSubtracted
  obtain ⟨ioOffsetIs, _⟩ := checkedSub_some ioSubtracted
  obtain ⟨imageEndIs, _⟩ := checkedAdd_some imageAdded
  have ioBelow : ioOffset / 8 ≤ imageOffset / 8 := by
    apply Nat.div_le_div_right
    omega
  have imageEndAbove : ioOffset / 8 ≤ imageEnd := by
    simp only [Option.getD_some] at imageEndIs
    omega
  dsimp only at computed
  rw [Nat.max_eq_left imageEndAbove] at computed
  dsimp only [VerifierSizes.checkedNextPowerOfTwo] at computed
  split at computed
  · cases computed
    unfold WitnessParams.ramSize HonestTrace.witness_params
    dsimp only
    unfold HonestTrace.prover_config at accepted
    rw [bind_some_iff] at accepted
    obtain ⟨_, _, accepted⟩ := accepted
    rw [bind_some_iff] at accepted
    obtain ⟨_, _, accepted⟩ := accepted
    rw [bind_some_iff] at accepted
    obtain ⟨_, _, accepted⟩ := accepted
    cases accepted
    dsimp only
    rw [Nat.log2_two_pow]
    apply Nat.pow_le_pow_right (by decide : 0 < 2)
    apply Nat.clog_mono_right
    simp only [remap_address, if_neg imageNonzero, Option.getD_some]
    simp only [Option.getD_some] at imageEndIs
    omega
  · cases computed

-- The prover's chosen RAM size passes the verifier's RAM bounds.
-- FIXME: false until a16z/jolt#1951 item 4 is fixed, so this stays sorry (the upper
-- half below cannot be proved before then).
-- An empty program is excluded by the a16z-confirmed assumption below.
-- Lower half: proved above once the minimum computes; still to prove that both
-- bounds compute successfully.
-- Upper half: false until a16z/jolt#1951 item 4 is fixed. compute_max_ram_k rounds
-- total_bytes / 8 down. When heap_end is not a multiple of 8, a program may access
-- the word that straddles heap_end, and touched + 1 then rounds past the maximum.
theorem _root_.HonestTrace.witness_params_ram_bounds
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (trace : HonestTrace joltInstance privateInputs)
    (config : ProverConfig) (accepted : trace.prover_config = some config)
    -- Assumed: a16z told us by phone on 2026-10-08 that Jolt can assume a program
    -- is never empty, so its memory image loads at least one byte. Rust's prover does
    -- not reject an empty ELF; only its verifier does (bug-report/verifier-ram-minimum).
    (imageNonempty : joltInstance.program.ImageNonempty) :
    joltInstance.ram_size_in_bounds (trace.witness_params config accepted).ramSize = true := by
  sorry

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

-- The honest prover's one-hot chunks fit the verifier's Dory setup: its trace is no
-- longer than the maximum padded length, and its chunk width is the setup's.
theorem _root_.HonestTrace.witness_params_one_hot_fits_setup
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (trace : HonestTrace joltInstance privateInputs)
    (config : ProverConfig) (accepted : trace.prover_config = some config)
    (layout : MemoryLayout) (hasLayout : joltInstance.memory_layout = some layout) :
    joltInstance.one_hot_fits_setup (trace.witness_params config accepted).logT
      (trace.witness_params config accepted).chunkBits = true := by
  obtain ⟨isPadded, bounded⟩ := trace.prover_config_trace_length config accepted
  have fits : 2 ^ (trace.witness_params config accepted).logT ≤
      joltInstance.max_padded_trace_length.toNat := by
    have length := trace.witness_params_trace_length config accepted
    unfold WitnessParams.traceLength at length
    rw [length, ← isPadded]
    exact bounded
  have shorter : (trace.witness_params config accepted).logT ≤
      Nat.clog 2 joltInstance.max_padded_trace_length.toNat := by
    have := Nat.clog_mono_right 2 fits
    rwa [Nat.clog_pow 2 _ (by decide)] at this
  have chunk : (trace.witness_params config accepted).chunkBits =
      VerifierSizes.committedLogKChunk (trace.witness_params config accepted).logT := rfl
  unfold JoltInstance.one_hot_fits_setup
  rw [hasLayout, chunk, decide_eq_true_eq]
  exact VerifierSizes.chunks_fit_dorySetupLogN layout _ _ shorter

end JoltConstraints
