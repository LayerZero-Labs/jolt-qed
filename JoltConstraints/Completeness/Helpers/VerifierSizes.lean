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

end JoltConstraints
