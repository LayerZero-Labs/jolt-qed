import JoltConstraints.Soundness.Layer6.ExecutionPrefix
import JoltConstraints.prover_config

set_option autoImplicit false

namespace JoltInstance

/-- A represented completed relaxed execution passes the prover's last-row
check: it is empty or its final instruction is JAL or JALR.
The trace supplies execution and stopping certificates, while representation
identifies its row observations with the constrained witness.
For example, a taken BEQ with offset zero is a stable stall, but cannot end
such a represented trace because its nonzero target cannot reach witness padding
or the final zero PC shift.
See jolt/crates/jolt-prover/src/config.rs
(`ProverConfig::derive_from_dimensions`) at 5def437f. -/
theorem represented_trace_ends_in_jump
    {F : Type} [Field F] (joltField : JoltField F)
    (joltInstance : JoltInstance SourceInstruction)
    {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (equations : JoltConstraints.ConstraintEquations context.bytecode context.initialRam
      context.io context.entry witness)
    (trace : JoltConstraints.Soundness.UntrustedAnswerTrace joltInstance privateInputs)
    (bytecodeEq : trace.bytecode = context.bytecode)
    (represented : RepresentsRows witness trace.toUntrustedAnswerRun.toTrace) :
    trace.rows.size = 0 ∨ trace.execution_dimensions.ends_in_jump = true := by
  sorry

/-- Checked padding adds a no-op, rounds up to a power of two and enforces the
256-cycle floor, within a 64-bit public maximum.
The row count fits a power-of-two witness domain within that maximum and differs
from the largest admissible power of two; the caller obtains this last condition
from `NoMaxLengthTrace`.
For example, 256 rows under maximum 1024 pad to 512, while 1024 rows are excluded.
See jolt/crates/jolt-prover/src/config.rs
(`ProverConfig::derive_from_dimensions`) and jolt/crates/jolt-verifier/src/config.rs
(`MIN_PADDED_TRACE_LENGTH`, base/Dory) at 5def437f. -/
theorem checked_trace_length_fits
    (rows logT : Nat) (maximum : BitVec 64)
    (rowsBound : rows ≤ 2 ^ logT)
    (witnessBound : 2 ^ logT ≤ maximum.toNat)
    (floor : 256 ≤ maximum.toNat)
    (notMax : rows ≠ 2 ^ Nat.log2 maximum.toNat) :
    ∃ padded, ProverConfig.checkedTraceLength rows = some padded ∧
      padded ≤ maximum.toNat := by
  let maxPower := 2 ^ Nat.log2 maximum.toNat
  have maximumPositive : maximum.toNat ≠ 0 := by omega
  have maxPowerBound : maxPower ≤ maximum.toNat := by
    dsimp [maxPower]
    rw [Nat.log2_eq_log_two]
    exact Nat.pow_log_le_self 2 maximumPositive
  have exponentBound : logT ≤ Nat.log2 maximum.toNat := by
    rw [Nat.log2_eq_log_two]
    exact Nat.le_log_of_pow_le (by decide : 1 < 2) witnessBound
  have rowsBound' : rows ≤ maxPower :=
    rowsBound.trans (Nat.pow_le_pow_right (by decide) exponentBound)
  have withNoopBound : rows + 1 ≤ maxPower := by
    have different : rows ≠ maxPower := notMax
    omega
  have roundedExponentBound : Nat.clog 2 (rows + 1) ≤ Nat.log2 maximum.toNat :=
    Nat.clog_le_of_le_pow withNoopBound
  have roundedBound : 2 ^ Nat.clog 2 (rows + 1) ≤ maxPower :=
    Nat.pow_le_pow_right (by decide) roundedExponentBound
  have withNoopFits : rows + 1 < 2 ^ 64 :=
    lt_of_le_of_lt (withNoopBound.trans maxPowerBound) maximum.isLt
  have roundedFits : 2 ^ Nat.clog 2 (rows + 1) < 2 ^ 64 :=
    lt_of_le_of_lt (roundedBound.trans maxPowerBound) maximum.isLt
  have added : MemoryLayout.checkedAdd rows 1 = some (rows + 1) := by
    simp only [MemoryLayout.checkedAdd, if_pos withNoopFits]
  have rounded : JoltConstraints.VerifierSizes.checkedNextPowerOfTwo (rows + 1) =
      some (2 ^ Nat.clog 2 (rows + 1)) := by
    simp only [JoltConstraints.VerifierSizes.checkedNextPowerOfTwo, if_pos roundedFits]
  refine ⟨max (2 ^ Nat.clog 2 (rows + 1)) 256, ?_, ?_⟩
  · simp [ProverConfig.checkedTraceLength, added, rounded]
  · exact max_le (roundedBound.trans maxPowerBound) floor

/-- Represented RAM addresses and the verifier's RAM bounds make checked prover
RAM sizing succeed for a trace with the instance's initial state.
Only the row-count bound and RAM-address observations are needed from row
representation; no execution or final-memory agreement is assumed here.
Every nonzero address is the layout base plus eight times a selected RAM index;
for example, selected index 3 gives a byte address 24 above that base.
The verifier bounds the image end, and 64-bit addresses bound the touched slots,
so adding the image sentinel and rounding cannot overflow the 64-bit host size.
See jolt/crates/jolt-prover/src/config.rs
(`ProverConfig::derive_from_dimensions`, `checked_remap_address`) and
jolt/crates/jolt-program/src/preprocess/ram.rs
(`compute_min_ram_k`, `compute_max_ram_k`) at 5def437f. -/
theorem represented_ram_size_computes
    {F : Type} [Field F] (joltField : JoltField F)
    (joltInstance : JoltInstance SourceInstruction)
    {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (equations : JoltConstraints.ConstraintEquations context.bytecode context.initialRam
      context.io context.entry witness)
    (trace : Trace)
    (initialized : joltInstance.initial_state privateInputs = some trace.initialState)
    (rowsBound : trace.rows.size ≤ params.traceLength)
    (ramAddress : ∀ t : Fin params.traceLength, t.val < trace.rows.size →
      witness.RamAddress t = TraceWitness.RamAddress params trace t) :
    ∃ ramK, ProverConfig.checkedRamSize trace.execution_dimensions
      trace.initialState.jolt_device.memory_layout
      (min_bytecode_address joltInstance.program.memory_init)
      (program_image_len_words joltInstance.program.memory_init) = some ramK := by
  sorry

end JoltInstance
