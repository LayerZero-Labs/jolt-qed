import JoltConstraints.witness

set_option autoImplicit false

namespace WitnessDimensionsChecks

-- Rust's ordinary prover policy uses four-bit committed chunks and
-- sixteen-bit virtual chunks below the 2^25-cycle threshold.
def ordinary : WitnessParams where
  logT := 8
  logRamK := 0
  logBytecodeK := 1
  chunkBits := 4
  virtualChunkBits := 16
  chunkBits_pos := by decide
  virtualChunkBits_pos := by decide
  chunkBits_dvd_virtual := by decide
  virtualChunkBits_dvd_lookup := by decide
  proverChunkConfig := by decide
  logT_lt_usizeBits := by decide
  logRamK_lt_usizeBits := by decide
  logBytecodeK_lt_usizeBits := by decide

-- `ram_k = 1` is accepted by Rust's dimension formula and has zero chunks.
example : ordinary.ramSize = 1 ∧ ordinary.ramChunks = 0 := by decide

example : ordinary.TraceBackendGridFits 32 := by
  simp [WitnessParams.TraceBackendGridFits, WitnessParams.traceLength,
    WitnessParams.ramSize, ordinary]

-- At the threshold Rust selects eight-bit committed chunks and
-- thirty-two-bit virtual chunks.
def wide : WitnessParams where
  logT := 25
  logRamK := 12
  logBytecodeK := 4
  chunkBits := 8
  virtualChunkBits := 32
  chunkBits_pos := by decide
  virtualChunkBits_pos := by decide
  chunkBits_dvd_virtual := by decide
  virtualChunkBits_dvd_lookup := by decide
  proverChunkConfig := by decide
  logT_lt_usizeBits := by decide
  logRamK_lt_usizeBits := by decide
  logBytecodeK_lt_usizeBits := by decide

example : wide.chunkBits = 8 ∧ wide.virtualChunkBits = 32 := by decide

-- The shape is formula-valid, but its RAM grid exceeds the trace backend's
-- 32 GiB allocation ceiling for a 32-byte field.
example : ¬ wide.TraceBackendGridFits 32 := by
  simp [WitnessParams.TraceBackendGridFits, WitnessParams.traceLength,
    WitnessParams.ramSize, wide]

-- No accepted prover configuration can reach the selector's 128-bit limit.
example (p : WitnessParams) : p.chunkBits ≠ 128 := by
  exact Nat.ne_of_lt (p.chunkBits_lt_128)

end WitnessDimensionsChecks
