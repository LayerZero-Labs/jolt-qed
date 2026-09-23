import JoltConstraints.honest_witness

set_option autoImplicit false

namespace ProverPaddingChecks

-- Rust's default PCS floor is 256. A trace of exactly 256 rows must grow
-- to 512 cycles to leave the required successor padding row.
example : WitnessParams.proverTraceLength 8 0 = 256 ∧
    WitnessParams.proverTraceLength 8 255 = 256 ∧
    WitnessParams.proverTraceLength 8 256 = 512 ∧
    WitnessParams.proverTraceLength 8 511 = 512 ∧
    WitnessParams.proverTraceLength 8 512 = 1024 := by
  decide

-- The Akita build uses a 4096-cycle floor with the same strict padding rule.
example : WitnessParams.proverTraceLength 12 0 = 4096 ∧
    WitnessParams.proverTraceLength 12 4095 = 4096 ∧
    WitnessParams.proverTraceLength 12 4096 = 8192 := by
  decide

example (p : WitnessParams) (logT : p.logT = 8) :
    p.ProverPaddedFor 255 ∧ ¬ p.ProverPaddedFor 256 := by
  simp [WitnessParams.ProverPaddedFor, WitnessParams.proverTraceLength,
    WitnessParams.traceLength, logT]; decide

example (p : WitnessParams) (logT : p.logT = 12) :
    p.ProverPaddedFor 4095 ∧ ¬ p.ProverPaddedFor 4096 := by
  simp [WitnessParams.ProverPaddedFor, WitnessParams.proverTraceLength,
    WitnessParams.traceLength, logT]; decide

-- An arbitrary larger power of two is not the length Rust derives.
example (p : WitnessParams) (logT : p.logT = 10) :
    ¬ p.ProverPaddedFor 1 := by
  simp [WitnessParams.ProverPaddedFor, WitnessParams.proverTraceLength,
    WitnessParams.traceLength, logT]; decide

end ProverPaddingChecks
