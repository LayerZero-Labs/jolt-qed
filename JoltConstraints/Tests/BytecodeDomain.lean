import JoltConstraints.honest_witness

set_option autoImplicit false

namespace BytecodeDomainChecks

-- Rust inserts a leading no-op, then pads to at least two bytecode rows.
example : WitnessParams.preprocessedBytecodeSize 0 = 2 := by decide
example : WitnessParams.preprocessedBytecodeSize 1 = 2 := by decide
example : WitnessParams.preprocessedBytecodeSize 2 = 4 := by decide
example : WitnessParams.preprocessedBytecodeSize 3 = 4 := by decide
example : WitnessParams.preprocessedBytecodeSize 4 = 8 := by decide

example (p : WitnessParams) (h : p.logBytecodeK = 2) :
    p.BytecodeDomainFor 2 := by
  simp only [WitnessParams.BytecodeDomainFor,
    WitnessParams.preprocessedBytecodeSize, h]
  decide

-- Two expanded rows need four slots: one leading no-op and one trailing no-op.
example (p : WitnessParams) (h : p.logBytecodeK = 1) :
    ¬ p.BytecodeDomainFor 2 := by
  simp only [WitnessParams.BytecodeDomainFor,
    WitnessParams.preprocessedBytecodeSize, h]
  decide

-- The exact Rust domain also rejects an arbitrary larger bytecode commitment.
example (p : WitnessParams) (h : p.logBytecodeK = 3) :
    ¬ p.BytecodeDomainFor 2 := by
  simp only [WitnessParams.BytecodeDomainFor,
    WitnessParams.preprocessedBytecodeSize, h]
  decide

end BytecodeDomainChecks
