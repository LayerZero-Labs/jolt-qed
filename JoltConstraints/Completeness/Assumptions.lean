/-
What the completeness theorem assumes, grouped by what each assumption is about:
the instance, and Jolt's prover accepting the honest trace.
-/
import JoltConstraints.prover_config_facts

set_option autoImplicit false

-- What the completeness theorem assumes about the instance. a16z has confirmed both.
structure JoltInstance.CompletenessAssumptions
    (joltInstance : JoltInstance SourceInstruction) : Prop where
  -- No instruction's next PC, its address plus its length (2 or 4), passes 2^64.
  -- Confirmed by a16z on 2026-10-07: an ELF that breaks this is illegal.
  pcNoWrap : joltInstance.program.NextPCNoWrap
  -- The program's memory image loads at least one byte.
  -- Confirmed by a16z by phone on 2026-10-08: Jolt can assume a program is never
  -- empty. Jolt's prover does not reject an empty ELF; only Jolt's verifier does
  -- (bug-report/verifier-ram-minimum).
  imageNonempty : joltInstance.program.ImageNonempty

-- Jolt's prover accepts the honest trace and proves it at the sizes in `config`: the
-- padded trace length and the RAM size `ram_K`, in 64-bit words.
-- See : jolt/jolt-sdk/src/host_utils.rs:321 (ProverConfig::derive_from_dimensions)
structure HonestTrace.ProverAccepts {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (config : ProverConfig) : Prop where
  -- Jolt's prover picks the sizes in `config` for this honest trace.
  -- See : jolt/crates/jolt-prover/src/config.rs:63-109 (derive_from_dimensions)
  proverSizes : trace.prover_config = some config
  -- Every spoil assert the honest trace runs has equal sides. Jolt only proves such
  -- a trace (`HonestTrace.SpoilAssertsPass`).
  spoilAssertsPass : trace.SpoilAssertsPass
  -- FIXME: the highest RAM slot the honest trace touches is below `ram_K`. Jolt's
  -- prover rounds that slot up to a power of two without adding one: a trace that
  -- touches slot 1024 gets `ram_K = 1024`, and its witness is rejected
  -- (a16z/jolt#1951 item 4; bug-report/ram-k-off-by-one). Remove once fixed.
  ramBoundary : trace.highest_touched_slot < config.ram_K
