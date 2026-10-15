import JoltConstraints.trace_facts
import JoltConstraints.verifier_sizes

set_option autoImplicit false

/- Checked base/Dory sizing at public pin 8bbb2357, on a 64-bit host.
   Rust: crates/jolt-program/src/execution/trace.rs:193-288 and
   crates/jolt-prover/src/config.rs:62-149. Error variants are erased to none.
   Addresses and lengths use Nat as in the layout model; summaries produced
   from an honest trace contain 64-bit addresses. Akita is outside this model. -/

/-- The dimension summary produced below. Like Rust’s `RamAddressBounds`,
`ram_bounds` is absent for no nonzero accesses, otherwise an ordered pair of
nonzero 64-bit byte addresses. The Nat representation does not encode those
producer invariants as verifier checks or theorem premises. -/
structure ExecutionDimensions where
  trace_length : Nat
  ends_in_jump : Bool
  ram_bounds : Option (Nat × Nat)

/-- `RamAddressBounds::observe`: zero is the no-access sentinel. -/
def ExecutionDimensions.observe (bounds : Option (Nat × Nat)) (address : Nat) :
    Option (Nat × Nat) :=
  if address = 0 then bounds else
    match bounds with
    | none => some (address, address)
    | some (lo, hi) => some (min lo address, max hi address)

/-- `ExecutionDimensions::from_rows`, before padding. Only accesses contribute
to the bounds, including stores whose value is unchanged. -/
def HonestTrace.execution_dimensions {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs) :
    ExecutionDimensions :=
  { trace_length := trace.rows.size
    ends_in_jump := trace.rows.back?.any fun last =>
      trace.bytecode[last.rowIndex].instruction.is_jump
    ram_bounds := (trace.rows.toList.filterMap (·.ram_address)).foldl
      ExecutionDimensions.observe none }

namespace ProverConfig

/-- The checked padding path in `derive_from_dimensions`, before the public
maximum check. Both the addition and the rounding can fail. -/
def checkedTraceLength (rows : Nat) : Option Nat := do
  let withNoop ← MemoryLayout.checkedAdd rows 1
  let rounded ← JoltConstraints.VerifierSizes.checkedNextPowerOfTwo withNoop
  return max rounded 256

/-- Validate the nonzero address bounds and remap the largest address. -/
def checkedTouched (bounds : Option (Nat × Nat)) (layout : MemoryLayout) : Option Nat :=
  match bounds with
  | none => some 0
  | some (lo, hi) => do
    let _ ← MemoryLayout.checkedSub lo layout.get_lowest_address.toNat
    let offset ← MemoryLayout.checkedSub hi layout.get_lowest_address.toNat
    pure (offset / 8)

/-- Rust's RAM policy, including the existing off-by-one discrepancy: the
highest touched slot is rounded directly, without adding one. -/
def checkedRamSize (dimensions : ExecutionDimensions) (layout : MemoryLayout)
    (minBytecodeAddress imageWords : Nat) : Option Nat := do
  let touched ← checkedTouched dimensions.ram_bounds layout
  let imageStart ← JoltConstraints.VerifierSizes.remapWordAddress layout minBytecodeAddress
  let imageEnd ← MemoryLayout.checkedAdd (imageStart.getD 0) imageWords
  let imageEnd ← MemoryLayout.checkedAdd imageEnd 1
  JoltConstraints.VerifierSizes.checkedNextPowerOfTwo (max touched imageEnd)

/-- The two size fields returned by Rust's `derive_from_dimensions`. Its final
power-of-two checks cannot fail after checked rounding and the 256 floor. The
remaining fields follow the base chunk policy in `WitnessParams.ProverChunkConfig`
and cycle-major order; they are not additional acceptance conditions. -/
def deriveFromDimensions (dimensions : ExecutionDimensions) (layout : MemoryLayout)
    (minBytecodeAddress imageWords maxPaddedTraceLength : Nat) : Option ProverConfig := do
  guard (dimensions.trace_length = 0 ∨ dimensions.ends_in_jump = true)
  let traceLength ← checkedTraceLength dimensions.trace_length
  let ramK ← checkedRamSize dimensions layout minBytecodeAddress imageWords
  guard (traceLength ≤ maxPaddedTraceLength)
  return { trace_length := traceLength, ram_K := ramK }

private theorem checkedRound_some (value rounded : Nat)
    (accepted : JoltConstraints.VerifierSizes.checkedNextPowerOfTwo value = some rounded) :
    rounded = 2 ^ Nat.clog 2 value ∧ rounded < 2 ^ 64 := by
  dsimp only [JoltConstraints.VerifierSizes.checkedNextPowerOfTwo] at accepted
  split at accepted
  · cases accepted
    exact ⟨rfl, by assumption⟩
  · cases accepted

private theorem checkedTraceLength_rounding (rows padded : Nat)
    (accepted : checkedTraceLength rows = some padded) :
    padded = max (2 ^ Nat.clog 2 (rows + 1)) 256 ∧
      2 ^ Nat.clog 2 (rows + 1) < 2 ^ 64 := by
  unfold checkedTraceLength at accepted
  simp only [bind_some_iff] at accepted
  obtain ⟨withNoop, added, rounded, roundedOk, result⟩ := accepted
  obtain ⟨rfl, _⟩ := checkedAdd_some added
  obtain ⟨rfl, bound⟩ := checkedRound_some _ _ roundedOk
  cases result
  exact ⟨rfl, bound⟩

theorem checkedTraceLength_eq (rows padded : Nat)
    (accepted : checkedTraceLength rows = some padded) :
    padded = max (2 ^ Nat.clog 2 (rows + 1)) 256 :=
  (checkedTraceLength_rounding rows padded accepted).1

theorem deriveFromDimensions_sizes (dimensions : ExecutionDimensions) (layout : MemoryLayout)
    (minBytecodeAddress imageWords maximum : Nat) (config : ProverConfig)
    (accepted : deriveFromDimensions dimensions layout minBytecodeAddress imageWords maximum =
      some config) :
    (dimensions.trace_length = 0 ∨ dimensions.ends_in_jump = true) ∧
    checkedTraceLength dimensions.trace_length = some config.trace_length ∧
    checkedRamSize dimensions layout minBytecodeAddress imageWords = some config.ram_K ∧
    config.trace_length ≤ maximum := by
  unfold deriveFromDimensions at accepted
  simp only [bind_some_iff] at accepted
  obtain ⟨_, jump, traceLength, traceSize, ramK, ramSize, _, limit, result⟩ := accepted
  cases result
  exact ⟨guard_some jump, traceSize, ramSize,
    guard_some limit⟩

end ProverConfig

/-- Rust's checked sizing policy. Completeness currently uses the separately
named `corrected_prover_config`, whose RAM domain contains the highest slot. -/
def HonestTrace.prover_config {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs) :
    Option ProverConfig :=
  ProverConfig.deriveFromDimensions trace.execution_dimensions
    trace.initialState.jolt_device.memory_layout
    (min_bytecode_address joltInstance.program.memory_init)
    (program_image_len_words joltInstance.program.memory_init)
    joltInstance.max_padded_trace_length.toNat
