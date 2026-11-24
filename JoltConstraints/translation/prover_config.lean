import JoltConstraints.translation.honest_trace
import JoltConstraints.translation.verifier_sizes

open LeanRV64D

set_option autoImplicit false

/- Checked base/Dory sizing at public pin ff6fc6568, on a 64-bit host.
   Rust: crates/jolt-program/src/execution/trace.rs:193-288 and
   crates/jolt-prover/src/config.rs (derive_from_dimensions, padded_trace_length). Error variants are erased to none.
   Addresses and lengths use Nat as in the layout model; summaries produced
   from an honest trace contain 64-bit addresses. Akita is outside this model. -/

/-- The dimension summary produced below. Like Rust’s `RamAddressBounds`,
`ram_bounds` is absent for no nonzero accesses, otherwise an ordered pair of
nonzero 64-bit byte addresses. The Nat representation does not encode those
producer invariants as verifier checks or theorem premises. -/
structure ExecutionDimensions where
  trace_length : Nat
  ends_in_halt : Bool
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
def Trace.execution_dimensions (trace : Trace) : ExecutionDimensions :=
  { trace_length := trace.rows.size
    ends_in_halt := trace.rows.back?.any fun last =>
      trace.bytecode[last.rowIndex].instruction.haltKind?.isSome
    ram_bounds := (trace.rows.toList.filterMap (·.ram_address)).foldl
      ExecutionDimensions.observe none }

namespace ProverConfig

/-- The checked padding path in `derive_from_dimensions`, before the public
maximum check. The power-of-two rounding can overflow. -/
def checkedTraceLength (rows : Nat) : Option Nat := do
  let rounded ← JoltConstraints.VerifierSizes.checkedNextPowerOfTwo rows
  return max rounded 256

/-- Validate the nonzero address bounds and remap the largest address. -/
def checkedTouched (bounds : Option (Nat × Nat)) (layout : MemoryLayout) : Option Nat :=
  match bounds with
  | none => some 0
  | some (lo, hi) => do
    let _ ← MemoryLayout.checkedSub lo layout.get_lowest_address.toNat
    let offset ← MemoryLayout.checkedSub hi layout.get_lowest_address.toNat
    pure (offset / 8)

/-- Jolt's prover's RAM size, as a16z/jolt#2250 fixed it for a16z/jolt#1951 item 4:
`touched` is the word index of the highest touched
address, `imageEnd` is the image's first word index plus its word count plus one,
and the RAM size is the power of two that rounds up `max (touched + 1) imageEnd`,
so the table holds word `touched`.
For example, `touched = 1024` with `imageEnd = 40` gives `pow2(1025) = 2048`, where
Jolt's prover before #2250 rounded `max touched imageEnd` and got 1024.
See jolt/crates/jolt-prover/src/config.rs (`ProverConfig::derive_from_dimensions`) at
c97e9300. `touched + 1` cannot overflow, since `touched < 2^61`. -/
def checkedRamSize (dimensions : ExecutionDimensions) (layout : MemoryLayout)
    (minBytecodeAddress imageWords : Nat) : Option Nat := do
  let touched ← checkedTouched dimensions.ram_bounds layout
  let imageStart ← JoltConstraints.VerifierSizes.remapWordAddress layout minBytecodeAddress
  let imageEnd ← MemoryLayout.checkedAdd (imageStart.getD 0) imageWords
  let imageEnd ← MemoryLayout.checkedAdd imageEnd 1
  JoltConstraints.VerifierSizes.checkedNextPowerOfTwo (max (touched + 1) imageEnd)

/-- The two size fields returned by Rust's `derive_from_dimensions`. Its final
power-of-two checks cannot fail after checked rounding and the 256 floor. The
remaining fields follow the base chunk policy in `WitnessParams.ProverChunkConfig`
and cycle-major order; they are not additional acceptance conditions. -/
def deriveFromDimensions (dimensions : ExecutionDimensions) (layout : MemoryLayout)
    (minBytecodeAddress imageWords maxPaddedTraceLength : Nat) : Option ProverConfig := do
  guard (dimensions.trace_length ≠ 0 ∧ dimensions.ends_in_halt = true)
  let traceLength ← checkedTraceLength dimensions.trace_length
  let ramK ← checkedRamSize dimensions layout minBytecodeAddress imageWords
  guard (traceLength ≤ maxPaddedTraceLength)
  return { trace_length := traceLength, ram_K := ramK }

end ProverConfig

/-- Jolt's prover's checked sizing policy. Completeness uses its sizes
(`HonestTrace.witness_params`); its RAM size follows the fix that a16z/jolt#1951
item 4 proposes, so its RAM domain holds the highest touched slot
(`HonestTrace.prover_config_holds_highest_slot`). -/
def Trace.prover_config (joltInstance : JoltInstance SourceInstruction)
    (trace : Trace) : Option ProverConfig :=
  ProverConfig.deriveFromDimensions trace.execution_dimensions
    trace.initialState.jolt_device.memory_layout
    (min_bytecode_address joltInstance.program.memory_init)
    (program_image_len_words joltInstance.program.memory_init)
    joltInstance.max_padded_trace_length.toNat
