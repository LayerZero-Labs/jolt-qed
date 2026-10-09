import JoltConstraints.program

set_option autoImplicit false

namespace JoltConstraints.VerifierSizes

/-- Rust's `usize::checked_next_power_of_two` on the modeled 64-bit host.
Zero rounds up to one; a result outside `usize` is rejected. -/
def checkedNextPowerOfTwo (value : Nat) : Option Nat :=
  let rounded := 2 ^ Nat.clog 2 value
  if rounded < 2 ^ 64 then some rounded else none

/-- `MemoryLayout::remap_word_address`: zero means no access; a nonzero
address below the lowest mapped address is an error. -/
def remapWordAddress (layout : MemoryLayout) (address : Nat) : Option (Option Nat) := do
  if address = 0 then return none
  let offset ← MemoryLayout.checkedSub address layout.get_lowest_address.toNat
  return some (offset / 8)

/-- `compute_min_ram_k` in `crates/jolt-program/src/preprocess/ram.rs`.
The RAM domain must contain both the program image and the region below RAM. -/
def minRamSize {Source : Type} (program : Rv64ProgramImage Source)
    (layout : MemoryLayout) : Option Nat := do
  let bytecodeStart ← remapWordAddress layout (min_bytecode_address program.memory_init)
  let bytecodeEnd ← MemoryLayout.checkedAdd (bytecodeStart.getD 0)
    (program_image_len_words program.memory_init)
  let some ioEnd ← remapWordAddress layout JoltISA.RAM_START_ADDRESS | none
  checkedNextPowerOfTwo (max bytecodeEnd ioEnd)

/-- `compute_max_ram_k` in `crates/jolt-program/src/preprocess/ram.rs`.
The division by eight precedes rounding, exactly as in Rust. -/
def maxRamSize (layout : MemoryLayout) : Option Nat := do
  let totalBytes ← MemoryLayout.checkedSub layout.heap_end.toNat layout.get_lowest_address.toNat
  checkedNextPowerOfTwo (totalBytes / 8)

/-- `committed_log_k_chunk` in `crates/jolt-prover/src/config.rs:221-243`: the width of
the honest prover's one-hot chunks over `2^logT` cycles, 4 below 2^25 cycles, else 8. -/
def committedLogKChunk (logT : Nat) : Nat := if logT < 25 then 4 else 8

/-- `advice_vars` in `crates/jolt-prover/src/dory/preprocessing.rs:189-196`: the
number of variables of an advice polynomial of at most `bytes` bytes. -/
def adviceVars (bytes : Nat) : Nat :=
  let words := max (bytes / 8) 1
  if words = 1 then 0 else Nat.log 2 (words - 1) + 1

/-- The number of variables of the verifier's Dory setup: `setup_total_vars` in
`crates/jolt-prover/src/dory/preprocessing.rs:198-211`, rounded up to even by
`canonical_setup_log_n` in `crates/jolt-dory/src/scheme.rs:120-126`. Programs
committed in preprocessing add more candidates; they are not modeled. -/
def dorySetupLogN (layout : MemoryLayout) (maxPaddedTraceLength : Nat) : Nat :=
  let maxLogT := Nat.clog 2 maxPaddedTraceLength
  let vars := max (maxLogT + committedLogKChunk maxLogT)
    (max (adviceVars layout.max_trusted_advice_size.toNat)
      (adviceVars layout.max_untrusted_advice_size.toNat))
  if vars % 2 = 0 then vars else vars + 1

end JoltConstraints.VerifierSizes

/-- The verifier's RAM bounds depend only on its public program and layout. -/
def JoltInstance.verifier_ram_bounds {Source : Type} (joltInstance : JoltInstance Source) :
    Option (Nat × Nat) := do
  let layout ← joltInstance.memory_layout
  let minimum ← JoltConstraints.VerifierSizes.minRamSize joltInstance.program layout
  let maximum ← JoltConstraints.VerifierSizes.maxRamSize layout
  return (minimum, maximum)

/-- Whether a RAM domain lies within the verifier's public bounds. The
power-of-two requirement is separately built into `WitnessParams.ramSize`. -/
def JoltInstance.ram_size_in_bounds {Source : Type} (joltInstance : JoltInstance Source)
    (ramSize : Nat) : Bool :=
  match joltInstance.verifier_ram_bounds with
  | none => false
  | some (minimum, maximum) => decide (minimum ≤ ramSize ∧ ramSize ≤ maximum)

/-- Whether one-hot chunks of `chunkBits` bits over `2^logT` cycles fit the verifier's
Dory setup. Dory's verifier rejects an opening point with more coordinates than its
setup has variables, and Jolt opens the committed one-hot chunks at a point with
`logT + chunkBits` coordinates. The prover picks `chunkBits`; the setup is the
verifier's.
Rust: dory-pcs-0.4.2/src/evaluation_proof.rs:341-352, 394-399 (point size, setup bound)
      crates/jolt-claims/src/protocols/jolt/geometry/booleanity.rs:28
      crates/jolt-verifier/src/stages/stage8/verify.rs:132-135 -/
def JoltInstance.one_hot_fits_setup {Source : Type} (joltInstance : JoltInstance Source)
    (logT chunkBits : Nat) : Bool :=
  match joltInstance.memory_layout with
  | none => false
  | some layout => decide (logT + chunkBits ≤
      JoltConstraints.VerifierSizes.dorySetupLogN layout
        joltInstance.max_padded_trace_length.toNat)
