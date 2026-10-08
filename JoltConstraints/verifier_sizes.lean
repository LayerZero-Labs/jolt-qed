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
