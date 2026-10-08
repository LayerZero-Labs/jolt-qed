import JoltConstraints.Constraints.All
import JoltConstraints.verifier_sizes

set_option autoImplicit false

namespace JoltConstraints.Checks.VerifierInputs

private def baseInstance : JoltInstance SourceInstruction where
  program := {
    instructions := #[]
    memory_init := []
    program_end := 0x80000000
    entry_address := 0
    program_end_ge_ram_start := by decide
    memory_init_in_program := by simp }
  memory_config := {
    max_input_size := 0, max_trusted_advice_size := 0, max_untrusted_advice_size := 0,
    max_output_size := 64, stack_size := 0, heap_size := 0, program_size := none }
  inputs := #[]
  outputs := #[]
  panic := false
  max_padded_trace_length := 256

-- Match the actual Rust run in bug-report/verifier-ram-minimum.
example : baseInstance.validate_inputs = true := by native_decide
example : baseInstance.verifier_ram_bounds = some (16, 32) := by native_decide
example : baseInstance.ram_size_in_bounds 2 = false := by native_decide
example : baseInstance.ram_size_in_bounds 4 = false := by native_decide
example : baseInstance.ram_size_in_bounds 16 = true := by native_decide
example : baseInstance.ram_size_in_bounds 32 = true := by native_decide
example : baseInstance.ram_size_in_bounds 64 = false := by native_decide
example : 2 ^ Nat.clog 2 (max (0 + 1) (0 + program_image_len_words [] + 1)) = 4 := by decide

-- The RAM bounds must be enforced by AllConstraints itself. In particular,
-- neither a two-slot witness nor Rust's four-slot empty-run witness is admitted.
private theorem rejects_ram_size {F : Type} [Field F] {params : WitnessParams}
    {ramSize : Nat} (invalid : baseInstance.ram_size_in_bounds ramSize = false)
    (privateInputs : JoltPrivateInputs) (witness : WitnessType F params)
    (size : params.ramSize = ramSize) : ¬ AllConstraints baseInstance privateInputs witness := by
  rintro ⟨context, _⟩
  have checked := context.ramSizeBounds
  rw [size, invalid] at checked
  contradiction

example {F : Type} [Field F] {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params) (size : params.ramSize = 2) :
    ¬ AllConstraints baseInstance privateInputs witness :=
  rejects_ram_size (by native_decide) privateInputs witness size

example {F : Type} [Field F] {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params) (size : params.ramSize = 4) :
    ¬ AllConstraints baseInstance privateInputs witness :=
  rejects_ram_size (by native_decide) privateInputs witness size

-- The same instance has maximum RAM size 32, so a 64-slot table is also rejected.
example {F : Type} [Field F] {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params) (size : params.ramSize = 64) :
    ¬ AllConstraints baseInstance privateInputs witness :=
  rejects_ram_size (by native_decide) privateInputs witness size

-- Bytes beyond the output region must be rejected before the I/O equations
-- overwrite the panic and termination words.
private def pastPanic : JoltInstance SourceInstruction :=
  { baseInstance with outputs := Array.replicate 72 1 }

private def pastTermination : JoltInstance SourceInstruction :=
  { baseInstance with outputs := Array.replicate 80 1 }

private theorem rejects_invalid {F : Type} [Field F] {params : WitnessParams}
    (joltInstance : JoltInstance SourceInstruction) (privateInputs : JoltPrivateInputs)
    (invalid : joltInstance.validate_inputs = false) (witness : WitnessType F params) :
    ¬ AllConstraints joltInstance privateInputs witness := by
  rintro ⟨context, _⟩
  have checked := context.validInputs
  rw [invalid] at checked
  contradiction

example {F : Type} [Field F] {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params) : ¬ AllConstraints pastPanic privateInputs witness :=
  rejects_invalid _ _ (by native_decide) witness

example {F : Type} [Field F] {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params) : ¬ AllConstraints pastTermination privateInputs witness :=
  rejects_invalid _ _ (by native_decide) witness

-- This layout constructs successfully but its lowest mapped address is zero.
private def zeroBased : JoltInstance SourceInstruction :=
  { baseInstance with memory_config :=
    { baseInstance.memory_config with max_trusted_advice_size := 2 ^ 30 } }

example : zeroBased.memory_layout.isSome = true := by native_decide
example : (zeroBased.memory_layout.map (·.get_lowest_address)) = some 0 := by native_decide
example {F : Type} [Field F] {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params) : ¬ AllConstraints zeroBased privateInputs witness :=
  rejects_invalid _ _ (by native_decide) witness

-- Oversized padded traces and a one-slot bytecode domain are rejected for
-- every witness, independently of whether the equations happen to hold.
example {F : Type} [Field F] {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params) (tooLong : 256 < params.traceLength) :
    ¬ AllConstraints baseInstance privateInputs witness := by
  rintro ⟨context, _⟩
  exact Nat.not_le_of_lt tooLong context.traceLengthBound

example {F : Type} [Field F] {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params) (tooSmall : params.logBytecodeK = 0) :
    ¬ AllConstraints baseInstance privateInputs witness := by
  rintro ⟨context, _⟩
  have domain := context.bytecodeDomain
  unfold WitnessParams.BytecodeDomainFor WitnessParams.preprocessedBytecodeSize at domain
  rw [tooSmall] at domain
  have lower := Nat.le_max_left 2 (2 ^ Nat.clog 2 (context.bytecode.size + 1))
  omega

example : VerifierSizes.checkedNextPowerOfTwo (2 ^ 63) = some (2 ^ 63) := by native_decide
example : VerifierSizes.checkedNextPowerOfTwo (2 ^ 63 + 1) = none := by native_decide

end JoltConstraints.Checks.VerifierInputs
