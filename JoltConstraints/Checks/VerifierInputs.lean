import JoltConstraints.Completeness.All
import Lean.Util.CollectAxioms

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
  trusted_advice := #[]
  inputs := #[]
  outputs := #[]
  panic := false
  max_padded_trace_length := 256

-- Match the actual Rust run in bug-report/verifier-ram-minimum. All evaluation
-- below is checked by Lean's kernel, including the recursive layout computation.
example : baseInstance.validate_inputs = true := by decide +kernel
example : baseInstance.verifier_ram_bounds = some (16, 32) := by decide +kernel
example : baseInstance.ram_size_in_bounds 2 = false := by decide +kernel
example : baseInstance.ram_size_in_bounds 4 = false := by decide +kernel
example : baseInstance.ram_size_in_bounds 16 = true := by decide +kernel
example : baseInstance.ram_size_in_bounds 32 = true := by decide +kernel
example : baseInstance.ram_size_in_bounds 64 = false := by decide +kernel
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
  rejects_ram_size (by decide +kernel) privateInputs witness size

example {F : Type} [Field F] {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params) (size : params.ramSize = 4) :
    ¬ AllConstraints baseInstance privateInputs witness :=
  rejects_ram_size (by decide +kernel) privateInputs witness size

-- The same instance has maximum RAM size 32, so a 64-slot table is also rejected.
example {F : Type} [Field F] {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params) (size : params.ramSize = 64) :
    ¬ AllConstraints baseInstance privateInputs witness :=
  rejects_ram_size (by decide +kernel) privateInputs witness size

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
  rejects_invalid _ _ (by decide +kernel) witness

example {F : Type} [Field F] {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params) : ¬ AllConstraints pastTermination privateInputs witness :=
  rejects_invalid _ _ (by decide +kernel) witness

-- This layout constructs successfully but its lowest mapped address is zero.
private def zeroBased : JoltInstance SourceInstruction :=
  { baseInstance with memory_config :=
    { baseInstance.memory_config with max_trusted_advice_size := 2 ^ 30 } }

example : zeroBased.memory_layout.isSome = true := by decide +kernel
example : (zeroBased.memory_layout.map (·.get_lowest_address)) = some 0 := by decide +kernel
example {F : Type} [Field F] {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params) : ¬ AllConstraints zeroBased privateInputs witness :=
  rejects_invalid _ _ (by decide +kernel) witness

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

example : VerifierSizes.checkedNextPowerOfTwo (2 ^ 63) = some (2 ^ 63) := by decide +kernel
example : VerifierSizes.checkedNextPowerOfTwo (2 ^ 63 + 1) = none := by decide +kernel

-- Keep the proved lower inequality independent of the admitted general claim,
-- and keep compiler-evaluation axioms out of both the checks and completeness.
run_cmd do
  let env ← Lean.getEnv
  let lowerName := `HonestTrace.witness_params_ram_minimum_of_nonempty
  let lowerAxioms ← Lean.collectAxioms lowerName
  if lowerAxioms.contains `sorryAx then
    throwError "the nonempty-image RAM lower bound depends on sorryAx"
  let finalName := `HonestTrace.allConstraints_rust_sizes
  let (_, dependencies) := ((Lean.CollectAxioms.collect finalName).run env).run {}
  unless dependencies.visited.contains `HonestTrace.witness_params_ram_bounds do
    throwError "completeness lost its explicit RAM-size obligation"
  let names := env.constants.toList.filterMap fun (name, _) =>
    if (env.getModuleIdxFor? name).isNone then some name else none
  for name in lowerName :: finalName :: names do
    let axioms ← Lean.collectAxioms name
    if axioms.contains `Lean.ofReduceBool then
      throwError "{name} depends on compiler evaluation"

end JoltConstraints.Checks.VerifierInputs
