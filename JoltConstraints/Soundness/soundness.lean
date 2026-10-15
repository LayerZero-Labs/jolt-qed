/-
The base non-succinct soundness statement: a witness that satisfies every modeled
constraint shows the instance is in Jolt's language, under the premises below.
Source programs are limited to the instructions represented by `SourceInstruction`.
Jolt's inline/precompile opcodes 0x0B and 0x2B, including the SHA-256 and Keccak
inlines, are outside that type. Guests using them are outside this theorem's scope.
Akita's extra constraints are to be modeled separately; PCS security is out of scope.
The proof is left as `sorry`; it is not expected to hold yet
(methods/review_completeness_and_soundness.md, B6).
-/
import JoltConstraints.Constraints.All
import JoltConstraints.Soundness.Assumptions
import JoltConstraints.language

set_option autoImplicit false

-- Soundness: if some private inputs and witness satisfy every constraint, the instance
-- is in Jolt's language. The field is a `JoltField`. The instance satisfies
-- `JoltInstance.SoundnessAssumptions` and, for now, the workarounds in
-- `JoltInstance.TemporaryRestrictions`; both are in Soundness/Assumptions.lean.
-- The private inputs of the run need not be the ones given.
-- FIXME: false today for programs that stop or panic in ways SDK guests never do
-- (B6, "Known not sound for this L"); the temporary restrictions do not cover these.
theorem JoltInstance.soundness {F : Type} [Field F] (joltField : JoltField F)
    (joltInstance : JoltInstance SourceInstruction)
    (assumptions : joltInstance.SoundnessAssumptions)
    (restrictions : joltInstance.TemporaryRestrictions)
    {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params)
    (satisfied : JoltConstraints.AllConstraints joltInstance privateInputs witness) :
    joltInstance.InLanguage := by
  sorry
