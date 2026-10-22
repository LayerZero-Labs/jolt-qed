/-
The base non-succinct soundness statement: a witness that satisfies every modeled
constraint shows the instance is in Jolt's language, under the premises below.
Source programs are limited to the instructions represented by `SourceInstruction`.
Jolt's inline/precompile opcodes 0x0B and 0x2B, including the SHA-256 and Keccak
inlines, are outside that type. Guests using them are outside this theorem's scope.
Akita's extra constraints are to be modeled separately; PCS security is out of scope.
The top-level proof is a short chain of named helpers. B6's known
counterexamples are excluded by temporary restrictions
(methods/review_completeness_and_soundness.md, B6).
-/
import JoltConstraints.Soundness.TopLevel
import JoltConstraints.Soundness.Layer7.TapeRebuild

set_option autoImplicit false

-- Soundness: if some private inputs and witness satisfy every constraint, the instance
-- is in Jolt's language. The field is a `JoltField`. The instance satisfies
-- `JoltInstance.SoundnessAssumptions` and, for now, the workarounds in
-- `JoltInstance.TemporaryRestrictions`; both are in Soundness/Assumptions.lean.
-- The private inputs of the run need not be the ones given.
-- FIXME: B6's known counterexamples are excluded only by temporary restrictions:
-- `terminationThenStall` for stopping early on a "no panic" claim, `claimsNoPanic`
-- for stopping early on a "panicked" claim, and `panicStoresOne` for a store of 0
-- proved as "no panic". These are Jolt bugs that must be fixed in Jolt.
-- ⚠️ DANGER ⚠️ `soundness_prover_accepts` (TopLevel.lean) is known false in two
-- cases and is assumed on purpose until a16z answers; see its docstring and
-- blog/content/blog/prover-verifier-trace-length/index.md.
theorem JoltInstance.soundness {F : Type} [Field F] (joltField : JoltField F)
    (joltInstance : JoltInstance SourceInstruction)
    (assumptions : joltInstance.SoundnessAssumptions)
    (restrictions : joltInstance.TemporaryRestrictions)
    {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params)
    (satisfied : JoltConstraints.AllConstraints joltInstance privateInputs witness) :
    joltInstance.InLanguage := by
  obtain ⟨context, equations⟩ := satisfied
  obtain ⟨trace, bytecodeEq, represented⟩ :=
    soundness_reconstruct_trace joltField joltInstance assumptions restrictions
      privateInputs witness context equations
  apply JoltConstraints.Soundness.untrustedAnswerLanguage_implies_inLanguage
  refine ⟨privateInputs, trace, ?_, ?_, ?_⟩
  · exact soundness_matches_outputs joltField joltInstance privateInputs witness
      context equations trace represented
  · exact soundness_prover_accepts joltField joltInstance privateInputs witness
      context equations trace bytecodeEq represented
  · exact soundness_spoil_asserts_pass joltField joltInstance privateInputs witness
      context equations trace bytecodeEq represented
