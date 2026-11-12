/-
The base non-succinct soundness statement: a witness that satisfies every modeled
constraint shows the instance is in Jolt's language, under the premises below.
Source programs are limited to the instructions represented by `SourceInstruction`.
Jolt's inline/precompile opcodes 0x0B and 0x2B, including the SHA-256 and Keccak
inlines, are outside that type. Guests using them are outside this theorem's scope.
Akita's extra constraints are to be modeled separately; PCS security is out of scope.
The top-level proof is a short chain of named helpers. B6's known
counterexamples are excluded by temporary restrictions
(their FIXMEs in Soundness/Assumptions.lean).
-/
import JoltConstraints.Soundness.TopLevel
import JoltConstraints.Soundness.Layer7.TapeRebuild
import JoltConstraints.Soundness.UntrustedAdvice.Bytes

open LeanRV64D

set_option autoImplicit false

-- Soundness for the byte relation: if some private inputs, with untrusted advice given
-- as bytes, and a witness satisfy every constraint, the instance is in Jolt's language.
-- `JoltInstance.soundness` below is the statement for the relation Jolt's verifier
-- checks, where the untrusted advice is committed field elements.
-- The field is a `JoltField`. The instance satisfies `JoltInstance.SoundnessAssumptions`
-- and, for now, the workarounds in `JoltInstance.TemporaryRestrictions`; both are in
-- Soundness/Assumptions.lean.
-- The private inputs of the run need not be the ones given.
-- FIXME: B6's known counterexamples are excluded only by temporary restrictions:
-- `terminationThenStall` for stopping early on a "no panic" claim, `claimsNoPanic`
-- for stopping early on a "panicked" claim, and `panicStoresOne` for a store of 0
-- proved as "no panic". These are Jolt bugs that must be fixed in Jolt.
theorem JoltInstance.soundness_onBytes {F : Type} [Field F] (joltField : JoltField F)
    (joltInstance : JoltInstance SourceInstruction)
    (assumptions : joltInstance.SoundnessAssumptions)
    (restrictions : joltInstance.TemporaryRestrictions)
    {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params)
    (satisfied : JoltConstraints.AllConstraintsOnBytes joltInstance privateInputs witness) :
    joltInstance.InLanguage := by
  obtain ⟨context, equations⟩ := satisfied
  obtain ⟨trace, bytecodeEq, represented⟩ :=
    soundness_reconstruct_trace joltField joltInstance assumptions restrictions
      privateInputs witness context equations
  apply JoltConstraints.Soundness.untrustedAnswerLanguage_implies_inLanguage
  refine ⟨privateInputs, trace, ?_, ?_, ?_⟩
  · exact soundness_matches_outputs joltField joltInstance privateInputs witness
      context equations trace represented
  · exact soundness_prover_accepts joltField joltInstance restrictions.noMaxLengthTrace
      privateInputs witness
      context equations trace bytecodeEq represented
  · exact soundness_spoil_asserts_pass joltField joltInstance privateInputs witness
      context equations trace bytecodeEq represented

-- Soundness: if committed untrusted-advice words and a witness satisfy every constraint,
-- the instance is in Jolt's language. Jolt's verifier holds only a commitment to the
-- untrusted advice, so each advice word is an arbitrary field element.
-- The field is a `JoltField`. The instance satisfies `JoltInstance.SoundnessAssumptions`
-- and, for now, the workarounds in `JoltInstance.TemporaryRestrictions`; both are in
-- Soundness/Assumptions.lean. The run's private inputs are built from the words: each
-- word that is not the cast of a 64-bit word is replaced by zero, which no load can tell
-- apart (`JoltConstraints.Soundness.UntrustedAdvice.onBytes_of_allConstraints`).
-- FIXME: B6's known counterexamples are excluded only by temporary restrictions, as
-- for `JoltInstance.soundness_onBytes`. `untrustedAdviceBlockFits` also excludes a
-- configured maximum untrusted-advice size that is not a multiple of 8 (its FIXME in
-- Soundness/Assumptions.lean).
theorem JoltInstance.soundness {F : Type} [Field F] (joltField : JoltField F)
    (joltInstance : JoltInstance SourceInstruction)
    (assumptions : joltInstance.SoundnessAssumptions)
    (restrictions : joltInstance.TemporaryRestrictions)
    {params : WitnessParams} (untrustedAdvice : Nat → F)
    (witness : WitnessType F params)
    (satisfied : JoltConstraints.AllConstraints joltInstance untrustedAdvice witness) :
    joltInstance.InLanguage := by
  obtain ⟨privateInputs, witness', onBytes⟩ :=
    JoltConstraints.Soundness.UntrustedAdvice.onBytes_of_allConstraints joltField
      restrictions.untrustedAdviceBlockFits untrustedAdvice satisfied
  exact JoltInstance.soundness_onBytes joltField joltInstance assumptions restrictions
    privateInputs witness' onBytes
