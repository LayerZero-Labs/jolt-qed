/-
The base non-succinct soundness statement: a witness that satisfies every modeled
constraint shows the instance is in Jolt's language, under the premises below.
Source programs are limited to the instructions represented by `SourceInstruction`.
That type includes twelve registered inlines at opcode 0x0B: SHA256, SHA256_INIT,
KECCAK256, KECCAK256_ABSORB_PERMUTE, BLAKE2 and the seven secp256k1 inlines MULQ,
SQUAREQ, DIVQ, MULR, SQUARER, DIVR and GLVR_ADV (`JoltBytecode/Inlines/Keys.lean`).
Every other 0x0B encoding, opcode 0x2B and the field-inline opcode 0x7B are outside
that type. Guests using them are outside this theorem's scope.
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

/-- Soundness for the byte relation: if some private inputs, with untrusted advice given
as bytes, and a witness satisfy every constraint, the instance is in Jolt's language.
`JoltInstance.soundness` below is the statement for the relation Jolt's verifier
checks, where the untrusted advice is committed field elements.
The field is a `JoltField`. The instance satisfies `JoltInstance.SoundnessAssumptions`
and, for now, the workarounds in `JoltInstance.TemporaryRestrictions`; both are in
Soundness/Assumptions.lean.
The private inputs of the run need not be the ones given.
For example, a witness for a guest that echoes its input, with 8 bytes of untrusted
advice, shows that some run of the guest has the claimed outputs.
FIXME: B6's known counterexamples are excluded only by temporary restrictions:
`terminationThenStall` for stopping early on a "no panic" claim, `claimsNoPanic`
for stopping early on a "panicked" claim, and `panicStoresOne` for a store of 0
proved as "no panic". These are Jolt bugs that must be fixed in Jolt. -/
theorem JoltInstance.soundness_onBytes {F : Type} [Field F] (joltField : JoltField F)
    (joltInstance : JoltInstance SourceInstruction)
    (assumptions : joltInstance.SoundnessAssumptions)
    (restrictions : joltInstance.TemporaryRestrictions)
    {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params)
    (satisfied : JoltConstraints.AllConstraintsOnBytes joltInstance privateInputs witness) :
    joltInstance.InLanguage := by
  obtain ⟨context, equations⟩ := satisfied
  obtain ⟨words, trace, bytecodeEq, represented⟩ :=
    soundness_reconstruct_trace joltField joltInstance assumptions restrictions
      privateInputs witness context equations
  -- The trace's private inputs differ from `privateInputs` only in `inline_advice`,
  -- which the constraints do not read.
  let inputs := { privateInputs with inline_advice := words }
  apply JoltConstraints.Soundness.untrustedAnswerLanguage_implies_inLanguage
  refine ⟨inputs, trace, ?_, ?_, ?_⟩
  · exact soundness_matches_outputs joltField joltInstance inputs witness
      (context.withInlineAdvice words) equations trace represented
  · exact soundness_prover_accepts joltField joltInstance restrictions.noMaxLengthTrace
      inputs witness
      (context.withInlineAdvice words) equations trace bytecodeEq represented
  · exact soundness_spoil_asserts_pass joltField joltInstance inputs witness
      (context.withInlineAdvice words) equations trace bytecodeEq represented

/-- Soundness: if committed untrusted-advice words and a witness satisfy every constraint,
the instance is in Jolt's language. Jolt's verifier holds only a commitment to the
untrusted advice, so each advice word `untrustedAdvice index` is an arbitrary field
element.
The field is a `JoltField`. The instance satisfies `JoltInstance.SoundnessAssumptions`
and, for now, the workarounds in `JoltInstance.TemporaryRestrictions`; both are in
Soundness/Assumptions.lean. The run's private inputs are built from the words: each
word that is not the cast of a 64-bit word is replaced by zero, which no load can tell
apart (`JoltConstraints.Soundness.UntrustedAdvice.onBytes_of_allConstraints`).
For example, a prover that commits to the advice word `2^64` and overwrites it before
any load gives a run whose advice holds zero in that word.
FIXME: B6's known counterexamples are excluded only by temporary restrictions, as
for `JoltInstance.soundness_onBytes`. The separate temporary premise `adviceBlockFits`
(`JoltInstance.UntrustedAdviceBlockFits`, with its FIXME in Soundness/Assumptions.lean)
excludes a configured maximum untrusted-advice size that is not a multiple of 8. -/
theorem JoltInstance.soundness {F : Type} [Field F] (joltField : JoltField F)
    (joltInstance : JoltInstance SourceInstruction)
    (assumptions : joltInstance.SoundnessAssumptions)
    (restrictions : joltInstance.TemporaryRestrictions)
    (adviceBlockFits : joltInstance.UntrustedAdviceBlockFits)
    {params : WitnessParams} (untrustedAdvice : Nat → F)
    (witness : WitnessType F params)
    (satisfied : JoltConstraints.AllConstraints joltInstance untrustedAdvice witness) :
    joltInstance.InLanguage := by
  obtain ⟨privateInputs, witness', onBytes⟩ :=
    JoltConstraints.Soundness.UntrustedAdvice.onBytes_of_allConstraints joltField
      adviceBlockFits untrustedAdvice satisfied
  exact JoltInstance.soundness_onBytes joltField joltInstance assumptions restrictions
    privateInputs witness' onBytes
