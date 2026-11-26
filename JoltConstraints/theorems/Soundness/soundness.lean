/-
The base non-succinct soundness statement: a witness that satisfies every modeled
constraint shows the instance is in Jolt's language, under the premises below.
Source programs are limited to the instructions represented by `SourceInstruction`.
Jolt's inline/precompile opcodes 0x0B and 0x2B, including the SHA-256 and Keccak
inlines, are outside that type. Guests using them are outside this theorem's scope.
Of the extra checks in Jolt's `akita` build, the model includes the canonical
lookup-address check as constraint (63), `instructionAddressCanonical`, which applies
when the field characteristic is below 2^128. The build's other changes only
re-encode or add constraints, which soundness does not need. PCS security is out of scope.
The top-level proof is a short chain of named helpers.
It takes no temporary program restrictions.
-/
import JoltConstraints.theorems.Soundness.TopLevel
import JoltConstraints.theorems.Soundness.Layer7.TapeRebuild
import JoltConstraints.theorems.Soundness.UntrustedAdvice.Bytes

open LeanRV64D

set_option autoImplicit false

/-- Soundness for the byte relation: if some private inputs, with untrusted advice given
as bytes, and a witness satisfy every constraint, the instance is in Jolt's language.
`JoltInstance.soundness` below states the theorem for the relation Jolt's verifier
checks, where the untrusted advice is committed field elements.
The field is a `JoltField`; nothing is assumed about the instance.
The private inputs of the run need not be the ones given.
For example, a witness for a guest that echoes its input, with 8 bytes of untrusted
advice, shows that some run of the guest has the claimed outputs. -/
theorem JoltInstance.soundness_onBytes {F : Type} [Field F] (joltField : JoltField F)
    (joltInstance : JoltInstance SourceInstruction)
    {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params)
    (satisfied : JoltConstraints.AllConstraintsOnBytes joltInstance privateInputs witness) :
    joltInstance.InLanguage := by
  obtain ⟨context, equations⟩ := satisfied
  obtain ⟨trace, bytecodeEq, represented⟩ :=
    soundness_reconstruct_trace joltField joltInstance
      privateInputs witness context equations
  apply JoltConstraints.Soundness.untrustedAnswerLanguage_implies_inLanguage
  refine ⟨privateInputs, trace, ?_, ?_, ?_⟩
  · exact soundness_matches_outputs joltField joltInstance privateInputs witness
      context equations trace represented
  · exact soundness_prover_accepts joltField joltInstance
      privateInputs witness
      context equations trace bytecodeEq represented
  · exact soundness_spoil_asserts_pass joltField joltInstance privateInputs witness
      context equations trace bytecodeEq represented

/-- Soundness: if committed untrusted-advice words and a witness satisfy every
constraint, the instance is in Jolt's language. Jolt's verifier holds only a commitment
to the untrusted advice, so each advice word `untrustedAdvice index` is an arbitrary
field element. The field is a `JoltField`; nothing is assumed about the instance.
The run's private inputs are built from the words: each word that is not the cast of a
64-bit word becomes zero. No row reads or writes such a word
(`JoltConstraints.Soundness.UntrustedAdvice.allConstraintsOnBytes_of_allConstraints`).
For example, a prover that commits to the advice word `2 ^ 64` and never touches it
gives a run whose advice holds zero in that word. -/
theorem JoltInstance.soundness {F : Type} [Field F] (joltField : JoltField F)
    (joltInstance : JoltInstance SourceInstruction)
    {params : WitnessParams} (untrustedAdvice : Nat → F)
    (witness : WitnessType F params)
    (satisfied : JoltConstraints.AllConstraints joltInstance untrustedAdvice witness) :
    joltInstance.InLanguage := by
  obtain ⟨privateInputs, witness', onBytes⟩ :=
    JoltConstraints.Soundness.UntrustedAdvice.allConstraintsOnBytes_of_allConstraints
      joltField untrustedAdvice satisfied
  exact JoltInstance.soundness_onBytes joltField joltInstance privateInputs witness' onBytes

#print axioms JoltInstance.soundness
