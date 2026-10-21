import JoltConstraints.Soundness.Layer5.TapeTrace

set_option autoImplicit false

namespace JoltConstraints.Soundness

/-- Every instance in the relaxed-answer language is in Jolt's language.
Together with `inLanguage_implies_untrustedAnswerLanguage`, this makes the two
languages equal. -/
theorem untrustedAnswerLanguage_implies_inLanguage
    {joltInstance : JoltInstance SourceInstruction}
    (member : UntrustedAnswerLanguage joltInstance) :
    joltInstance.InLanguage := by
  -- Rebuild the tape from each answer's low 1, 2, 4 or 8 bytes in read order.
  -- Replay the rows, preserving final device, prover dimensions and spoil operands.
  sorry

end JoltConstraints.Soundness
