import JoltConstraints.Constraints.LookupOutputEqInstructionReadRaf
import JoltConstraints.Constraints.InstructionLookupRa
import JoltConstraints.Constraints.InstructionReadSelection
import JoltConstraints.Constraints.LookupEntryProofHelpers

set_option autoImplicit false

namespace JoltConstraints

open scoped BigOperators

/-
For every padded trace index t ∈ T:

  LookupOutput(t) =
    ∑_{x ∈ X} (∏_{j=0}^{J−1} InstructionRaⱼ(vⱼ(x),t))
              · (∑_{q ∈ Q} LookupTableFlag_q(t) · Table_q(x)).

T = {0, …, params.traceLength − 1}, X = {0, …, 2^128 − 1}, and Q is the set
of lookup-table kinds. J = params.virtualInstructionChunks, and vⱼ(x) is the
jth virtual address chunk, most significant first. All arithmetic is in F.
-/

/-- Completeness of the lookup-output constraint. The execution-row case
reduces to `lookupEntryCorrect_of_lookupTable` (one lemma per lookup table in
`LookupEntryProofHelpers.lean`); some of those remain `sorry`, see there. -/
theorem honestWitness_lookupOutputEqInstructionReadRaf
    {F : Type} [Field F] (params : WitnessParams)
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (ramFits : params.RamFits trace)
    (traceFits : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor trace.bytecode.size) :
    lookupOutputEqInstructionReadRaf
      (HonestTrace.honestWitness (F := F) params trace) := by
  intro t
  by_cases inBounds : t.val < trace.rows.size
  · -- Execution row: collapse the address sum to the honest index, the table
    -- sum to the flagged table, and apply the per-table entry lemmas.
    set row := getElem trace.rows t.val inBounds with hrow
    rw [instructionRead_honest params trace ramFits traceFits bytecodeDomain
      (fun a => ∑ table : LookupTableKind,
        (HonestTrace.honestWitness (F := F) params trace).LookupTableFlag
          table t * lookupTableEntry table a) t]
    have hidx : (⟨(HonestWitness.lookupIndex trace t.val).toNat,
        (HonestWitness.lookupIndex trace t.val).isLt⟩ : Fin (2 ^ 128)) = rowLookupAddress row := by
      simp only [HonestWitness.lookupIndex, dif_pos inBounds, rowLookupAddress, rowLookupIndex, hrow]
      rfl
    rw [hidx]
    have hflag : ∀ table : LookupTableKind,
        (HonestTrace.honestWitness (F := F) params trace).LookupTableFlag
          table t = if JoltMetadata.lookupTable (rowInstruction row) = some table then 1 else 0 := by
      intro table
      simp only [HonestTrace.honestWitness, HonestWitness.LookupTableFlag, dif_pos inBounds,
        JoltMetadata.lookupTableFlag, beq_iff_eq, rowInstruction, hrow]
    have hout : (HonestTrace.honestWitness (F := F) params trace).LookupOutput t
        = ((HonestWitness.rowLookupOutput row).toNat : F) := by
      simp only [HonestTrace.honestWitness, HonestWitness.LookupOutput, dif_pos inBounds]
      rfl
    simp only [hflag, hout, ite_mul, one_mul, zero_mul]
    cases hk : JoltMetadata.lookupTable (rowInstruction row) with
    | none =>
      simp [rowLookupOutput_eq_zero_of_lookupTable_none row hk]
    | some k =>
      simp only [Option.some.injEq, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      exact (lookupEntryCorrect_of_lookupTable row k hk).symm
  · -- Padding has zero output and every table flag is zero.
    simp [HonestTrace.honestWitness, HonestWitness.LookupOutput,
      HonestWitness.LookupTableFlag, inBounds]

end JoltConstraints
