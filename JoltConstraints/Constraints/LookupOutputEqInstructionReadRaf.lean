import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.lookup_table
import JoltConstraints.honest_witness

set_option autoImplicit false

namespace JoltConstraints

open scoped BigOperators

/-- The `chunk`th virtual chunk of a 128-bit lookup address, most significant first. -/
def instructionLookupChunk (params : WitnessParams) (address : Fin (2 ^ 128))
    (chunk : Fin params.virtualInstructionChunks) : Fin (2 ^ params.virtualChunkBits) :=
  ⟨(address.val /
      2 ^ ((params.virtualInstructionChunks - 1 - chunk.val) * params.virtualChunkBits)) %
      2 ^ params.virtualChunkBits,
    Nat.mod_lt _ (pow_pos (by decide : 0 < (2 : Nat)) _)⟩

/-- `LookupRa(x,t)` in `constraints.md`: multiply the virtual instruction-address
entries selected by the chunks of `x`. -/
noncomputable def instructionLookupRa {F : Type} [Field F] {params : WitnessParams}
    (witness : WitnessType F params) (address : Fin (2 ^ 128))
    (t : Fin params.traceLength) : F :=
  ∏ chunk : Fin params.virtualInstructionChunks,
    witness.InstructionRa chunk (instructionLookupChunk params address chunk) t

/-
For every padded trace index t ∈ T:

  LookupOutput(t) =
    ∑_{x ∈ X} (∏_{j=0}^{J−1} InstructionRaⱼ(vⱼ(x),t))
              · (∑_{q ∈ Q} LookupTableFlag_q(t) · Table_q(x)).

T = {0, …, params.traceLength − 1}, X = {0, …, 2^128 − 1}, and Q is the set
of lookup-table kinds. J = params.virtualInstructionChunks, and vⱼ(x) is the
jth virtual address chunk, most significant first. All arithmetic is in F.
-/

/-- Constraint (39) in `constraints.md` (stage 5): the lookup output is the sum
of fixed table entries weighted by the witness's address and table selectors. -/
def lookupOutputEqInstructionReadRaf {F : Type} [Field F] {params : WitnessParams}
    (witness : WitnessType F params) : Prop :=
  ∀ t : Fin params.traceLength,
    witness.LookupOutput t =
      ∑ address : Fin (2 ^ 128), instructionLookupRa witness address t *
        ∑ table : LookupTableKind, witness.LookupTableFlag table t * lookupTableEntry table address

/-- Completeness of the lookup-output constraint. The execution-row case is
pending the fixed table definitions and their correspondence with ISA outputs. -/
theorem honestWitness_lookupOutputEqInstructionReadRaf
    {F : Type} [Field F] (params : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program)
    (ramFits : params.RamFits trace)
    (traceFits : params.ProverPaddedFor trace.rows.size) :
    lookupOutputEqInstructionReadRaf
      (JoltProgram.honestWitness (F := F) params trace ramFits traceFits) := by
  intro t
  by_cases inBounds : t.val < trace.rows.size
  · -- TODO: Show that the product of honest address chunks selects exactly
    -- `HonestWitness.lookupIndex trace t.val`, using the chunk-width divisibility.
    -- Then reduce the table flags to `JoltMetadata.lookupTable` and prove that
    -- its entry at this address equals `HonestWitness.rowLookupOutput` in F.
    -- Instructions with no lookup table must have lookup output zero.
    sorry
  · -- Padding has zero output and every table flag is zero.
    simp [JoltProgram.honestWitness, HonestWitness.LookupOutput,
      HonestWitness.LookupTableFlag, inBounds]

end JoltConstraints
