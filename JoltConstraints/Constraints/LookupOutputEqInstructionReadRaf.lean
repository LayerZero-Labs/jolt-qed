import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.Defs
import JoltConstraints.Constraints.InstructionLookupRa

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

/-- Constraint (39) in `constraints.md` (stage 5): the lookup output is the sum
of fixed table entries weighted by the witness's address and table selectors. -/
def lookupOutputEqInstructionReadRaf {F : Type} [Field F] {params : WitnessParams}
    (witness : WitnessType F params) : Prop :=
  ∀ t : Fin params.traceLength,
    witness.LookupOutput t =
      ∑ address : Fin (2 ^ 128), instructionLookupRa witness address t *
        ∑ table : LookupTableKind, witness.LookupTableFlag table t * lookupTableEntry table address

end JoltConstraints
