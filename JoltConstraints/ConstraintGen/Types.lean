set_option autoImplicit false

/-! # Shapes of the generated constraint data (T3)

The files under `JoltConstraints/ConstraintGen/Generated/` are written by
`scripts/expansion-parity/src/bin/constraint-gen.rs` from Jolt's own code.
This file only fixes the shapes they use. What the data means for a witness is
in `ConstraintGen/Semantics.lean`, and the proofs that the handwritten
constraints say the same thing are in `ConstraintGen/Equiv.lean`. -/

namespace JoltConstraints.ConstraintGen

/-- One R1CS row `⟨A, z⟩ · ⟨B, z⟩ = ⟨C, z⟩` over variables `V`, each linear
combination a list of (variable, integer coefficient) pairs.
For example, Jolt's row 2 is `a = [(OpFlags_Load, 1)]`,
`b = [(RamReadValue, 1), (RamWriteValue, -1)]`, `c = []`.
Jolt: `crates/jolt-r1cs/src/constraint.rs` (`ConstraintMatrices`). -/
structure R1CSRow (V : Type) where
  name : String
  a : List (V × Int)
  b : List (V × Int)
  c : List (V × Int)

/-- An expression over polynomial names `P`, as Jolt's `UnbatchedClaimExpr`.
For example, `.mul (.poly RamRa) (.poly RamVal)`.
Jolt: `crates/jolt-claims/src/protocols/jolt/unbatched.rs`. -/
inductive ClaimExpr (P : Type) where
  | const (value : Int)
  | poly (polynomial : P)
  | add (left right : ClaimExpr P)
  | mul (left right : ClaimExpr P)
  | sub (left right : ClaimExpr P)

/-- One claim of a relation, as Jolt's `UnbatchedClaim`: the `input` expression,
opened in `inputRelation`, equals the `output` expression weighted by
`outputWeight`; `offset` marks a claim whose output is read at the next cycle.
Jolt: `crates/jolt-claims/src/protocols/jolt/unbatched.rs`. -/
structure RelationClaim (R P W : Type) where
  inputRelation : R
  input : ClaimExpr P
  output : ClaimExpr P
  outputWeight : W
  offset : Bool

/-- A relation, as Jolt's `UnbatchedRelation` without its batching challenge. -/
structure Relation (R P W : Type) where
  outputRelation : R
  claims : List (RelationClaim R P W)

end JoltConstraints.ConstraintGen
