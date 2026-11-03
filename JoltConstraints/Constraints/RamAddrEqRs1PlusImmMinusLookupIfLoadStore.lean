import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.witness_helpers

set_option autoImplicit false

namespace JoltConstraints

/-- Constraint (01) in `constraints.md` (stage 1):
loads and stores use base plus immediate minus the lookup offset as their RAM address.
For example, a halfword floor row with effective address 10 and offset 2 records 8.
Jolt's verifier: `crates/jolt-claims/src/protocols/composed/r1cs/rv64.rs`
(`RV64_CONSTRAINT_NAMES`, row 0) at `c6703570`. -/
def ramAddrEqRs1PlusImmMinusLookupIfLoadStore {F : Type} [Field F] {params : WitnessParams}
    (witness : WitnessType F params) : Prop :=
  ∀ t : Fin params.traceLength,
    (witness.OpFlags .Load t + witness.OpFlags .Store t) *
      (witness.RamAddress t - witness.Rs1Value t - witness.Imm t + witness.LookupOutput t) = 0

end JoltConstraints
