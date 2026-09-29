import JoltConstraints.Constraints.BytecodeReadSelectors
import JoltConstraints.Constraints.BytecodeReadSelection
import JoltConstraints.honest_witness

set_option autoImplicit false

namespace JoltConstraints

open scoped BigOperators

/-- Constraint (51) in `constraints.md`:
The flag agrees with the selected fixed bytecode row.
Rust: https://github.com/abiswas3/jolt/tree/main/crates/jolt-claims/src/protocols/jolt/geometry/bytecode.rs#L603-L609 -/
def lookupTableFlagEqBytecodeRead {F : Type} [Field F] {params : WitnessParams}
    (program : JoltProgram) (witness : WitnessType F params) : Prop :=
  ∀ (table : LookupTableKind) (t : Fin params.traceLength),
    witness.LookupTableFlag table t =
      ∑ address : Fin (2 ^ params.logBytecodeK),
        bytecodeLookupTableFlag program table address.val * bytecodeRa witness address t

/-- Completeness target for the honest witness.
The domain contains every expanded row and the leading no-op slot. -/
theorem honestWitness_lookupTableFlagEqBytecodeRead
    {F : Type} [Field F] (params : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program)
    (ramFits : params.RamFits trace)
    (traceFits : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor program.expandedBytecode.size)
    : lookupTableFlagEqBytecodeRead program
      (JoltProgram.honestWitness (F := F) params trace ramFits traceFits bytecodeDomain) := by
  intro table t
  rw [bytecodeRead_honest params trace ramFits traceFits bytecodeDomain
    (bytecodeLookupTableFlag program table) t]
  by_cases h : t.val < trace.rows.size
  · simp [JoltProgram.honestWitness, HonestWitness.LookupTableFlag,
      HonestWitness.bytecodePc, bytecodeLookupTableFlag, bytecodeRow, h]
  · simp [JoltProgram.honestWitness, HonestWitness.LookupTableFlag,
      HonestWitness.bytecodePc, bytecodeLookupTableFlag, bytecodeRow, h]

end JoltConstraints
