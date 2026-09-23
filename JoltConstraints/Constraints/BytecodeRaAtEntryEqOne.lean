import JoltConstraints.Constraints.BytecodeReadSelectors
import JoltConstraints.honest_witness

set_option autoImplicit false

namespace JoltConstraints

open scoped BigOperators

/-- Constraint (53) in `constraints.md`:
At cycle zero, the full bytecode selector selects the supplied public entry slot.
The entry slot comes from preprocessing; it need not be slot 1.
Rust: https://github.com/abiswas3/jolt/tree/main/crates/jolt-claims/src/protocols/jolt/geometry/bytecode.rs#L358-L378 -/
def bytecodeRaAtEntryEqOne {F : Type} [Field F] {params : WitnessParams}
    (entry : Fin (2 ^ params.logBytecodeK)) (witness : WitnessType F params) : Prop :=
  bytecodeRa witness entry ⟨0, pow_pos (by decide : 0 < (2 : Nat)) _⟩ = 1

/-- Completeness target for the honest witness; proof pending.
Trace linkage alone does not select the first instruction. startsAtEntry
connects the first executed row to the public entry slot. -/
theorem honestWitness_bytecodeRaAtEntryEqOne
    {F : Type} [Field F] (params : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program)
    (ramFits : params.RamFits trace)
    (traceFits : trace.rows.size ≤ params.traceLength)
    (bytecodeFits : program.expandedBytecode.size + 1 ≤ 2 ^ params.logBytecodeK)
    (entry : Fin (2 ^ params.logBytecodeK))
    (nonempty : 0 < trace.rows.size)
    (startsAtEntry : (getElem trace.rows 0 nonempty).rowIndex.val + 1 = entry.val)
    : bytecodeRaAtEntryEqOne entry
      (JoltProgram.honestWitness (F := F) params trace ramFits traceFits) := by
  sorry

end JoltConstraints
