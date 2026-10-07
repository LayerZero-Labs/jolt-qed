import JoltConstraints.Constraints.RegistersValEqPrefixRdInc
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.honest_witness
import JoltConstraints.Constraints.RegistersValHistoryProofHelpers

set_option autoImplicit false

namespace JoltConstraints

open scoped BigOperators

/-- Completeness target for the honest witness.
Initial register contents must agree with the zero-initialized Rust witness array.
Each bytecode row certifies that its register operands follow the ISA address map.
The proof must relate the replayed register history to the captured ISA values. -/
theorem honestWitness_registersValEqPrefixRdInc
    {F : Type} [Field F] (params : WitnessParams)
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (ramFits : params.RamFits trace)
    (traceFits : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor trace.bytecode.size)
    (initialRegistersZero : ∀ src : JoltISA.Src,
      JoltISA.sourceValue src trace.initialState = 0) :
    registersValEqPrefixRdInc
      (HonestTrace.honestWitness (F := F) params trace) := by
  intro register t
  exact honestRegistersVal_eq_prefixRdInc params trace traceFits initialRegistersZero register t

end JoltConstraints
