import JoltConstraints.Constraints.AssertLookupOne
import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.honest_witness

set_option autoImplicit false

namespace JoltConstraints

/-- Completeness for traces whose equality assertions can satisfy Rust's
unmodified assertion constraint. The extra premise excludes a failed spoiled
assertion; the unrestricted statement is false. -/
theorem honestWitness_assertLookupOne
    {F : Type} [Field F] (params : WitnessParams)
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (ramFits : params.RamFits trace)
    (traceFits : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor trace.bytecode.size)
    (hAssertEqPasses : assertEqPasses trace) :
    assertLookupOne
      (HonestTrace.honestWitness (F := F) params trace) := by
  intro t
  by_cases inBounds : t.val < trace.rows.size
  · let row := trace.rows[t.val]'inBounds
    let instruction :=
      (getElem trace.bytecode row.rowIndex.val row.rowIndex.isLt).instruction
    have hPass :
        match instruction with
        | .VirtualAssertEQ lhs rhs _ =>
            JoltISA.sourceValue lhs row.preState = JoltISA.sourceValue rhs row.preState
        | _ => True := by
      exact hAssertEqPasses ⟨t.val, inBounds⟩
    change TraceWitness.OpFlags params trace .Assert t *
      (TraceWitness.LookupOutput params trace t - 1) = 0
    simp only [TraceWitness.OpFlags, TraceWitness.LookupOutput, inBounds,
      dite_true]
    change (if JoltMetadata.circuitFlag
        (getElem trace.bytecode row.rowIndex.val row.rowIndex.isLt) .Assert
      then (1 : F) else 0) *
      (((TraceWitness.rowLookupOutput row).toNat : F) - 1) = 0
    change (if JoltMetadata.opcodeFlag instruction .Assert then (1 : F) else 0) *
      (((TraceWitness.rowLookupOutput row).toNat : F) - 1) = 0
    by_cases hAssert : JoltMetadata.opcodeFlag instruction .Assert = true
    · have hLookup : TraceWitness.rowLookupOutput row = 1 := by
        dsimp [instruction] at hAssert hPass
        change JoltMetadata.opcodeFlag
          (getElem trace.bytecode row.rowIndex.val row.rowIndex.isLt).instruction
          .Assert = true at hAssert
        change (match (getElem trace.bytecode row.rowIndex.val row.rowIndex.isLt).instruction with
          | .VirtualAssertEQ lhs rhs _ =>
              JoltISA.sourceValue lhs row.preState = JoltISA.sourceValue rhs row.preState
          | _ => True) at hPass
        cases hInstr : (getElem trace.bytecode row.rowIndex.val row.rowIndex.isLt).instruction <;>
          (rw [hInstr] at hAssert hPass
           simp [JoltMetadata.opcodeFlag] at hAssert)
        all_goals simp [TraceWitness.rowLookupOutput, hInstr, hPass, jolt_assert_eq]
      simp [hAssert, hLookup]
    · simp [hAssert]
  · simp [HonestTrace.honestWitness, TraceWitness.OpFlags,
      TraceWitness.LookupOutput, inBounds]

end JoltConstraints
