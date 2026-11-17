import JoltConstraints.translation.Constraints.AssertLookupOne
import Mathlib.Algebra.Field.Defs
import JoltConstraints.translation.witness
import JoltConstraints.translation.honest_witness
import JoltConstraints.theorems.witness_domain

open LeanRV64D

set_option autoImplicit false

namespace JoltConstraints

/-- The equality assertions in this trace have equal operands. For an immediate
of zero, successful execution already enforces this. For a nonzero immediate,
this excludes the failing spoil execution that Rust permits to retire but whose
proof is deliberately unsatisfiable.
Rust: tracer/src/instruction/virtual_assert_eq.rs and
crates/jolt-lookup-tables/src/instructions/virt/assert_eq.rs. -/
def assertEqPasses (trace : Trace) : Prop :=
  ∀ t : Fin trace.rows.size,
    let row := trace.rows[t]
    match (getElem trace.bytecode row.rowIndex.val row.rowIndex.isLt).instruction with
    | .VirtualAssertEQ lhs rhs _ =>
        JoltISA.sourceValue lhs row.preState = JoltISA.sourceValue rhs row.preState
    | _ => True

/-- Completeness for traces whose equality assertions can satisfy Rust's
unmodified assertion constraint. The extra premise excludes a failed spoiled
assertion; the unrestricted statement is false. -/
theorem honestWitness_assertLookupOne
    {F : Type} [Field F] (params : WitnessParams)
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (_ramFits : params.RamFits trace)
    (_traceFits : params.ProverPaddedFor trace.rows.size)
    (_bytecodeDomain : params.BytecodeDomainFor trace.bytecode.size)
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

open JoltConstraints

-- Every assert in the run has equal sides: an ordinary one (imm = 0) executed, so its
-- sides were equal; a spoil one (imm ≠ 0) is assumed to pass.
theorem HonestTrace.assert_eq_passes {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (spoilAssertsPass : trace.SpoilAssertsPass) : assertEqPasses trace := by
  intro t
  dsimp only
  split
  · rename_i lhs rhs imm isAssert
    by_cases zero : imm = 0
    · -- an ordinary assert
      subst zero
      have runs := trace.executes trace.rows[t] (Array.getElem_mem t.isLt)
      rw [withRuntimeAdvice_assert (instruction := trace.bytecode[trace.rows[t].rowIndex].instruction)
        _ lhs rhs 0 isAssert] at runs
      exact assert_eq_holds lhs rhs _ _ _ runs
    · -- a spoil assert
      exact spoilAssertsPass _ (Array.getElem_mem t.isLt) lhs rhs imm isAssert zero
  · trivial
