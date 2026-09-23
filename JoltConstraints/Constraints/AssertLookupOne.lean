import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.honest_witness

set_option autoImplicit false

namespace JoltConstraints

/-- The equality assertions in this trace have equal operands. For an immediate
of zero, successful execution already enforces this. For a nonzero immediate,
this excludes the failing spoil execution that Rust permits to retire but whose
proof is deliberately unsatisfiable.
Rust: tracer/src/instruction/virtual_assert_eq.rs and
crates/jolt-lookup-tables/src/instructions/virt/assert_eq.rs. -/
def assertEqPasses {program : JoltProgram} (trace : JoltTrace program) : Prop :=
  ∀ t : Fin trace.rows.size,
    let row := trace.rows[t]
    match (getElem program.expandedBytecode row.rowIndex.val row.rowIndex.isLt).instruction with
    | .VirtualAssertEQ lhs rhs _ =>
        JoltISA.sourceValue lhs row.preState = JoltISA.sourceValue rhs row.preState
    | _ => True

/-- Constraint (12) in `constraints.md` (stage 1):
assertion rows require lookup output one.
Rust: https://github.com/abiswas3/jolt/tree/main/crates/jolt-r1cs/src/constraints/rv64.rs -/
def assertLookupOne {F : Type} [Field F] {params : WitnessParams}
    (witness : WitnessType F params) : Prop :=
  ∀ t : Fin params.traceLength,
    witness.OpFlags .Assert t * (witness.LookupOutput t - 1) = 0

/-- Completeness for traces whose equality assertions can satisfy Rust's
unmodified assertion constraint. The extra premise excludes a failed spoiled
assertion; the unrestricted statement is false. -/
theorem honestWitness_assertLookupOne
    {F : Type} [Field F] (params : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program)
    (ramFits : params.RamFits trace)
    (traceFits : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor program.expandedBytecode.size)
    (hAssertEqPasses : assertEqPasses trace) :
    assertLookupOne
      (JoltProgram.honestWitness (F := F) params trace ramFits traceFits bytecodeDomain) := by
  intro t
  by_cases inBounds : t.val < trace.rows.size
  · let row := trace.rows[t.val]'inBounds
    let instruction :=
      (getElem program.expandedBytecode row.rowIndex.val row.rowIndex.isLt).instruction
    have hPass :
        match instruction with
        | .VirtualAssertEQ lhs rhs _ =>
            JoltISA.sourceValue lhs row.preState = JoltISA.sourceValue rhs row.preState
        | _ => True := by
      exact hAssertEqPasses ⟨t.val, inBounds⟩
    change HonestWitness.OpFlags params trace .Assert t *
      (HonestWitness.LookupOutput params trace t - 1) = 0
    simp only [HonestWitness.OpFlags, HonestWitness.LookupOutput, inBounds,
      dite_true]
    change (if JoltMetadata.circuitFlag
        (getElem program.expandedBytecode row.rowIndex.val row.rowIndex.isLt) .Assert
      then (1 : F) else 0) *
      (((HonestWitness.rowLookupOutput row).toNat : F) - 1) = 0
    change (if JoltMetadata.opcodeFlag instruction .Assert then (1 : F) else 0) *
      (((HonestWitness.rowLookupOutput row).toNat : F) - 1) = 0
    by_cases hAssert : JoltMetadata.opcodeFlag instruction .Assert = true
    · have hLookup : HonestWitness.rowLookupOutput row = 1 := by
        dsimp [instruction] at hAssert hPass
        change JoltMetadata.opcodeFlag
          (getElem program.expandedBytecode row.rowIndex.val row.rowIndex.isLt).instruction
          .Assert = true at hAssert
        change (match (getElem program.expandedBytecode row.rowIndex.val row.rowIndex.isLt).instruction with
          | .VirtualAssertEQ lhs rhs _ =>
              JoltISA.sourceValue lhs row.preState = JoltISA.sourceValue rhs row.preState
          | _ => True) at hPass
        cases hInstr : (getElem program.expandedBytecode row.rowIndex.val row.rowIndex.isLt).instruction <;>
          (rw [hInstr] at hAssert hPass
           simp [JoltMetadata.opcodeFlag] at hAssert)
        all_goals simp [HonestWitness.rowLookupOutput, hInstr, hPass, jolt_assert_eq]
      simp [hAssert, hLookup]
    · simp [hAssert]
  · simp [JoltProgram.honestWitness, HonestWitness.OpFlags,
      HonestWitness.LookupOutput, inBounds]

end JoltConstraints
