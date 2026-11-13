import JoltConstraints.Completeness.Helpers.InstructionReadSelection
import JoltConstraints.Completeness.RightLookupAdd
import JoltConstraints.Constraints.InstructionAddressCanonical
import JoltConstraints.Soundness.Layer4.Identity

open LeanRV64D

set_option autoImplicit false

namespace JoltConstraints

open JoltConstraints.Soundness

/-- A 64-bit value widened to 128 bits lies below `2^128 - 2^64`. -/
private theorem setWidthIndex_lt (value : BitVec 64) :
    (value.setWidth 128).toNat < 2 ^ 128 - 2 ^ 64 := by
  have := value.isLt
  rw [BitVec.toNat_setWidth]
  omega

/-- A floor row's index `base + imm`, when not negative, lies below
`2^64 + 2^63`, hence below `2^128 - 2^64`. -/
private theorem floorIndex_lt (base imm : BitVec 64)
    (nonneg : 0 ≤ (base.toNat : Int) + imm.toInt) :
    (BitVec.ofInt 128 ((base.toNat : Int) + imm.toInt)).toNat < 2 ^ 128 - 2 ^ 64 := by
  have baseLt := base.isLt
  have immLt := BitVec.toInt_lt (x := imm)
  have below : (base.toNat : Int) + imm.toInt < 2 ^ 128 := by
    norm_num at baseLt immLt ⊢
    omega
  have exactValue : ((BitVec.ofInt 128 ((base.toNat : Int) + imm.toInt)).toNat : Int) =
      (base.toNat : Int) + imm.toInt := by
    rw [BitVec.toNat_ofInt, Nat.cast_pow, Nat.cast_ofNat,
      Int.emod_eq_of_lt nonneg below, Int.toNat_of_nonneg nonneg]
  norm_num at baseLt immLt ⊢
  omega

/-- Every lookup index the honest prover forms with identity RAF lies below
`2^128 - 2^64`: additions are below `2^65`, subtractions below `2^65`,
products at most `(2^64 - 1)^2`, widened words below `2^64`, and floor
addresses below `2^64 + 2^63` once they are not negative. For example, the
largest product `(2^64 - 1)^2 = 2^128 - 2^65 + 1` is still `2^64 - 1` below the
bound.
Rust: `crates/jolt-claims/src/protocols/jolt/geometry/instruction.rs`
(`canonical_predicate_separates_aliases_from_honest_indices`) at `c97e9300`. -/
theorem instructionLookupIndex_lt_of_raf (instruction : JoltISA.Instr)
    (address : BitVec 64) (preState postState : SailJoltState)
    (raf : JoltMetadata.instructionRafFlag instruction = true)
    (floorNonneg : ∀ (base : JoltISA.Src) (imm : BitVec 64),
      floorAccess? instruction = some (base, imm) →
        0 ≤ ((JoltISA.sourceValue base preState).toNat : Int) + imm.toInt) :
    (TraceWitness.instructionLookupIndex instruction address preState postState).toNat <
      2 ^ 128 - 2 ^ 64 := by
  cases instruction <;>
    simp only [JoltMetadata.instructionRafFlag, JoltMetadata.opcodeFlag, Bool.false_or,
      Bool.or_false, Bool.false_eq_true] at raf <;>
    simp only [TraceWitness.instructionLookupIndex]
  all_goals first
    | exact addWideIndex_lt _ _
    | exact subWideIndex_lt _ _
    | exact mulWideIndex_lt _ _
    | exact setWidthIndex_lt _
    | exact floorIndex_lt _ _ (floorNonneg _ _ rfl)

/-- Completeness of constraint (63) for the honest witness, in every field.
Identity-RAF rows select their honest lookup index, which lies below
`2^128 - 2^64` (`instructionLookupIndex_lt_of_raf`), so its upper half is not
all ones; other rows have `InstructionRafFlag = 0`.
Floor rows use the same nonnegativity obligation as constraint (08)
(`HonestTrace.floorAccess_address_nonneg`, a16z/jolt#1949).
Jolt's prover: `crates/jolt-kernels/src/optimized/instruction_read_raf.rs`
(`CANONICAL_INSTRUCTION_ADDRESS`) at `c97e9300`. -/
theorem honestWitness_instructionAddressCanonical
    {F : Type} [Field F] (params : WitnessParams)
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (trace : HonestTrace joltInstance privateInputs)
    (ramFits : params.RamFits trace)
    (traceFits : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor trace.bytecode.size) :
    instructionAddressCanonical (HonestTrace.honestWitness (F := F) params trace) := by
  intro _ t
  rw [instructionRead_honest params trace ramFits traceFits bytecodeDomain upperHalfAllOnes t]
  by_cases inBounds : t.val < trace.rows.size
  · by_cases raf : JoltMetadata.instructionRafFlag
        (trace.bytecode[(trace.rows[t.val]'inBounds).rowIndex]).instruction = true
    · rw [upperHalfAllOnes_eq_zero_of_lt, mul_zero]
      simp only [TraceWitness.lookupIndex, inBounds, dite_true]
      exact instructionLookupIndex_lt_of_raf _ _ _ _ raf
        (fun _ _ floor => trace.floorAccess_address_nonneg t.val inBounds floor)
    · simp [HonestTrace.honestWitness, TraceWitness.InstructionRafFlag, inBounds]
      exact fun rafTrue => absurd rafTrue raf
  · simp [HonestTrace.honestWitness, TraceWitness.InstructionRafFlag, inBounds]

end JoltConstraints
