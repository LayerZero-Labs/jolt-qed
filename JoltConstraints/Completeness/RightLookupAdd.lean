import JoltConstraints.Constraints.RightLookupAdd
import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.honest_witness
import JoltConstraints.Completeness.Helpers.AddressSum

set_option autoImplicit false

namespace JoltConstraints

/-- The base and signed immediate of a floor memory instruction, or `none`
for other instructions; for example, LoadH with base x2 and offset -2
returns `(x2, -2)`.
Jolt's prover: `crates/jolt-lookup-tables/src/instructions/virt/floor_access.rs`
(`to_instruction_inputs`) at `c6703570`. -/
def floorAccess? : JoltISA.Instr → Option (JoltISA.Src × BitVec 64)
  | .VirtualLoadB _ _ base imm _ | .VirtualLoadH _ _ base imm _
  | .VirtualLoadW _ _ base imm _ | .VirtualStoreB base _ imm _
  | .VirtualStoreH base _ imm _ | .VirtualStoreW base _ imm _ => some (base, imm)
  | _ => none

end JoltConstraints

open JoltConstraints in
/-- Constraint (08) has the form
`AddOperands t · (RightLookupOperand t - LeftInstructionInput t - RightInstructionInput t) = 0`.
When the instruction at cycle `t` is `VirtualLoadB/H/W` or `VirtualStoreB/H/W`,
`AddOperands t = 1`.
So (08) needs `RightLookupOperand t = LeftInstructionInput t + RightInstructionInput t`.
Each cell is a trace value cast into the field: `LeftInstructionInput t` is
the 64-bit `rs1`, `RightInstructionInput t` is the signed offset `imm`, and
`RightLookupOperand t` is a 128-bit value.
The equation adds them in the field, but Jolt's prover computed
`RightLookupOperand t` as `rs1 + imm` modulo `2^128`.
So the equation holds only when `rs1 + imm` is not negative. For example,
`lb x1, -16(x0)` gives `RightLookupOperand t = 2^128 - 16`, but the right side
is `0 + (-16) = -16`; they differ by `2^128`, and the constraint is not
satisfied.
Left as `sorry` until a16z/jolt#1949 is fixed.

Rust, at `c6703570`:
- (08): `crates/jolt-claims/src/protocols/composed/r1cs/rv64.rs` (`RightLookupAdd`).
- Flags of these instructions, so `AddOperands t = 1`:
  `crates/jolt-riscv/src/instructions/virt/{load,store}_{b,h,w}.rs` (`jolt_instruction!`).
- Inputs `(rs1, imm)` and `RightLookupOperand = (rs1 as i128 + imm) as u128`:
  `crates/jolt-lookup-tables/src/instructions/virt/floor_access.rs`
  (`to_instruction_inputs`, `to_lookup_operands`).
- Read by Jolt's prover in `crates/jolt-witness/src/witnesses/operands.rs`
  (`LeftInstructionInput`, `RightInstructionInput`, `RightLookupOperand`). -/
theorem HonestTrace.floorAccess_address_nonneg
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (trace : HonestTrace joltInstance privateInputs) (t : Nat) (inBounds : t < trace.rows.size)
    {base : JoltISA.Src} {imm : BitVec 64}
    (floor : floorAccess? trace.bytecode[(trace.rows[t]'inBounds).rowIndex].instruction =
      some (base, imm)) :
    0 ≤ ((JoltISA.sourceValue base (trace.rows[t]'inBounds).preState).toNat : Int) +
      imm.toInt := by
  sorry

namespace JoltConstraints

/-- A floor row's 128-bit lookup index casts to the sum of its instruction
inputs; for example, base 10 with immediate -2 yields field value 8.
Only its nonnegativity uses the honest-row #1949 obligation; the upper bound
follows from the operand widths.
Jolt's prover: `crates/jolt-lookup-tables/src/instructions/virt/floor_access.rs`
(`to_lookup_operands`) at `c6703570`. -/
private theorem floor_lookup_sum {F : Type} [Field F]
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (trace : HonestTrace joltInstance privateInputs) (t : Nat) (ht : t < trace.rows.size)
    {base : JoltISA.Src} {imm : BitVec 64}
    (floor : floorAccess? trace.bytecode[(trace.rows[t]'ht).rowIndex].instruction =
      some (base, imm)) :
    ((BitVec.ofInt 128
      ((JoltISA.sourceValue base (trace.rows[t]'ht).preState).toNat + imm.toInt)).toNat : F) =
      ((JoltISA.sourceValue base (trace.rows[t]'ht).preState).toNat : F) + (imm.toInt : F) := by
  have nonneg := trace.floorAccess_address_nonneg t ht floor
  have baseLt := (JoltISA.sourceValue base (trace.rows[t]'ht).preState).isLt
  have immLt := BitVec.toInt_lt (x := imm)
  have below : ((JoltISA.sourceValue base (trace.rows[t]'ht).preState).toNat : Int) +
      imm.toInt < 2 ^ 128 := by
    norm_num at baseLt immLt ⊢
    omega
  simpa only [Int.cast_add, Int.cast_natCast] using encodedInt_cast (F := F) 128 _ nonneg below

private theorem addWide_mod (left right : BitVec 64) :
    JoltISA.addWide left right % 340282366920938463463374607431768211456 =
      JoltISA.addWide left right := by
  have hl := left.isLt
  have hr := right.isLt
  apply Nat.mod_eq_of_lt
  dsimp [JoltISA.addWide]
  omega

private theorem addWide_cast {F : Type} [Field F] (left right : BitVec 64) :
    (JoltISA.addWide left right : F) = (left.toNat : F) + (right.toNat : F) := by
  simp [JoltISA.addWide]

private theorem narrow_mod_128 (value : BitVec 64) :
    value.toNat % 340282366920938463463374607431768211456 = value.toNat :=
  Nat.mod_eq_of_lt (value.isLt.trans (by norm_num))

private theorem masked_mod_128 (value : Nat) :
    value % 18446744073709551616 % 340282366920938463463374607431768211456 =
      value % 18446744073709551616 := by
  apply Nat.mod_eq_of_lt
  exact (Nat.mod_lt _ (by norm_num)).trans (by norm_num)

/-- Constraint (08) combines the selected inputs by addition, including floor
addresses; for example, base 10 and immediate -2 produce index 8.
The floor address equality depends on the explicit #1949 wrap obligation.
Jolt's verifier: `crates/jolt-claims/src/protocols/composed/r1cs/rv64.rs`
(`RightLookupAdd`) at `c6703570`. -/
theorem honestWitness_rightLookupAdd
    {F : Type} [Field F] (params : WitnessParams)
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (ramFits : params.RamFits trace)
    (traceFits : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor trace.bytecode.size) :
    rightLookupAdd
      (HonestTrace.honestWitness (F := F) params trace) := by
  intro t
  by_cases h : t.val < trace.rows.size
  · let row := getElem trace.rows t.val h
    let bytecodeRow := getElem trace.bytecode row.rowIndex.val row.rowIndex.isLt
    by_cases ha : JoltMetadata.opcodeFlag bytecodeRow.instruction .AddOperands = true
    · have heq : TraceWitness.RightLookupOperand (F := F) params trace t =
          TraceWitness.LeftInstructionInput (F := F) params trace t +
          TraceWitness.RightInstructionInput (F := F) params trace t := by
        cases hi : bytecodeRow.instruction
        all_goals simp [JoltMetadata.opcodeFlag, hi] at ha
        all_goals simp only [bytecodeRow, row] at hi
        all_goals
          simp [TraceWitness.RightLookupOperand, TraceWitness.lookupIndex,
            TraceWitness.instructionLookupIndex, TraceWitness.LeftInstructionInput,
            TraceWitness.RightInstructionInput, TraceWitness.Rs1Value,
            TraceWitness.Rs2Value, TraceWitness.Imm, TraceWitness.UnexpandedPC,
            JoltMetadata.hasCombinedLookupOperands, JoltMetadata.opcodeFlag,
            JoltMetadata.instructionFlag, addWide_mod, hi, h]
        all_goals (try simp [addWide_cast, narrow_mod_128, JoltMetadata.immediate])
        all_goals first
        | exact floor_lookup_sum trace t.val h (by simp [floorAccess?, hi])
        | (simp [masked_mod_128] <;> norm_cast)
      simp [HonestTrace.honestWitness, TraceWitness.OpFlags,
        JoltMetadata.circuitFlag, h, heq]
    · simp [HonestTrace.honestWitness,
        TraceWitness.OpFlags, JoltMetadata.circuitFlag, h, ha, bytecodeRow, row]
  · simp [HonestTrace.honestWitness, TraceWitness.OpFlags, h]

end JoltConstraints
