import JoltConstraints.translation.Constraints.RamAddrEqRs1PlusImmMinusLookupIfLoadStore
import JoltConstraints.translation.honest_witness
import JoltConstraints.theorems.witness_domain
import JoltConstraints.theorems.Completeness.Helpers.AddressWindow

open LeanRV64D

set_option autoImplicit false

namespace JoltConstraints

/-- Constraint (01) has the form
`(Load t + Store t) · (RamAddress t - Rs1Value t - Imm t + LookupOutput t) = 0`.
On a memory row, that is when the instruction at cycle `t` is LD, SD,
`VirtualLoadB/H/W` or `VirtualStoreB/H/W`, `Load t + Store t = 1`.
So (01) needs `RamAddress t = Rs1Value t + Imm t - LookupOutput t`.
Each cell is a trace value cast into the field: `RamAddress t`, `Rs1Value t`
and `LookupOutput t` are 64-bit values, and `Imm t` is the signed offset.
The equation adds them in the field, but Jolt's tracer computed
`RamAddress t` with 64-bit addition, which wraps.
So the equation holds only when `rs1 + imm` does not wrap. For example,
`ld x1, -16(x0)` gives `RamAddress t = 2^64 - 16`, but the right side is
`0 + (-16) - 0 = -16`; they differ by `2^64`, and the constraint is not
satisfied.
That row never retires in an honest trace, so `rs1 + imm` does not wrap there.
The tracer accepts a memory row's doubleword only inside the address window
`[0x40000000, 2^63 + 2^31)`, and every memory offset is a sign-extended 12-bit
value (`HonestTrace.access_noWrap`).
In the example, the wrapped address `2^64 - 16` lies above the window, and the
tracer stops before the row retires.
Jolt at ff6fc6568: `tracer/src/emulator/mmu.rs` (`assert_effective_address`).

Rust, at `ff6fc6568`:
- (01): `crates/jolt-claims/src/protocols/composed/r1cs/rv64.rs`
  (`RamAddrEqRs1PlusImmMinusLookupIfLoadStore`, row 0).
- 64-bit address addition: `tracer/src/instruction/ld.rs` (`LD::exec`),
  `tracer/src/instruction/sd.rs` (`SD::exec`) and
  `tracer/src/instruction/floor_access.rs` (`addresses`), all `wrapping_add`.
- The cells: `crates/jolt-witness/src/witnesses/ram.rs` (`RamAddress`),
  `crates/jolt-witness/src/witnesses/registers.rs` (`Rs1Value`),
  `crates/jolt-witness/src/witnesses/operands.rs` (`Imm`) and
  `crates/jolt-witness/src/witnesses/lookups.rs` (`LookupOutput`). -/
theorem honestWitness_ramAddrEqRs1PlusImmMinusLookupIfLoadStore
    {F : Type} [Field F] (params : WitnessParams)
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (_ramFits : params.RamFits trace)
    (_traceFits : params.ProverPaddedFor trace.rows.size)
    (_bytecodeDomain : params.BytecodeDomainFor trace.bytecode.size) :
    ramAddrEqRs1PlusImmMinusLookupIfLoadStore
      (HonestTrace.honestWitness (F := F) params trace) := by
  intro t
  change (TraceWitness.OpFlags params trace .Load t + TraceWitness.OpFlags params trace .Store t) *
    (TraceWitness.RamAddress (F := F) params trace t - TraceWitness.Rs1Value (F := F) params trace t -
      TraceWitness.Imm (F := F) params trace t + TraceWitness.LookupOutput (F := F) params trace t) = 0
  by_cases inside : t.val < trace.rows.size
  · by_cases memory :
        JoltMetadata.opcodeFlag trace.bytecode[(trace.rows[t.val]'inside).rowIndex].instruction
          .Load = true ∨
        JoltMetadata.opcodeFlag trace.bytecode[(trace.rows[t.val]'inside).rowIndex].instruction
          .Store = true
    · obtain ⟨width, base, imm, access⟩ : ∃ width base imm, Soundness.AccessRow
          trace.bytecode[(trace.rows[t.val]'inside).rowIndex].instruction width base imm := by
        rcases memory with load | store
        · obtain ⟨width, _, base, imm, row⟩ := Soundness.loadRow_of_flag _ load
          exact ⟨width, base, imm, row.access⟩
        · obtain ⟨width, base, _, imm, row⟩ := Soundness.storeRow_of_flag _ store
          exact ⟨width, base, imm, row.access⟩
      -- With no wrap, the recorded address plus the lookup offset is `base + imm`.
      have bounds := trace.access_noWrap t.val inside access
      have ram : TraceWitness.RamAddress (F := F) params trace t =
          ((width.recorded (JoltISA.sourceValue base (trace.rows[t.val]'inside).preState +
            imm)).toNat : F) := by
        have recorded := access.ramAccessAddress (trace.rows[t.val]'inside).preState
        simp only [Fin.getElem_fin] at recorded
        simp [TraceWitness.RamAddress, inside, recorded]
      have rs1 : TraceWitness.Rs1Value (F := F) params trace t =
          ((JoltISA.sourceValue base (trace.rows[t.val]'inside).preState).toNat : F) := by
        have operand : rs1Operand?
            trace.bytecode[(trace.rows[t.val]'inside).rowIndex].instruction = some base := by
          rcases access with ⟨_, load⟩ | ⟨_, store⟩
          · exact load.metadata.rs1Operand
          · exact store.metadata.rs1Operand
        rw [rs1Value_real params trace t inside, operand]
      have immediate : TraceWitness.Imm (F := F) params trace t = ((imm.toInt : Int) : F) := by
        have value := access.metadata.2.1
        simp only [Fin.getElem_fin] at value
        simp [TraceWitness.Imm, inside, value]
      have output : TraceWitness.LookupOutput (F := F) params trace t =
          (((JoltISA.sourceValue base (trace.rows[t.val]'inside).preState + imm) &&&
            width.offsetMask).toNat : F) := by
        have value := Soundness.AccessRow.rowLookupOutput (trace.rows[t.val]'inside) access
        simp [TraceWitness.LookupOutput, inside, value]
      have sum := add_toNat_cast_of_noWrap (F := F) _ _ bounds.1 bounds.2
      have parts : ((width.recorded (JoltISA.sourceValue base (trace.rows[t.val]'inside).preState +
            imm)).toNat : F) +
          (((JoltISA.sourceValue base (trace.rows[t.val]'inside).preState + imm) &&&
            width.offsetMask).toNat : F) =
          ((JoltISA.sourceValue base (trace.rows[t.val]'inside).preState + imm).toNat : F) := by
        rw [Soundness.MemoryWidth.recorded_toNat, BitVec.toNat_and, ← Nat.cast_add,
          Nat.sub_add_cancel Nat.and_le_left]
      have zero : TraceWitness.RamAddress (F := F) params trace t -
          TraceWitness.Rs1Value (F := F) params trace t - TraceWitness.Imm (F := F) params trace t +
          TraceWitness.LookupOutput (F := F) params trace t = 0 := by
        rw [ram, rs1, immediate, output]
        linear_combination parts + sum
      rw [zero, mul_zero]
    · have notLoad : JoltMetadata.opcodeFlag
          trace.bytecode[(trace.rows[t.val]'inside).rowIndex].instruction .Load = false :=
        Bool.eq_false_iff.mpr (fun load => memory (Or.inl load))
      have notStore : JoltMetadata.opcodeFlag
          trace.bytecode[(trace.rows[t.val]'inside).rowIndex].instruction .Store = false :=
        Bool.eq_false_iff.mpr (fun store => memory (Or.inr store))
      simp only [Fin.getElem_fin] at notLoad notStore
      simp [TraceWitness.OpFlags, JoltMetadata.circuitFlag, inside, notLoad, notStore]
  · simp [TraceWitness.OpFlags, inside]

end JoltConstraints
