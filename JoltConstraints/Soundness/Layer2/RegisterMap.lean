import JoltConstraints.trace_interface
import JoltConstraints.witness_helpers.register_address
import JoltConstraints.constraint_context
import JoltConstraints.Constraints.BytecodeReadSelectors

/-! Register addresses identify operands only when their representations are
canonical: x0–x31 use architectural registers, and addresses 32–127 use virtual
registers. The raw constructors can alias, so decoding an encoded operand
requires canonicality. Expanded bytecode supplies that condition. -/

set_option autoImplicit false

namespace JoltConstraints.Soundness

private theorem slot_setWidth (bits : BitVec 5) :
    JoltISA.joltRegisterSlot (bits.setWidth 7) = .xreg (.Regidx bits) := by
  have bound : bits.toNat < 32 := bits.isLt
  interval_cases h : bits.toNat <;>
    simp [JoltISA.joltRegisterSlot, BitVec.toNat_setWidth, h] <;>
    apply BitVec.eq_of_toNat_eq <;> simpa using h.symm

/-- Decoding any table index and encoding the source returns that index. -/
theorem source_encode_decode (address : JoltISA.VReg) :
    TraceWitness.sourceRegisterAddress (JoltRegisterEncoding.source address) =
      address.toFin := by
  unfold JoltRegisterEncoding.source
  split
  · rename_i index slot
    unfold JoltISA.joltRegisterSlot at slot
    split at slot <;> cases slot <;>
      apply Fin.ext <;> simp_all [TraceWitness.sourceRegisterAddress]
  · rfl

/-- Decoding an encoded canonical source recovers that source. -/
theorem source_decode_encode (source : JoltISA.Src)
    (canonical : JoltRegisterEncoding.sourceIsCanonical source = true) :
    JoltRegisterEncoding.source
      (BitVec.ofFin (TraceWitness.sourceRegisterAddress source)) = source := by
  cases source with
  | xreg r =>
    cases r with
    | Regidx bits =>
      exact congrArg (fun slot => match slot with
        | .xreg index => JoltISA.Src.xreg index | _ => .vreg (bits.setWidth 7))
        (slot_setWidth bits)
  | vreg r =>
    change (match JoltISA.joltRegisterSlot r with
      | .xreg index => JoltISA.Src.xreg index | _ => .vreg r) = .vreg r
    cases slot : JoltISA.joltRegisterSlot r <;>
      simp_all [JoltRegisterEncoding.sourceIsCanonical]

/-- Decoding an encoded canonical destination recovers that destination. -/
theorem destination_decode_encode (destination : JoltISA.Dst)
    (canonical : JoltRegisterEncoding.destinationIsCanonical destination = true) :
    JoltRegisterEncoding.destination
      (BitVec.ofFin (TraceWitness.destinationRegisterAddress destination)) = destination := by
  cases destination with
  | xreg r =>
    cases r with
    | Regidx bits =>
      exact congrArg (fun slot => match slot with
        | .xreg index => JoltISA.Dst.xreg index | _ => .vreg (bits.setWidth 7))
        (slot_setWidth bits)
  | vreg r =>
    change (match JoltISA.joltRegisterSlot r with
      | .xreg index => JoltISA.Dst.xreg index | _ => .vreg r) = .vreg r
    cases slot : JoltISA.joltRegisterSlot r <;>
      simp_all [JoltRegisterEncoding.destinationIsCanonical]

/-- Distinct canonical sources have distinct register-table indices. -/
theorem sourceRegisterAddress_injective
    {a b : JoltISA.Src}
    (canonicalA : JoltRegisterEncoding.sourceIsCanonical a = true)
    (canonicalB : JoltRegisterEncoding.sourceIsCanonical b = true)
    (same : TraceWitness.sourceRegisterAddress a = TraceWitness.sourceRegisterAddress b) :
    a = b := by
  rw [← source_decode_encode a canonicalA, ← source_decode_encode b canonicalB, same]

/-- Distinct canonical destinations have distinct register-table indices. -/
theorem destinationRegisterAddress_injective
    {a b : JoltISA.Dst}
    (canonicalA : JoltRegisterEncoding.destinationIsCanonical a = true)
    (canonicalB : JoltRegisterEncoding.destinationIsCanonical b = true)
    (same : TraceWitness.destinationRegisterAddress a = TraceWitness.destinationRegisterAddress b) :
    a = b := by
  rw [← destination_decode_encode a canonicalA,
    ← destination_decode_encode b canonicalB, same]

/-- Canonicality of an instruction includes its destination, if present. -/
theorem instruction_destination_canonical (instruction : JoltISA.Instr)
    (destination : JoltISA.Dst)
    (canonical : JoltRegisterEncoding.instructionIsCanonical instruction = true)
    (present : instruction.destination? = some destination) :
    JoltRegisterEncoding.destinationIsCanonical destination = true := by
  cases instruction <;>
    simp_all [JoltISA.Instr.destination?, JoltRegisterEncoding.instructionIsCanonical]

/-- The fixed destination selector encodes exactly the instruction's destination. -/
theorem bytecodeRdRegister_eq_destination (instruction : JoltISA.Instr) :
    bytecodeRdRegister instruction =
      instruction.destination?.map TraceWitness.destinationRegisterAddress := by
  cases instruction <;> rfl

/-- A real bytecode row inherits validity and operand canonicality directly
from expansion. The larger `expand_program_rows_valid` bundle's
`noEarlyNextPCChange` field depends on `sys_enable_experimental_extensions`;
the narrower facts here do not need that Sail configuration constant. -/
theorem bytecodeRow_rowOk
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    {params : WitnessParams}
    (context : ConstraintContext joltInstance privateInputs params)
    {address : Nat} {row : JoltInstructionRow}
    (present : bytecodeRow context.bytecode address = some row) :
    ExpansionRows.RowOk row := by
  cases address with
  | zero => simp [bytecodeRow] at present
  | succ index =>
    obtain ⟨inRange, rowEq⟩ := Array.getElem?_eq_some_iff.mp present
    subst row
    exact ExpansionRows.expand_program_rowOk _ _ context.expands _
      (Array.getElem_mem_toList inRange)

end JoltConstraints.Soundness
