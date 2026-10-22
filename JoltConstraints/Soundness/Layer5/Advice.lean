import JoltConstraints.Soundness.Layer5.LookupWrite

/-! Internal VirtualAdvice obtains its word from the witness's selected
RangeCheck entry, independently of honest division advice.
See jolt/crates/jolt-lookup-tables/src/instructions/virt/advice.rs
(`LookupQuery::to_lookup_output`) and
jolt/tracer/src/instruction/virtual_advice.rs (`RISCVInstruction::execute`)
at 5def437f. -/

set_option autoImplicit false

namespace JoltConstraints.Soundness

open Sail PreSail LeanRV64D.Functions JoltISA

/-- A selected VirtualAdvice row writes a 64-bit word chosen by the witness.
`live` names the registers already agreeing with the prepared state; the
destination is added after the write without requiring its old value to agree.
The returned runtime advice patches the instruction to that same word, and
the write and execution conclusions also cover the last witness cycle.
For example, REM may write witness quotient 5 to temporary 40 even when the
honest quotient is 0; this theorem establishes execution, not advice honesty.
See jolt/crates/jolt-riscv/src/instructions/virt/advice.rs (VirtualAdvice flags)
and jolt/crates/jolt-lookup-tables/src/tables/range_check.rs
(`RangeCheckTable::materialize_entry`) at 5def437f. -/
theorem advice_step {F : Type} [Field F] {params : WitnessParams}
    {witness : WitnessType F params} {live : Fin 128 → Prop}
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (charAbove2pow128 : 2 ^ 128 < ringChar F)
    (context : ConstraintContext joltInstance privateInputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
    {t : Fin params.traceLength} {slot : Fin (2 ^ params.logBytecodeK)}
    (selected : bytecodeRa witness slot t = 1)
    {row : JoltInstructionRow} (rowIs : bytecodeRow context.bytecode slot.val = some row)
    {destination : Dst} {placeholder imm : BitVec 64}
    (instructionIs : row.instruction = .VirtualAdvice destination placeholder imm)
    {pre : SailJoltState} (agrees : RegisterAgreementOn live witness t pre)
    (answer : BitVec 64) :
    ∃ (value : BitVec 64) (advice : row.instruction.RuntimeAdvice),
      row.instruction.withRuntimeAdvice advice = .VirtualAdvice destination value imm ∧
      witness.RdWriteValue t = (value.toNat : F) ∧
      execWithTapeAnswer (row.instruction.withRuntimeAdvice advice) answer pre =
        .ok RETIRE_SUCCESS (afterWriteDst destination value pre) ∧
      ∀ next : t.val + 1 < params.traceLength,
        RegisterAgreementOn
          (fun register => live register ∨ register = TraceWitness.destinationRegisterAddress destination)
          witness ⟨t.val + 1, next⟩ (afterWriteDst destination value pre) := by
  have bound := two_pow_127_lt_char charAbove2pow128
  obtain ⟨address, lookupSelected, _⟩ := instructionLookupRa_unique bound context equations t
  let value : BitVec 64 := ((BitVec.ofFin address &&& ((1#128 <<< 64) - 1)).setWidth 64)
  have output : witness.LookupOutput t = (value.toNat : F) := by
    simpa only [rowIs, Option.bind_some, instructionIs, JoltMetadata.lookupTable,
      lookupTableEntry, rangeCheckTableEntry] using
      lookupOutput_of_selected_bytecode bound context equations t slot selected address lookupSelected
  have writeFlag : witness.OpFlags .WriteLookupOutputToRD t = 1 := by
    simpa only [bytecodeCircuitFlag, rowIs, instructionIs, JoltMetadata.circuitFlag,
      JoltMetadata.opcodeFlag] using
      opFlag_of_selected_bytecode bound context equations .WriteLookupOutputToRD t slot selected
  have encoded := (rdWriteValue_eq_lookupOutput
    equations.rdWriteEqLookupIfWriteLookupToRd t writeFlag).trans output
  obtain ⟨advice, patched⟩ : ∃ advice : row.instruction.RuntimeAdvice,
      row.instruction.withRuntimeAdvice advice = .VirtualAdvice destination value imm := by
    rw [instructionIs]
    exact ⟨value, rfl⟩
  refine ⟨value, advice, patched, ?_⟩
  exact registerWriteOn_step context equations selected rowIs charAbove2pow128 agrees
    destination (by rw [instructionIs]; rfl) value encoded answer advice
    (by rw [patched]; rfl)

end JoltConstraints.Soundness
