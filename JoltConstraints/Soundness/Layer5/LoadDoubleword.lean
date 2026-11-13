import JoltConstraints.Soundness.Layer5.RamAgreement
import JoltConstraints.Soundness.Layer5.MemoryRows

open LeanRV64D

/-! A selected load row in ordinary RAM reads the interpreter's word at its
accessed doubleword through the agreed table, writes it to its destination, and
leaves the RAM table unchanged. The rows are LD and the floor loads
VirtualLoadB/H/W, classified by `LoadRow`.
Jolt's tracer at c6703570: `tracer/src/instruction/ld.rs` (`LD::exec`),
`tracer/src/instruction/floor_access.rs` (`load`) and
`tracer/src/emulator/mmu.rs` (`Mmu::load_doubleword`). -/

set_option autoImplicit false

namespace JoltConstraints.Soundness

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail LeanRV64D LeanRV64D.Functions JoltISA

variable {F : Type} [Field F] {params : WitnessParams} {witness : WitnessType F params}
  {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
  (charAbove2pow128Minus2pow64 : 2 ^ 128 - 2 ^ 64 < ringChar F)
  (context : ConstraintContext joltInstance privateInputs params)
  (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
  {t : Fin params.traceLength} {slot : Fin (2 ^ params.logBytecodeK)}
  (selected : bytecodeRa witness slot t = 1)
  {row : JoltInstructionRow} (rowIs : bytecodeRow context.bytecode slot.val = some row)
  {width : MemoryWidth} {destination : Dst} {base : Src} {imm : BitVec 64}
  (loadRow : LoadRow row.instruction width destination base imm)

include context rowIs loadRow in
/-- A selected load row has canonical destination and base operands.
For example, a floor load's temporary destination 40 is a canonical virtual
register. -/
theorem LoadRow.canonical :
    JoltRegisterEncoding.destinationIsCanonical destination = true ∧
    JoltRegisterEncoding.sourceIsCanonical base = true := by
  have valid := (bytecodeRow_rowOk context rowIs).canonical
  rw [loadRow.metadata.canonical] at valid
  simpa only [Bool.and_eq_true] using valid

include charAbove2pow128Minus2pow64 context equations selected rowIs loadRow

/-- An ordinary-RAM load row succeeds with the value constrained by RamReadValue
at its accessed doubleword.
The checked address is a local consequence of the tracer restriction.
Only the base must be live; for example, a preceding expansion row can initialize
a temporary base, and the load makes its destination live after the write.
VirtualLoadH at `ea = 0x80000012` reads the word at `0x80000010`. -/
theorem load_ram_step (regionFits : joltInstance.RamRegionFits)
    {live : Fin 128 → Prop} {pre : SailJoltState}
    (registers : RegisterAgreementOn live witness t pre)
    (baseLive : live (TraceWitness.sourceRegisterAddress base))
    (ram : OrdinaryRamAgreement context.io.memory_layout (fun index => witness.RamVal index t) pre)
    (inRam : RAM_START_ADDRESS ≤ (width.accessed (sourceValue base pre + imm)).toNat)
    (checked : DoublewordAddressChecks pre.jolt_device
      (width.accessed (sourceValue base pre + imm)) false)
    (answer : BitVec 64) (advice : row.instruction.RuntimeAdvice) :
    let address := width.accessed (sourceValue base pre + imm)
    let value := Mmu.ram_doubleword pre.sail.mem address.toNat
    let post := afterWriteDst destination value pre
    witness.RdWriteValue t = (value.toNat : F) ∧
    execWithTapeAnswer (row.instruction.withRuntimeAdvice advice) answer pre =
      .ok RETIRE_SUCCESS post ∧
    (∀ next : t.val + 1 < params.traceLength,
      RegisterAgreementOn
        (fun register => live register ∨ register = TraceWitness.destinationRegisterAddress destination)
        witness ⟨t.val + 1, next⟩ post ∧
      OrdinaryRamAgreement context.io.memory_layout
        (fun index => witness.RamVal index ⟨t.val + 1, next⟩) post) ∧
    (∀ _last : t.val + 1 = params.traceLength,
      OrdinaryRamAgreement context.io.memory_layout witness.RamValFinal post) := by
  dsimp only
  have bound := two_pow_127_lt_char charAbove2pow128Minus2pow64
  have facts := loadRow.metadata
  have canonical := loadRow.canonical context rowIs
  have baseRead := (registers.read base canonical.2 baseLive).1
  have baseIs := registers.rs1Value bound context equations selected rowIs base canonical.2
    facts.rs1Register baseLive
  obtain ⟨encoded, aligned, -⟩ := AccessRow.address_encoded charAbove2pow128Minus2pow64 context equations
    selected rowIs loadRow.access regionFits (sourceValue base pre) baseIs
  have wordAligned := ramAddress_mask_aligned bound context equations t _ encoded
  have nonzero := ramAddress_nonzero_of_inRam bound t _ encoded inRam
  obtain ⟨chosen, one, _⟩ := ramRa_unique_of_address_ne_zero bound context equations t nonzero
  have read := OrdinaryRamAgreement.read bound context equations ram chosen one _ encoded inRam
  have loadOne : witness.OpFlags .Load t = 1 := by
    simpa only [bytecodeCircuitFlag, rowIs, JoltMetadata.circuitFlag, facts.load] using!
      opFlag_of_selected_bytecode bound context equations .Load t slot selected
  have written : witness.RdWriteValue t =
      ((Mmu.ram_doubleword pre.sail.mem
        (width.accessed (sourceValue base pre + imm)).toNat).toNat : F) := by
    have relation := equations.ramReadEqRdWriteIfLoad t
    rw [loadOne, one_mul, read] at relation
    exact (sub_eq_zero.mp relation).symm
  have legal : Mmu.effective_address_ok pre.jolt_device
      (width.accessed (sourceValue base pre + imm)).toNat false = true := by
    simpa only [DoublewordAddressChecks, inRam, ↓reduceIte] using checked
  have loaded := Mmu.load_doubleword_ram pre (width.accessed (sourceValue base pre + imm))
    wordAligned inRam legal
  obtain ⟨output, executed, registerNext⟩ :=
    registerWriteOn_step context equations selected rowIs charAbove2pow128Minus2pow64 registers
      destination facts.destinationIs _ written answer advice
      (loadRow.exec_rule pre baseRead aligned _ loaded answer advice)
  have postRam := ram.afterWriteDst destination
    (Mmu.ram_doubleword pre.sail.mem (width.accessed (sourceValue base pre + imm)).toNat)
  have ramNext := postRam.noEffect context equations rfl
    (fun index => ram_write_effect_zero_of_load bound context equations t loadOne index)
  exact ⟨output, executed, fun next => ⟨registerNext next, ramNext.1 next⟩, ramNext.2⟩

end JoltConstraints.Soundness
