import JoltConstraints.Soundness.Layer5.RamAgreement
import JoltConstraints.Soundness.Layer5.RamAlignment
import JoltConstraints.Soundness.Layer5.MemoryAddress
import JoltConstraints.Soundness.Layer5.MemoryAccessRestriction
import JoltConstraints.Soundness.Layer5.LookupWrite

/-! A selected LD row reads the interpreter's ordinary-RAM word through the
agreed table, writes it to its destination, and leaves the RAM table unchanged.
Rust casts LD's immediate through i32 before adding it; modeled LD rows use
the sign-extended 12-bit immediate from `Encoded.LD`, for which the cast agrees.
At public pin 8bbb2357:
See : jolt/tracer/src/instruction/ld.rs:17-33
See : jolt/tracer/src/emulator/mmu.rs:321-329
See : jolt/tracer/src/emulator/mmu.rs:611-628 -/

set_option autoImplicit false

namespace JoltConstraints.Soundness

open Sail PreSail LeanRV64D.Functions JoltISA

variable {F : Type} [Field F] {params : WitnessParams} {witness : WitnessType F params}
  {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
  (charAbove2pow128 : 2 ^ 128 < ringChar F)
  (context : ConstraintContext joltInstance privateInputs params)
  (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
  {t : Fin params.traceLength} {slot : Fin (2 ^ params.logBytecodeK)}
  (selected : bytecodeRa witness slot t = 1)
  {row : JoltInstructionRow} (rowIs : bytecodeRow context.bytecode slot.val = some row)
  {fault : LoadFaultClass} {destination : Dst} {base : Src} {imm : BitVec 64}
  (instructionIs : row.instruction = .LD fault destination base imm)

include charAbove2pow128 context equations selected rowIs instructionIs

/-- An ordinary-RAM LD succeeds with the value constrained by RamReadValue.
The checked address is a local consequence of the tracer restriction.
Only the base must be live; for example, a preceding expansion row can initialize
a temporary base, and LD makes its destination live after the write. -/
theorem ld_ram_step (regionFits : joltInstance.RamRegionFits)
    {live : Fin 128 → Prop} {pre : SailJoltState}
    (registers : RegisterAgreementOn live witness t pre)
    (baseLive : live (TraceWitness.sourceRegisterAddress base))
    (ram : OrdinaryRamAgreement context.io.memory_layout (fun index => witness.RamVal index t) pre)
    (inRam : RAM_START_ADDRESS ≤ (sourceValue base pre + imm).toNat)
    (checked : DoublewordAddressChecks pre.jolt_device (sourceValue base pre + imm) false)
    (answer : BitVec 64) (advice : row.instruction.RuntimeAdvice) :
    let address := sourceValue base pre + imm
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
  have bound := two_pow_127_lt_char charAbove2pow128
  have canonical : JoltRegisterEncoding.sourceIsCanonical base = true := by
    have both : JoltRegisterEncoding.destinationIsCanonical destination = true ∧
        JoltRegisterEncoding.sourceIsCanonical base = true := by
      simpa only [instructionIs, JoltRegisterEncoding.instructionIsCanonical,
        Bool.and_eq_true] using (bytecodeRow_rowOk context rowIs).canonical
    exact both.2
  have baseRead := (registers.read base canonical baseLive).1
  have baseIs := registers.rs1Value bound context equations selected rowIs base canonical
    (by rw [instructionIs]; rfl) baseLive
  have encoded := ld_address_encoded bound context equations regionFits t slot selected row rowIs
    fault destination base (sourceValue base pre) imm instructionIs baseIs
  have aligned := ramAddress_mask_aligned bound context equations t _ encoded
  have nonzero := ramAddress_nonzero_of_inRam bound t _ encoded inRam
  obtain ⟨chosen, one, _⟩ := ramRa_unique_of_address_ne_zero bound context equations t nonzero
  have read := OrdinaryRamAgreement.read bound context equations ram chosen one _ encoded inRam
  have loadFlag : witness.OpFlags .Load t = 1 := by
    simpa only [bytecodeCircuitFlag, rowIs, instructionIs, JoltMetadata.circuitFlag,
      JoltMetadata.opcodeFlag] using
      opFlag_of_selected_bytecode bound context equations .Load t slot selected
  have written : witness.RdWriteValue t =
      ((Mmu.ram_doubleword pre.sail.mem (sourceValue base pre + imm).toNat).toNat : F) := by
    have relation := equations.ramReadEqRdWriteIfLoad t
    rw [loadFlag, one_mul, read] at relation
    exact (sub_eq_zero.mp relation).symm
  have legal : Mmu.effective_address_ok pre.jolt_device
      (sourceValue base pre + imm).toNat false = true := by
    simpa only [DoublewordAddressChecks, inRam, ↓reduceIte] using checked
  have loaded := Mmu.load_doubleword_ram pre (sourceValue base pre + imm)
    aligned inRam legal
  have rule : execWithTapeAnswer (row.instruction.withRuntimeAdvice advice) answer pre =
      (do
        writeDst destination (Mmu.ram_doubleword pre.sail.mem
          (sourceValue base pre + imm).toNat)
        pure RETIRE_SUCCESS) pre := by
    rw [withRuntimeAdvice_eq_of_noAdvice _ advice (by rw [instructionIs]; rfl), instructionIs]
    simp only [execWithTapeAnswer, execInstr, bind, EStateM.bind, baseRead,
      aligned, ↓reduceIte, loaded, pure, EStateM.pure]
  obtain ⟨output, executed, registerNext⟩ :=
    registerWriteOn_step context equations selected rowIs charAbove2pow128 registers
      destination (by rw [instructionIs]; rfl)
      (Mmu.ram_doubleword pre.sail.mem (sourceValue base pre + imm).toNat)
      written answer advice rule
  have postRam := ram.afterWriteDst destination
    (Mmu.ram_doubleword pre.sail.mem (sourceValue base pre + imm).toNat)
  have ramNext := postRam.noEffect context equations rfl
    (fun index => ram_write_effect_zero_of_load bound context equations t loadFlag index)
  exact ⟨output, executed, fun next => ⟨registerNext next, ramNext.1 next⟩, ramNext.2⟩

end JoltConstraints.Soundness
