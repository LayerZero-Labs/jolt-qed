import JoltConstraints.Soundness.Layer5.RamAlignment
import JoltConstraints.Soundness.Layer5.RamStore
import JoltConstraints.Soundness.Layer5.LookupWrite
import JoltConstraints.Soundness.Layer5.MemoryAccessRestriction
import JoltConstraints.Soundness.Layer3.Updates

/-! Connect a selected SD row to an actual ordinary-RAM write. Register
agreement supplies both operands; the constraints force the address, alignment,
stored value and single-word table update. The address checks are the local
facts supplied by the existing TracerAddressChecks restriction through
sd_address_checks. The ordinary-RAM case starts at RAM_START_ADDRESS; device
stores need a separate argument about their effects.
At public pin 8bbb2357:
See : jolt/tracer/src/instruction/sd.rs:19-30
See : jolt/tracer/src/emulator/mmu.rs:429-435
See : jolt/tracer/src/emulator/mmu.rs:721-740 -/

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
  {base source : Src} {imm : BitVec 64}
  (instructionIs : row.instruction = .SD base source imm)

include context rowIs instructionIs in
private theorem sd_canonical :
    JoltRegisterEncoding.sourceIsCanonical base = true ∧
    JoltRegisterEncoding.sourceIsCanonical source = true := by
  simpa only [instructionIs, JoltRegisterEncoding.instructionIsCanonical,
    Bool.and_eq_true] using (bytecodeRow_rowOk context rowIs).canonical

include charAbove2pow128 context equations selected rowIs instructionIs

private theorem sd_write_value {pre : SailJoltState}
    (agrees : RegisterAgreement witness t pre) :
    witness.RamWriteValue t = ((sourceValue source pre).toNat : F) := by
  have bound := two_pow_127_lt_char charAbove2pow128
  have sourceIs := agrees.rs2Value bound context equations selected rowIs source
    (sd_canonical context rowIs instructionIs).2 (by rw [instructionIs]; rfl)
  have store : witness.OpFlags .Store t = 1 := by
    simpa only [bytecodeCircuitFlag, rowIs, instructionIs, JoltMetadata.circuitFlag,
      JoltMetadata.opcodeFlag] using
      opFlag_of_selected_bytecode bound context equations .Store t slot selected
  have relation := equations.rs2EqRamWriteIfStore t
  rw [store, one_mul, sourceIs] at relation
  exact (sub_eq_zero.mp relation).symm

/-- In the ordinary-RAM case, SD succeeds with the constrained value and exact
byte-map update. The selected table word receives that value, all other words
stay unchanged, and register agreement is preserved. The final-cycle case
updates RamValFinal rather than assuming a following trace column exists. -/
theorem sd_ram_step (regionFits : joltInstance.RamRegionFits)
    {pre : SailJoltState} (agrees : RegisterAgreement witness t pre)
    (inRam : RAM_START_ADDRESS ≤ (sourceValue base pre + imm).toNat)
    (checked : DoublewordAddressChecks pre.jolt_device (sourceValue base pre + imm) true)
    (answer : BitVec 64) (advice : row.instruction.RuntimeAdvice) :
    let address := sourceValue base pre + imm
    let value := sourceValue source pre
    let post := { pre with sail := { pre.sail with
      mem := Mmu.write_ram_doubleword pre.sail.mem address.toNat value } }
    witness.RamWriteValue t = (value.toNat : F) ∧
    execWithTapeAnswer (row.instruction.withRuntimeAdvice advice) answer pre =
      .ok RETIRE_SUCCESS post ∧
    ∃ chosen : Fin params.ramSize,
      witness.RamRa chosen t = 1 ∧
      address.toNat = ramLowestAddress context.io.memory_layout + 8 * chosen.val ∧
      (∀ index : Fin params.ramSize,
        Mmu.ram_doubleword post.sail.mem
          (ramLowestAddress context.io.memory_layout + 8 * index.val) =
          if index = chosen then value else Mmu.ram_doubleword pre.sail.mem
            (ramLowestAddress context.io.memory_layout + 8 * index.val)) ∧
      (∀ next : t.val + 1 < params.traceLength,
        RegisterAgreement witness ⟨t.val + 1, next⟩ post ∧
        ∀ index, witness.RamVal index ⟨t.val + 1, next⟩ =
          if index = chosen then (value.toNat : F) else witness.RamVal index t) ∧
      (∀ _last : t.val + 1 = params.traceLength, ∀ index,
        witness.RamValFinal index =
          if index = chosen then (value.toNat : F) else witness.RamVal index t) := by
  dsimp only
  have bound := two_pow_127_lt_char charAbove2pow128
  have canonical := sd_canonical context rowIs instructionIs
  have baseRead := (agrees.read base canonical.1).1
  have sourceRead := (agrees.read source canonical.2).1
  have baseIs := agrees.rs1Value bound context equations selected rowIs base canonical.1
    (by rw [instructionIs]; rfl)
  have encoded := sd_address_encoded bound context equations regionFits t slot selected row rowIs
    base source (sourceValue base pre) imm instructionIs baseIs
  have aligned := ramAddress_mask_aligned bound context equations t _ encoded
  have stored := sd_write_value charAbove2pow128 context equations selected rowIs instructionIs agrees
  have legal : Mmu.effective_address_ok pre.jolt_device
      (sourceValue base pre + imm).toNat true = true := by
    simpa only [DoublewordAddressChecks, inRam, ↓reduceIte] using checked
  have write := Mmu.store_doubleword_ram pre (sourceValue base pre + imm)
    (sourceValue source pre) aligned inRam legal
  have nonzero := ramAddress_nonzero_of_inRam bound t _ encoded inRam
  obtain ⟨chosen, one, _⟩ := ramRa_unique_of_address_ne_zero bound context equations t nonzero
  have addressIs := ramAddress_eq_of_selected bound context equations t chosen one _ encoded
  refine ⟨stored, ?_, chosen, one, addressIs, ?_, ?_, ?_⟩
  · rw [withRuntimeAdvice_eq_of_noAdvice _ advice (by rw [instructionIs]; rfl), instructionIs]
    simp only [execWithTapeAnswer, execInstr, bind, EStateM.bind, baseRead, sourceRead,
      aligned, ↓reduceIte, write, pure, EStateM.pure]
  · intro index
    simpa only [Fin.val_inj] using ram_store_index pre.sail
      (sourceValue base pre + imm) (sourceValue source pre)
      (ramLowestAddress context.io.memory_layout) chosen.val index.val addressIs
  · intro next
    have after : RegisterAgreement witness t
        { pre with sail := { pre.sail with
          mem := Mmu.write_ram_doubleword pre.sail.mem
            (sourceValue base pre + imm).toNat (sourceValue source pre) } } :=
      ⟨agrees.present, agrees.values⟩
    refine ⟨after.noWrite bound context equations next slot selected rowIs
      (by rw [instructionIs]; rfl), ?_⟩
    intro index
    rw [ramVal_succ_of_selected bound context equations index t next chosen one, stored]
  · intro last index
    rw [ramValFinal_of_selected bound context equations index t last chosen one, stored]

end JoltConstraints.Soundness
