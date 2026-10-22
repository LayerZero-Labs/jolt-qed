import JoltConstraints.Soundness.Layer5.RamAgreement
import JoltConstraints.Soundness.Layer5.StoreDoubleword

/-! An ordinary SD updates the selected table word and interpreter memory
word together, preserving their agreement through the next or final column. -/

set_option autoImplicit false

namespace JoltConstraints.Soundness

open Sail PreSail LeanRV64D.Functions JoltISA

variable {F : Type} [Field F] {params : WitnessParams} {witness : WitnessType F params}
  {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}

/-- The ordinary-RAM SD step preserves register and RAM agreement. The
address checks are local facts of the already approved tracer restriction. -/
theorem sd_ram_step_agreement
    (charAbove2pow128 : 2 ^ 128 < ringChar F)
    (context : ConstraintContext joltInstance privateInputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
    {t : Fin params.traceLength} {slot : Fin (2 ^ params.logBytecodeK)}
    (selected : bytecodeRa witness slot t = 1)
    {row : JoltInstructionRow} (rowIs : bytecodeRow context.bytecode slot.val = some row)
    {base source : Src} {imm : BitVec 64}
    (instructionIs : row.instruction = .SD base source imm)
    (regionFits : joltInstance.RamRegionFits)
    {pre : SailJoltState} (registers : RegisterAgreement witness t pre)
    (ram : OrdinaryRamAgreement context.io.memory_layout (fun index => witness.RamVal index t) pre)
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
    (∀ next : t.val + 1 < params.traceLength,
      RegisterAgreement witness ⟨t.val + 1, next⟩ post ∧
      OrdinaryRamAgreement context.io.memory_layout
        (fun index => witness.RamVal index ⟨t.val + 1, next⟩) post) ∧
    (∀ _last : t.val + 1 = params.traceLength,
      OrdinaryRamAgreement context.io.memory_layout witness.RamValFinal post) := by
  dsimp only
  obtain ⟨stored, executed, chosen, one, addressIs, memory, nextTable, finalTable⟩ :=
    sd_ram_step charAbove2pow128 context equations selected rowIs instructionIs
      regionFits registers inRam checked answer advice
  refine ⟨stored, executed, ?_, ?_⟩
  · intro next
    obtain ⟨registersNext, tableNext⟩ := nextTable next
    refine ⟨registersNext, ?_⟩
    intro index inOrdinary
    change witness.RamVal index ⟨t.val + 1, next⟩ = _
    rw [tableNext index, memory index]
    split
    · rfl
    · exact ram index inOrdinary
  · intro last index inOrdinary
    rw [finalTable last index, memory index]
    split
    · rfl
    · exact ram index inOrdinary

end JoltConstraints.Soundness
