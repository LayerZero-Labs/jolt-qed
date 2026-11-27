import JoltConstraints.theorems.Soundness.Layer5.StoreDoubleword

open LeanRV64D

/-! An shared-memory store row updates the selected table word and interpreter
memory word together, preserving their agreement through the next or final
column. The rows are SD and VirtualStoreB/H/W, classified by `StoreRow`. -/

set_option autoImplicit false

namespace JoltConstraints.Soundness

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail LeanRV64D LeanRV64D.Functions JoltISA

variable {F : Type} [Field F] {params : WitnessParams} {witness : WitnessType F params}
  {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}

/-- The shared-memory store-row step preserves register and RAM agreement at its
accessed doubleword. The address checks are consequences of the verifier domain and protected-increment claims. Agreement is required only on live registers, including the
base and source; for example, an SD through a live temporary preserves all other
live values, and a VirtualStoreH at `ea = 0x80000012` updates the word at
`0x80000010`. -/
theorem store_shared_step_agreement
    (charAbove2pow128Minus2pow64 : 2 ^ 128 - 2 ^ 64 < ringChar F)
    (context : ConstraintContext joltInstance privateInputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
    {t : Fin params.traceLength} {slot : Fin (2 ^ params.logBytecodeK)}
    (selected : bytecodeRa witness slot t = 1)
    {row : JoltInstructionRow} (rowIs : bytecodeRow context.bytecode slot.val = some row)
    {width : MemoryWidth} {base source : Src} {imm : BitVec 64}
    (storeRow : StoreRow row.instruction width base source imm)
    (regionFits : joltInstance.RamRegionFits)
    {live : Fin 128 → Prop} {pre : SailJoltState}
    (registers : RegisterAgreementOn live witness t pre)
    (baseLive : live (TraceWitness.sourceRegisterAddress base))
    (sourceLive : live (TraceWitness.sourceRegisterAddress source))
    (ram : SharedRamAgreement context.io.memory_layout (fun index => witness.RamVal index t) pre)
    (layoutIs : pre.jolt_device.memory_layout = context.io.memory_layout)
    (codeIs : pre.codeRegion = ramCodeRegion context.bytecode context.io.memory_layout)
    (answer : BitVec 64) (advice : row.instruction.RuntimeAdvice) :
    let value := sourceValue source pre
    witness.RamWriteValue t = (value.toNat : F) ∧
    ∃ post : SailJoltState,
    execWithTapeAnswer (row.instruction.withRuntimeAdvice advice) answer pre =
      .ok RETIRE_SUCCESS post ∧
    (∀ next : t.val + 1 < params.traceLength,
      RegisterAgreementOn live witness ⟨t.val + 1, next⟩ post ∧
      SharedRamAgreement context.io.memory_layout
        (fun index => witness.RamVal index ⟨t.val + 1, next⟩) post) ∧
    (∀ _last : t.val + 1 = params.traceLength,
      SharedRamAgreement context.io.memory_layout witness.RamValFinal post) := by
  dsimp only
  obtain ⟨stored, post, _, executed, chosen, one, addressIs, memory, nextTable, finalTable⟩ :=
    store_shared_step charAbove2pow128Minus2pow64 context equations selected rowIs storeRow
      regionFits registers baseLive sourceLive layoutIs codeIs ram answer advice
  refine ⟨stored, post, executed, ?_, ?_⟩
  · intro next
    obtain ⟨registersNext, tableNext⟩ := nextTable next
    refine ⟨registersNext, ?_⟩
    intro index
    change witness.RamVal index ⟨t.val + 1, next⟩ = _
    rw [tableNext index, memory index]
    split
    · rfl
    · exact ram index
  · intro last index
    rw [finalTable last index, memory index]
    split
    · rfl
    · exact ram index

end JoltConstraints.Soundness
