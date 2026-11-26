import JoltConstraints.theorems.Soundness.Layer5.LoadDoubleword
import JoltConstraints.theorems.Soundness.Layer5.RamStoreAgreement
import JoltConstraints.theorems.Soundness.Assumptions

open LeanRV64D

/-! Load and store execution use one shared-memory agreement at every address. -/
set_option autoImplicit false
namespace JoltInstance
open JoltConstraints JoltConstraints.Soundness
open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail
  LeanRV64D.Functions JoltISA

section
variable {F : Type} [Field F] (joltField : JoltField F)
    {inst : JoltInstance SourceInstruction} {inputs : JoltPrivateInputs} {params : WitnessParams}
    (witness : WitnessType F params) (context : ConstraintContext inst inputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
    (run : UntrustedAnswerRun inst inputs) (t : Fin params.traceLength)
    (next : Fin run.bytecode.size) (pre : SailJoltState)
    (slot : Fin (2 ^ params.logBytecodeK)) (selected : bytecodeRa witness slot t = 1)
    (rowIs : bytecodeRow context.bytecode slot.val = some run.bytecode[next])
    {live : Fin 128 → Prop} (registers : RegisterAgreementOn live witness t pre)
    (ram : SharedRamAgreement context.io.memory_layout (fun index => witness.RamVal index t) pre)
    (layoutIs : pre.jolt_device.memory_layout = context.io.memory_layout)
    (advice : run.bytecode[next].instruction.RuntimeAdvice)

include joltField equations selected rowIs registers ram layoutIs

/-- A load succeeds with its constrained shared word and preserves the full memory table.
For example, an input LD and a RAM floor load have the same register/memory contract. -/
theorem load_row_execution
    {width : MemoryWidth} {destination : Dst} {base : Src} {imm : BitVec 64}
    (loadRow : LoadRow run.bytecode[next].instruction width destination base imm)
    (baseLive : live (TraceWitness.sourceRegisterAddress base)) :
    ∃ value : BitVec 64,
      let post := afterWriteDst destination value pre
      execWithTapeAnswer (run.bytecode[next].instruction.withRuntimeAdvice advice) 0 pre =
        .ok RETIRE_SUCCESS post ∧
      (∀ bound : t.val + 1 < params.traceLength,
        RegisterAgreementOn (fun register => live register ∨
          register = TraceWitness.destinationRegisterAddress destination) witness ⟨t.val + 1, bound⟩ post) ∧
      (∀ bound : t.val + 1 < params.traceLength,
        SharedRamAgreement context.io.memory_layout
          (fun index => witness.RamVal index ⟨t.val + 1, bound⟩) post) ∧
      (∀ last : t.val + 1 = params.traceLength,
        SharedRamAgreement context.io.memory_layout witness.RamValFinal post) := by
  obtain ⟨_, executes, nextRam, finalRam⟩ := load_shared_step joltField context equations selected rowIs
    loadRow inst.ramRegionFits registers baseLive ram layoutIs 0 advice
  exact ⟨_, executes, fun next => (nextRam next).1, fun next => (nextRam next).2, finalRam⟩

/-- A store succeeds with the constrained update and preserves full shared-word agreement.
For example, an output SD and a value-preserving protected SD use the same contract. -/
theorem store_row_execution
    (codeIs : pre.codeRegion = ramCodeRegion context.bytecode context.io.memory_layout)
    {width : MemoryWidth} {base source : Src} {imm : BitVec 64}
    (storeRow : StoreRow run.bytecode[next].instruction width base source imm)
    (baseLive : live (TraceWitness.sourceRegisterAddress base))
    (sourceLive : live (TraceWitness.sourceRegisterAddress source)) :
    ∃ post : SailJoltState,
      execWithTapeAnswer (run.bytecode[next].instruction.withRuntimeAdvice advice) 0 pre =
        .ok RETIRE_SUCCESS post ∧
      (∀ bound : t.val + 1 < params.traceLength,
        RegisterAgreementOn live witness ⟨t.val + 1, bound⟩ post) ∧
      (∀ bound : t.val + 1 < params.traceLength,
        SharedRamAgreement context.io.memory_layout
          (fun index => witness.RamVal index ⟨t.val + 1, bound⟩) post) ∧
      (∀ last : t.val + 1 = params.traceLength,
        SharedRamAgreement context.io.memory_layout witness.RamValFinal post) := by
  obtain ⟨_, executes, nextRam, finalRam⟩ := store_shared_step_agreement joltField context equations
    selected rowIs storeRow inst.ramRegionFits registers baseLive sourceLive ram layoutIs codeIs 0 advice
  exact ⟨_, executes, fun next => (nextRam next).1, fun next => (nextRam next).2, finalRam⟩
end
end JoltInstance
