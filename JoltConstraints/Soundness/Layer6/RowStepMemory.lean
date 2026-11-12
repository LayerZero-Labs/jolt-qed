import JoltConstraints.Soundness.Layer6.MemoryRowExecution

open LeanRV64D

/-! The load and store row extensions, sharing their regional memory contract. -/
set_option autoImplicit false
namespace JoltInstance
open JoltConstraints JoltConstraints.Soundness
open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail LeanRV64D LeanRV64D.Functions JoltISA

section
variable {F : Type} [Field F] (joltField : JoltField F)
    {inst : JoltInstance SourceInstruction} {inputs : JoltPrivateInputs} {params : WitnessParams}
    (assumptions : inst.SoundnessAssumptions) (restrictions : inst.TemporaryRestrictions)
    (witness : WitnessType F params) (context : ConstraintContext inst inputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
    (run : UntrustedAnswerRun inst inputs) (first : Fin context.bytecode.size) (done : Nat)
    (state : ExpansionState witness context run first done)
    (unfinished : done < expansionRowCount context.bytecode first)
    (honestAdvice : BuiltinAdviceHonest inst.program run.rows)
    (bound : run.rows.size < params.traceLength)
    (next : Fin run.bytecode.size) (pre : SailJoltState)
    (indexIs : next.val = first.val + done) (entry : RawRowEntry run next pre)
    (registers : RegisterAgreementOn (ExpansionLive context.bytecode first done)
      witness ⟨run.rows.size, bound⟩ pre)

include joltField assumptions restrictions equations state unfinished honestAdvice indexIs entry registers

/-- A load row appends its row with live-register and cut-RAM agreement in
either address region; for example, a live temporary can address RAM or an
input word, and VirtualLoadH reads the doubleword containing its halfword.
See jolt/tracer/src/instruction/ld.rs (`LD::exec`) at 5def437f and
jolt/tracer/src/instruction/floor_access.rs (`load`) at c6703570. -/
theorem append_load_row {width : MemoryWidth} {destination : Dst} {base : Src} {imm : BitVec 64}
    (loadRow : LoadRow run.bytecode[next].instruction width destination base imm) :
    PlainRowExtension witness context run first done bound := by
  obtain ⟨atRow, slot, selected, slotIs, rowIs⟩ := state.selectedRow unfinished bound next indexIs
  have ready : run.NextStep next pre := ⟨honestAdvice, state.noEarlierStop, entry⟩
  have facts := loadRow.metadata
  have canonical := loadRow.canonical context rowIs
  have baseLive := expansion_sources_live inst.program context.bytecode context.expands first
    state.starts done unfinished _ atRow base (by rw [facts.readSources]; simp)
  have rs1 := registers.rs1Value (two_pow_127_lt_char joltField) context equations selected rowIs
    base canonical.2 facts.rs1Register baseLive
  obtain ⟨encoded, _, recorded⟩ := AccessRow.address_encoded joltField context equations selected
    rowIs loadRow.access assumptions.ramRegionFits (sourceValue base pre) rs1
  have prepared := rawEntry_prepared entry (state.registers bound)
  obtain ⟨ram, device⟩ := state.memoryAt bound entry
  let advice := runtimeAdviceFor run.bytecode[next].instruction 0
  obtain ⟨value, executes, registerNext, memory⟩ := load_row_execution joltField assumptions restrictions witness
    context equations run ⟨run.rows.size, bound⟩ next pre ready slot selected slotIs rowIs registers ram device
    (state.terminationWord bound) prepared.2.2 advice loadRow baseLive encoded
  let step : TraceRow run.bytecode := ⟨next, advice, pre, afterWriteDst destination value pre⟩
  have rs2 := rs2Value_of_selected_bytecode (two_pow_127_lt_char joltField) context equations
    ⟨run.rows.size, bound⟩ slot selected
  have rows := representsRows_push_operands joltField witness context equations run.toTrace step
    state.represents.toRepresentsRows bound slot selected slotIs
    (by simpa only [step, facts.rs1Operand] using rs1)
    (by simpa only [step, rowIs, Option.bind_some, facts.rs2Operand, facts.rs2Register] using rs2)
    (by simpa only [step, loadRow.access.ramAccessAddress, recorded] using encoded)
  apply append_memory_row joltField witness context equations run first done state unfinished bound step
    indexIs entry registers.present facts.noAdvice loadRow.access.not_tape executes rows
  · intro nextCycle
    simpa [step, facts.destinationIs, -Fin.getElem_fin] using registerNext nextCycle
  · exact memory_step_mono memory Or.inl

/-- A store row appends its row in either address region, preserving live
registers and excluding only the termination word from cut agreement.
For example, an output SD, a RAM SD and a VirtualStoreB use the same append proof.
See jolt/tracer/src/instruction/sd.rs (`SD::exec`) at 5def437f and
jolt/tracer/src/instruction/floor_access.rs (`store`) at c6703570. -/
theorem append_store_row {width : MemoryWidth} {base source : Src} {imm : BitVec 64}
    (storeRow : StoreRow run.bytecode[next].instruction width base source imm) :
    PlainRowExtension witness context run first done bound := by
  obtain ⟨atRow, slot, selected, slotIs, rowIs⟩ := state.selectedRow unfinished bound next indexIs
  have ready : run.NextStep next pre := ⟨honestAdvice, state.noEarlierStop, entry⟩
  have facts := storeRow.metadata
  have canonical := storeRow.canonical context rowIs
  have live (source : Src) (member : source ∈ ExpansionTempLiveness.readSources run.bytecode[next].instruction) :=
    expansion_sources_live inst.program context.bytecode context.expands first state.starts done unfinished _ atRow source member
  have baseLive := live base (by rw [facts.readSources]; simp)
  have sourceLive := live source (by rw [facts.readSources]; simp)
  have rs1 := registers.rs1Value (two_pow_127_lt_char joltField) context equations selected rowIs
    base canonical.1 facts.rs1Register baseLive
  have rs2 := registers.rs2Value (two_pow_127_lt_char joltField) context equations selected rowIs
    source canonical.2 facts.rs2Register sourceLive
  obtain ⟨encoded, _, recorded⟩ := AccessRow.address_encoded joltField context equations selected
    rowIs storeRow.access assumptions.ramRegionFits (sourceValue base pre) rs1
  have prepared := rawEntry_prepared entry (state.registers bound)
  obtain ⟨ram, device⟩ := state.memoryAt bound entry
  let advice := runtimeAdviceFor run.bytecode[next].instruction 0
  obtain ⟨post, executes, registerNext, memory⟩ := store_row_execution joltField assumptions restrictions witness
    context equations run ⟨run.rows.size, bound⟩ next pre ready slot selected slotIs rowIs registers ram device
    (state.terminationWord bound) prepared.2.2 advice storeRow baseLive sourceLive encoded
  let step : TraceRow run.bytecode := ⟨next, advice, pre, post⟩
  have rows := representsRows_push_operands joltField witness context equations run.toTrace step
    state.represents.toRepresentsRows bound slot selected slotIs
    (by simpa only [step, facts.rs1Operand] using rs1)
    (by simpa only [step, facts.rs2Operand] using rs2)
    (by simpa only [step, storeRow.access.ramAccessAddress, recorded] using encoded)
  apply append_memory_row joltField witness context equations run first done state unfinished bound step
    indexIs entry registers.present facts.noAdvice storeRow.access.not_tape executes rows
  · intro nextCycle
    simpa only [step, facts.noDestination, Option.not_mem_none, false_and, exists_false, or_false]
      using registerNext nextCycle
  · exact memory_step_mono memory (Or.imp_right fun touch =>
      (storeTouches_iff _ step).mpr ⟨width, base, source, imm, storeRow, touch⟩)
end
end JoltInstance
