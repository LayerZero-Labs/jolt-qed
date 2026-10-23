import JoltConstraints.Soundness.Assumptions
import JoltConstraints.Soundness.Layer5.LoadDoubleword
import JoltConstraints.Soundness.Layer5.RamStoreAgreement

set_option autoImplicit false

namespace JoltConstraints.Soundness

open Sail PreSail LeanRV64D.Functions JoltISA

/-- The disjoint device cases for a doubleword access below `RAM_START_ADDRESS`.
`unmapped` means none of the six device regions contains the starting address.
For example, address zero is unmapped and the first panic byte is in `panic`,
although Jolt's broader `is_output` predicate also includes that byte.
See jolt/common/src/jolt_device.rs (`JoltDevice::load`, `JoltDevice::store`)
at 5def437f. -/
inductive DeviceMemoryRegion where
  | trustedAdvice | untrustedAdvice | input | output | panic | termination | unmapped
  deriving DecidableEq

/-- Classify the starting byte using the device's dispatch order, giving panic
and termination precedence over buffers.
For example, `device.memory_layout.panic.toNat` selects `panic` in a generated
layout, while an unused word after `io_end` selects `unmapped`.
Alignment and the generated layout keep a permitted doubleword within one region.
See jolt/common/src/jolt_device.rs (`JoltDevice::load`) at 5def437f. -/
def deviceMemoryRegion (device : JoltDevice) (address : Nat) : DeviceMemoryRegion :=
  if device.is_panic address then .panic
  else if device.is_termination address then .termination
  else if device.is_input address then .input
  else if device.is_trusted_advice address then .trustedAdvice
  else if device.is_untrusted_advice address then .untrustedAdvice
  else if device.is_output address then .output
  else .unmapped

/-- The device portion of cut RAM agreement: each table word below ordinary RAM,
except the termination word, equals the final device image of `trace`.
`finalRamWord` overlays zero-padded advice, input and output buffers and encodes
panic as the single word zero or one.
For example, a panicked trace has panic table word 1, even though a device LD
after panic would read `0x0101010101010101`.
For initialized execution prefixes, the generated layout and bounded buffers
make this and ordinary-RAM agreement cover `RepresentsPrefix.cutRam`.
See jolt/crates/jolt-witness/src/backend/trace/ram.rs (`final_ram_state`)
and jolt/common/src/jolt_device.rs (`JoltDevice::load`) at 5def437f. -/
def DeviceRamAgreement {F : Type} [Field F] {size : Nat}
    (values : Fin size → F) (trace : Trace) : Prop :=
  ∀ index : Fin size,
    ramLowestAddress trace.initialState.jolt_device.memory_layout + 8 * index.val <
      RAM_START_ADDRESS →
    index.val ≠ (trace.initialState.jolt_device.memory_layout.termination.toNat -
      ramLowestAddress trace.initialState.jolt_device.memory_layout) / 8 →
    values index = ((TraceWitness.finalRamWord trace index.val).toNat : F)

/-- The table entry at the layout's termination index is zero.
The execution invariant requires this only before a termination store has occurred;
for example, the LD in an exit SB expansion then reads zero before its SD.
This condition does not equate the table with the synthetic final termination word.
See jolt/common/src/jolt_device.rs (`JoltDevice::load`, `JoltDevice::store`)
and jolt/crates/jolt-witness/src/backend/trace/ram.rs (`final_ram_state`)
at 5def437f. -/
def TerminationTableZero {F : Type} [Field F] {size : Nat}
    (layout : MemoryLayout) (values : Fin size → F) : Prop :=
  ∀ index : Fin size,
    index.val = (layout.termination.toNat - ramLowestAddress layout) / 8 →
      values index = 0

/-- Memory agreement after appending one executed row to a prefix.
`storedTermination` records whether the extended prefix has touched termination
with an SD; its negation requires the next termination table entry to remain zero.
Both the next-cycle and final table agree on ordinary RAM and nontermination
device words, using the appended trace's final image.
For example, an output SD changes its selected output word, while a termination
SD may change the excluded table word without changing the device.
See jolt/crates/jolt-witness/src/backend/trace/ram.rs (`final_ram_state`) and
jolt/common/src/jolt_device.rs (`JoltDevice::store`) at 5def437f. -/
def DeviceMemoryStepAgreement {F : Type} [Field F] {params : WitnessParams}
    (witness : WitnessType F params) (t : Fin params.traceLength)
    (trace : Trace) (step : TraceRow trace.bytecode) (storedTermination : Prop) : Prop :=
  let extended : Trace := { trace with rows := trace.rows.push step }
  (∀ next : t.val + 1 < params.traceLength,
    OrdinaryRamAgreement trace.initialState.jolt_device.memory_layout
      (fun index => witness.RamVal index ⟨t.val + 1, next⟩) step.postState ∧
    DeviceRamAgreement (fun index => witness.RamVal index ⟨t.val + 1, next⟩) extended ∧
    (¬ storedTermination → TerminationTableZero trace.initialState.jolt_device.memory_layout
      (fun index => witness.RamVal index ⟨t.val + 1, next⟩))) ∧
  (∀ _last : t.val + 1 = params.traceLength,
    OrdinaryRamAgreement trace.initialState.jolt_device.memory_layout
      witness.RamValFinal step.postState ∧
    DeviceRamAgreement witness.RamValFinal extended)

/-- Stage an LD step for each `region`, using a reachable ready prefix and
agreement only on the live registers, including its base operand.
The value read is the device doubleword and its field encoding is `RdWriteValue`.
Panic and termination loads are permitted only before their respective stores,
and an admissible unmapped load is at address zero; all three cases read zero.
For example, loading a one-byte input `[7]` at its aligned start reads word 7.
The appended trace keeps device and ordinary RAM agreement and the termination
invariant, and the destination becomes live in the next register column.
See jolt/tracer/src/instruction/ld.rs (`LD::exec`),
jolt/tracer/src/emulator/mmu.rs (`Mmu::load_doubleword_raw`, `Mmu::load_raw`),
and jolt/common/src/jolt_device.rs (`JoltDevice::load`) at 5def437f. -/
theorem ld_device_step
    {F : Type} [Field F] (joltField : JoltField F)
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    {params : WitnessParams} (witness : WitnessType F params)
    (context : ConstraintContext joltInstance privateInputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam
      context.io context.entry witness)
    (regionFits : joltInstance.RamRegionFits)
    (addressChecks : joltInstance.TracerAddressChecks)
    (panicStoresOne : joltInstance.PanicStoresOne)
    (terminationThenStall : joltInstance.TerminationThenStall)
    (run : UntrustedAnswerRun joltInstance privateInputs)
    (bytecodeEq : run.bytecode = context.bytecode)
    (t : Fin params.traceLength) (atCut : t.val = run.rows.size)
    (next : Fin run.bytecode.size) (pre : SailJoltState)
    (ready : run.NextStep next pre)
    (slot : Fin (2 ^ params.logBytecodeK))
    (selected : bytecodeRa witness slot t = 1) (slotIs : slot.val = next.val + 1)
    (fault : LoadFaultClass) (destination : Dst) (base : Src) (imm : BitVec 64)
    (instructionIs : run.bytecode[next].instruction = .LD fault destination base imm)
    (live : Fin 128 → Prop) (registers : RegisterAgreementOn live witness t pre)
    (baseLive : live (TraceWitness.sourceRegisterAddress base))
    (ram : OrdinaryRamAgreement run.initialState.jolt_device.memory_layout
      (fun index => witness.RamVal index t) pre)
    (device : DeviceRamAgreement (fun index => witness.RamVal index t) run.toTrace)
    (terminationWord : (¬ ∃ i : Fin run.rows.size, run.StoresTerminationAt i) →
      TerminationTableZero run.initialState.jolt_device.memory_layout
        (fun index => witness.RamVal index t))
    (belowRam : (sourceValue base pre + imm).toNat < RAM_START_ADDRESS)
    (region : DeviceMemoryRegion)
    (inRegion : deviceMemoryRegion pre.jolt_device (sourceValue base pre + imm).toNat = region)
    (answer : BitVec 64) (advice : run.bytecode[next].instruction.RuntimeAdvice) :
    ∃ value : BitVec 64,
      let post := afterWriteDst destination value pre
      let step : TraceRow run.bytecode :=
        { rowIndex := next, runtimeAdvice := advice, preState := pre, postState := post }
      read_doubleword? pre.jolt_device.load? (sourceValue base pre + imm).toNat = some value ∧
      ((region = .panic ∨ region = .termination ∨ region = .unmapped) → value = 0) ∧
      witness.RamAddress t = ((sourceValue base pre + imm).toNat : F) ∧
      witness.RdWriteValue t = (value.toNat : F) ∧
      execWithTapeAnswer (run.bytecode[next].instruction.withRuntimeAdvice advice) answer pre =
        .ok RETIRE_SUCCESS post ∧
      (∀ bound : t.val + 1 < params.traceLength,
        RegisterAgreementOn
          (fun register => live register ∨
            register = TraceWitness.destinationRegisterAddress destination)
          witness ⟨t.val + 1, bound⟩ post) ∧
      DeviceMemoryStepAgreement witness t run.toTrace step
        (∃ i : Fin run.rows.size, run.StoresTerminationAt i) := by
  sorry

/-- Stage an SD step for each device `region`.
The address restriction excludes trusted advice, untrusted advice, inputs and
unmapped addresses; the remaining cases are output, panic and termination.
An output store writes its eight little-endian bytes and zero-fills output gaps.
A panic store must write word 1 and sets the flag; a termination store leaves the
device unchanged while its table entry is excluded from device RAM agreement.
For example, storing 7 to the second output word creates an initial zero word
when the output buffer was empty.
The live registers and both memory agreements persist, and termination stays
zero whenever neither the old prefix nor this store touched it.
See jolt/tracer/src/instruction/sd.rs (`SD::exec`),
jolt/tracer/src/emulator/mmu.rs (`Mmu::store_doubleword_raw`, `Mmu::store_raw`),
and jolt/common/src/jolt_device.rs (`JoltDevice::store`) at 5def437f. -/
theorem sd_device_step
    {F : Type} [Field F] (joltField : JoltField F)
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    {params : WitnessParams} (witness : WitnessType F params)
    (context : ConstraintContext joltInstance privateInputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam
      context.io context.entry witness)
    (regionFits : joltInstance.RamRegionFits)
    (addressChecks : joltInstance.TracerAddressChecks)
    (panicStoresOne : joltInstance.PanicStoresOne)
    (run : UntrustedAnswerRun joltInstance privateInputs)
    (bytecodeEq : run.bytecode = context.bytecode)
    (t : Fin params.traceLength) (atCut : t.val = run.rows.size)
    (next : Fin run.bytecode.size) (pre : SailJoltState)
    (ready : run.NextStep next pre)
    (slot : Fin (2 ^ params.logBytecodeK))
    (selected : bytecodeRa witness slot t = 1) (slotIs : slot.val = next.val + 1)
    (base source : Src) (imm : BitVec 64)
    (instructionIs : run.bytecode[next].instruction = .SD base source imm)
    (live : Fin 128 → Prop) (registers : RegisterAgreementOn live witness t pre)
    (baseLive : live (TraceWitness.sourceRegisterAddress base))
    (sourceLive : live (TraceWitness.sourceRegisterAddress source))
    (ram : OrdinaryRamAgreement run.initialState.jolt_device.memory_layout
      (fun index => witness.RamVal index t) pre)
    (device : DeviceRamAgreement (fun index => witness.RamVal index t) run.toTrace)
    (terminationWord : (¬ ∃ i : Fin run.rows.size, run.StoresTerminationAt i) →
      TerminationTableZero run.initialState.jolt_device.memory_layout
        (fun index => witness.RamVal index t))
    (belowRam : (sourceValue base pre + imm).toNat < RAM_START_ADDRESS)
    (region : DeviceMemoryRegion)
    (inRegion : deviceMemoryRegion pre.jolt_device (sourceValue base pre + imm).toNat = region)
    (answer : BitVec 64) (advice : run.bytecode[next].instruction.RuntimeAdvice) :
    ∃ post : SailJoltState,
      let step : TraceRow run.bytecode :=
        { rowIndex := next, runtimeAdvice := advice, preState := pre, postState := post }
      (region = .output ∨ region = .panic ∨ region = .termination) ∧
      (region = .panic → sourceValue source pre = 1 ∧
        post = { pre with jolt_device := { pre.jolt_device with panic := true } }) ∧
      (region = .termination → post = pre) ∧
      witness.RamAddress t = ((sourceValue base pre + imm).toNat : F) ∧
      witness.RamWriteValue t = ((sourceValue source pre).toNat : F) ∧
      execWithTapeAnswer (run.bytecode[next].instruction.withRuntimeAdvice advice) answer pre =
        .ok RETIRE_SUCCESS post ∧
      (∀ bound : t.val + 1 < params.traceLength,
        RegisterAgreementOn live witness ⟨t.val + 1, bound⟩ post) ∧
      DeviceMemoryStepAgreement witness t run.toTrace step
        ((∃ i : Fin run.rows.size, run.StoresTerminationAt i) ∨
          TouchesTermination pre.jolt_device (sourceValue base pre + imm)) := by
  sorry

end JoltConstraints.Soundness
