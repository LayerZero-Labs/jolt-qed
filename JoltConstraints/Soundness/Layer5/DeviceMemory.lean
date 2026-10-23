import JoltConstraints.Soundness.Assumptions
import JoltConstraints.Soundness.Layer5.LoadDoubleword
import JoltConstraints.Soundness.Layer5.RamStoreAgreement
import JoltConstraints.Soundness.Layer5.HostCallRegisterFrame

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

/-- The semantic effect needed from a device SD, independently of a witness.
The MMU succeeds, Sail and virtual registers stay fixed, and each nontermination
device image word is updated exactly when its byte address is `address`.
For example, an output store changes one image word even when it grows the buffer.
See jolt/tracer/src/emulator/mmu.rs (`Mmu::store_doubleword_raw`) and
jolt/crates/jolt-witness/src/backend/trace/ram.rs (`final_ram_state`) at 5def437f. -/
structure DeviceStoreResult (trace : Trace) (step : TraceRow trace.bytecode)
    (address value : BitVec 64) : Prop where
  stored : Mmu.store_doubleword address value step.preState =
    .ok (.Ok true) step.postState
  sail : step.postState.sail = step.preState.sail
  vregs : step.postState.vregs = step.preState.vregs
  image : ∀ index : Nat,
    ramLowestAddress trace.initialState.jolt_device.memory_layout + 8 * index <
      RAM_START_ADDRESS →
    index ≠ (trace.initialState.jolt_device.memory_layout.termination.toNat -
      ramLowestAddress trace.initialState.jolt_device.memory_layout) / 8 →
    TraceWitness.finalRamWord { trace with rows := trace.rows.push step } index =
      if ramLowestAddress trace.initialState.jolt_device.memory_layout + 8 * index =
          address.toNat then value else TraceWitness.finalRamWord trace index

/-- Classify a checked store in a reachable device and locate its flag words.
For example, neither an input address nor address zero can pass these checks.
The termination-index implication relates the initial image grid to the ready device.
See jolt/tracer/src/emulator/mmu.rs (`Mmu::assert_effective_address`) and
jolt/common/src/jolt_device.rs (`MemoryLayout::try_new`) at 5def437f. -/
theorem device_store_cases
    {inst : JoltInstance SourceInstruction} {inputs : JoltPrivateInputs}
    (run : UntrustedAnswerRun inst inputs) (next : Fin run.bytecode.size)
    (pre : SailJoltState) (ready : run.NextStep next pre) (address : BitVec 64)
    (below : address.toNat < RAM_START_ADDRESS)
    (checked : DoublewordAddressChecks pre.jolt_device address true)
    (region : DeviceMemoryRegion) (inRegion : deviceMemoryRegion pre.jolt_device address.toNat = region) :
    (region = .output ∨ region = .panic ∨ region = .termination) ∧
    address.toNat ≠ 0 ∧
    (region = .panic → TouchesPanic pre.jolt_device address) ∧
    (∀ index : Nat,
      address.toNat = ramLowestAddress run.initialState.jolt_device.memory_layout + 8 * index →
      index = (run.initialState.jolt_device.memory_layout.termination.toNat -
        ramLowestAddress run.initialState.jolt_device.memory_layout) / 8 →
      TouchesTermination pre.jolt_device address) := by
  sorry

/-- An aligned output SD has the single-word image effect, including zero-filled
growth of the output buffer; for example, storing to the second word of an empty
buffer fills its first word with zeros.
The ready run supplies buffer bounds and the initial-to-current device frame.
See jolt/common/src/jolt_device.rs (`JoltDevice::store`) and
jolt/tracer/src/emulator/mmu.rs (`Mmu::store_doubleword_raw`) at 5def437f. -/
theorem device_output_store_image
    {inst : JoltInstance SourceInstruction} {inputs : JoltPrivateInputs}
    (run : UntrustedAnswerRun inst inputs) (next : Fin run.bytecode.size)
    (pre : SailJoltState) (ready : run.NextStep next pre) (address value : BitVec 64)
    (aligned : address &&& 7 = 0) (below : address.toNat < RAM_START_ADDRESS)
    (checked : DoublewordAddressChecks pre.jolt_device address true)
    (inRegion : deviceMemoryRegion pre.jolt_device address.toNat = .output)
    (advice : run.bytecode[next].instruction.RuntimeAdvice) :
    ∃ post, DeviceStoreResult run.toTrace
      ⟨next, advice, pre, post⟩ address value := by
  sorry

/-- Storing word 1 to panic sets the flag and writes normalized image word 1.
For example, a second such store keeps that image word at 1.
The image assertion excludes termination, whose synthetic value may also change.
See jolt/common/src/jolt_device.rs (`JoltDevice::store`) and
jolt/crates/jolt-witness/src/backend/trace/ram.rs (`final_ram_state`) at 5def437f. -/
theorem device_panic_store_image
    {inst : JoltInstance SourceInstruction} {inputs : JoltPrivateInputs}
    (run : UntrustedAnswerRun inst inputs) (next : Fin run.bytecode.size)
    (pre : SailJoltState) (ready : run.NextStep next pre) (address : BitVec 64)
    (aligned : address &&& 7 = 0) (below : address.toNat < RAM_START_ADDRESS)
    (checked : DoublewordAddressChecks pre.jolt_device address true)
    (inRegion : deviceMemoryRegion pre.jolt_device address.toNat = .panic)
    (advice : run.bytecode[next].instruction.RuntimeAdvice) :
    DeviceStoreResult run.toTrace
      ⟨next, advice, pre, { pre with jolt_device := { pre.jolt_device with panic := true } }⟩
      address 1 := by
  sorry

/-- A termination SD leaves the state and every compared device image word fixed.
For example, storing 9 changes only the excluded termination table entry.
See jolt/common/src/jolt_device.rs (`JoltDevice::store`) at 5def437f. -/
theorem device_termination_store_image
    {inst : JoltInstance SourceInstruction} {inputs : JoltPrivateInputs}
    (run : UntrustedAnswerRun inst inputs) (next : Fin run.bytecode.size)
    (pre : SailJoltState) (ready : run.NextStep next pre) (address value : BitVec 64)
    (aligned : address &&& 7 = 0) (below : address.toNat < RAM_START_ADDRESS)
    (checked : DoublewordAddressChecks pre.jolt_device address true)
    (inRegion : deviceMemoryRegion pre.jolt_device address.toNat = .termination)
    (advice : run.bytecode[next].instruction.RuntimeAdvice) :
    DeviceStoreResult run.toTrace ⟨next, advice, pre, pre⟩ address value := by
  sorry

private theorem device_store_result
    {inst : JoltInstance SourceInstruction} {inputs : JoltPrivateInputs}
    (run : UntrustedAnswerRun inst inputs) (next : Fin run.bytecode.size)
    (pre : SailJoltState) (ready : run.NextStep next pre) (address value : BitVec 64)
    (aligned : address &&& 7 = 0) (below : address.toNat < RAM_START_ADDRESS)
    (checked : DoublewordAddressChecks pre.jolt_device address true)
    (region : DeviceMemoryRegion) (inRegion : deviceMemoryRegion pre.jolt_device address.toNat = region)
    (allowed : region = .output ∨ region = .panic ∨ region = .termination)
    (panicOne : region = .panic → value = 1)
    (advice : run.bytecode[next].instruction.RuntimeAdvice) :
    ∃ post,
      (region = .panic → value = 1 ∧
        post = { pre with jolt_device := { pre.jolt_device with panic := true } }) ∧
      (region = .termination → post = pre) ∧
      DeviceStoreResult run.toTrace ⟨next, advice, pre, post⟩ address value := by
  rcases allowed with rfl | rfl | rfl
  · obtain ⟨post, result⟩ := device_output_store_image run next pre ready address value
      aligned below checked inRegion advice
    exact ⟨post, by simp, by simp, result⟩
  · have one := panicOne rfl
    subst value
    exact ⟨_, fun _ => ⟨rfl, rfl⟩, by simp,
      device_panic_store_image run next pre ready address aligned below checked inRegion advice⟩
  · exact ⟨pre, by simp, fun _ => rfl,
      device_termination_store_image run next pre ready address value
        aligned below checked inRegion advice⟩

private theorem device_store_column
    {F : Type} [Field F] {size : Nat} (trace : Trace) (step : TraceRow trace.bytecode)
    (address value : BitVec 64) (result : DeviceStoreResult trace step address value)
    (chosen : Fin size)
    (addressIs : address.toNat = ramLowestAddress trace.initialState.jolt_device.memory_layout +
      8 * chosen.val) (below : address.toNat < RAM_START_ADDRESS)
    (old values : Fin size → F)
    (update : ∀ index, values index = if index = chosen then (value.toNat : F) else old index)
    (ram : OrdinaryRamAgreement trace.initialState.jolt_device.memory_layout old step.preState)
    (device : DeviceRamAgreement old trace) :
    OrdinaryRamAgreement trace.initialState.jolt_device.memory_layout values step.postState ∧
    DeviceRamAgreement values { trace with rows := trace.rows.push step } := by
  constructor
  · intro index inRam
    have different : index ≠ chosen := by intro same; subst index; omega
    rw [update, if_neg different]
    simpa only [result.sail] using ram index inRam
  · intro index low notTermination
    rw [update, result.image index.val low notTermination]
    have same : (ramLowestAddress trace.initialState.jolt_device.memory_layout +
        8 * index.val = address.toNat) ↔ index = chosen := by
      rw [addressIs, Fin.ext_iff]
      omega
    simp only [same]
    split
    · rfl
    · exact device index low notTermination

private theorem device_store_agreement
    {F : Type} [Field F] {params : WitnessParams} {witness : WitnessType F params}
    {inst : JoltInstance SourceInstruction} {inputs : JoltPrivateInputs}
    (bound : 2 ^ 127 < ringChar F) (context : ConstraintContext inst inputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
    (t : Fin params.traceLength) (trace : Trace) (step : TraceRow trace.bytecode)
    (address value : BitVec 64) (result : DeviceStoreResult trace step address value)
    (chosen : Fin params.ramSize) (selected : witness.RamRa chosen t = 1)
    (addressIs : address.toNat = ramLowestAddress trace.initialState.jolt_device.memory_layout +
      8 * chosen.val) (below : address.toNat < RAM_START_ADDRESS)
    (stored : witness.RamWriteValue t = (value.toNat : F))
    (ram : OrdinaryRamAgreement trace.initialState.jolt_device.memory_layout
      (fun index => witness.RamVal index t) step.preState)
    (device : DeviceRamAgreement (fun index => witness.RamVal index t) trace)
    (oldTermination : Prop)
    (terminationWord : ¬ oldTermination → TerminationTableZero
      trace.initialState.jolt_device.memory_layout (fun index => witness.RamVal index t))
    (atTermination : chosen.val = (trace.initialState.jolt_device.memory_layout.termination.toNat -
      ramLowestAddress trace.initialState.jolt_device.memory_layout) / 8 →
      TouchesTermination step.preState.jolt_device address) :
    DeviceMemoryStepAgreement witness t trace step
      (oldTermination ∨ TouchesTermination step.preState.jolt_device address) := by
  have columns := device_store_column trace step address value result chosen addressIs below
    (fun index => witness.RamVal index t)
  constructor
  · intro next
    have update := fun index => (ramVal_succ_of_selected bound context equations
      index t next chosen selected).trans (by rw [stored])
    obtain ⟨ramNext, deviceNext⟩ := columns _ update ram device
    refine ⟨ramNext, deviceNext, ?_⟩
    intro noStore index indexIs
    have different : index ≠ chosen := by
      intro same
      subst index
      exact noStore (Or.inr (atTermination indexIs))
    change witness.RamVal index ⟨t.val + 1, next⟩ = 0
    rw [update, if_neg different]
    exact terminationWord (fun old => noStore (Or.inl old)) index indexIs
  · intro last
    exact columns _ (fun index => (ramValFinal_of_selected bound context equations
      index t last chosen selected).trans (by rw [stored])) ram device

private theorem device_address_selection
    {F : Type} [Field F] {params : WitnessParams} {witness : WitnessType F params}
    {inst : JoltInstance SourceInstruction} {inputs : JoltPrivateInputs}
    (bound : 2 ^ 127 < ringChar F) (context : ConstraintContext inst inputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
    (t : Fin params.traceLength) (address : BitVec 64)
    (encoded : witness.RamAddress t = (address.toNat : F)) :
    address.toNat = 0 ∨ ∃ chosen : Fin params.ramSize,
      witness.RamRa chosen t = 1 ∧
      address.toNat = ramLowestAddress context.io.memory_layout + 8 * chosen.val := by
  rcases ramRa_zero_or_unique bound context equations t with zero | ⟨chosen, one, _⟩
  · have fieldZero := (ramRa_zero_iff_address_zero bound context equations t).mp zero
    exact Or.inl (natCast_injective_below_char (word_toNat_lt_char bound address)
      (lt_trans (by decide) bound) (encoded.symm.trans (fieldZero.trans Nat.cast_zero.symm)))
  · exact Or.inr ⟨chosen, one,
      ramAddress_eq_of_selected bound context equations t chosen one address encoded⟩

/-- Pack eight successful byte reads into the same little-endian image word.
For example, bytes `7,0,0,0,0,0,0,0` read word 7, regardless of the buffer used.
The image offset can differ from the actual byte address.
See jolt/tracer/src/emulator/mmu.rs (`Mmu::load_doubleword_raw`) and
jolt/crates/jolt-witness/src/backend/trace/ram.rs (`populate_ram_bytes`) at 5def437f. -/
theorem read_doubleword_of_image_bytes (readByte : Nat → Option (BitVec 8))
    (bytes : Nat → BitVec 8) (address start : Nat)
    (reads : ∀ offset < 8, readByte (address + offset) = some (bytes (start + offset))) :
    read_doubleword? readByte address = some (TraceWitness.ramImageWord bytes start) := by
  have first := reads 0 (by decide)
  simp only [Nat.add_zero] at first
  simp only [read_doubleword?, first, reads 1 (by decide), reads 2 (by decide),
    reads 3 (by decide), reads 4 (by decide), reads 5 (by decide),
    reads 6 (by decide), reads 7 (by decide), TraceWitness.ramImageWord]

/-- A permitted device LD reads eight image bytes through both dispatch paths.
`mapped` is the address-grid fact supplied by RAM selection, excluding low peripherals.
Buffer regions use one shared byte sequence; panic and termination use their run history,
and unmapped accesses must be at zero.
At termination the readable word is zero and no earlier termination store exists.
For example, an input buffer `[7]` supplies byte 7 followed by seven zero bytes.
Writing the resulting register keeps every final image word unchanged.
See jolt/common/src/jolt_device.rs (`JoltDevice::load`),
jolt/tracer/src/emulator/mmu.rs (`Mmu::load_raw`), and
jolt/crates/jolt-witness/src/backend/trace/ram.rs (`final_ram_state`) at 5def437f. -/
theorem device_load_image_bytes
    {inst : JoltInstance SourceInstruction} {inputs : JoltPrivateInputs}
    (run : UntrustedAnswerRun inst inputs) (next : Fin run.bytecode.size)
    (pre : SailJoltState) (ready : run.NextStep next pre)
    (panicStoresOne : inst.PanicStoresOne) (terminationThenStall : inst.TerminationThenStall)
    (fault : LoadFaultClass) (destination : Dst) (base : Src) (imm : BitVec 64)
    (instructionIs : run.bytecode[next].instruction = .LD fault destination base imm)
    (aligned : (sourceValue base pre + imm) &&& 7 = 0)
    (below : (sourceValue base pre + imm).toNat < RAM_START_ADDRESS)
    (checked : DoublewordAddressChecks pre.jolt_device (sourceValue base pre + imm) false)
    (mapped : (sourceValue base pre + imm).toNat = 0 ∨ ∃ index : Nat,
      (sourceValue base pre + imm).toNat =
        ramLowestAddress run.initialState.jolt_device.memory_layout + 8 * index)
    (region : DeviceMemoryRegion)
    (inRegion : deviceMemoryRegion pre.jolt_device (sourceValue base pre + imm).toNat = region)
    (advice : run.bytecode[next].instruction.RuntimeAdvice) :
    ∃ bytes : Nat → BitVec 8,
      (∀ offset < 8, pre.jolt_device.load? ((sourceValue base pre + imm).toNat + offset) =
        some (bytes offset)) ∧
      (∀ offset < 8, Mmu.load_raw? pre ((sourceValue base pre + imm).toNat + offset) =
        some (bytes offset)) ∧
      ((region = .panic ∨ region = .termination ∨ region = .unmapped) →
        TraceWitness.ramImageWord bytes 0 = 0) ∧
      ((sourceValue base pre + imm).toNat = 0 → TraceWitness.ramImageWord bytes 0 = 0) ∧
      (∀ index : Nat,
        (sourceValue base pre + imm).toNat =
          ramLowestAddress run.initialState.jolt_device.memory_layout + 8 * index →
        if index = (run.initialState.jolt_device.memory_layout.termination.toNat -
            ramLowestAddress run.initialState.jolt_device.memory_layout) / 8 then
          TraceWitness.ramImageWord bytes 0 = 0 ∧
            ¬ ∃ i : Fin run.rows.size, run.StoresTerminationAt i
        else TraceWitness.ramImageWord bytes 0 = TraceWitness.finalRamWord run.toTrace index) ∧
      (∀ index : Nat, TraceWitness.finalRamWord
        { run.toTrace with rows := (run.rows.push
            ⟨next, advice, pre, afterWriteDst destination (TraceWitness.ramImageWord bytes 0) pre⟩) }
        index = TraceWitness.finalRamWord run.toTrace index) := by
  sorry

private theorem device_load_read
    {F : Type} [Field F] {params : WitnessParams} {witness : WitnessType F params}
    {inst : JoltInstance SourceInstruction} {inputs : JoltPrivateInputs}
    (bound : 2 ^ 127 < ringChar F) (context : ConstraintContext inst inputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
    (t : Fin params.traceLength) (run : UntrustedAnswerRun inst inputs)
    (next : Fin run.bytecode.size) (pre : SailJoltState) (ready : run.NextStep next pre)
    (panicStoresOne : inst.PanicStoresOne) (terminationThenStall : inst.TerminationThenStall)
    (fault : LoadFaultClass) (destination : Dst) (base : Src) (imm : BitVec 64)
    (instructionIs : run.bytecode[next].instruction = .LD fault destination base imm)
    (encoded : witness.RamAddress t = ((sourceValue base pre + imm).toNat : F))
    (aligned : (sourceValue base pre + imm) &&& 7 = 0)
    (below : (sourceValue base pre + imm).toNat < RAM_START_ADDRESS)
    (checked : DoublewordAddressChecks pre.jolt_device (sourceValue base pre + imm) false)
    (device : DeviceRamAgreement (fun index => witness.RamVal index t) run.toTrace)
    (terminationWord : (¬ ∃ i : Fin run.rows.size, run.StoresTerminationAt i) →
      TerminationTableZero run.initialState.jolt_device.memory_layout
        (fun index => witness.RamVal index t))
    (region : DeviceMemoryRegion)
    (inRegion : deviceMemoryRegion pre.jolt_device (sourceValue base pre + imm).toNat = region)
    (advice : run.bytecode[next].instruction.RuntimeAdvice) :
    ∃ value : BitVec 64,
      read_doubleword? pre.jolt_device.load? (sourceValue base pre + imm).toNat = some value ∧
      read_doubleword? (Mmu.load_raw? pre) (sourceValue base pre + imm).toNat = some value ∧
      ((region = .panic ∨ region = .termination ∨ region = .unmapped) → value = 0) ∧
      witness.RamReadValue t = (value.toNat : F) ∧
      (∀ index : Nat, TraceWitness.finalRamWord
        { run.toTrace with rows := (run.rows.push
            ⟨next, advice, pre, afterWriteDst destination value pre⟩) } index =
        TraceWitness.finalRamWord run.toTrace index) := by
  have selection := device_address_selection bound context equations t _ encoded
  rw [← initial_state_memory_layout context run.initialized] at selection
  have mapped : (sourceValue base pre + imm).toNat = 0 ∨ ∃ index : Nat,
      (sourceValue base pre + imm).toNat =
        ramLowestAddress run.initialState.jolt_device.memory_layout + 8 * index :=
    selection.imp id (fun ⟨chosen, _, addressIs⟩ => ⟨chosen.val, addressIs⟩)
  obtain ⟨bytes, deviceBytes, rawBytes, specialZero, zeroWord, word, image⟩ :=
    device_load_image_bytes run next pre ready panicStoresOne terminationThenStall
      fault destination base imm instructionIs aligned below checked mapped region inRegion advice
  refine ⟨TraceWitness.ramImageWord bytes 0, ?_, ?_, specialZero, ?_, image⟩
  · exact read_doubleword_of_image_bytes _ bytes _ 0 (by simpa only [Nat.zero_add] using deviceBytes)
  · exact read_doubleword_of_image_bytes _ bytes _ 0 (by simpa only [Nat.zero_add] using rawBytes)
  · rcases selection with zero | ⟨chosen, one, addressIs⟩
    · have fieldZero : witness.RamAddress t = 0 := by simpa only [zero, Nat.cast_zero] using encoded
      rw [(ram_zero_effects bound context equations t fieldZero).1, zeroWord zero]
      simp
    · rw [ramReadValue_of_selected bound context equations t chosen one]
      have meaning := word chosen.val addressIs
      split at meaning
      · rename_i atTermination
        simpa [meaning.1] using
          terminationWord meaning.2 chosen atTermination
      · rename_i outside
        simpa only [meaning] using
          device chosen (by simpa only [← addressIs] using below) outside

private theorem device_load_agreement
    {F : Type} [Field F] {params : WitnessParams} {witness : WitnessType F params}
    {inst : JoltInstance SourceInstruction} {inputs : JoltPrivateInputs}
    (context : ConstraintContext inst inputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
    (t : Fin params.traceLength) (trace : Trace) (step : TraceRow trace.bytecode)
    (layout : trace.initialState.jolt_device.memory_layout = context.io.memory_layout)
    (ram : OrdinaryRamAgreement trace.initialState.jolt_device.memory_layout
      (fun index => witness.RamVal index t) step.preState)
    (device : DeviceRamAgreement (fun index => witness.RamVal index t) trace)
    (storedTermination : Prop)
    (terminationWord : ¬ storedTermination → TerminationTableZero
      trace.initialState.jolt_device.memory_layout (fun index => witness.RamVal index t))
    (sameMemory : step.postState.sail.mem = step.preState.sail.mem)
    (sameImage : ∀ index : Nat,
      TraceWitness.finalRamWord { trace with rows := trace.rows.push step } index =
        TraceWitness.finalRamWord trace index)
    (zero : ∀ index, witness.RamRa index t * witness.RamInc t = 0) :
    DeviceMemoryStepAgreement witness t trace step storedTermination := by
  have ramInContext : OrdinaryRamAgreement context.io.memory_layout
      (fun index => witness.RamVal index t) step.preState := layout ▸ ram
  obtain ⟨ramNext, ramFinal⟩ := ramInContext.noEffect context equations sameMemory zero
  rw [← layout] at ramNext ramFinal
  have deviceSame : DeviceRamAgreement (fun index => witness.RamVal index t)
      { trace with rows := trace.rows.push step } := by
    intro index below outside
    rw [sameImage]
    exact device index below outside
  constructor
  · intro next
    have same : (fun index => witness.RamVal index ⟨t.val + 1, next⟩) =
        (fun index => witness.RamVal index t) := by
      funext index
      rw [ramVal_succ equations.ramValEqInitialPlusPrefixRamInc index t next, zero, add_zero]
    exact ⟨ramNext next, same.symm ▸ deviceSame, fun noStore => same.symm ▸ terminationWord noStore⟩
  · intro last
    have same : witness.RamValFinal = (fun index => witness.RamVal index t) := by
      funext index
      rw [ramValFinal_eq_last_update equations.ramValEqInitialPlusPrefixRamInc
        equations.ramValFinalEqInitialPlusRamInc index t last, zero, add_zero]
    exact ⟨ramFinal last, same.symm ▸ deviceSame⟩

/-- An LD step for each `region`, using a reachable ready prefix and
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
  have bound := two_pow_127_lt_char joltField
  have rowIs : bytecodeRow context.bytecode slot.val = some run.bytecode[next] := by
    rw [← bytecodeEq, slotIs]
    simp [bytecodeRow]
  have canonical : JoltRegisterEncoding.sourceIsCanonical base = true := by
    have both : JoltRegisterEncoding.destinationIsCanonical destination = true ∧
        JoltRegisterEncoding.sourceIsCanonical base = true := by
      simpa only [instructionIs, JoltRegisterEncoding.instructionIsCanonical, Bool.and_eq_true]
        using (bytecodeRow_rowOk context rowIs).canonical
    exact both.2
  have baseIs := registers.rs1Value bound context equations selected rowIs base canonical
    (by rw [instructionIs]; rfl) baseLive
  have encoded := ld_address_encoded bound context equations regionFits t slot selected
    _ rowIs fault destination base (sourceValue base pre) imm instructionIs baseIs
  have aligned := ramAddress_mask_aligned bound context equations t _ encoded
  have checked := ld_address_checks addressChecks run next pre ready
    fault destination base imm instructionIs
  obtain ⟨value, deviceRead, rawRead, specialZero, readValue, sameImage⟩ :=
    device_load_read bound context equations t run next pre ready panicStoresOne
      terminationThenStall fault destination base imm instructionIs encoded aligned belowRam
      checked device terminationWord region inRegion advice
  have loadFlag : witness.OpFlags .Load t = 1 := by
    simpa only [bytecodeCircuitFlag, rowIs, instructionIs, JoltMetadata.circuitFlag,
      JoltMetadata.opcodeFlag] using
      opFlag_of_selected_bytecode bound context equations .Load t slot selected
  have written : witness.RdWriteValue t = (value.toNat : F) := by
    have relation := equations.ramReadEqRdWriteIfLoad t
    rw [loadFlag, one_mul, readValue] at relation
    exact (sub_eq_zero.mp relation).symm
  have loaded : Mmu.load_doubleword (sourceValue base pre + imm) pre =
      .ok (.Ok value) pre := by
    simp only [Mmu.load_doubleword, Mmu.toNat_mod_eight_of_align aligned,
      ne_self_iff_false, ↓reduceIte, Nat.not_le.mpr belowRam, rawRead]
  have rule : execWithTapeAnswer (run.bytecode[next].instruction.withRuntimeAdvice advice)
      answer pre = (do writeDst destination value; pure RETIRE_SUCCESS) pre := by
    have baseRead := (registers.read base canonical baseLive).1
    rw [withRuntimeAdvice_eq_of_noAdvice _ advice (by rw [instructionIs]; rfl), instructionIs]
    simp only [execWithTapeAnswer, execInstr, bind, EStateM.bind, baseRead,
      aligned, ↓reduceIte, loaded, pure, EStateM.pure]
  obtain ⟨output, executed, registerNext⟩ := registerWriteOn_step context equations selected rowIs
    joltField registers destination (by rw [instructionIs]; rfl) value written answer advice rule
  refine ⟨value, deviceRead, specialZero, encoded, output, executed, registerNext, ?_⟩
  exact device_load_agreement context equations t run.toTrace
    ⟨next, advice, pre, afterWriteDst destination value pre⟩
    (initial_state_memory_layout context run.initialized) ram device _ terminationWord
    (by cases destination <;> rfl) sameImage
    (fun index => ram_write_effect_zero_of_load bound context equations t loadFlag index)

/-- An SD step for each device `region`.
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
  have bound := two_pow_127_lt_char joltField
  have rowIs : bytecodeRow context.bytecode slot.val = some run.bytecode[next] := by
    rw [← bytecodeEq, slotIs]
    simp [bytecodeRow]
  have canonical := sd_canonical context rowIs instructionIs
  have baseIs := registers.rs1Value bound context equations selected rowIs base canonical.1
    (by rw [instructionIs]; rfl) baseLive
  have encoded := sd_address_encoded bound context equations regionFits t slot selected
    _ rowIs base source (sourceValue base pre) imm instructionIs baseIs
  have aligned := ramAddress_mask_aligned bound context equations t _ encoded
  have sourceIs := registers.rs2Value bound context equations selected rowIs source canonical.2
    (by rw [instructionIs]; rfl) sourceLive
  have store : witness.OpFlags .Store t = 1 := by
    simpa only [bytecodeCircuitFlag, rowIs, instructionIs, JoltMetadata.circuitFlag,
      JoltMetadata.opcodeFlag] using
      opFlag_of_selected_bytecode bound context equations .Store t slot selected
  have stored : witness.RamWriteValue t = ((sourceValue source pre).toNat : F) := by
    have relation := equations.rs2EqRamWriteIfStore t
    rw [store, one_mul, sourceIs] at relation
    exact (sub_eq_zero.mp relation).symm
  have checked := sd_address_checks addressChecks run next pre ready base source imm instructionIs
  obtain ⟨allowed, nonzero, panicTouch, terminationTouch⟩ :=
    device_store_cases run next pre ready _ belowRam checked region inRegion
  have panicOne : region = .panic → sourceValue source pre = 1 := by
    intro isPanic
    have rule := panicStoresOne privateInputs run next pre ready
    rw [instructionIs] at rule
    exact rule (panicTouch isPanic)
  obtain ⟨post, panicPost, terminationPost, result⟩ := device_store_result run next pre ready
    _ (sourceValue source pre) aligned belowRam checked region inRegion allowed panicOne advice
  obtain ⟨chosen, one, addressIs⟩ :=
    (device_address_selection bound context equations t _ encoded).resolve_left nonzero
  rw [← initial_state_memory_layout context run.initialized] at addressIs
  refine ⟨post, allowed, panicPost, terminationPost, encoded, stored, ?_, ?_, ?_⟩
  · have baseRead := (registers.read base canonical.1 baseLive).1
    have sourceRead := (registers.read source canonical.2 sourceLive).1
    rw [withRuntimeAdvice_eq_of_noAdvice _ advice (by rw [instructionIs]; rfl), instructionIs]
    simp only [execWithTapeAnswer, execInstr, bind, EStateM.bind, baseRead, sourceRead,
      aligned, ↓reduceIte, result.stored, pure, EStateM.pure]
  · intro nextCycle
    have after : RegisterAgreementOn live witness t post := by
      refine ⟨result.sail ▸ registers.present, ?_⟩
      intro register member
      rw [sourceValue_of_host_frame _ pre post result.sail result.vregs]
      exact registers.values register member
    exact after.noWrite bound context equations nextCycle slot selected rowIs
      (by rw [instructionIs]; rfl)
  · exact device_store_agreement bound context equations t run.toTrace
      ⟨next, advice, pre, post⟩ _ _ result chosen one addressIs belowRam stored ram device
      _ terminationWord (terminationTouch chosen.val addressIs)

end JoltConstraints.Soundness
