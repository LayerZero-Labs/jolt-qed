import JoltConstraints.Soundness.Assumptions
import JoltConstraints.Soundness.Layer5.LoadDoubleword
import JoltConstraints.Soundness.Layer5.RamStoreAgreement
import JoltConstraints.Soundness.Layer5.HostCallRegisterFrame
import JoltConstraints.Soundness.Layer5.TapeDeviceFrame
import JoltConstraints.Completeness.Helpers.RamOutputProofHelpers

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

private theorem ready_observation {α : Type} (observe : SailJoltState → α)
    (advance : ∀ state address compressed,
      observe (advance_pc address compressed state) = observe state)
    {inst : JoltInstance SourceInstruction} {inputs : JoltPrivateInputs}
    (run : UntrustedAnswerRun inst inputs) (next : Fin run.bytecode.size)
    (pre : SailJoltState) (ready : run.NextStep next pre) :
    observe pre = observe (TraceWitness.finalTraceState run.toTrace) := by
  have entry := ready.ready
  unfold TraceWitness.finalTraceState
  split
  · rename_i nonempty
    rw [Array.back?_eq_getElem?, Array.getElem?_eq_getElem (by exact Nat.sub_lt nonempty (by decide))]
      at entry
    dsimp only at entry
    split at entry
    · exact congrArg observe entry.2
    · obtain ⟨address, _, _, _, _, prepared⟩ := entry
      rw [prepared, advance]
  · rename_i empty
    have rows : run.rows = #[] := Array.size_eq_zero_iff.mp (by omega)
    simp only [rows, Array.back?_empty] at entry
    rw [entry.2.2, advance]

private theorem store_raw_panic (pre post : SailJoltState) (address : Nat) (value : BitVec 8)
    (stored : Mmu.store_raw? pre address value = some post)
    (away : address ≠ pre.jolt_device.memory_layout.panic.toNat) :
    post.jolt_device.panic = pre.jolt_device.panic := by
  simp only [Mmu.store_raw?, JoltDevice.store?, if_neg away] at stored
  split_ifs at stored <;> cases stored <;> rfl

private theorem store_doubleword_panic (pre post : SailJoltState) (address value : BitVec 64)
    (ordered : pre.jolt_device.memory_layout.panic.toNat < pre.jolt_device.memory_layout.termination.toNat)
    (away : ¬ TouchesPanic pre.jolt_device address)
    (result : Result Bool ExecutionResult)
    (stored : Mmu.store_doubleword address value pre = .ok result post) :
    post.jolt_device.panic = pre.jolt_device.panic := by
  have noByte : ∀ k < 8, address.toNat + k ≠ pre.jolt_device.memory_layout.panic.toNat := by
    intro k small equal
    apply away
    exact ⟨k, small, by simp [JoltDevice.is_panic, equal, ordered]⟩
  have foldKeeps : ∀ after,
      (List.range 8).foldl (fun current k => current.bind fun s =>
        Mmu.store_raw? s (address.toNat + k) (value.extractLsb' (8 * k) 8))
        (some pre) = some after → after.jolt_device.panic = pre.jolt_device.panic := by
    intro after runs
    have kept := InstructionFrame.storeFold_rule_of_step
      (relation := fun s t => t.jolt_device.memory_layout = s.jolt_device.memory_layout ∧
        t.jolt_device.panic = s.jolt_device.panic)
      address.toNat value pre (List.range 8) (by
        intro k member before after fixed writes
        refine ⟨(JoltIOSetupFrame.store_raw_same _ _ _ _ writes).1.trans fixed.1, ?_⟩
        exact (store_raw_panic before after _ _ writes (by rw [fixed.1]; exact noByte k (List.mem_range.mp member))).trans fixed.2)
      (some pre) (by intro s eq; cases eq; exact ⟨rfl, rfl⟩) after runs
    exact kept.2
  simp only [Mmu.store_doubleword] at stored
  split at stored
  · cases stored
  · split at stored
    · split at stored <;> cases stored
      rfl
    · split at stored
      · cases stored
        exact foldKeeps _ (by assumption)
      · cases stored

private theorem sd_store_of_run (base source : Src) (imm answer : BitVec 64)
    (pre post : SailJoltState)
    (runs : execWithTapeAnswer (.SD base source imm) answer pre = .ok RETIRE_SUCCESS post) :
    ∃ result, Mmu.store_doubleword (sourceValue base pre + imm) (sourceValue source pre) pre =
      .ok result post := by
  simp only [execWithTapeAnswer, execInstr] at runs
  cases baseRead : readSrc base pre with
  | error err state => simp [bind, EStateM.bind, baseRead] at runs
  | ok baseValue state =>
    obtain ⟨stateSame, baseIs⟩ := readSrc_value base pre state baseValue baseRead
    subst state
    simp only [bind, EStateM.bind, baseRead] at runs
    cases sourceRead : readSrc source pre with
    | error err state => simp [sourceRead] at runs
    | ok sourceWord state =>
      obtain ⟨stateSame, sourceIs⟩ := readSrc_value source pre state sourceWord sourceRead
      subst state
      simp only [sourceRead] at runs
      split at runs
      · cases writes : Mmu.store_doubleword (baseValue + imm) sourceWord pre with
        | error err state => simp [EStateM.bind, writes] at runs
        | ok result state =>
          cases result <;> simp only [EStateM.bind, writes, pure, EStateM.pure] at runs <;> cases runs <;>
            exact ⟨_, by simpa only [baseIs, sourceIs] using writes⟩
      · cases runs

private theorem row_panic_of_no_store
    {inst : JoltInstance SourceInstruction} {inputs : JoltPrivateInputs}
    (run : UntrustedAnswerRun inst inputs) (i : Fin run.rows.size)
    (ordered : run.rows[i].preState.jolt_device.memory_layout.panic.toNat <
      run.rows[i].preState.jolt_device.memory_layout.termination.toNat)
    (noStore : ¬ run.StoresPanicAt i) :
    run.rows[i].postState.jolt_device.panic = run.rows[i].preState.jolt_device.panic := by
  classical
  have executed := run.executes i
  rcases Classical.em (∃ base source imm, run.bytecode[run.rows[i].rowIndex].instruction = .SD base source imm) with store | store
  · obtain ⟨base, source, imm, isStore⟩ := store
    rw [withRuntimeAdvice_store _ base source imm isStore] at executed
    obtain ⟨result, stored⟩ := sd_store_of_run base source imm _ _ _ executed
    exact store_doubleword_panic _ _ _ _ ordered
      (by simpa only [UntrustedAnswerRun.StoresPanicAt, isStore] using noStore) result stored
  · have kept := execWithTapeAnswer_device_of_not_sd _ (run.answers i) (by
      intro base source imm patched
      unfold Instr.withRuntimeAdvice at patched
      split at patched
      · cases patched
      · exact store ⟨base, source, imm, patched⟩) _ _ _ executed
    exact congrArg JoltDevice.panic kept.symm

private theorem initial_panic_false {inst : JoltInstance SourceInstruction} {inputs : JoltPrivateInputs}
    (run : UntrustedAnswerRun inst inputs) : run.initialState.jolt_device.panic = false := by
  have initialized := run.initialized
  unfold JoltInstance.initial_state at initialized
  simp only [bind, Option.bind] at initialized
  split at initialized
  · cases initialized
  · repeat' split at initialized
    all_goals first | cases initialized | skip
    all_goals simp_all [pure, Pure.pure]
    rw [← initialized, init_state_jolt_device]

private theorem run_panic_false {inst : JoltInstance SourceInstruction} {inputs : JoltPrivateInputs}
    (run : UntrustedAnswerRun inst inputs)
    (noStore : ¬ ∃ i : Fin run.rows.size, run.StoresPanicAt i) :
    (TraceWitness.finalTraceState run.toTrace).jolt_device.panic = false := by
  let layout := run.initialState.jolt_device.memory_layout
  have ordered : layout.panic.toNat < layout.termination.toNat :=
    new_panic_lt_termination _ layout
      (initial_state_device inst inputs run.initialState run.initialized).1
  have initial := initial_panic_false run
  have step (i : Fin run.rows.size)
      (before : run.rows[i].preState.jolt_device.memory_layout = layout ∧
        run.rows[i].preState.jolt_device.panic = false) :
      run.rows[i].postState.jolt_device.memory_layout = layout ∧
        run.rows[i].postState.jolt_device.panic = false := by
    have same := execWithTapeAnswer_rule_of_device_relation JoltIOSetupFrame.Same
      JoltIOSetupFrame.Same.refl (fun _ _ _ a b => a.trans b)
      JoltIOSetupFrame.storeDeviceByte_same _ _ _ _ _ (run.executes i)
    have unchanged := row_panic_of_no_store run i (by rw [before.1]; exact ordered)
      (fun yes => noStore ⟨i, yes⟩)
    exact ⟨same.1.trans before.1, unchanged.trans before.2⟩
  have each : ∀ (i : Nat) (hi : i < run.rows.size),
      run.rows[i].postState.jolt_device.memory_layout = layout ∧
      run.rows[i].postState.jolt_device.panic = false := by
    intro i
    induction i with
    | zero =>
      intro hi
      have starts := (run.starts run.rows[0] (Array.getElem?_eq_getElem hi)).2.2
      apply step ⟨0, hi⟩
      change run.rows[0].preState.jolt_device.memory_layout = layout ∧
        run.rows[0].preState.jolt_device.panic = false
      rw [starts]
      exact ⟨rfl, initial⟩
    | succ n ih =>
      intro hi
      have previous := ih (by omega)
      have link := run.linked n run.rows[n] run.rows[n + 1]
        (Array.getElem?_eq_getElem (by omega)) (Array.getElem?_eq_getElem hi)
      have before : run.rows[n + 1].preState.jolt_device = run.rows[n].postState.jolt_device := by
        split at link
        · exact congrArg SailJoltState.jolt_device link.2
        · obtain ⟨_, _, _, _, state⟩ := link
          rw [state]
          rfl
      apply step ⟨n + 1, hi⟩
      change run.rows[n + 1].preState.jolt_device.memory_layout = layout ∧
        run.rows[n + 1].preState.jolt_device.panic = false
      rw [before]
      exact previous
  unfold TraceWitness.finalTraceState
  split
  · exact (each _ (by omega)).2
  · exact initial

private theorem power_padding_small (words bytes : Nat) (positive : bytes < RAM_START_ADDRESS)
    (multiplied : bytes = words.nextPowerOfTwo * 8) :
    0x40000000 ≤ RAM_START_ADDRESS - bytes := by
  obtain ⟨exponent, power⟩ := Nat.isPowerOfTwo_nextPowerOfTwo words
  rw [power] at multiplied
  have limit : exponent ≤ 27 := by
    by_contra large
    have grows := Nat.pow_le_pow_right (by decide : 0 < 2) (show 28 ≤ exponent by omega)
    norm_num [RAM_START_ADDRESS] at positive
    norm_num at grows
    omega
  have small := Nat.pow_le_pow_right (by decide : 0 < 2) limit
  norm_num at small
  norm_num [RAM_START_ADDRESS]
  omega

private theorem advice_start_lower {trustedSize untrustedSize ioBytes : Nat}
    {trustedStart trustedEnd untrustedStart untrustedEnd : Nat}
    (placed : MemoryLayout.adviceRegions trustedSize untrustedSize ioBytes =
      some (trustedStart, trustedEnd, untrustedStart, untrustedEnd)) :
    RAM_START_ADDRESS - ioBytes ≤ min trustedStart untrustedStart := by
  unfold MemoryLayout.adviceRegions at placed
  simp only [bind_some_iff] at placed
  obtain ⟨start, subtracted, placed⟩ := placed
  have sub := checkedSub_some subtracted
  split_ifs at placed with zero ordered
  all_goals
    simp only [bind_some_iff] at placed
    obtain ⟨firstEnd, firstAdded, lastEnd, _, same⟩ := placed
    have sum := checkedAdd_some firstAdded
    cases same
    omega

private theorem layout_above_peripherals (config : MemoryConfig) (layout : MemoryLayout)
    (built : MemoryLayout.new config = some layout) :
    0x40000000 ≤ layout.get_lowest_address.toNat := by
  unfold MemoryLayout.new at built
  repeat' (rw [bind_some_iff] at built; obtain ⟨_, _, built⟩ := built)
  cases built
  have positive := adviceRegions_starts_pos (by assumption)
  obtain ⟨topTrusted, topUntrusted, adjacent, starts, boundTrusted, boundUntrusted⟩ :=
    adviceRegions_some (by assumption)
  have multiplied := checkedMul_some (by assumption)
  have startBound := power_padding_small _ _ (by omega) multiplied
  have lowest := advice_start_lower (by assumption)
  unfold MemoryLayout.get_lowest_address
  split <;> simp only [BitVec.toNat_ofNat] <;> omega

private theorem io_grid (config : MemoryConfig) (layout : MemoryLayout)
    (built : MemoryLayout.new config = some layout) :
    ramLowestAddress layout + 8 * ((layout.output_start.toNat - ramLowestAddress layout) / 8) =
      layout.output_start.toNat ∧
    ramLowestAddress layout + 8 * ((layout.panic.toNat - ramLowestAddress layout) / 8) =
      layout.panic.toNat ∧
    ramLowestAddress layout + 8 * ((layout.termination.toNat - ramLowestAddress layout) / 8) =
      layout.termination.toNat := by
  have order := new_io_ordered config layout built
  have inputAligned := new_input_word_aligned config layout built
  have output := new_outputs_after_inputs config layout built
  have flags := new_io_geometry config layout built
  simp only [ramLowestAddress, ← MemoryLayout.get_lowest_address_toNat]
  omega

private theorem remap_at_or_above (layout : MemoryLayout) (address : BitVec 64)
    (positive : 0 < ramLowestAddress layout) (above : ramLowestAddress layout ≤ address.toNat) :
    TraceWitness.remapRamAddress layout address =
      some ((address.toNat - ramLowestAddress layout) / 8) := by
  unfold TraceWitness.remapRamAddress
  rw [if_neg (by change ¬ (address.toNat = 0 ∨ address.toNat < ramLowestAddress layout); omega)]
  rfl

private theorem output_address_range (config : MemoryConfig) (device : JoltDevice)
    (built : MemoryLayout.new config = some device.memory_layout) (address : BitVec 64)
    (aligned : address &&& 7 = 0)
    (region : deviceMemoryRegion device address.toNat = .output) :
    0x10002000 ≤ address.toNat ∧ address.toNat + 8 ≤ RAM_START_ADDRESS ∧
    device.memory_layout.output_start.toNat ≤ address.toNat ∧
    address.toNat + 8 ≤ device.memory_layout.panic.toNat ∧
    device.memory_layout.panic.toNat ≤ device.memory_layout.termination.toNat := by
  have dispatched : device.is_panic address.toNat = false ∧
      device.is_output address.toNat = true := by
    unfold deviceMemoryRegion at region
    split_ifs at region
    simp_all
  have order := new_io_ordered config device.memory_layout built
  have geometry := new_io_geometry config device.memory_layout built
  have grid := io_grid config device.memory_layout built
  have lowAligned := new_lowest_address_aligned config device.memory_layout built
  have lowBound := layout_above_peripherals config device.memory_layout built
  have addressAligned := Mmu.toNat_mod_eight_of_align aligned
  simp only [JoltDevice.is_panic, JoltDevice.is_output, Bool.and_eq_true,
    decide_eq_true_eq, Bool.and_eq_false_iff, decide_eq_false_iff_not] at dispatched
  simp only [ramLowestAddress, ← MemoryLayout.get_lowest_address_toNat] at grid
  omega

private theorem run_inputs_fit {inst : JoltInstance SourceInstruction} {inputs : JoltPrivateInputs}
    (run : UntrustedAnswerRun inst inputs) :
    run.initialState.jolt_device.inputs.size ≤
      run.initialState.jolt_device.memory_layout.max_input_size.toNat := by
  have configured : inst.inputs.size ≤ inst.memory_config.max_input_size.toNat := by
    by_contra large
    have initialized := run.initialized
    simp [JoltInstance.initial_state,
      show inst.memory_config.max_input_size.toNat < inst.inputs.size by omega] at initialized
  have built := (initial_state_device inst inputs run.initialState run.initialized).1
  have capacity := new_input_size_bound _ _ built
  rw [initial_state_inputs inst inputs run.initialState run.initialized]
  exact configured.trans capacity

private theorem input_end_eq_output (config : MemoryConfig) (layout : MemoryLayout)
    (built : MemoryLayout.new config = some layout) : layout.input_end = layout.output_start := by
  unfold MemoryLayout.new at built
  repeat' (rw [bind_some_iff] at built; obtain ⟨_, _, built⟩ := built)
  cases built
  rfl

private theorem ready_device_data {inst : JoltInstance SourceInstruction} {inputs : JoltPrivateInputs}
    (run : UntrustedAnswerRun inst inputs) (next : Fin run.bytecode.size)
    (pre : SailJoltState) (ready : run.NextStep next pre) :
    pre.jolt_device = (TraceWitness.finalTraceState run.toTrace).jolt_device ∧
    JoltIOSetupFrame.Same run.initialState.jolt_device pre.jolt_device ∧
    MemoryLayout.new { inst.memory_config with program_size := some inst.program.program_size } =
      some pre.jolt_device.memory_layout ∧
    pre.jolt_device.trusted_advice.size ≤ pre.jolt_device.memory_layout.max_trusted_advice_size.toNat ∧
    pre.jolt_device.untrusted_advice.size ≤ pre.jolt_device.memory_layout.max_untrusted_advice_size.toNat ∧
    pre.jolt_device.inputs.size ≤ pre.jolt_device.memory_layout.max_input_size.toNat ∧
    pre.jolt_device.outputs.size ≤ pre.jolt_device.memory_layout.max_output_size.toNat := by
  have current := ready_observation SailJoltState.jolt_device (fun _ _ _ => rfl) run next pre ready
  have fixed := run.final_device_same
  rw [← current] at fixed
  have initialized := initial_state_device inst inputs run.initialState run.initialized
  have built : MemoryLayout.new { inst.memory_config with program_size := some inst.program.program_size } =
      some pre.jolt_device.memory_layout := by rw [fixed.1]; exact initialized.1
  have advice := new_advice_regions _ _ built
  refine ⟨current, fixed, built, ?_, ?_, ?_, ?_⟩
  · rw [fixed.2.1, initialized.2.1]
    exact initialized.2.2.2.1.trans advice.1
  · rw [fixed.2.2.1, initialized.2.2.1]
    exact initialized.2.2.2.2.trans advice.2.2.1
  · rw [fixed.1, fixed.2.2.2]
    exact run_inputs_fit run
  · rw [fixed.1, current]
    exact run.final_outputs_fit_layout

private theorem padded_byte_store_read {α : Type} (zero value : α)
    (bytes : Array α) (offset index : Nat) :
    ((bytes ++ Array.replicate (offset + 1 - bytes.size) zero).set! offset value)[index]?.getD zero =
      if index = offset then value else bytes[index]?.getD zero := by
  have room : offset < (bytes ++ Array.replicate (offset + 1 - bytes.size) zero).size := by
    simp only [Array.size_append, Array.size_replicate]
    omega
  rw [Array.set!_eq_setIfInBounds, Array.setIfInBounds_def, dif_pos room,
    Array.getElem?_set]
  by_cases same : index = offset
  · simp [same]
  · simp only [Ne.symm same, same, ↓reduceIte]
    rw [Array.getElem?_append]
    split
    · rfl
    · rename_i outside
      rw [Array.getElem?_eq_none (xs := bytes) (by omega), Array.getElem?_replicate]
      split <;> rfl

/-- Store successive bytes beginning at `start`, extending an array with zeros.
For example, two bytes at offset 8 in an empty array leave eight leading zeros.
This is the output-buffer fold in `jolt/common/src/jolt_device.rs`
(`JoltDevice::store`) and `jolt/tracer/src/emulator/mmu.rs`
(`Mmu::store_doubleword_raw`) at 5def437f. -/
private def storeOutputBytes (bytes : Array (BitVec 8)) (start count : Nat)
    (value : Nat → BitVec 8) : Array (BitVec 8) :=
  (List.range count).foldl (fun current offset =>
    (current ++ Array.replicate (start + offset + 1 - current.size) 0).set!
      (start + offset) (value offset)) bytes

private theorem storeOutputBytes_read (bytes : Array (BitVec 8)) (start count index : Nat)
    (value : Nat → BitVec 8) :
    (storeOutputBytes bytes start count value)[index]?.getD 0 =
      if start ≤ index ∧ index < start + count then value (index - start)
      else bytes[index]?.getD 0 := by
  induction count with
  | zero => simp [storeOutputBytes]
  | succ count ih =>
    simp only [storeOutputBytes, List.range_succ, List.foldl_append,
      List.foldl_cons, List.foldl_nil] at ⊢
    rw [padded_byte_store_read]
    change (if index = start + count then value count else
      (storeOutputBytes bytes start count value)[index]?.getD 0) = _
    rw [ih]
    by_cases last : index = start + count
    · subst index
      simp
    · by_cases inside : start ≤ index ∧ index < start + count
      · simp [last, inside, show index < start + (count + 1) by omega]
      · simp [last, inside, show ¬ (start ≤ index ∧ index < start + (count + 1)) by omega]

private theorem image_word_congr (f g : Nat → BitVec 8) (start finish : Nat)
    (same : ∀ offset < 8, f (start + offset) = g (finish + offset)) :
    TraceWitness.ramImageWord f start = TraceWitness.ramImageWord g finish := by
  have first := same 0 (by decide)
  simp only [Nat.add_zero] at first
  simp only [TraceWitness.ramImageWord, same 7 (by decide), same 6 (by decide),
    same 5 (by decide), same 4 (by decide), same 3 (by decide), same 2 (by decide),
    same 1 (by decide), first]

private theorem image_word_extract (value : BitVec 64) :
    TraceWitness.ramImageWord (fun k => value.extractLsb' (8 * k) 8) 0 = value := by
  have first := ram_store_byte default 0 value 0 (by decide)
  simp only [Nat.add_zero] at first
  simpa only [Mmu.ram_doubleword, Mmu.ram_byte, TraceWitness.ramImageWord,
    ram_store_byte default 0 value 7 (by decide), ram_store_byte default 0 value 6 (by decide),
    ram_store_byte default 0 value 5 (by decide), ram_store_byte default 0 value 4 (by decide),
    ram_store_byte default 0 value 3 (by decide), ram_store_byte default 0 value 2 (by decide),
    ram_store_byte default 0 value 1 (by decide), first, Option.getD_some,
    Nat.zero_add, Nat.mul_zero] using ram_store_word default 0 value

private theorem storeOutputBytes_word (bytes : Array (BitVec 8)) (chosen index : Nat)
    (value : BitVec 64) :
    TraceWitness.ramImageWord (fun i =>
      (storeOutputBytes bytes (8 * chosen) 8 (fun k => value.extractLsb' (8 * k) 8))[i]?.getD 0)
      (8 * index) =
      if index = chosen then value
      else TraceWitness.ramImageWord (fun i => bytes[i]?.getD 0) (8 * index) := by
  by_cases same : index = chosen
  · rw [if_pos same, same]
    refine Eq.trans ?_ (image_word_extract value)
    apply image_word_congr
    intro offset within
    rw [storeOutputBytes_read, if_pos (by omega)]
    congr 1
    omega
  · rw [if_neg same]
    apply image_word_congr
    intro offset within
    rw [storeOutputBytes_read, if_neg (by omega)]

private theorem overlay_as_padded (layout : MemoryLayout) (start : BitVec 64)
    (bytes : Array (BitVec 8)) (first index : Nat) (previous : BitVec 64)
    (remapped : TraceWitness.remapRamAddress layout start = some first)
    (underZero : first ≤ index → previous = 0) :
    TraceWitness.overlayRamBytes layout start bytes index previous =
      if first ≤ index then
        TraceWitness.ramImageWord (fun i => bytes[i]?.getD 0) (8 * (index - first))
      else previous := by
  unfold TraceWitness.overlayRamBytes
  rw [remapped]
  dsimp only
  by_cases above : first ≤ index
  · rw [if_pos above]
    by_cases present : (index - first) * 8 < bytes.size
    · simp [above, present, Nat.mul_comm]
    · rw [if_neg (by omega), underZero above]
      symm
      apply ramImageWord_zero
      intro offset within
      rw [Array.getElem?_eq_none (by omega)]
      rfl
  · simp [above]

private theorem overlay_store_word (layout : MemoryLayout) (start : BitVec 64)
    (bytes : Array (BitVec 8)) (first chosen index : Nat) (value previous : BitVec 64)
    (remapped : TraceWitness.remapRamAddress layout start = some first)
    (underZero : first ≤ index → previous = 0) :
    TraceWitness.overlayRamBytes layout start
      (storeOutputBytes bytes (8 * chosen) 8 (fun k => value.extractLsb' (8 * k) 8))
      index previous = if index = first + chosen then value
      else TraceWitness.overlayRamBytes layout start bytes index previous := by
  rw [overlay_as_padded _ _ _ _ _ _ remapped underZero,
    overlay_as_padded _ _ _ _ _ _ remapped underZero]
  by_cases above : first ≤ index
  · rw [if_pos above, storeOutputBytes_word]
    simp [above, show index - first = chosen ↔ index = first + chosen by omega]
  · simp [above, show index ≠ first + chosen by omega]

private theorem device_store_raw (state : SailJoltState) (address : Nat) (value : BitVec 8)
    (device : JoltDevice) (afterPeripherals : 0x10002000 ≤ address)
    (below : address < RAM_START_ADDRESS)
    (checked : Mmu.effective_address_ok state.jolt_device address true = true)
    (stored : state.jolt_device.store? address value = some device) :
    Mmu.store_raw? state address value = some { state with jolt_device := device } := by
  have outside : ¬ (address ≤ 0x0200ffff) ∧ ¬ (address ≤ 0x0fffffff) ∧
      ¬ (address ≤ 0x100000ff) ∧ ¬ (address ≤ 0x10001fff) := by omega
  simp [Mmu.store_raw?, Nat.not_le.mpr below, outside, checked, stored]

private theorem store_doubleword_of_bytes (pre : SailJoltState) (address value : BitVec 64)
    (states : Nat → SailJoltState) (aligned : address &&& 7 = 0)
    (below : address.toNat < RAM_START_ADDRESS) (initial : states 0 = pre)
    (step : ∀ k < 8, Mmu.store_raw? (states k) (address.toNat + k)
      (value.extractLsb' (8 * k) 8) = some (states (k + 1))) :
    Mmu.store_doubleword address value pre = .ok (.Ok true) (states 8) := by
  have folded (count : Nat) (within : count ≤ 8) :
      (List.range count).foldl (fun current k => current.bind fun s =>
        Mmu.store_raw? s (address.toNat + k) (value.extractLsb' (8 * k) 8))
        (some pre) = some (states count) := by
    induction count with
    | zero => simp only [List.range_zero, List.foldl_nil, initial]
    | succ count ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
        ih (by omega), Option.bind_some, step count (by omega)]
  simp only [Mmu.store_doubleword, Mmu.toNat_mod_eight_of_align aligned, ne_eq,
    not_true_eq_false, ↓reduceIte, show ¬ RAM_START_ADDRESS ≤ address.toNat by omega,
    folded 8 (by omega)]

private theorem output_store_raw (state : SailJoltState) (address : Nat) (value : BitVec 8)
    (afterPeripherals : 0x10002000 ≤ address) (below : address < RAM_START_ADDRESS)
    (checked : Mmu.effective_address_ok state.jolt_device address true = true)
    (inOutput : state.jolt_device.memory_layout.output_start.toNat ≤ address ∧
      address < state.jolt_device.memory_layout.panic.toNat)
    (flagsOrdered : state.jolt_device.memory_layout.panic.toNat ≤
      state.jolt_device.memory_layout.termination.toNat) :
    Mmu.store_raw? state address value = some { state with jolt_device :=
      { state.jolt_device with outputs :=
        ((state.jolt_device.outputs ++ Array.replicate
          (address - state.jolt_device.memory_layout.output_start.toNat + 1 -
            state.jolt_device.outputs.size) 0).set!
          (address - state.jolt_device.memory_layout.output_start.toNat) value) } } := by
  have notPanic : address ≠ state.jolt_device.memory_layout.panic.toNat := by omega
  have beforeTermination : address < state.jolt_device.memory_layout.termination.toNat := by omega
  apply device_store_raw state address value _ afterPeripherals below checked
  simp [JoltDevice.store?, notPanic, JoltDevice.is_panic, JoltDevice.is_termination,
    JoltDevice.is_output, Nat.not_le.mpr inOutput.2, Nat.not_le.mpr beforeTermination,
    inOutput.1, beforeTermination]

private theorem output_store_doubleword (state : SailJoltState) (address value : BitVec 64)
    (aligned : address &&& 7 = 0) (afterPeripherals : 0x10002000 ≤ address.toNat)
    (below : address.toNat + 8 ≤ RAM_START_ADDRESS)
    (checked : DoublewordAddressChecks state.jolt_device address true)
    (inOutput : state.jolt_device.memory_layout.output_start.toNat ≤ address.toNat ∧
      address.toNat + 8 ≤ state.jolt_device.memory_layout.panic.toNat)
    (flagsOrdered : state.jolt_device.memory_layout.panic.toNat ≤
      state.jolt_device.memory_layout.termination.toNat) :
    Mmu.store_doubleword address value state = .ok (.Ok true)
      { state with jolt_device := { state.jolt_device with outputs :=
        (storeOutputBytes state.jolt_device.outputs
          (address.toNat - state.jolt_device.memory_layout.output_start.toNat) 8
          (fun k => value.extractLsb' (8 * k) 8)) } } := by
  have belowStart : ¬ RAM_START_ADDRESS ≤ address.toNat := by omega
  simp only [DoublewordAddressChecks, if_neg belowStart] at checked
  have raw (k : Nat) (within : k < 8) (outputs : Array (BitVec 8)) :=
    output_store_raw { state with jolt_device := { state.jolt_device with outputs := outputs } }
      (address.toNat + k) (value.extractLsb' (8 * k) 8) (by omega) (by omega)
      (checked k within) ⟨by dsimp; omega, by dsimp; omega⟩ flagsOrdered
  apply store_doubleword_of_bytes state address value
    (fun count => { state with jolt_device := { state.jolt_device with outputs :=
      (storeOutputBytes state.jolt_device.outputs
        (address.toNat - state.jolt_device.memory_layout.output_start.toNat) count
        (fun k => value.extractLsb' (8 * k) 8)) } }) aligned (by omega) rfl
  intro count within
  rw [raw count within]
  simp only [storeOutputBytes, List.range_succ, List.foldl_append,
    List.foldl_cons, List.foldl_nil]
  congr 3
  rw [show address.toNat + count - state.jolt_device.memory_layout.output_start.toNat =
    address.toNat - state.jolt_device.memory_layout.output_start.toNat + count by omega]

private theorem input_overlays_zero_at_output (config : MemoryConfig) (device : JoltDevice)
    (built : MemoryLayout.new config = some device.memory_layout)
    (trustedFit : device.memory_layout.trusted_advice_start.toNat + device.trusted_advice.size ≤
      device.memory_layout.input_start.toNat)
    (untrustedFit : device.memory_layout.untrusted_advice_start.toNat + device.untrusted_advice.size ≤
      device.memory_layout.input_start.toNat)
    (inputsFit : device.inputs.size ≤ device.memory_layout.max_input_size.toNat)
    (index : Nat) (above : (device.memory_layout.output_start.toNat -
      ramLowestAddress device.memory_layout) / 8 ≤ index) :
    TraceWitness.overlayRamBytes device.memory_layout device.memory_layout.input_start device.inputs index
      (TraceWitness.overlayRamBytes device.memory_layout device.memory_layout.untrusted_advice_start
        device.untrusted_advice index
        (TraceWitness.overlayRamBytes device.memory_layout device.memory_layout.trusted_advice_start
          device.trusted_advice index 0)) = 0 := by
  have order := new_io_ordered config device.memory_layout built
  have output := new_outputs_after_inputs config device.memory_layout built
  have grid := (io_grid config device.memory_layout built).1
  have outputAligned : (device.memory_layout.output_start.toNat -
      ramLowestAddress device.memory_layout) % 8 = 0 := by omega
  have belowOutput (start : BitVec 64) (bytes : Array (BitVec 8))
      (fits : start.toNat + bytes.size ≤ device.memory_layout.output_start.toNat)
      (previous : BitVec 64) :
      TraceWitness.overlayRamBytes device.memory_layout start bytes index previous = previous :=
    overlayRamBytes_below_input
      { device.memory_layout with input_start := device.memory_layout.output_start }
      start bytes outputAligned fits index above previous
  rw [belowOutput _ _ (by omega), belowOutput _ _ (by omega), belowOutput _ _ (by omega)]

private theorem final_state_push (trace : Trace) (step : TraceRow trace.bytecode) :
    TraceWitness.finalTraceState { trace with rows := trace.rows.push step } = step.postState := by
  simp only [TraceWitness.finalTraceState, Array.size_push, Nat.zero_lt_succ,
    ↓reduceDIte, Nat.add_sub_cancel, Array.getElem_push_eq]

private theorem final_image_of_memory_device (trace : Trace) (step : TraceRow trace.bytecode)
    (memory : step.postState.sail.mem = (TraceWitness.finalTraceState trace).sail.mem)
    (device : step.postState.jolt_device = (TraceWitness.finalTraceState trace).jolt_device)
    (index : Nat) :
    TraceWitness.finalRamWord { trace with rows := trace.rows.push step } index =
      TraceWitness.finalRamWord trace index := by
  simp only [TraceWitness.finalRamWord, final_state_push, memory, device]

private theorem output_image_update (trace : Trace) (step : TraceRow trace.bytecode)
    (config : MemoryConfig) (built : MemoryLayout.new config = some step.preState.jolt_device.memory_layout)
    (readyDevice : step.preState.jolt_device = (TraceWitness.finalTraceState trace).jolt_device)
    (sameLayout : step.preState.jolt_device.memory_layout = trace.initialState.jolt_device.memory_layout)
    (trustedFit : step.preState.jolt_device.memory_layout.trusted_advice_start.toNat +
      step.preState.jolt_device.trusted_advice.size ≤ step.preState.jolt_device.memory_layout.input_start.toNat)
    (untrustedFit : step.preState.jolt_device.memory_layout.untrusted_advice_start.toNat +
      step.preState.jolt_device.untrusted_advice.size ≤ step.preState.jolt_device.memory_layout.input_start.toNat)
    (inputsFit : step.preState.jolt_device.inputs.size ≤ step.preState.jolt_device.memory_layout.max_input_size.toNat)
    (address value : BitVec 64) (chosen : Nat)
    (addressIs : address.toNat = step.preState.jolt_device.memory_layout.output_start.toNat + 8 * chosen)
    (beforePanic : address.toNat + 8 ≤ step.preState.jolt_device.memory_layout.panic.toNat)
    (postDevice : step.postState.jolt_device = { step.preState.jolt_device with outputs :=
      (storeOutputBytes step.preState.jolt_device.outputs (8 * chosen) 8
        (fun k => value.extractLsb' (8 * k) 8)) })
    (index : Nat)
    (below : ramLowestAddress trace.initialState.jolt_device.memory_layout + 8 * index < RAM_START_ADDRESS)
    (notTermination : index ≠ (trace.initialState.jolt_device.memory_layout.termination.toNat -
      ramLowestAddress trace.initialState.jolt_device.memory_layout) / 8) :
    TraceWitness.finalRamWord { trace with rows := trace.rows.push step } index =
      if ramLowestAddress trace.initialState.jolt_device.memory_layout + 8 * index = address.toNat
      then value else TraceWitness.finalRamWord trace index := by
  generalize ioIs : step.preState.jolt_device = io at *
  have grid := io_grid config io.memory_layout built
  have order := new_io_ordered config io.memory_layout built
  have positive := new_lowest_address_pos config io.memory_layout built
  rw [MemoryLayout.get_lowest_address_toNat] at positive order
  have outputMap := remap_at_or_above io.memory_layout io.memory_layout.output_start positive (by omega)
  have panicMap := remap_at_or_above io.memory_layout io.memory_layout.panic positive (by omega)
  have termMap := remap_at_or_above io.memory_layout io.memory_layout.termination positive (by omega)
  rw [← sameLayout] at below notTermination ⊢
  have ramZero : ¬ RAM_START_ADDRESS ≤ ramLowestAddress io.memory_layout + 8 * index := by
    omega
  have termZero : (some ((io.memory_layout.termination.toNat - ramLowestAddress io.memory_layout) / 8)
      == some index) = false := by simp [Ne.symm notTermination]
  have finalPost := final_state_push trace step
  unfold TraceWitness.finalRamWord
  dsimp only
  simp only [finalPost, ← readyDevice, postDevice]
  rw [← sameLayout]
  simp only [show min io.memory_layout.trusted_advice_start.toNat io.memory_layout.untrusted_advice_start.toNat =
    ramLowestAddress io.memory_layout from rfl, if_neg ramZero, termMap, termZero, Bool.and_false,
    Bool.false_eq_true, ↓reduceIte, panicMap]
  by_cases panicIndex : index = (io.memory_layout.panic.toNat - ramLowestAddress io.memory_layout) / 8
  · have notSelected : ramLowestAddress io.memory_layout + 8 * index ≠ address.toNat := by
      dsimp only [ramLowestAddress] at *
      omega
    rw [if_neg notSelected]
    simp [panicIndex]
  · simp only [show ¬ some ((io.memory_layout.panic.toNat - ramLowestAddress io.memory_layout) / 8) =
        some index by simp [Ne.symm panicIndex], ↓reduceIte]
    have effect := overlay_store_word io.memory_layout io.memory_layout.output_start io.outputs
      _ chosen index value _ outputMap
      (input_overlays_zero_at_output config io built trustedFit untrustedFit inputsFit index)
    have selected : index = (io.memory_layout.output_start.toNat - ramLowestAddress io.memory_layout) / 8 + chosen ↔
        ramLowestAddress io.memory_layout + 8 * index = address.toNat := by
      dsimp only [ramLowestAddress] at *
      omega
    simpa only [selected] using effect

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
  let config := { inst.memory_config with program_size := some inst.program.program_size }
  obtain ⟨readyDevice, fixed, built, _, _, inputsFit, _⟩ := ready_device_data run next pre ready
  obtain ⟨above, belowWord, outputLower, beforePanic, flagsOrdered⟩ :=
    output_address_range config pre.jolt_device built address aligned inRegion
  have lowAligned := new_lowest_address_aligned config pre.jolt_device.memory_layout built
  rw [MemoryLayout.get_lowest_address_toNat] at lowAligned
  have grid := (io_grid config pre.jolt_device.memory_layout built).1
  have alignedNat := Mmu.toNat_mod_eight_of_align aligned
  let chosen := (address.toNat - pre.jolt_device.memory_layout.output_start.toNat) / 8
  have offsetIs : address.toNat - pre.jolt_device.memory_layout.output_start.toNat = 8 * chosen := by
    dsimp only [chosen, ramLowestAddress] at *
    omega
  have addressIs : address.toNat = pre.jolt_device.memory_layout.output_start.toNat + 8 * chosen := by omega
  let post := { pre with jolt_device := { pre.jolt_device with outputs :=
    (storeOutputBytes pre.jolt_device.outputs (8 * chosen) 8 (fun k => value.extractLsb' (8 * k) 8)) } }
  have stored := output_store_doubleword pre address value aligned above belowWord checked
    ⟨outputLower, beforePanic⟩ flagsOrdered
  rw [offsetIs] at stored
  refine ⟨post, stored, rfl, rfl, ?_⟩
  have adviceFits := initial_state_advice_below_input inst inputs run.initialState run.initialized
  have trustedFit : pre.jolt_device.memory_layout.trusted_advice_start.toNat + pre.jolt_device.trusted_advice.size ≤
      pre.jolt_device.memory_layout.input_start.toNat := by
    rw [fixed.1, fixed.2.1]
    exact adviceFits.2.1
  have untrustedFit : pre.jolt_device.memory_layout.untrusted_advice_start.toNat + pre.jolt_device.untrusted_advice.size ≤
      pre.jolt_device.memory_layout.input_start.toNat := by
    rw [fixed.1, fixed.2.2.1]
    exact adviceFits.2.2
  exact output_image_update run.toTrace ⟨next, advice, pre, post⟩ config built readyDevice fixed.1
    trustedFit untrustedFit inputsFit address value chosen addressIs beforePanic rfl

private theorem flag_byte_store (device : JoltDevice) (address : Nat) (value : BitVec 8)
    (flag : (device.is_panic address || device.is_termination address) = true) :
    device.store? address value = some { device with panic :=
      (device.panic || decide (address = device.memory_layout.panic.toNat)) } := by
  unfold JoltDevice.store?
  by_cases first : address = device.memory_layout.panic.toNat
  · simp [first]
  · simp [first, flag]

private theorem flag_store_doubleword (config : MemoryConfig) (state : SailJoltState)
    (built : MemoryLayout.new config = some state.jolt_device.memory_layout)
    (address value : BitVec 64) (flag : Bool)
    (atFlag : address.toNat = if flag then state.jolt_device.memory_layout.panic.toNat
      else state.jolt_device.memory_layout.termination.toNat)
    (aligned : address &&& 7 = 0)
    (checked : DoublewordAddressChecks state.jolt_device address true) :
    Mmu.store_doubleword address value state = .ok (.Ok true)
      { state with jolt_device := { state.jolt_device with panic := state.jolt_device.panic || flag } } := by
  have io := new_io_geometry config state.jolt_device.memory_layout built
  have order := new_io_ordered config state.jolt_device.memory_layout built
  have low := layout_above_peripherals config state.jolt_device.memory_layout built
  have bounds : 0x10002000 ≤ address.toNat ∧ address.toNat + 8 ≤ RAM_START_ADDRESS := by
    cases flag <;> simp only [Bool.false_eq_true, ↓reduceIte] at atFlag <;> omega
  simp only [DoublewordAddressChecks, show ¬ RAM_START_ADDRESS ≤ address.toNat by omega,
    ↓reduceIte] at checked
  have raw (k : Nat) (small : k < 8) (old : Bool) :
      Mmu.store_raw? { state with jolt_device := { state.jolt_device with panic := old } }
        (address.toNat + k) (value.extractLsb' (8 * k) 8) =
        some { state with jolt_device := { state.jolt_device with panic :=
          old || (flag && decide (k = 0)) } } := by
    have within : (state.jolt_device.is_panic (address.toNat + k) ||
        state.jolt_device.is_termination (address.toNat + k)) = true := by
      simp only [JoltDevice.is_panic, JoltDevice.is_termination, Bool.or_eq_true,
        Bool.and_eq_true, decide_eq_true_eq]
      cases flag <;> simp only [Bool.false_eq_true, ↓reduceIte] at atFlag <;> omega
    have hit : decide (address.toNat + k = state.jolt_device.memory_layout.panic.toNat) =
        (flag && decide (k = 0)) := by
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      cases flag <;> simp only [Bool.false_eq_true, ↓reduceIte, false_and, true_and] at atFlag ⊢
      · simp only [iff_false]
        omega
      · rw [atFlag]
        simp
    simpa only [hit] using device_store_raw
      { state with jolt_device := { state.jolt_device with panic := old } } _ _ _
      (by omega) (by omega) (checked k small)
      (flag_byte_store { state.jolt_device with panic := old } _ _ within)
  let states (count : Nat) := { state with jolt_device := { state.jolt_device with
    panic := state.jolt_device.panic || (flag && decide (0 < count)) } }
  have initial : states 0 = state := by simp [states]
  have step (k : Nat) (small : k < 8) : Mmu.store_raw? (states k) (address.toNat + k)
      (value.extractLsb' (8 * k) 8) = some (states (k + 1)) := by
    have nextFlag : ((state.jolt_device.panic || (flag && decide (0 < k))) ||
        (flag && decide (k = 0))) = (state.jolt_device.panic || (flag && decide (0 < k + 1))) := by
      cases flag <;> by_cases zero : k = 0 <;> simp [zero, Nat.pos_iff_ne_zero]
    dsimp only [states]
    rw [raw k small, nextFlag]
  simpa [states] using
    store_doubleword_of_bytes state address value states aligned (by omega) initial step

private theorem flag_region_address (config : MemoryConfig) (device : JoltDevice)
    (built : MemoryLayout.new config = some device.memory_layout)
    (address : BitVec 64) (aligned : address &&& 7 = 0) (flag : Bool)
    (region : deviceMemoryRegion device address.toNat = if flag then .panic else .termination) :
    address.toNat = if flag then device.memory_layout.panic.toNat else device.memory_layout.termination.toNat := by
  have io := new_io_geometry config device.memory_layout built
  have grid := io_grid config device.memory_layout built
  have lowGrid := new_lowest_address_aligned config device.memory_layout built
  rw [MemoryLayout.get_lowest_address_toNat] at lowGrid
  have alignedNat := Mmu.toNat_mod_eight_of_align aligned
  simp only [ramLowestAddress] at grid
  unfold deviceMemoryRegion at region
  cases flag <;> simp only [Bool.false_eq_true, ↓reduceIte] at region ⊢ <;>
    split_ifs at region <;> simp_all [JoltDevice.is_panic, JoltDevice.is_termination] <;> omega

private theorem panic_image_update (trace : Trace) (step : TraceRow trace.bytecode)
    (config : MemoryConfig) (built : MemoryLayout.new config = some step.preState.jolt_device.memory_layout)
    (current : step.preState.jolt_device = (TraceWitness.finalTraceState trace).jolt_device)
    (layout : step.preState.jolt_device.memory_layout = trace.initialState.jolt_device.memory_layout)
    (post : step.postState.jolt_device = { step.preState.jolt_device with panic := true })
    (address : BitVec 64) (atPanic : address.toNat = step.preState.jolt_device.memory_layout.panic.toNat)
    (index : Nat)
    (below : ramLowestAddress trace.initialState.jolt_device.memory_layout + 8 * index < RAM_START_ADDRESS)
    (notTermination : index ≠ (trace.initialState.jolt_device.memory_layout.termination.toNat -
      ramLowestAddress trace.initialState.jolt_device.memory_layout) / 8) :
    TraceWitness.finalRamWord { trace with rows := trace.rows.push step } index =
      if ramLowestAddress trace.initialState.jolt_device.memory_layout + 8 * index = address.toNat
      then 1 else TraceWitness.finalRamWord trace index := by
  generalize ioIs : step.preState.jolt_device = io at *
  have grid := io_grid config io.memory_layout built
  have order := new_io_ordered config io.memory_layout built
  have positive := new_lowest_address_pos config io.memory_layout built
  rw [MemoryLayout.get_lowest_address_toNat] at order positive
  have panicMap := remap_at_or_above io.memory_layout io.memory_layout.panic positive (by omega)
  have termMap := remap_at_or_above io.memory_layout io.memory_layout.termination positive (by omega)
  rw [← layout] at below notTermination ⊢
  have baseZero : ¬ RAM_START_ADDRESS ≤ ramLowestAddress io.memory_layout + 8 * index := by omega
  have termOff : (some ((io.memory_layout.termination.toNat - ramLowestAddress io.memory_layout) / 8) == some index) = false := by
    simp [Ne.symm notTermination]
  have selected : ramLowestAddress io.memory_layout + 8 * index = address.toNat ↔
      (io.memory_layout.panic.toNat - ramLowestAddress io.memory_layout) / 8 = index := by omega
  unfold TraceWitness.finalRamWord
  dsimp only
  simp only [final_state_push, ← current, post]
  rw [← layout]
  simp only [show min io.memory_layout.trusted_advice_start.toNat io.memory_layout.untrusted_advice_start.toNat =
    ramLowestAddress io.memory_layout from rfl, if_neg baseZero, termMap, panicMap,
    termOff, Bool.and_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    Option.some.injEq, selected]
  split_ifs <;> rfl

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
  let config := { inst.memory_config with program_size := some inst.program.program_size }
  obtain ⟨current, fixed, built, _, _, _, _⟩ := ready_device_data run next pre ready
  have atPanic : address.toNat = pre.jolt_device.memory_layout.panic.toNat :=
    flag_region_address config pre.jolt_device built address aligned true inRegion
  have stored := flag_store_doubleword config pre built address 1 true atPanic aligned checked
  refine ⟨by simpa only [Bool.or_true] using stored, rfl, rfl, ?_⟩
  exact panic_image_update run.toTrace
    ⟨next, advice, pre, { pre with jolt_device := { pre.jolt_device with panic := true } }⟩
    config built current fixed.1 rfl address atPanic


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
  let config := { inst.memory_config with program_size := some inst.program.program_size }
  obtain ⟨current, fixed, built, _, _, _, _⟩ := ready_device_data run next pre ready
  have atTermination : address.toNat = pre.jolt_device.memory_layout.termination.toNat :=
    flag_region_address config pre.jolt_device built address aligned false inRegion
  have stored := flag_store_doubleword config pre built address value false atTermination aligned checked
  refine ⟨by simpa only [Bool.or_false] using stored, rfl, rfl, ?_⟩
  intro index belowIndex notTermination
  have memory := ready_observation (fun state => state.sail.mem) (fun _ _ _ => rfl) run next pre ready
  rw [final_image_of_memory_device run.toTrace ⟨next, advice, pre, pre⟩ memory current]
  have grid := (io_grid config pre.jolt_device.memory_layout built).2.2
  rw [fixed.1] at grid atTermination
  rw [if_neg (by intro selected; apply notTermination; omega)]


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
  obtain ⟨_, fixed, built, _, _, _, _⟩ := ready_device_data run next pre ready
  have io := new_io_geometry _ _ built
  have order := new_io_ordered _ _ built
  have advice := new_advice_regions _ _ built
  have inputEnd := congrArg BitVec.toNat (input_end_eq_output _ _ built)
  have positive := new_lowest_address_pos _ _ built
  have legal := checked
  simp only [DoublewordAddressChecks, show ¬ RAM_START_ADDRESS ≤ address.toNat by omega,
    ↓reduceIte] at legal
  have first := legal 0 (by decide)
  simp only [Nat.add_zero, Mmu.effective_address_ok, below, ↓reduceIte,
    Bool.and_eq_true, Bool.or_eq_true, JoltDevice.is_output, JoltDevice.is_panic,
    JoltDevice.is_termination, decide_eq_true_eq] at first
  have allowed : region = .output ∨ region = .panic ∨ region = .termination := by
    unfold deviceMemoryRegion at inRegion
    split_ifs at inRegion <;> simp_all [JoltDevice.is_input, JoltDevice.is_trusted_advice,
      JoltDevice.is_untrusted_advice, JoltDevice.is_panic, JoltDevice.is_termination,
      JoltDevice.is_output] <;> omega
  refine ⟨allowed, ?_, ?_, ?_⟩
  · intro zero
    have lower := new_io_ordered _ _ built
    omega
  · intro panic
    refine ⟨0, by decide, ?_⟩
    simp only [Nat.add_zero]
    rw [panic] at inRegion
    unfold deviceMemoryRegion at inRegion
    split_ifs at inRegion
    assumption
  · intro index indexIs termination
    have grid := io_grid _ _ built
    have localIndex : address.toNat = ramLowestAddress pre.jolt_device.memory_layout + 8 * index := by
      rw [fixed.1]; exact indexIs
    have localTermination : index = (pre.jolt_device.memory_layout.termination.toNat -
        ramLowestAddress pre.jolt_device.memory_layout) / 8 := by rw [fixed.1]; exact termination
    refine ⟨0, by decide, ?_⟩
    simp only [Nat.add_zero, JoltDevice.is_termination, Bool.and_eq_true, decide_eq_true_eq]
    omega

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

private theorem overlay_interval (layout : MemoryLayout) (start : BitVec 64)
    (finish address index : Nat) (bytes : Array (BitVec 8)) (previous : BitVec 64)
    (positive : 0 < ramLowestAddress layout) (startLower : ramLowestAddress layout ≤ start.toNat)
    (startGrid : (start.toNat - ramLowestAddress layout) % 8 = 0)
    (addressIs : address = ramLowestAddress layout + 8 * index)
    (fits : start.toNat + bytes.size ≤ finish)
    (zero : start.toNat ≤ address ∧ address < finish → previous = 0) :
    TraceWitness.overlayRamBytes layout start bytes index previous =
      if start.toNat ≤ address ∧ address < finish then
        TraceWitness.ramImageWord (fun k => bytes[k]?.getD 0) (address - start.toNat)
      else previous := by
  have mapped := remap_at_or_above layout start positive startLower
  unfold TraceWitness.overlayRamBytes
  rw [mapped]
  dsimp only
  by_cases inside : start.toNat ≤ address ∧ address < finish
  · rw [if_pos inside]
    have lower : (start.toNat - ramLowestAddress layout) / 8 ≤ index := by omega
    have offset : (index - (start.toNat - ramLowestAddress layout) / 8) * 8 =
        address - start.toNat := by omega
    rw [offset]
    by_cases hasBytes : address - start.toNat < bytes.size
    · rw [if_pos ⟨lower, hasBytes⟩]
    · rw [if_neg (by omega), zero inside]
      symm
      apply ramImageWord_zero
      intro k small
      rw [Array.getElem?_eq_none (by omega)]
      rfl
  · rw [if_neg inside, if_neg (by omega)]

private theorem device_predicates_offset (config : MemoryConfig) (device : JoltDevice)
    (built : MemoryLayout.new config = some device.memory_layout)
    (address offset : Nat) (aligned : address % 8 = 0) (small : offset < 8) :
    device.is_panic (address + offset) = device.is_panic address ∧
    device.is_termination (address + offset) = device.is_termination address ∧
    device.is_input (address + offset) = device.is_input address ∧
    device.is_trusted_advice (address + offset) = device.is_trusted_advice address ∧
    device.is_untrusted_advice (address + offset) = device.is_untrusted_advice address ∧
    device.is_output (address + offset) = device.is_output address := by
  have advice := new_advice_regions config device.memory_layout built
  have input := new_outputs_after_inputs config device.memory_layout built
  have inputEnd := congrArg BitVec.toNat (input_end_eq_output config device.memory_layout built)
  have io := new_io_geometry config device.memory_layout built
  have inputGrid := new_input_word_aligned config device.memory_layout built
  have lowest := new_lowest_address_aligned config device.memory_layout built
  have order := new_io_ordered config device.memory_layout built
  have interval (lo hi : Nat) (loGrid : lo % 8 = 0) (hiGrid : hi % 8 = 0) :
      (decide (lo ≤ address + offset) && decide (address + offset < hi)) =
        (decide (lo ≤ address) && decide (address < hi)) := by
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    omega
  unfold JoltDevice.is_panic JoltDevice.is_termination JoltDevice.is_input
    JoltDevice.is_trusted_advice JoltDevice.is_untrusted_advice JoltDevice.is_output
  exact ⟨interval _ _ (by omega) (by omega), interval _ _ (by omega) (by omega),
    interval _ _ (by omega) (by omega), interval _ _ (by omega) (by omega),
    interval _ _ (by omega) (by omega), interval _ _ (by omega) (by omega)⟩

private theorem buffer_image_word (config : MemoryConfig) (device : JoltDevice)
    (built : MemoryLayout.new config = some device.memory_layout)
    (trustedFit : device.trusted_advice.size ≤ device.memory_layout.max_trusted_advice_size.toNat)
    (untrustedFit : device.untrusted_advice.size ≤ device.memory_layout.max_untrusted_advice_size.toNat)
    (inputFit : device.inputs.size ≤ device.memory_layout.max_input_size.toNat)
    (outputFit : device.outputs.size ≤ device.memory_layout.max_output_size.toNat)
    (address index : Nat) (addressIs : address = ramLowestAddress device.memory_layout + 8 * index) :
    TraceWitness.overlayRamBytes device.memory_layout device.memory_layout.output_start device.outputs index
      (TraceWitness.overlayRamBytes device.memory_layout device.memory_layout.input_start device.inputs index
        (TraceWitness.overlayRamBytes device.memory_layout device.memory_layout.untrusted_advice_start device.untrusted_advice index
          (TraceWitness.overlayRamBytes device.memory_layout device.memory_layout.trusted_advice_start device.trusted_advice index 0))) =
      if device.memory_layout.output_start.toNat ≤ address ∧ address < device.memory_layout.panic.toNat then
        TraceWitness.ramImageWord (fun k => device.outputs[k]?.getD 0) (address - device.memory_layout.output_start.toNat)
      else if device.memory_layout.input_start.toNat ≤ address ∧ address < device.memory_layout.input_end.toNat then
        TraceWitness.ramImageWord (fun k => device.inputs[k]?.getD 0) (address - device.memory_layout.input_start.toNat)
      else if device.memory_layout.untrusted_advice_start.toNat ≤ address ∧ address < device.memory_layout.untrusted_advice_end.toNat then
        TraceWitness.ramImageWord (fun k => device.untrusted_advice[k]?.getD 0) (address - device.memory_layout.untrusted_advice_start.toNat)
      else if device.memory_layout.trusted_advice_start.toNat ≤ address ∧ address < device.memory_layout.trusted_advice_end.toNat then
        TraceWitness.ramImageWord (fun k => device.trusted_advice[k]?.getD 0) (address - device.memory_layout.trusted_advice_start.toNat)
      else 0 := by
  have advice := new_advice_regions config device.memory_layout built
  have input := new_outputs_after_inputs config device.memory_layout built
  have inputEnd := congrArg BitVec.toNat (input_end_eq_output config device.memory_layout built)
  have io := new_io_geometry config device.memory_layout built
  have inputGrid := new_input_word_aligned config device.memory_layout built
  have lowGrid := new_lowest_address_aligned config device.memory_layout built
  have order := new_io_ordered config device.memory_layout built
  have positive := new_lowest_address_pos config device.memory_layout built
  rw [MemoryLayout.get_lowest_address_toNat] at inputGrid lowGrid order positive
  have lowTrusted : ramLowestAddress device.memory_layout ≤ device.memory_layout.trusted_advice_start.toNat := Nat.min_le_left _ _
  have lowUntrusted : ramLowestAddress device.memory_layout ≤ device.memory_layout.untrusted_advice_start.toNat := Nat.min_le_right _ _
  simp only [ramLowestAddress] at *
  have lowestIs : ramLowestAddress device.memory_layout =
      min device.memory_layout.trusted_advice_start.toNat device.memory_layout.untrusted_advice_start.toNat := rfl
  let trustedValue := TraceWitness.overlayRamBytes device.memory_layout device.memory_layout.trusted_advice_start device.trusted_advice index 0
  let untrustedValue := TraceWitness.overlayRamBytes device.memory_layout device.memory_layout.untrusted_advice_start device.untrusted_advice index trustedValue
  let inputValue := TraceWitness.overlayRamBytes device.memory_layout device.memory_layout.input_start device.inputs index untrustedValue
  have trusted := overlay_interval device.memory_layout device.memory_layout.trusted_advice_start
    device.memory_layout.trusted_advice_end.toNat address index device.trusted_advice 0
    positive lowTrusted (by omega) addressIs (by omega) (fun _ => rfl)
  change trustedValue = _ at trusted
  have untrusted := overlay_interval device.memory_layout device.memory_layout.untrusted_advice_start
    device.memory_layout.untrusted_advice_end.toNat address index device.untrusted_advice trustedValue
    positive lowUntrusted (by omega) addressIs (by omega) (by
      intro within
      rw [trusted, if_neg (by omega)])
  change untrustedValue = _ at untrusted
  have inputs := overlay_interval device.memory_layout device.memory_layout.input_start
    device.memory_layout.input_end.toNat address index device.inputs untrustedValue
    positive order.1 inputGrid addressIs (by omega) (by
      intro within
      rw [untrusted, if_neg (by omega), trusted, if_neg (by omega)])
  change inputValue = _ at inputs
  have outputs := overlay_interval device.memory_layout device.memory_layout.output_start
    device.memory_layout.panic.toNat address index device.outputs inputValue
    positive (by omega) (by omega) addressIs (by omega) (by
      intro within
      rw [inputs, if_neg (by omega), untrusted, if_neg (by omega), trusted, if_neg (by omega)])
  rw [outputs, inputs, untrusted, trusted]

/-- Bytes of a device load whose panic flag, if selected, is false.
Flag regions and unmapped addresses supply zero; buffer regions use their padded
array bytes, for example input `[7]` supplies 7 followed by zeros.
See `jolt/common/src/jolt_device.rs` (`JoltDevice::load`) at 5def437f. -/
private def loadImageBytes (device : JoltDevice) (address offset : Nat) : BitVec 8 :=
  if device.is_panic address || device.is_termination address then 0
  else if device.is_input address then device.inputs[address + offset - device.memory_layout.input_start.toNat]?.getD 0
  else if device.is_trusted_advice address then device.trusted_advice[address + offset - device.memory_layout.trusted_advice_start.toNat]?.getD 0
  else if device.is_untrusted_advice address then device.untrusted_advice[address + offset - device.memory_layout.untrusted_advice_start.toNat]?.getD 0
  else if device.is_output address then device.outputs[address + offset - device.memory_layout.output_start.toNat]?.getD 0
  else 0

private theorem loadImageBytes_read (config : MemoryConfig) (device : JoltDevice)
    (built : MemoryLayout.new config = some device.memory_layout) (address : BitVec 64)
    (aligned : address &&& 7 = 0) (below : address.toNat < RAM_START_ADDRESS)
    (checked : DoublewordAddressChecks device address false)
    (notPanicked : device.is_panic address.toNat = true → device.panic = false)
    (offset : Nat) (small : offset < 8) :
    device.load? (address.toNat + offset) = some (loadImageBytes device address.toNat offset) := by
  have alignedNat := Mmu.toNat_mod_eight_of_align aligned
  have belowByte : address.toNat + offset < RAM_START_ADDRESS := by
    have ramAligned : RAM_START_ADDRESS % 8 = 0 := by decide
    omega
  obtain ⟨panic, termination, input, trusted, untrusted, output⟩ :=
    device_predicates_offset config device built address.toNat offset alignedNat small
  have legal := checked
  simp only [DoublewordAddressChecks, show ¬ RAM_START_ADDRESS ≤ address.toNat by omega,
    ↓reduceIte] at legal
  have byteLegal := legal offset small
  simp only [Mmu.effective_address_ok, belowByte, ↓reduceIte, Bool.false_eq_true,
    panic, termination, input, trusted, untrusted, output] at byteLegal
  unfold JoltDevice.load? loadImageBytes
  rw [panic, termination, input, trusted, untrusted, output]
  split_ifs <;> simp_all

private theorem loadImageBytes_word (device : JoltDevice) (address : Nat) :
    TraceWitness.ramImageWord (loadImageBytes device address) 0 =
      if device.is_panic address || device.is_termination address then 0
      else if device.is_input address then
        TraceWitness.ramImageWord (fun k => device.inputs[k]?.getD 0) (address - device.memory_layout.input_start.toNat)
      else if device.is_trusted_advice address then
        TraceWitness.ramImageWord (fun k => device.trusted_advice[k]?.getD 0) (address - device.memory_layout.trusted_advice_start.toNat)
      else if device.is_untrusted_advice address then
        TraceWitness.ramImageWord (fun k => device.untrusted_advice[k]?.getD 0) (address - device.memory_layout.untrusted_advice_start.toNat)
      else if device.is_output address then
        TraceWitness.ramImageWord (fun k => device.outputs[k]?.getD 0) (address - device.memory_layout.output_start.toNat)
      else 0 := by
  have pack (bytes : Array (BitVec 8)) (start : Nat) (lower : start ≤ address) :
      TraceWitness.ramImageWord (fun k => bytes[address + k - start]?.getD 0) 0 =
        TraceWitness.ramImageWord (fun k => bytes[k]?.getD 0) (address - start) := by
    apply image_word_congr
    intro k small
    congr 2
    omega
  unfold loadImageBytes
  split_ifs with flags input trusted untrusted output
  · rfl
  · apply pack
    simp only [JoltDevice.is_input, Bool.and_eq_true, decide_eq_true_eq] at input
    exact input.1
  · apply pack
    simp only [JoltDevice.is_trusted_advice, Bool.and_eq_true, decide_eq_true_eq] at trusted
    exact trusted.1
  · apply pack
    simp only [JoltDevice.is_untrusted_advice, Bool.and_eq_true, decide_eq_true_eq] at untrusted
    exact untrusted.1
  · apply pack
    simp only [JoltDevice.is_output, Bool.and_eq_true, decide_eq_true_eq] at output
    exact output.1
  · rfl

private theorem loadImageBytes_image (trace : Trace) (device : JoltDevice) (config : MemoryConfig)
    (current : device = (TraceWitness.finalTraceState trace).jolt_device)
    (layout : device.memory_layout = trace.initialState.jolt_device.memory_layout)
    (built : MemoryLayout.new config = some device.memory_layout)
    (trustedFit : device.trusted_advice.size ≤ device.memory_layout.max_trusted_advice_size.toNat)
    (untrustedFit : device.untrusted_advice.size ≤ device.memory_layout.max_untrusted_advice_size.toNat)
    (inputFit : device.inputs.size ≤ device.memory_layout.max_input_size.toNat)
    (outputFit : device.outputs.size ≤ device.memory_layout.max_output_size.toNat)
    (address index : Nat) (addressIs : address = ramLowestAddress device.memory_layout + 8 * index)
    (below : address < RAM_START_ADDRESS)
    (notPanicked : device.is_panic address = true → device.panic = false)
    (notTermination : index ≠ (device.memory_layout.termination.toNat - ramLowestAddress device.memory_layout) / 8) :
    TraceWitness.ramImageWord (loadImageBytes device address) 0 = TraceWitness.finalRamWord trace index := by
  have grid := io_grid config device.memory_layout built
  have io := new_io_geometry config device.memory_layout built
  have advice := new_advice_regions config device.memory_layout built
  have input := new_outputs_after_inputs config device.memory_layout built
  have inputEnd := congrArg BitVec.toNat (input_end_eq_output config device.memory_layout built)
  have order := new_io_ordered config device.memory_layout built
  have positive := new_lowest_address_pos config device.memory_layout built
  rw [MemoryLayout.get_lowest_address_toNat] at order positive
  have panicMap := remap_at_or_above device.memory_layout device.memory_layout.panic positive (by omega)
  have termMap := remap_at_or_above device.memory_layout device.memory_layout.termination positive (by omega)
  have termFalse : device.is_termination address = false := by
    apply Bool.eq_false_iff.mpr
    intro within
    simp only [JoltDevice.is_termination, Bool.and_eq_true, decide_eq_true_eq] at within
    omega
  have flagOff : (some ((device.memory_layout.termination.toNat - ramLowestAddress device.memory_layout) / 8) == some index) = false := by
    simp [Ne.symm notTermination]
  unfold TraceWitness.finalRamWord
  dsimp only
  rw [← current, ← layout]
  change _ = if !device.panic && TraceWitness.remapRamAddress device.memory_layout device.memory_layout.termination == some index then 1 else _
  rw [termMap, flagOff]
  simp only [Bool.and_false, Bool.false_eq_true, ↓reduceIte]
  have baseZero : ¬ RAM_START_ADDRESS ≤ min device.memory_layout.trusted_advice_start.toNat device.memory_layout.untrusted_advice_start.toNat + 8 * index := by
    simpa only [ramLowestAddress] using (show ¬ RAM_START_ADDRESS ≤ ramLowestAddress device.memory_layout + 8 * index by omega)
  rw [if_neg baseZero, panicMap, loadImageBytes_word]
  by_cases panic : device.is_panic address = true
  · have within := panic
    simp only [JoltDevice.is_panic, Bool.and_eq_true, decide_eq_true_eq] at within
    have indexIs : (device.memory_layout.panic.toNat - ramLowestAddress device.memory_layout) / 8 = index := by omega
    simp [panic, notPanicked panic, indexIs]
  · have panicIndex : (device.memory_layout.panic.toNat - ramLowestAddress device.memory_layout) / 8 ≠ index := by
      intro equal
      apply panic
      simp only [JoltDevice.is_panic, Bool.and_eq_true, decide_eq_true_eq]
      omega
    simp only [show device.is_panic address = false from Bool.eq_false_iff.mpr panic,
      termFalse, Bool.false_or, Bool.false_eq_true, ↓reduceIte, Option.some.injEq, panicIndex]
    rw [buffer_image_word config device built trustedFit untrustedFit inputFit outputFit address index addressIs]
    simp only [JoltDevice.is_input, JoltDevice.is_trusted_advice, JoltDevice.is_untrusted_advice,
      JoltDevice.is_output, Bool.and_eq_true, decide_eq_true_eq] at panic ⊢
    have noPanic : ¬ (device.memory_layout.panic.toNat ≤ address ∧ address < device.memory_layout.termination.toNat) := by
      simpa [JoltDevice.is_panic] using panic
    generalize TraceWitness.ramImageWord (fun k => device.inputs[k]?.getD 0) (address - device.memory_layout.input_start.toNat) = inputWord
    generalize TraceWitness.ramImageWord (fun k => device.trusted_advice[k]?.getD 0) (address - device.memory_layout.trusted_advice_start.toNat) = trustedWord
    generalize TraceWitness.ramImageWord (fun k => device.untrusted_advice[k]?.getD 0) (address - device.memory_layout.untrusted_advice_start.toNat) = untrustedWord
    generalize TraceWitness.ramImageWord (fun k => device.outputs[k]?.getD 0) (address - device.memory_layout.output_start.toNat) = outputWord
    split_ifs <;> first | rfl | omega

private theorem load_raw_device (pre : SailJoltState) (address : Nat)
    (below : address < RAM_START_ADDRESS) (outside : address < 8 ∨ 0x10002000 ≤ address)
    (checked : Mmu.effective_address_ok pre.jolt_device address false = true) :
    Mmu.load_raw? pre address = pre.jolt_device.load? address := by
  have legal := checked
  simp only [Mmu.effective_address_ok, below, ↓reduceIte, Bool.false_eq_true,
    Bool.and_eq_true] at legal
  have peripherals : ¬ ((0x1020 ≤ address && address ≤ 0x1fff) ||
      (0x02000000 ≤ address && address ≤ 0x0200ffff) ||
      (0x0c000000 ≤ address && address ≤ 0x0fffffff) ||
      (0x10000000 ≤ address && address ≤ 0x100000ff) ||
      (0x10001000 ≤ address && address ≤ 0x10001fff)) = true := by
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    omega
  simp only [Mmu.load_raw?, checked, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    show ¬ RAM_START_ADDRESS ≤ address by omega, peripherals, legal.2]

private theorem write_image_same {inst : JoltInstance SourceInstruction} {inputs : JoltPrivateInputs}
    (run : UntrustedAnswerRun inst inputs) (next : Fin run.bytecode.size)
    (pre : SailJoltState) (ready : run.NextStep next pre) (destination : Dst) (value : BitVec 64)
    (advice : run.bytecode[next].instruction.RuntimeAdvice) (index : Nat) :
    TraceWitness.finalRamWord { run.toTrace with rows := (run.rows.push
      ⟨next, advice, pre, afterWriteDst destination value pre⟩) } index =
      TraceWitness.finalRamWord run.toTrace index := by
  have memory := ready_observation (fun state => state.sail.mem) (fun _ _ _ => rfl) run next pre ready
  have device := ready_observation SailJoltState.jolt_device (fun _ _ _ => rfl) run next pre ready
  apply final_image_of_memory_device
  · change (afterWriteDst destination value pre).sail.mem = _
    cases destination <;> exact memory
  · change (afterWriteDst destination value pre).jolt_device = _
    cases destination <;> exact device

private theorem loadImageBytes_zero (device : JoltDevice) (address : Nat)
    (region : deviceMemoryRegion device address = .panic ∨
      deviceMemoryRegion device address = .termination ∨ deviceMemoryRegion device address = .unmapped) :
    TraceWitness.ramImageWord (loadImageBytes device address) 0 = 0 := by
  apply ramImageWord_zero
  intro offset small
  unfold deviceMemoryRegion at region
  unfold loadImageBytes
  split_ifs at region <;> simp_all

private theorem ready_ld_panic_false {inst : JoltInstance SourceInstruction} {inputs : JoltPrivateInputs}
    (run : UntrustedAnswerRun inst inputs) (next : Fin run.bytecode.size)
    (pre : SailJoltState) (ready : run.NextStep next pre) (restricted : inst.PanicStoresOne)
    (fault : LoadFaultClass) (destination : Dst) (base : Src) (imm : BitVec 64)
    (instruction : run.bytecode[next].instruction = .LD fault destination base imm)
    (touch : pre.jolt_device.is_panic (sourceValue base pre + imm).toNat = true) :
    pre.jolt_device.panic = false := by
  have noStore : ¬ ∃ i : Fin run.rows.size, run.StoresPanicAt i := by
    intro stored
    have rule := restricted inputs run next pre ready
    rw [instruction] at rule
    exact rule stored ⟨0, by decide, by simpa only [Nat.add_zero] using touch⟩
  rw [ready_observation SailJoltState.jolt_device (fun _ _ _ => rfl) run next pre ready]
  exact run_panic_false run noStore

private theorem mapped_load_raw (config : MemoryConfig) (pre : SailJoltState) (address : BitVec 64)
    (built : MemoryLayout.new config = some pre.jolt_device.memory_layout)
    (mapped : address.toNat = 0 ∨ ∃ index : Nat,
      address.toNat = ramLowestAddress pre.jolt_device.memory_layout + 8 * index)
    (aligned : address &&& 7 = 0) (below : address.toNat < RAM_START_ADDRESS)
    (checked : DoublewordAddressChecks pre.jolt_device address false)
    (offset : Nat) (small : offset < 8) :
    Mmu.load_raw? pre (address.toNat + offset) = pre.jolt_device.load? (address.toNat + offset) := by
  have low := layout_above_peripherals config pre.jolt_device.memory_layout built
  rw [MemoryLayout.get_lowest_address_toNat] at low
  simp only [ramLowestAddress] at mapped
  have alignedNat := Mmu.toNat_mod_eight_of_align aligned
  have ramAligned : RAM_START_ADDRESS % 8 = 0 := by decide
  have outside : address.toNat + offset < 8 ∨ 0x10002000 ≤ address.toNat + offset := by
    rcases mapped with zero | ⟨index, indexIs⟩
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  apply load_raw_device pre _ (by omega) outside
  simp only [DoublewordAddressChecks, show ¬ RAM_START_ADDRESS ≤ address.toNat by omega,
    ↓reduceIte] at checked
  exact checked offset small

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
  let address := sourceValue base pre + imm
  let config := { inst.memory_config with program_size := some inst.program.program_size }
  obtain ⟨current, fixed, built, trustedFit, untrustedFit, inputFit, outputFit⟩ :=
    ready_device_data run next pre ready
  have notPanicked := ready_ld_panic_false run next pre ready panicStoresOne
    fault destination base imm instructionIs
  have reads := loadImageBytes_read config pre.jolt_device built address aligned below checked notPanicked
  have mappedCurrent : address.toNat = 0 ∨ ∃ index : Nat,
      address.toNat = ramLowestAddress pre.jolt_device.memory_layout + 8 * index := by
    rw [fixed.1]
    exact mapped
  refine ⟨loadImageBytes pre.jolt_device address.toNat, reads, ?_, ?_, ?_, ?_,
    write_image_same run next pre ready destination _ advice⟩
  · intro offset small
    rw [mapped_load_raw config pre address built mappedCurrent aligned below checked offset small]
    exact reads offset small
  · intro special
    apply loadImageBytes_zero
    simpa only [address, inRegion] using special
  · intro zero
    have low := layout_above_peripherals config pre.jolt_device.memory_layout built
    have free := pre.jolt_device.low_address_free config built (by omega) 0 (by decide)
    obtain ⟨input, trusted, untrusted, output, panic, termination, _⟩ := free
    rw [loadImageBytes_word]
    simp only [show address.toNat = 0 from zero, input, trusted, untrusted,
      output, panic, termination, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
  · intro index indexIs
    have grid := io_grid config pre.jolt_device.memory_layout built
    have io := new_io_geometry config pre.jolt_device.memory_layout built
    have localIndex : address.toNat = ramLowestAddress pre.jolt_device.memory_layout + 8 * index := by
      rw [fixed.1]; exact indexIs
    split_ifs with termination
    · have localTermination : index = (pre.jolt_device.memory_layout.termination.toNat -
          ramLowestAddress pre.jolt_device.memory_layout) / 8 := by rw [fixed.1]; exact termination
      have addressIs : address.toNat = pre.jolt_device.memory_layout.termination.toNat := by omega
      have selected : pre.jolt_device.is_termination address.toNat = true := by
        simp only [JoltDevice.is_termination, Bool.and_eq_true, decide_eq_true_eq]
        omega
      refine ⟨?_, ?_⟩
      · simp only [loadImageBytes_word, selected, Bool.or_true, ↓reduceIte]
      · intro earlier
        exact termination_next_ld_disjoint terminationThenStall run next pre ready earlier
          fault destination base imm instructionIs ⟨0, by decide, by simpa only [Nat.add_zero] using selected⟩
    · apply loadImageBytes_image run.toTrace pre.jolt_device config current fixed.1 built
        trustedFit untrustedFit inputFit outputFit address.toNat index localIndex below notPanicked
      simpa only [fixed.1] using termination


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
