import JoltConstraints.Soundness.Layer7.StallSuffix
import JoltConstraints.Soundness.Layer7.LastJump
import JoltConstraints.Soundness.Layer5.TerminationRestriction
import JoltConstraints.Soundness.Layer5.PanicRestriction
import JoltConstraints.Soundness.Layer3.Address
import JoltConstraints.Completeness.Helpers.IOSetupFrame

set_option autoImplicit false

open Sail PreSail LeanRV64D.Functions JoltISA

namespace JoltConstraints.Soundness

/-- Extracting the first `n` rows from a run with at least `n` rows produces
exactly `n` rows. For example, taking three rows from a five-row run gives size 3. -/
theorem UntrustedAnswerRun.truncate_rows_size
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (run : UntrustedAnswerRun joltInstance privateInputs)
    (n : Nat) (within : n ≤ run.rows.size) :
    (run.rows.extract 0 n).size = n := by
  simpa [Array.size_extract] using within

/-- The answer assigned to truncated row `i` is the answer of original row `i`.
For example, row 2 retains its answer when the run is cut after row 3. -/
def UntrustedAnswerRun.truncateAnswer
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (run : UntrustedAnswerRun joltInstance privateInputs)
    (n : Nat) (within : n ≤ run.rows.size) :
    Fin (run.rows.extract 0 n).size → BitVec 64 :=
  fun i => run.answers ⟨i.val, by
    have size := run.truncate_rows_size n within
    omega⟩

/-- Every extracted row executes with its original answer and states.
For example, truncating before row 4 keeps the execution certificate for row 2. -/
theorem UntrustedAnswerRun.truncate_executes
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (run : UntrustedAnswerRun joltInstance privateInputs)
    (n : Nat) (within : n ≤ run.rows.size) :
  ∀ step : Fin (run.rows.extract 0 n).size,
      execWithTapeAnswer
        (run.bytecode[(run.rows.extract 0 n)[step].rowIndex].instruction.withRuntimeAdvice
          (run.rows.extract 0 n)[step].runtimeAdvice)
        (run.truncateAnswer n within step)
        (run.rows.extract 0 n)[step].preState =
          .ok (.Retire_Success ()) (run.rows.extract 0 n)[step].postState := by
  intro step
  have hn : step.val < run.rows.size := by
    have hs := run.truncate_rows_size n within
    omega
  have hrow : (run.rows.extract 0 n)[step] = run.rows[step.val]'hn := by
    change (run.rows.extract 0 n)[step.val]'step.isLt = run.rows[step.val]'hn
    simp only [Array.getElem_extract, Nat.zero_add]
  have hinstr := congrArg
    (fun row : TraceRow run.bytecode =>
      run.bytecode[row.rowIndex].instruction.withRuntimeAdvice row.runtimeAdvice) hrow
  change run.bytecode[(run.rows.extract 0 n)[step].rowIndex].instruction.withRuntimeAdvice
      (run.rows.extract 0 n)[step].runtimeAdvice =
    run.bytecode[(run.rows[step.val]'hn).rowIndex].instruction.withRuntimeAdvice
      (run.rows[step.val]'hn).runtimeAdvice at hinstr
  have hpre := congrArg TraceRow.preState hrow
  have hpost := congrArg TraceRow.postState hrow
  rw [hinstr, hpre, hpost]
  exact run.executes ⟨step.val, hn⟩

/-- A nonempty extracted run has the same first row and entry state as the
original run. For example, taking two rows preserves row 0's entry address. -/
theorem UntrustedAnswerRun.truncate_starts
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (run : UntrustedAnswerRun joltInstance privateInputs)
    (n : Nat) (within : n ≤ run.rows.size) :
    ∀ first ∈ (run.rows.extract 0 n)[0]?,
      run.bytecode[first.rowIndex].address = joltInstance.program.entry_address ∧
      run.bytecode[first.rowIndex].starts_source ∧
      first.preState = advance_pc joltInstance.program.entry_address
        (source_is_compressed run.bytecode first.rowIndex) run.initialState := by
  intro first hfirst
  have hzero : (run.rows.extract 0 n)[0]? = run.rows[0]? := by
    by_cases h : 0 < n
    · simp [within, h]
    · have hn : n = 0 := by omega
      subst n
      simp at hfirst
  rw [hzero] at hfirst
  exact run.starts first hfirst

/-- Adjacent extracted rows retain their original execution linkage.
For example, rows 1 and 2 remain linked when the run is cut after row 3. -/
theorem UntrustedAnswerRun.truncate_linked
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (run : UntrustedAnswerRun joltInstance privateInputs)
    (n : Nat) (within : n ≤ run.rows.size) :
    ∀ (i : Nat) (current next : TraceRow run.bytecode),
      (run.rows.extract 0 n)[i]? = some current →
      (run.rows.extract 0 n)[i + 1]? = some next →
      if run.bytecode[current.rowIndex].virtual_sequence_remaining.getD 0 ≠ 0 then
        next.rowIndex.val = current.rowIndex.val + 1 ∧ next.preState = current.postState
      else
        ∃ address, current.postState.sail.regs.get? Register.nextPC = some address ∧
          run.bytecode[next.rowIndex].address = address ∧
          run.bytecode[next.rowIndex].starts_source ∧
          next.preState = advance_pc address
            (source_is_compressed run.bytecode next.rowIndex) current.postState := by
  intro i current next hcurrent hnext
  have hi : i < n := by
    have hs := run.truncate_rows_size n within
    have : i < (run.rows.extract 0 n).size := (Array.getElem?_eq_some_iff.mp hcurrent).1
    omega
  have hj : i + 1 < n := by
    have hs := run.truncate_rows_size n within
    have : i + 1 < (run.rows.extract 0 n).size := (Array.getElem?_eq_some_iff.mp hnext).1
    omega
  have hcurrent' : run.rows[i]? = some current := by
    simpa only [Array.getElem?_extract, Nat.min_eq_left within, Nat.sub_zero,
      Nat.zero_add, if_pos hi] using hcurrent
  have hnext' : run.rows[i + 1]? = some next := by
    simpa only [Array.getElem?_extract, Nat.min_eq_left within, Nat.sub_zero,
      Nat.zero_add, if_pos hj] using hnext
  exact run.linked i current next hcurrent' hnext'

/-- The first `n` rows form an untrusted-answer run with literally the same
bytecode, initial state and answers. For example, cutting at 4 retains rows 0–3.
See jolt/tracer/src/emulator/cpu.rs:622-632 at 8bbb2357. -/
noncomputable def UntrustedAnswerRun.truncate
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (run : UntrustedAnswerRun joltInstance privateInputs)
    (n : Nat) (within : n ≤ run.rows.size) :
    UntrustedAnswerRun joltInstance privateInputs where
  toTrace := ⟨run.bytecode, run.rows.extract 0 n, run.initialState⟩
  answers := run.truncateAnswer n within
  expands := run.expands
  executes := run.truncate_executes n within
  initialized := run.initialized
  starts := run.truncate_starts n within
  linked := run.truncate_linked n within

/-- A completed termination store before a cut remains a completed store in the
truncated run. For example, a store at row 2 remains after cutting at row 4. -/
theorem UntrustedAnswerRun.truncate_storesTerminationAt
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (run : UntrustedAnswerRun joltInstance privateInputs)
    (n : Nat) (within : n ≤ run.rows.size)
    (i : Fin run.rows.size) (before : i.val < n)
    (stored : run.StoresTerminationAt i) :
    (run.truncate n within).StoresTerminationAt
      ⟨i.val, by
        change i.val < (run.rows.extract 0 n).size
        rw [run.truncate_rows_size n within]
        exact before⟩ := by
  have hsize := run.truncate_rows_size n within
  let j : Fin (run.rows.extract 0 n).size := ⟨i.val, by rw [hsize]; exact before⟩
  have hrow : (run.rows.extract 0 n)[j] = run.rows[i] := by
    change (run.rows.extract 0 n)[i.val]'j.isLt = run.rows[i.val]'i.isLt
    simp only [Array.getElem_extract, Nat.zero_add]
  change (match run.bytecode[(run.rows.extract 0 n)[j].rowIndex].instruction with
    | .SD base _ imm => TouchesTermination (run.rows.extract 0 n)[j].preState.jolt_device
        (sourceValue base (run.rows.extract 0 n)[j].preState + imm)
    | _ => False)
  have hs := congrArg (fun row : TraceRow run.bytecode =>
    match run.bytecode[row.rowIndex].instruction with
    | .SD base _ imm => TouchesTermination row.preState.jolt_device
        (sourceValue base row.preState + imm)
    | _ => False) hrow
  change (match run.bytecode[(run.rows.extract 0 n)[j].rowIndex].instruction with
    | .SD base _ imm => TouchesTermination (run.rows.extract 0 n)[j].preState.jolt_device
        (sourceValue base (run.rows.extract 0 n)[j].preState + imm)
    | _ => False) = (match run.bytecode[run.rows[i].rowIndex].instruction with
    | .SD base _ imm => TouchesTermination run.rows[i].preState.jolt_device
        (sourceValue base run.rows[i].preState + imm)
    | _ => False) at hs
  exact Eq.mpr hs stored

/-- Reading row `k` before the cut gives the same optional row in the prefix.
For example, row 1 is unchanged by a cut after row 3. -/
private theorem extract_getElem?_before {α : Type} (rows : Array α)
    (n k : Nat) (within : n ≤ rows.size) (before : k < n) :
    (rows.extract 0 n)[k]? = rows[k]? := by
  simp only [Array.getElem?_extract, Nat.min_eq_left within, Nat.sub_zero,
    Nat.zero_add, if_pos before]

/-- The flag that row `k` starts an expansion is unchanged before a cut.
For example, an ECALL expansion start at row 2 remains a start after row 3. -/
private theorem stepNOfTraceIsStartOfNewExpansion_extract
    {bytecode : Array JoltInstructionRow} (rows : Array (TraceRow bytecode))
    (n k : Nat) (within : n ≤ rows.size) (before : k < n) :
    stepNOfTraceIsStartOfNewExpansion (rows.extract 0 n) k =
      stepNOfTraceIsStartOfNewExpansion rows k := by
  simp only [stepNOfTraceIsStartOfNewExpansion,
    extract_getElem?_before rows n k within before]

/-- The expansion containing row `k` begins at the same row in a prefix.
For example, the start of a DIV expansion at row 2 remains row 2 after a later cut. -/
private theorem startOfExpansionContainingStepN_extract
    {bytecode : Array JoltInstructionRow} (rows : Array (TraceRow bytecode))
    (n k : Nat) (within : n ≤ rows.size) (before : k < n) :
    startOfExpansionContainingStepN (rows.extract 0 n) k =
      startOfExpansionContainingStepN rows k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [startOfExpansionContainingStepN,
        stepNOfTraceIsStartOfNewExpansion_extract rows n (k + 1) within before]
      by_cases h : stepNOfTraceIsStartOfNewExpansion rows (k + 1)
      · simp [h]
      · simp [h, ih (by omega)]

/-- The VirtualAdvice flag at row `k` is unchanged before a cut.
For example, row 2 remains an advice row in a prefix ending after row 3. -/
private theorem stepNOfTraceIsAdvice_extract
    {bytecode : Array JoltInstructionRow} (rows : Array (TraceRow bytecode))
    (n k : Nat) (within : n ≤ rows.size) (before : k < n) :
    stepNOfTraceIsAdvice (rows.extract 0 n) k = stepNOfTraceIsAdvice rows k := by
  simp only [stepNOfTraceIsAdvice, extract_getElem?_before rows n k within before]

/-- The number of earlier advice rows in an expansion is unchanged by a later cut.
For example, a DIV advice row still sees the same earlier advice count. -/
private theorem adviceStepsBeforeStepN_extract
    {bytecode : Array JoltInstructionRow} (rows : Array (TraceRow bytecode))
    (n i : Nat) (within : n ≤ rows.size) (earlier : i < n) :
    adviceStepsBeforeStepN (rows.extract 0 n) i = adviceStepsBeforeStepN rows i := by
  simp only [adviceStepsBeforeStepN,
    startOfExpansionContainingStepN_extract rows n i within earlier]
  congr 1
  apply List.filter_congr
  intro k hk
  have hk' : k < i := by
    rw [List.mem_range'] at hk
    obtain ⟨j, hj, rfl⟩ := hk
    omega
  exact stepNOfTraceIsAdvice_extract rows n k within (by omega)

/-- Honest tracer advice at row `i` depends only on rows through `i`.
For example, truncating a five-row DIV trace after row 3 preserves row 2's advice. -/
theorem honestTracerAdviceAtStepN_extract
    (program : Rv64ProgramImage SourceInstruction)
    {bytecode : Array JoltInstructionRow} (rows : Array (TraceRow bytecode))
    (n i : Nat) (within : n ≤ rows.size) (earlier : i < n) :
    honestTracerAdviceAtStepN program (rows.extract 0 n) i =
      honestTracerAdviceAtStepN program rows i := by
  simp only [honestTracerAdviceAtStepN,
    extract_getElem?_before rows n i within earlier,
    startOfExpansionContainingStepN_extract rows n i within earlier,
    adviceStepsBeforeStepN_extract rows n i within earlier]
  have hstart : startOfExpansionContainingStepN rows i ≤ i := by
    induction i with
    | zero => simp [startOfExpansionContainingStepN]
    | succ i ih =>
        simp only [startOfExpansionContainingStepN]
        split
        · omega
        · omega
  rw [extract_getElem?_before rows n (startOfExpansionContainingStepN rows i)
    within (by omega)]

/-- Each retained row uses the layout fixed by the emulator's initial device.
For example, an SD at row 3 interprets the termination region using the same
layout as row 0. See jolt/tracer/src/emulator/cpu.rs:622-632 at 8bbb2357. -/
theorem UntrustedAnswerRun.preState_layout
    {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs}
    (run : UntrustedAnswerRun joltInstance privateInputs)
    (i : Fin run.rows.size) :
    run.rows[i].preState.jolt_device.memory_layout =
      run.initialState.jolt_device.memory_layout := by
  let rel : JoltDevice → JoltDevice → Prop :=
    fun a b => b.memory_layout = a.memory_layout
  have refl : ∀ io, rel io io := by intro io; rfl
  have trans : ∀ a b c, rel a b → rel b c → rel a c := by
    intro a b c ab bc
    exact bc.trans ab
  have store : ∀ io io' address value,
      JoltDevice.store? io address value = some io' → rel io io' := by
    intro io io' address value stored
    exact (JoltIOSetupFrame.storeDeviceByte_same io io' address value stored).1
  have starts : ∀ first, run.rows[0]? = some first →
      first.preState.jolt_device = run.initialState.jolt_device := by
    intro first firstIs
    obtain ⟨_, _, firstState⟩ := run.starts first firstIs
    rw [firstState]
    rfl
  have linked : ∀ n current next,
      run.rows[n]? = some current → run.rows[n + 1]? = some next →
      next.preState.jolt_device = current.postState.jolt_device := by
    intro n current next currentIs nextIs
    have link := run.linked n current next currentIs nextIs
    split at link
    · exact congrArg SailJoltState.jolt_device link.2
    · obtain ⟨_, _, _, _, nextState⟩ := link
      rw [nextState]
      rfl
  have preserved : ∀ step : Fin run.rows.size,
      rel run.rows[step].preState.jolt_device run.rows[step].postState.jolt_device := by
    intro step
    exact execWithTapeAnswer_rule_of_device_relation rel refl trans store
      (run.bytecode[run.rows[step].rowIndex].instruction.withRuntimeAdvice
        run.rows[step].runtimeAdvice) (run.answers step) _ _ _ (run.executes step)
  exact Trace.preState_device_relation run.toTrace rel refl trans starts linked
    preserved i.val i.isLt

/-- A no-panic public I/O image assigns one to its termination word.
For example, the SDK exit claim uses word value 1 at its termination address.
See jolt/crates/jolt-program/src/preprocess/public_io.rs:47-52 at 8bbb2357. -/
theorem ramPublicIoWord_termination (config : MemoryConfig) (layout : MemoryLayout)
    (built : MemoryLayout.new config = some layout)
    (io : JoltDevice) (sameLayout : io.memory_layout = layout)
    (noPanic : io.panic = false) :
    ramPublicIoWord io
      ((layout.termination.toNat - ramLowestAddress layout) / 8) = 1 := by
  have ordered := new_io_ordered config layout built
  have lowPos := new_lowest_address_pos config layout built
  rw [MemoryLayout.get_lowest_address_toNat] at lowPos ordered
  let index := (layout.termination.toNat - ramLowestAddress layout) / 8
  have remap : TraceWitness.remapRamAddress layout layout.termination = some index := by
    unfold TraceWitness.remapRamAddress
    rw [if_neg (by omega)]
    rfl
  unfold ramPublicIoWord
  rw [sameLayout, noPanic, remap]
  simp [index]

/-- The termination word lies inside the verifier's masked public I/O interval.
For example, the SDK exit word is checked by constraint 26.
See jolt/crates/jolt-program/src/preprocess/public_io.rs:47-52 at 8bbb2357. -/
theorem ramPublicIoMask_termination {F : Type} [Field F]
    (config : MemoryConfig) (layout : MemoryLayout)
    (built : MemoryLayout.new config = some layout)
    (io : JoltDevice) (sameLayout : io.memory_layout = layout) :
    ramPublicIoMask (F := F) io
      ((layout.termination.toNat - ramLowestAddress layout) / 8) = 1 := by
  obtain ⟨lowLeInput, inputLeOutput, outputLePanic, panicLeTermination, _⟩ :=
    new_io_ordered config layout built
  rw [MemoryLayout.get_lowest_address_toNat] at lowLeInput
  obtain ⟨_, _, _, ioEndIs, ioEndBound⟩ := new_io_geometry config layout built
  let low := ramLowestAddress layout
  have lowLeTerm : low ≤ layout.termination.toNat := by
    dsimp only [low, ramLowestAddress]
    omega
  have inputLeTerm : layout.input_start.toNat ≤ layout.termination.toNat := by omega
  have termEnd : layout.termination.toNat + 8 ≤ JoltISA.RAM_START_ADDRESS := by
    omega
  have firstLe : (layout.input_start.toNat - low) / 8 ≤
      (layout.termination.toNat - low) / 8 := by omega
  have termLt : (layout.termination.toNat - low) / 8 <
      (JoltISA.RAM_START_ADDRESS - low) / 8 := by omega
  unfold ramPublicIoMask
  rw [sameLayout]
  simp [low, firstLe, termLt]

/-- A byte buffer ending before a word contributes nothing to that word.
For example, input bytes ending before the termination word leave it zero. -/
private theorem overlayRamBytes_after_end
    (layout : MemoryLayout) (start : BitVec 64) (bytes : Array (BitVec 8))
    (address : Nat) (previous : BitVec 64)
    (ended : start.toNat + bytes.size ≤ ramLowestAddress layout + 8 * address) :
    TraceWitness.overlayRamBytes layout start bytes address previous = previous := by
  unfold TraceWitness.overlayRamBytes
  cases remap : TraceWitness.remapRamAddress layout start with
  | none => rfl
  | some firstWord =>
      have hGuard : ¬(start.toNat = 0 ∨
          start.toNat < ramLowestAddress layout) := by
        change (if start.toNat = 0 ∨ start.toNat < ramLowestAddress layout then none
          else some ((start.toNat - ramLowestAddress layout) / 8)) = some firstWord at remap
        intro bad
        rw [if_pos bad] at remap
        cases remap
      have startGe : ramLowestAddress layout ≤ start.toNat := by omega
      have firstIs : firstWord =
          (start.toNat - ramLowestAddress layout) / 8 := by
        change (if start.toNat = 0 ∨ start.toNat < ramLowestAddress layout then none
          else some ((start.toNat - ramLowestAddress layout) / 8)) = some firstWord at remap
        rw [if_neg hGuard] at remap
        exact (Option.some.inj remap).symm
      apply if_neg
      intro takes
      obtain ⟨firstLe, readLt⟩ := takes
      rw [firstIs] at firstLe readLt
      omega

/-- The termination word's remapped byte address is its actual byte address.
For example, a termination word eight bytes after panic occupies one whole word. -/
private theorem termination_word_absolute
    (config : MemoryConfig) (layout : MemoryLayout)
    (built : MemoryLayout.new config = some layout) :
    ramLowestAddress layout +
      8 * ((layout.termination.toNat - ramLowestAddress layout) / 8) =
        layout.termination.toNat := by
  obtain ⟨lowLeInput, _, _, _, _⟩ := new_io_ordered config layout built
  obtain ⟨outputStart, inputMultiple⟩ := new_outputs_after_inputs config layout built
  obtain ⟨panicStart, _, terminationStart, _, _⟩ := new_io_geometry config layout built
  have inputAligned := new_input_word_aligned config layout built
  rw [MemoryLayout.get_lowest_address_toNat] at lowLeInput inputAligned
  change ramLowestAddress layout ≤ layout.input_start.toNat at lowLeInput
  change (layout.input_start.toNat - ramLowestAddress layout) % 8 = 0 at inputAligned
  have termOffset : layout.termination.toNat - ramLowestAddress layout =
      (layout.input_start.toNat - ramLowestAddress layout) +
        layout.max_input_size.toNat + layout.max_output_size.toNat + 8 := by
    omega
  have termAligned :
      (layout.termination.toNat - ramLowestAddress layout) % 8 = 0 := by
    rw [termOffset]
    omega
  omega

/-- The initial RAM image contains zero at the termination word because the
advice and input buffers end before it. For example, SDK exit changes that
word from its initial zero to one with a store. -/
private theorem initialRamWord_termination_zero
    (config : MemoryConfig) (layout : MemoryLayout)
    (built : MemoryLayout.new config = some layout)
    (state : SailJoltState)
    (sameLayout : state.jolt_device.memory_layout = layout)
    (adviceBelow : state.jolt_device.AdviceBelowInput)
    (inputFits : state.jolt_device.inputs.size ≤ layout.max_input_size.toNat) :
    TraceWitness.initialRamWordFromState state
      ((layout.termination.toNat - ramLowestAddress layout) / 8) = 0 := by
  obtain ⟨_, trustedBelow, untrustedBelow⟩ := adviceBelow
  rw [sameLayout] at trustedBelow untrustedBelow
  obtain ⟨_, inputLeOutput, outputLePanic, panicLeTerm, _⟩ :=
    new_io_ordered config layout built
  obtain ⟨outputStart, _⟩ := new_outputs_after_inputs config layout built
  obtain ⟨_, _, _, _, ioEndBound⟩ := new_io_geometry config layout built
  have absolute := termination_word_absolute config layout built
  have trustedEnd : layout.trusted_advice_start.toNat +
      state.jolt_device.trusted_advice.size ≤
      ramLowestAddress layout +
        8 * ((layout.termination.toNat - ramLowestAddress layout) / 8) := by
    rw [absolute]
    omega
  have untrustedEnd : layout.untrusted_advice_start.toNat +
      state.jolt_device.untrusted_advice.size ≤
      ramLowestAddress layout +
        8 * ((layout.termination.toNat - ramLowestAddress layout) / 8) := by
    rw [absolute]
    omega
  have inputEnd : layout.input_start.toNat + state.jolt_device.inputs.size ≤
      ramLowestAddress layout +
        8 * ((layout.termination.toNat - ramLowestAddress layout) / 8) := by
    rw [absolute]
    omega
  have belowRam : ¬ JoltISA.RAM_START_ADDRESS ≤
      ramLowestAddress layout +
        8 * ((layout.termination.toNat - ramLowestAddress layout) / 8) := by
    rw [absolute]
    omega
  unfold TraceWitness.initialRamWordFromState
  rw [sameLayout]
  dsimp only
  rw [overlayRamBytes_after_end layout layout.input_start state.jolt_device.inputs
      _ _ inputEnd]
  rw [overlayRamBytes_after_end layout layout.untrusted_advice_start
      state.jolt_device.untrusted_advice _ _ untrustedEnd]
  rw [overlayRamBytes_after_end layout layout.trusted_advice_start
      state.jolt_device.trusted_advice _ _ trustedEnd]
  change (if JoltISA.RAM_START_ADDRESS ≤ ramLowestAddress layout +
      8 * ((layout.termination.toNat - ramLowestAddress layout) / 8) then
      TraceWitness.ramImageWord (fun i => (state.sail.mem.get? i).getD 0)
        (ramLowestAddress layout +
          8 * ((layout.termination.toNat - ramLowestAddress layout) / 8))
    else 0) = 0
  rw [if_neg belowRam]

/-- The verifier's public I/O layout is the layout built from the instance.
For example, its termination address is the one used by the RAM constraints. -/
private theorem context_layout_built
    {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} {params : WitnessParams}
    (context : ConstraintContext joltInstance privateInputs params) :
    MemoryLayout.new
      {joltInstance.memory_config with program_size := some joltInstance.program.program_size} =
        some context.io.memory_layout := by
  have publicIo := context.publicIo
  unfold JoltInstance.public_io at publicIo
  obtain ⟨layout, hasLayout, sameIo⟩ := Option.bind_eq_some_iff.mp publicIo
  have layoutEq : layout = context.io.memory_layout :=
    congrArg JoltDevice.memory_layout (Option.some.inj sameIo)
  change MemoryLayout.new _ = some layout at hasLayout
  rw [layoutEq] at hasLayout
  exact hasLayout

/-- The verifier's initial RAM value at the termination word is zero.
For example, constraint 38 starts the SDK exit word at zero before its SD. -/
private theorem context_initial_termination_zero
    {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} {params : WitnessParams}
    (context : ConstraintContext joltInstance privateInputs params) :
    context.initialRam
      ((context.io.memory_layout.termination.toNat -
        ramLowestAddress context.io.memory_layout) / 8) = 0 := by
  have built := context_layout_built context
  obtain ⟨state, initialized, initialRamIs⟩ := context.initialized
  have stateLayout :=
    (initial_state_device joltInstance privateInputs state initialized).1
  have sameLayout := Option.some.inj (stateLayout.symm.trans (by
    change joltInstance.memory_layout = some context.io.memory_layout
    exact built))
  have adviceFacts :=
    initial_state_advice_below_input joltInstance privateInputs state initialized
  rw [MemoryLayout.get_lowest_address_toNat] at adviceFacts
  have adviceBelow : state.jolt_device.AdviceBelowInput :=
    ⟨adviceFacts.1, adviceFacts.2.1, adviceFacts.2.2⟩
  have valid := context.validInputs
  unfold JoltInstance.validate_inputs at valid
  change joltInstance.memory_layout = some context.io.memory_layout at built
  rw [built] at valid
  simp only [Bool.and_eq_true, decide_eq_true_eq] at valid
  have inputsIs := initial_state_inputs joltInstance privateInputs state initialized
  have inputFits : state.jolt_device.inputs.size ≤
      context.io.memory_layout.max_input_size.toNat := by
    rw [inputsIs]
    exact valid.1.2
  rw [initialRamIs]
  exact initialRamWord_termination_zero _ _ built state sameLayout adviceBelow inputFits

/-- A no-panic public claim forces some nonzero RAM update at the termination
word. For example, changing its initial zero to the claimed one needs a cycle. -/
private theorem termination_effect_exists
    {F : Type} [Field F]
    (joltInstance : JoltInstance SourceInstruction)
    (restrictions : joltInstance.TemporaryRestrictions)
    {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params)
    (context : ConstraintContext joltInstance privateInputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam
      context.io context.entry witness) :
    ∃ (address : Fin params.ramSize) (cycle : Fin params.traceLength),
      address.val =
        (context.io.memory_layout.termination.toNat -
          ramLowestAddress context.io.memory_layout) / 8 ∧
      witness.RamRa address cycle * witness.RamInc cycle ≠ 0 := by
  let layout := context.io.memory_layout
  let termWord := (layout.termination.toNat - ramLowestAddress layout) / 8
  have built := context_layout_built context
  have maskOne := ramPublicIoMask_termination (F := F)
    _ layout built context.io rfl
  have bound : termWord < params.ramSize := by
    have publicFits := public_io_words_fit_ram context
    unfold ramPublicIoMask at maskOne
    dsimp only [termWord, layout] at maskOne ⊢
    split_ifs at maskOne with h
    · exact lt_of_lt_of_le h.2 publicFits
    · simp at maskOne
  let address : Fin params.ramSize := ⟨termWord, bound⟩
  have ioPanic : context.io.panic = false := by
    have publicIo := context.publicIo
    unfold JoltInstance.public_io at publicIo
    obtain ⟨_, _, sameIo⟩ := Option.bind_eq_some_iff.mp publicIo
    have panicEq := congrArg JoltDevice.panic (Option.some.inj sameIo)
    exact panicEq.symm.trans restrictions.claimsNoPanic
  have publicOne : ramPublicIoWord context.io address.val = 1 := by
    exact ramPublicIoWord_termination _ layout built context.io rfl ioPanic
  have initialZero : context.initialRam address.val = 0 :=
    context_initial_termination_zero context
  have finalOne : witness.RamValFinal address = 1 := by
    have claim := equations.ramOutputEqPublicIo address
    change ramPublicIoMask context.io address.val *
      (witness.RamValFinal address - ((ramPublicIoWord context.io address.val).toNat : F)) = 0 at claim
    rw [maskOne, publicOne] at claim
    have wordOne : (((1 : BitVec 64).toNat : Nat) : F) = 1 := by
      simp
    rw [one_mul, wordOne] at claim
    exact sub_eq_zero.mp claim
  have sumOne : (∑ cycle : Fin params.traceLength,
      witness.RamRa address cycle * witness.RamInc cycle) = 1 := by
    have history := equations.ramValFinalEqInitialPlusRamInc address
    rw [finalOne] at history
    unfold ramInitialValue at history
    rw [initialZero] at history
    have wordZero : (((0 : BitVec 64).toNat : Nat) : F) = 0 := by
      simp
    rw [wordZero, zero_add] at history
    exact history.symm
  have existsCycle : ∃ cycle : Fin params.traceLength,
      witness.RamRa address cycle * witness.RamInc cycle ≠ 0 := by
    by_contra none
    push_neg at none
    have allZero : (∑ cycle : Fin params.traceLength,
        witness.RamRa address cycle * witness.RamInc cycle) = 0 := by
      apply Finset.sum_eq_zero
      intro cycle _
      exact none cycle
    rw [allZero] at sumOne
    exact one_ne_zero sumOne.symm
  obtain ⟨cycle, effect⟩ := existsCycle
  exact ⟨address, cycle, rfl, effect⟩

/-- A nonzero termination-word update lies among the retained execution rows.
For example, neither a padding suffix nor a stable-stall suffix can supply it. -/
private theorem termination_effect_in_run
    {F : Type} [Field F] (joltField : JoltField F)
    (joltInstance : JoltInstance SourceInstruction)
    (assumptions : joltInstance.SoundnessAssumptions)
    {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params)
    (context : ConstraintContext joltInstance privateInputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam
      context.io context.entry witness)
    (run : UntrustedAnswerRun joltInstance privateInputs)
    (bytecodeEq : run.bytecode = context.bytecode)
    (represented : JoltInstance.RepresentsPrefix witness run.toTrace)
    (cut : run.rows.size = params.traceLength ∨
      ∃ bound : run.rows.size < params.traceLength,
        witness.InstructionFlags .IsNoop ⟨run.rows.size, bound⟩ = 1 ∨
          ∃ last ∈ run.rows.back?, last.StableStall)
    (address : Fin params.ramSize) (cycle : Fin params.traceLength)
    (effect : witness.RamRa address cycle * witness.RamInc cycle ≠ 0) :
    cycle.val < run.rows.size := by
  by_contra outside
  have after : run.rows.size ≤ cycle.val := by omega
  rcases cut with full | ⟨bound, paddingOrStall⟩
  · omega
  · rcases paddingOrStall with padding | ⟨last, atEnd, stable⟩
    · have charAbove : 2 ^ 127 < ringChar F := by
        unfold JoltField at joltField
        omega
      have later := padding_from charAbove context equations
        ⟨run.rows.size, bound⟩ cycle padding after
      have addressZero := ramAddress_zero_of_padding charAbove context equations cycle later
      exact effect ((ram_zero_effects charAbove context equations cycle addressZero).2.2 address)
    · have nonempty : 0 < run.rows.size := by
        by_contra empty
        have emptyRows : run.rows = #[] := Array.eq_empty_of_size_eq_zero (by omega)
        simp [emptyRows] at atEnd
      have stops : ∀ row ∈ run.rows.back?, row.StableStall := by
        intro row rowAt
        have rowEq : row = last := by
          have a : run.rows.back? = some row := rowAt
          have b : run.rows.back? = some last := atEnd
          exact Option.some.inj (a.symm.trans b)
        rw [rowEq]
        exact stable
      exact effect (JoltInstance.soundness_stall_suffix_zero_ram_effects joltField joltInstance
        assumptions.pcNoWrap privateInputs witness context equations run bytecodeEq
        represented.toRepresentsRows nonempty stops cycle after address)

/-- A nonzero RAM effect in a represented cycle selects an SD instruction.
For example, an LD cannot change its selected RAM word. -/
private theorem termination_effect_is_sd
    {F : Type} [Field F] (joltField : JoltField F)
    (joltInstance : JoltInstance SourceInstruction)
    {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params)
    (context : ConstraintContext joltInstance privateInputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam
      context.io context.entry witness)
    (run : UntrustedAnswerRun joltInstance privateInputs)
    (bytecodeEq : run.bytecode = context.bytecode)
    (represented : JoltInstance.RepresentsRows witness run.toTrace)
    (address : Fin params.ramSize)
    (cycle : Fin params.traceLength) (inRun : cycle.val < run.rows.size)
    (effect : witness.RamRa address cycle * witness.RamInc cycle ≠ 0) :
    ∃ base value imm,
      run.bytecode[run.rows[cycle.val].rowIndex].instruction = .SD base value imm := by
  let i : Fin run.rows.size := ⟨cycle.val, inRun⟩
  let row := run.bytecode[run.rows[i].rowIndex]
  have charAbove := two_pow_127_lt_char joltField
  have selected := JoltInstance.selected_represented_row joltField joltInstance
    privateInputs witness context equations run bytecodeEq represented cycle inRun
  let slot : Fin (2 ^ params.logBytecodeK) :=
    ⟨run.rows[i].rowIndex.val + 1, by
      have domain : params.BytecodeDomainFor run.bytecode.size := by
        simpa only [bytecodeEq] using context.bytecodeDomain
      have fits := domain.rowsFit
      have rowBound := run.rows[i].rowIndex.isLt
      omega⟩
  have selectedSlot : bytecodeRa witness slot cycle = 1 := selected
  have rowAt : bytecodeRow context.bytecode slot.val = some row := by
    rw [← bytecodeEq]
    change bytecodeRow run.bytecode (run.rows[i].rowIndex.val + 1) =
      some run.bytecode[run.rows[i].rowIndex]
    simp [bytecodeRow]
  have loadFlag : witness.OpFlags .Load cycle =
      if JoltMetadata.circuitFlag row .Load then 1 else 0 := by
    rw [opFlag_of_selected_bytecode charAbove context equations .Load cycle slot selectedSlot]
    simp [bytecodeCircuitFlag, rowAt]
  have storeFlag : witness.OpFlags .Store cycle =
      if JoltMetadata.circuitFlag row .Store then 1 else 0 := by
    rw [opFlag_of_selected_bytecode charAbove context equations .Store cycle slot selectedSlot]
    simp [bytecodeCircuitFlag, rowAt]
  have isStore : JoltMetadata.circuitFlag row .Store = true := by
    by_cases isLoad : JoltMetadata.circuitFlag row .Load = true
    · have loadOne : witness.OpFlags .Load cycle = 1 := by simpa [isLoad] using loadFlag
      exact False.elim (effect (ram_write_effect_zero_of_load charAbove context equations
        cycle loadOne address))
    · have loadZero : witness.OpFlags .Load cycle = 0 := by simpa [isLoad] using loadFlag
      by_contra noStore
      have storeZero : witness.OpFlags .Store cycle = 0 := by
        simpa [noStore] using storeFlag
      have addressZero := ramAddress_zero_of_not_load_store
        equations.ramAddrEqZeroIfNotLoadStore cycle loadZero storeZero
      exact effect ((ram_zero_effects charAbove context equations cycle addressZero).2.2 address)
  have opcodeStore : JoltMetadata.opcodeFlag row.instruction .Store = true := by
    simpa only [JoltMetadata.circuitFlag] using isStore
  obtain ⟨base, value, imm, instructionIs⟩ :=
    JoltMetadata.opcodeFlag_store_requiresSD row.instruction opcodeStore
  exact ⟨base, value, imm, instructionIs⟩

/-- A selected SD at the termination word writes a byte address inside the
termination region. For example, the SDK's final SD touches that device word. -/
private theorem termination_sd_touches_termination
    {F : Type} [Field F] (joltField : JoltField F)
    (joltInstance : JoltInstance SourceInstruction)
    {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params)
    (context : ConstraintContext joltInstance privateInputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam
      context.io context.entry witness)
    (run : UntrustedAnswerRun joltInstance privateInputs)
    (represented : JoltInstance.RepresentsRows witness run.toTrace)
    (address : Fin params.ramSize)
    (atTermination : address.val =
      (context.io.memory_layout.termination.toNat -
        ramLowestAddress context.io.memory_layout) / 8)
    (cycle : Fin params.traceLength) (inRun : cycle.val < run.rows.size)
    (selectedRam : witness.RamRa address cycle = 1)
    (base value : Src) (imm : BitVec 64)
    (instructionAt : run.bytecode[run.rows[cycle.val].rowIndex].instruction =
      .SD base value imm) :
    TouchesTermination run.rows[cycle.val].preState.jolt_device
      (sourceValue base run.rows[cycle.val].preState + imm) := by
  let i : Fin run.rows.size := ⟨cycle.val, inRun⟩
  have charAbove := two_pow_127_lt_char joltField
  let raw := sourceValue base run.rows[i].preState + imm
  have encoded : witness.RamAddress cycle = (raw.toNat : F) := by
    rw [represented.ramAddress cycle inRun]
    unfold TraceWitness.RamAddress
    simp only [dif_pos inRun]
    change (match TraceWitness.ramAccessAddress
      run.bytecode[run.rows[i].rowIndex].instruction run.rows[i].preState with
      | some address => (address.toNat : F)
      | none => 0) = (raw.toNat : F)
    have atI : run.bytecode[run.rows[i].rowIndex].instruction = .SD base value imm :=
      instructionAt
    rw [atI]
    rfl
  have rawAddress := ramAddress_eq_of_selected charAbove context equations
    cycle address selectedRam raw encoded
  have built := context_layout_built context
  have absolute := termination_word_absolute _ context.io.memory_layout built
  have rawTermination : raw.toNat = context.io.memory_layout.termination.toNat := by
    rw [atTermination] at rawAddress
    exact rawAddress.trans absolute
  have initialLayout :=
    (initial_state_device joltInstance privateInputs run.initialState run.initialized).1
  have contextLayout : joltInstance.memory_layout = some context.io.memory_layout := built
  have sameInitialLayout : run.initialState.jolt_device.memory_layout =
      context.io.memory_layout :=
    Option.some.inj (initialLayout.symm.trans contextLayout)
  have rowLayout : run.rows[i].preState.jolt_device.memory_layout =
      context.io.memory_layout :=
    (run.preState_layout i).trans sameInitialLayout
  obtain ⟨_, _, _, ioEnd, _⟩ := new_io_geometry _ context.io.memory_layout built
  change TouchesTermination run.rows[i].preState.jolt_device raw
  refine ⟨0, by omega, ?_⟩
  simp only [JoltDevice.is_termination, Bool.and_eq_true, decide_eq_true_eq]
  rw [rowLayout, rawTermination, ioEnd]
  omega

/-- A nonzero write to the selected termination word is an executed SD touching
that word. For example, the SDK's termination store reaches the device region. -/
private theorem termination_effect_store_row
    {F : Type} [Field F] (joltField : JoltField F)
    (joltInstance : JoltInstance SourceInstruction)
    {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params)
    (context : ConstraintContext joltInstance privateInputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam
      context.io context.entry witness)
    (run : UntrustedAnswerRun joltInstance privateInputs)
    (bytecodeEq : run.bytecode = context.bytecode)
    (represented : JoltInstance.RepresentsPrefix witness run.toTrace)
    (address : Fin params.ramSize)
    (atTermination : address.val =
      (context.io.memory_layout.termination.toNat -
        ramLowestAddress context.io.memory_layout) / 8)
    (cycle : Fin params.traceLength) (inRun : cycle.val < run.rows.size)
    (effect : witness.RamRa address cycle * witness.RamInc cycle ≠ 0) :
    run.StoresTerminationAt ⟨cycle.val, inRun⟩ := by
  obtain ⟨base, value, imm, instructionAt⟩ :=
    termination_effect_is_sd joltField joltInstance privateInputs witness
      context equations run bytecodeEq represented.toRepresentsRows
      address cycle inRun effect
  have selectedRam : witness.RamRa address cycle = 1 := by
    rcases ramRa_zero_or_one context equations address cycle with zero | one
    · exact False.elim (effect (by simp [zero]))
    · exact one
  let i : Fin run.rows.size := ⟨cycle.val, inRun⟩
  change run.StoresTerminationAt i
  unfold UntrustedAnswerRun.StoresTerminationAt
  have atI : run.bytecode[run.rows[i].rowIndex].instruction =
      .SD base value imm := instructionAt
  rw [atI]
  exact termination_sd_touches_termination joltField joltInstance privateInputs witness
    context equations run represented.toRepresentsRows address atTermination cycle
    inRun selectedRam base value imm instructionAt

end JoltConstraints.Soundness

namespace JoltInstance

open JoltConstraints.Soundness

/-- A no-panic claim forces a completed SD to touch the termination word in
the retained run. For example, storing 1 to the SDK exit word supplies this row.
The final public word is set in
jolt/crates/jolt-program/src/preprocess/public_io.rs:47-52 at 8bbb2357;
the store is emitted in jolt/jolt-sdk/macros/src/lib.rs:880-887. -/
theorem soundness_termination_store_exists
    {F : Type} [Field F] (joltField : JoltField F)
    (joltInstance : JoltInstance SourceInstruction)
    (assumptions : joltInstance.SoundnessAssumptions)
    (restrictions : joltInstance.TemporaryRestrictions)
    {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (equations : JoltConstraints.ConstraintEquations context.bytecode context.initialRam
      context.io context.entry witness)
    (run : JoltConstraints.Soundness.UntrustedAnswerRun joltInstance privateInputs)
    (bytecodeEq : run.bytecode = context.bytecode)
    (represented : RepresentsPrefix witness run.toTrace)
    (realRows : ∀ cycle : Fin params.traceLength,
      cycle.val < run.rows.size → witness.InstructionFlags .IsNoop cycle = 0)
    (cut : run.rows.size = params.traceLength ∨
      ∃ bound : run.rows.size < params.traceLength,
        witness.InstructionFlags .IsNoop ⟨run.rows.size, bound⟩ = 1 ∨
        ∃ last ∈ run.rows.back?, last.StableStall) :
    ∃ i : Fin run.rows.size, run.StoresTerminationAt i := by
  obtain ⟨address, cycle, atTermination, effect⟩ :=
    termination_effect_exists joltInstance restrictions privateInputs witness
      context equations
  have inRun := termination_effect_in_run joltField joltInstance assumptions
    privateInputs witness context equations run bytecodeEq represented cut
    address cycle effect
  exact ⟨⟨cycle.val, inRun⟩,
    termination_effect_store_row joltField joltInstance privateInputs witness
      context equations run bytecodeEq represented address atTermination
      cycle inRun effect⟩

/-- A truncated run keeps the original honest runtime advice on every retained
row. For example, cutting after row 3 leaves row 2's advice unchanged. -/
private theorem truncate_honest_runtime_advice
    (joltInstance : JoltInstance SourceInstruction)
    (privateInputs : JoltPrivateInputs)
    (run : JoltConstraints.Soundness.UntrustedAnswerRun joltInstance privateInputs)
    (advice : ∀ n : Fin run.rows.size,
      run.rows[n].someTracerAdvice? =
        honestTracerAdviceAtStepN joltInstance.program run.rows n)
    (i : Fin run.rows.size) :
    ∀ m : Fin (run.truncate i.val (Nat.le_of_lt i.isLt)).rows.size,
      (run.truncate i.val (Nat.le_of_lt i.isLt)).rows[m].someTracerAdvice? =
        honestTracerAdviceAtStepN joltInstance.program
          (run.truncate i.val (Nat.le_of_lt i.isLt)).rows m := by
  intro m
  have hm : m.val < i.val := by
    have hs := run.truncate_rows_size i.val (Nat.le_of_lt i.isLt)
    have hlt : m.val < (run.rows.extract 0 i.val).size := m.isLt
    omega
  have hm' : m.val < run.rows.size := by omega
  have hrow : (run.truncate i.val (Nat.le_of_lt i.isLt)).rows[m] =
      run.rows[m.val]'hm' := by
    change (run.rows.extract 0 i.val)[m.val]'m.isLt = run.rows[m.val]'hm'
    simp only [Array.getElem_extract, Nat.zero_add]
  have hadvice := advice ⟨m.val, hm'⟩
  have hextract := honestTracerAdviceAtStepN_extract joltInstance.program
    run.rows i.val m.val (Nat.le_of_lt i.isLt) hm
  change (run.truncate i.val (Nat.le_of_lt i.isLt)).rows[m].someTracerAdvice? =
    honestTracerAdviceAtStepN joltInstance.program
      (run.truncate i.val (Nat.le_of_lt i.isLt)).rows m.val
  rw [hrow]
  exact hadvice.trans hextract.symm

/-- Truncation preserves the certificate that no retained row before another
retained row is a stable stall. For example, rows 1 and 2 keep that property. -/
private theorem truncate_no_earlier_stall
    (joltInstance : JoltInstance SourceInstruction)
    (privateInputs : JoltPrivateInputs)
    (run : JoltConstraints.Soundness.UntrustedAnswerRun joltInstance privateInputs)
    (noEarlierStop : ∀ (n : Nat) (current next : TraceRow run.bytecode),
      run.rows[n]? = some current → run.rows[n + 1]? = some next →
      ¬ current.StableStall)
    (i : Fin run.rows.size) :
    ∀ (n : Nat) (current following : TraceRow run.bytecode),
      (run.truncate i.val (Nat.le_of_lt i.isLt)).rows[n]? = some current →
      (run.truncate i.val (Nat.le_of_lt i.isLt)).rows[n + 1]? = some following →
      ¬ current.StableStall := by
  intro n current following hcurrent hfollowing
  change (run.rows.extract 0 i.val)[n]? = some current at hcurrent
  change (run.rows.extract 0 i.val)[n + 1]? = some following at hfollowing
  have hn : n < i.val := by
    have h := (Array.getElem?_eq_some_iff.mp hcurrent).1
    rw [run.truncate_rows_size i.val (Nat.le_of_lt i.isLt)] at h
    exact h
  have hnext : n + 1 < i.val := by
    have h := (Array.getElem?_eq_some_iff.mp hfollowing).1
    rw [run.truncate_rows_size i.val (Nat.le_of_lt i.isLt)] at h
    exact h
  have hcurrent' : run.rows[n]? = some current := by
    simpa only [extract_getElem?_before run.rows i.val n (Nat.le_of_lt i.isLt) hn]
      using hcurrent
  have hfollowing' : run.rows[n + 1]? = some following := by
    simpa only [extract_getElem?_before run.rows i.val (n + 1)
      (Nat.le_of_lt i.isLt) hnext] using hfollowing
  exact noEarlierStop n current following hcurrent' hfollowing'

/-- Truncating a run before its existing row `i` produces an initialized
prefix ready to execute that row, with honest advice and no earlier stall.
For example, truncating before row 4 leaves rows 0 through 3.
See jolt/tracer/src/emulator/cpu.rs:622-632 at 8bbb2357 and
PR #2109 head d2995380, jolt/tracer/src/emulator/cpu.rs:553-578. -/
theorem soundness_prefix_next_step
    (joltInstance : JoltInstance SourceInstruction)
    (privateInputs : JoltPrivateInputs)
    (run : JoltConstraints.Soundness.UntrustedAnswerRun joltInstance privateInputs)
    (noEarlierStop : ∀ (n : Nat) (current next : TraceRow run.bytecode),
      run.rows[n]? = some current → run.rows[n + 1]? = some next →
      ¬ current.StableStall)
    (advice : ∀ n : Fin run.rows.size,
      run.rows[n].someTracerAdvice? =
        honestTracerAdviceAtStepN joltInstance.program run.rows n)
    (i : Fin run.rows.size) :
    (run.truncate i.val (Nat.le_of_lt i.isLt)).NextStep
      run.rows[i].rowIndex run.rows[i].preState := by
  let cutRun := run.truncate i.val (Nat.le_of_lt i.isLt)
  change cutRun.NextStep run.rows[i].rowIndex run.rows[i].preState
  constructor
  · exact truncate_honest_runtime_advice joltInstance privateInputs run advice i
  · exact truncate_no_earlier_stall joltInstance privateInputs run noEarlierStop i
  · have hrowAt : run.rows[i.val]? = some run.rows[i] := by
      exact Array.getElem?_eq_getElem i.isLt
    by_cases iz : i.val = 0
    · have hEmpty : cutRun.rows.back? = none := by
        change (run.rows.extract 0 i.val).back? = none
        simp [iz]
      have hfirst : run.rows[0]? = some run.rows[i] := by simpa [iz] using hrowAt
      have start := run.starts run.rows[i] hfirst
      rw [hEmpty]
      exact start
    · let j := i.val - 1
      have hj : j < i.val := by dsimp [j]; omega
      have hji : j + 1 = i.val := by dsimp [j]; omega
      have hjRun : j < run.rows.size := by omega
      let prev := run.rows[j]'hjRun
      have hprev : run.rows[j]? = some prev := by
        exact Array.getElem?_eq_getElem hjRun
      have hBack : cutRun.rows.back? = some prev := by
        change (run.rows.extract 0 i.val).back? = some prev
        rw [Array.back?_eq_getElem?, run.truncate_rows_size i.val (Nat.le_of_lt i.isLt)]
        change (run.rows.extract 0 i.val)[j]? = some prev
        rw [extract_getElem?_before run.rows i.val j (Nat.le_of_lt i.isLt) hj]
        exact hprev
      have hnext : run.rows[j + 1]? = some run.rows[i] := by
        simpa only [hji] using hrowAt
      have link := run.linked j prev run.rows[i] hprev hnext
      have nostall := noEarlierStop j prev run.rows[i] hprev hnext
      rw [hBack]
      change (if run.bytecode[prev.rowIndex].virtual_sequence_remaining.getD 0 ≠ 0 then
        run.rows[i].rowIndex.val = prev.rowIndex.val + 1 ∧
          run.rows[i].preState = prev.postState
        else ∃ address, prev.postState.sail.regs.get? Register.nextPC = some address ∧
          ¬ prev.StableStall ∧ run.bytecode[run.rows[i].rowIndex].address = address ∧
          run.bytecode[run.rows[i].rowIndex].starts_source ∧
          run.rows[i].preState = advance_pc address
            (source_is_compressed run.bytecode run.rows[i].rowIndex) prev.postState)
      split at link
      · split
        · exact link
        · simp_all
      · obtain ⟨address, pc, addr, starts, state⟩ := link
        split
        · simp_all
        · exact ⟨address, pc, nostall, addr, starts, state⟩

/-- A termination store occurs before a final row that is a JAL or JALR.
For example, the SDK exit store precedes its final `j .` row.
See jolt/jolt-sdk/macros/src/lib.rs:880-887 at 8bbb2357. -/
private theorem store_precedes_last_jump
    {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs}
    (run : JoltConstraints.Soundness.UntrustedAnswerRun joltInstance privateInputs)
    (i : Fin run.rows.size) (stored : run.StoresTerminationAt i)
    (last : TraceRow run.bytecode) (hlast : last ∈ run.rows.back?)
    (lastKind : (∃ dst imm, run.bytecode[last.rowIndex].instruction = .JAL dst imm) ∨
      ∃ dst base imm, run.bytecode[last.rowIndex].instruction = .JALR dst base imm) :
    i.val < run.rows.size - 1 := by
  obtain ⟨earlier, hrows⟩ := Array.back?_eq_some_iff.mp hlast
  have hsize : 0 < run.rows.size := by rw [hrows]; simp
  by_contra h
  have hi : i.val = run.rows.size - 1 := by omega
  have hget : run.rows[i.val]? = some run.rows[i] := Array.getElem?_eq_getElem i.isLt
  have hgetAt : run.rows[run.rows.size - 1]? = some run.rows[i] := by
    simpa only [hi] using hget
  have hlastAt : run.rows[run.rows.size - 1]? = some last := by
    simpa only [Array.back?_eq_getElem?] using hlast
  have hrow : run.rows[i] = last := Option.some.inj (hgetAt.symm.trans hlastAt)
  have hInstr := congrArg
    (fun row : TraceRow run.bytecode => run.bytecode[row.rowIndex].instruction) hrow
  change run.bytecode[run.rows[i].rowIndex].instruction =
    run.bytecode[last.rowIndex].instruction at hInstr
  have hStore : ∃ base value imm, run.bytecode[run.rows[i].rowIndex].instruction =
      .SD base value imm := by
    unfold JoltConstraints.Soundness.UntrustedAnswerRun.StoresTerminationAt at stored
    split at stored
    · rename_i base value imm heq
      exact ⟨base, value, imm, heq⟩
    · contradiction
  rcases hStore with ⟨base, value, imm, hStore⟩
  rcases lastKind with ⟨dst, off, hJump⟩ | ⟨dst, src, off, hJump⟩
  · rw [hStore, hJump] at hInstr
    cases hInstr
  · rw [hStore, hJump] at hInstr
    cases hInstr

/-- Once a completed termination store precedes the final jump, the temporary
exit restriction makes that jump `JAL +0`, and execution makes it a stable stall.
For example, the SDK's `j .` after its exit store is the final row.
See jolt/jolt-sdk/macros/src/lib.rs:880-887 at 8bbb2357 and
PR #2109 head d2995380, jolt/crates/jolt-riscv/src/row.rs:105-132. -/
theorem soundness_termination_last_stall
    (joltInstance : JoltInstance SourceInstruction)
    (restricted : joltInstance.TerminationThenStall)
    (privateInputs : JoltPrivateInputs)
    (run : JoltConstraints.Soundness.UntrustedAnswerRun joltInstance privateInputs)
    (stored : ∃ i : Fin run.rows.size, run.StoresTerminationAt i)
    (noEarlierStop : ∀ (n : Nat) (current next : TraceRow run.bytecode),
      run.rows[n]? = some current → run.rows[n + 1]? = some next →
      ¬ current.StableStall)
    (advice : ∀ n : Fin run.rows.size,
      run.rows[n].someTracerAdvice? =
        honestTracerAdviceAtStepN joltInstance.program run.rows n)
    (lastJump : ∀ last ∈ run.rows.back?,
      run.bytecode[last.rowIndex].virtual_sequence_remaining.getD 0 = 0 ∧
      ((∃ dst imm, run.bytecode[last.rowIndex].instruction = .JAL dst imm) ∨
        ∃ dst base imm, run.bytecode[last.rowIndex].instruction = .JALR dst base imm)) :
    ∀ last ∈ run.rows.back?, last.StableStall := by
  intro last hlast
  obtain ⟨storeIndex, storedAt⟩ := stored
  obtain ⟨earlier, hrows⟩ := Array.back?_eq_some_iff.mp hlast
  have hsize : 0 < run.rows.size := by rw [hrows]; simp
  let lastIndex : Fin run.rows.size := ⟨run.rows.size - 1, by omega⟩
  have hlastAt : run.rows[lastIndex] = last := by
    have hget : run.rows[lastIndex.val]? = some run.rows[lastIndex] :=
      Array.getElem?_eq_getElem lastIndex.isLt
    have hback : run.rows[lastIndex.val]? = some last := by
      simpa only [Array.back?_eq_getElem?] using hlast
    exact Option.some.inj (hget.symm.trans hback)
  subst last
  have lastFacts := lastJump run.rows[lastIndex] hlast
  have before := store_precedes_last_jump run storeIndex storedAt
    run.rows[lastIndex] hlast lastFacts.2
  let cutRun := run.truncate lastIndex.val (Nat.le_of_lt lastIndex.isLt)
  have storedCut : ∃ j : Fin cutRun.rows.size, cutRun.StoresTerminationAt j := by
    exact ⟨⟨storeIndex.val, by
      change storeIndex.val < (run.rows.extract 0 lastIndex.val).size
      rw [run.truncate_rows_size lastIndex.val (Nat.le_of_lt lastIndex.isLt)]
      exact before⟩,
      run.truncate_storesTerminationAt lastIndex.val (Nat.le_of_lt lastIndex.isLt)
        storeIndex before storedAt⟩
  have ready := soundness_prefix_next_step joltInstance privateInputs run
    noEarlierStop advice lastIndex
  have pc := untrusted_row_pc joltInstance privateInputs run lastIndex
  have nextPC := untrusted_row_next_pc joltInstance privateInputs run lastIndex
  rcases lastFacts.2 with ⟨dst, imm, instr⟩ | ⟨dst, base, imm, instr⟩
  · have zero := termination_next_jal_zero restricted cutRun
      run.rows[lastIndex].rowIndex run.rows[lastIndex].preState ready storedCut dst imm instr
    have runs : JoltISA.execInstr (.JAL dst imm) run.rows[lastIndex].preState =
        .ok RETIRE_SUCCESS run.rows[lastIndex].postState := by
      have h := run.executes lastIndex
      have absent : run.bytecode[run.rows[lastIndex].rowIndex].instruction.adviceValue? =
          none := by rw [instr]; rfl
      rw [withRuntimeAdvice_eq_of_noAdvice _ _ absent, instr] at h
      exact h
    have stalled := termination_next_jal_stalls restricted cutRun
      run.rows[lastIndex].rowIndex run.rows[lastIndex].preState
      run.rows[lastIndex].postState ready storedCut dst imm
      run.bytecode[run.rows[lastIndex].rowIndex].address
      (run.bytecode[run.rows[lastIndex].rowIndex].address +
        if source_is_compressed run.bytecode run.rows[lastIndex].rowIndex then 2 else 4)
      instr pc nextPC runs
    have repeats : (run.bytecode[run.rows[lastIndex].rowIndex]).selfJumpRepeats = true := by
      unfold JoltInstructionRow.selfJumpRepeats
      rw [instr]
    exact ⟨lastFacts.1, stalled, repeats⟩
  · exact False.elim (termination_next_no_jalr restricted cutRun
      run.rows[lastIndex].rowIndex run.rows[lastIndex].preState ready storedCut
      dst base imm instr)

end JoltInstance
