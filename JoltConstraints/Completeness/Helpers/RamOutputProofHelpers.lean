import JoltConstraints.Constraints.RamOutputEqPublicIo
import JoltConstraints.Completeness.Helpers.IOSetupFrame
import JoltConstraints.Constraints.MemoryLayout

set_option autoImplicit false

namespace JoltConstraints

open scoped BigOperators

/-- An overlay whose bytes end at or below `input_start` leaves every word from
the input's first remapped word onward unchanged. The overlay start need not be
aligned: remapping rounds it down, which only moves the bytes lower. -/
theorem overlayRamBytes_below_input (layout : MemoryLayout)
    (start : BitVec 64) (bytes : Array (BitVec 8))
    (inputWordAligned : (layout.input_start.toNat - ramLowestAddress layout) % 8 = 0)
    (fits : start.toNat + bytes.size ≤ layout.input_start.toNat)
    (address : Nat)
    (above : (layout.input_start.toNat - ramLowestAddress layout) / 8 ≤ address)
    (previous : BitVec 64) :
    TraceWitness.overlayRamBytes layout start bytes address previous = previous := by
  unfold ramLowestAddress at inputWordAligned above
  unfold TraceWitness.overlayRamBytes TraceWitness.remapRamAddress
  dsimp only
  by_cases hnone : start.toNat = 0 ∨
      start.toNat < min layout.trusted_advice_start.toNat layout.untrusted_advice_start.toNat
  · rw [if_pos hnone]
  · rw [if_neg hnone]
    dsimp only
    rw [if_neg]
    omega

/-- On the public I/O interval, the final RAM word is the public I/O word.
Below `RAM_START_ADDRESS` the RAM image is zero, and both advice overlays end
before the input's first word, so only the public overlays remain. -/
theorem finalRamWord_eq_ramPublicIoWord (trace : Trace)
    (frame : JoltIOSetupFrame.Same trace.initialState.jolt_device
      (TraceWitness.finalTraceState trace).jolt_device)
    (adviceBelowInput : trace.initialState.jolt_device.AdviceBelowInput)
    (address : Nat)
    (lower : (trace.initialState.jolt_device.memory_layout.input_start.toNat -
      ramLowestAddress trace.initialState.jolt_device.memory_layout) / 8 ≤ address)
    (upper : address <
      (JoltISA.RAM_START_ADDRESS - ramLowestAddress trace.initialState.jolt_device.memory_layout) / 8) :
    TraceWitness.finalRamWord trace address =
      ramPublicIoWord (TraceWitness.finalTraceState trace).jolt_device address := by
  obtain ⟨hlayout, htrusted, huntrusted, _⟩ := frame
  have hram : ¬ JoltISA.RAM_START_ADDRESS ≤
      min trace.initialState.jolt_device.memory_layout.trusted_advice_start.toNat
        trace.initialState.jolt_device.memory_layout.untrusted_advice_start.toNat + 8 * address := by
    unfold ramLowestAddress at upper
    omega
  have htrustedOverlay := overlayRamBytes_below_input _
    trace.initialState.jolt_device.memory_layout.trusted_advice_start
      trace.initialState.jolt_device.trusted_advice
    adviceBelowInput.inputWordAligned adviceBelowInput.trustedAdviceBelowInput address lower
  have huntrustedOverlay := overlayRamBytes_below_input _
    trace.initialState.jolt_device.memory_layout.untrusted_advice_start
      trace.initialState.jolt_device.untrusted_advice
    adviceBelowInput.inputWordAligned adviceBelowInput.untrustedAdviceBelowInput address lower
  unfold TraceWitness.finalRamWord ramPublicIoWord
  dsimp only
  rw [hlayout, htrusted, huntrusted, if_neg hram, htrustedOverlay, huntrustedOverlay]

-- Trimming keeps the bytes before the trailing zeros: each kept byte is the byte at the
-- same place, and every byte after the kept ones is 0.
theorem trimTrailingZeros_spec (bytes : Array (BitVec 8)) :
    (trimTrailingZeros bytes).size ≤ bytes.size ∧
    (∀ i < (trimTrailingZeros bytes).size, bytes[i]? = (trimTrailingZeros bytes)[i]?) ∧
    (∀ i, (trimTrailingZeros bytes).size ≤ i → i < bytes.size → bytes[i]? = some 0) := by
  -- the bytes are the kept ones followed by the dropped zeros
  have split := List.takeWhile_append_dropWhile (p := (· == (0 : BitVec 8))) (l := bytes.toList.reverse)
  have whole : bytes.toList = (bytes.toList.reverse.dropWhile (· == 0)).reverse ++
      (bytes.toList.reverse.takeWhile (· == 0)).reverse := by
    rw [← List.reverse_append, split, List.reverse_reverse]
  have zeros : ∀ byte ∈ (bytes.toList.reverse.takeWhile (· == 0)).reverse, byte = 0 := by
    intro byte member
    rw [List.mem_reverse] at member
    simpa using List.mem_takeWhile_imp member
  have keptSize : (trimTrailingZeros bytes).size =
      (bytes.toList.reverse.dropWhile (· == 0)).reverse.length := by
    simp [trimTrailingZeros]
  have totalSize : bytes.size = (bytes.toList.reverse.dropWhile (· == 0)).reverse.length +
      (bytes.toList.reverse.takeWhile (· == 0)).reverse.length := by
    rw [← List.length_append, ← whole, Array.length_toList]
  refine ⟨by omega, ?_, ?_⟩
  · -- a kept byte
    intro i kept
    rw [← Array.getElem?_toList, whole, List.getElem?_append_left (by omega)]
    simp [trimTrailingZeros]
  · -- a dropped byte
    intro i notKept inBytes
    rw [← Array.getElem?_toList, whole, List.getElem?_append_right (by omega)]
    have inZeros : i - (bytes.toList.reverse.dropWhile (· == 0)).reverse.length <
        (bytes.toList.reverse.takeWhile (· == 0)).reverse.length := by omega
    rw [List.getElem?_eq_getElem inZeros]
    exact congrArg some (zeros _ (List.getElem_mem inZeros))

/-- Appending zero bytes does not change the trimmed output. -/
private theorem trimTrailingZeros_append_zeros (bytes : Array (BitVec 8)) (n : Nat) :
    trimTrailingZeros (bytes ++ Array.replicate n 0) = trimTrailingZeros bytes := by
  simp [trimTrailingZeros, Array.toList_append, List.reverse_append]

/-- Equal zero-padded bytes up to `limit` determine equal trimmed arrays. -/
theorem trimTrailingZeros_of_padded_eq (a b : Array (BitVec 8)) (limit : Nat)
    (ha : a.size ≤ limit) (hb : b.size ≤ limit)
    (same : ∀ i < limit, a[i]?.getD 0 = b[i]?.getD 0) :
    trimTrailingZeros a = trimTrailingZeros b := by
  have padRead (x : Array (BitVec 8)) (hx : x.size ≤ limit) (i : Nat)
      (hi : i < limit) :
      (x ++ Array.replicate (limit - x.size) 0)[i]?.getD 0 = x[i]?.getD 0 := by
    rw [Array.getElem?_append]
    split_ifs with within
    · rfl
    · rw [Array.getElem?_replicate, if_pos (by omega), Array.getElem?_eq_none (by omega)]
      rfl
  have padEq : a ++ Array.replicate (limit - a.size) 0 =
      b ++ Array.replicate (limit - b.size) 0 := by
    apply Array.ext
    · simp only [Array.size_append, Array.size_replicate]
      omega
    · intro i hiA hiB
      have hi : i < limit := by
        simp only [Array.size_append, Array.size_replicate] at hiA
        omega
      have haRead := padRead a ha i hi
      have hbRead := padRead b hb i hi
      rw [Array.getElem?_eq_getElem hiA] at haRead
      rw [Array.getElem?_eq_getElem hiB] at hbRead
      have := (haRead.trans (same i hi)).trans hbRead.symm
      simpa using this
  rw [← trimTrailingZeros_append_zeros a (limit - a.size),
    ← trimTrailingZeros_append_zeros b (limit - b.size), padEq]

/-- Trimming trailing zero output bytes twice has the same result as trimming once. -/
theorem trimTrailingZeros_idempotent (bytes : Array (BitVec 8)) :
    trimTrailingZeros (trimTrailingZeros bytes) = trimTrailingZeros bytes := by
  simp [trimTrailingZeros, List.dropWhile_idempotent]

-- Eight zero bytes make the zero word.
theorem ramImageWord_zero (byte : Nat → BitVec 8) (start : Nat)
    (allZero : ∀ offset < 8, byte (start + offset) = 0) :
    TraceWitness.ramImageWord byte start = 0 := by
  unfold TraceWitness.ramImageWord
  rw [allZero 7 (by decide), allZero 6 (by decide), allZero 5 (by decide),
    allZero 4 (by decide), allZero 3 (by decide), allZero 2 (by decide),
    allZero 1 (by decide)]
  have first := allZero 0 (by decide)
  rw [Nat.add_zero] at first
  rw [first]
  rfl

-- Overlaying bytes followed by zero bytes gives the same word as overlaying the bytes
-- alone, when the word underneath is 0 wherever the zero bytes could reach.
theorem overlayRamBytes_trailing_zeros (layout : MemoryLayout) (start : BitVec 64)
    (bytes trimmed : Array (BitVec 8)) (address : Nat) (previous : BitVec 64)
    (shorter : trimmed.size ≤ bytes.size)
    (prefixSame : ∀ i < trimmed.size, bytes[i]? = trimmed[i]?)
    (zerosAfter : ∀ i, trimmed.size ≤ i → i < bytes.size → bytes[i]? = some 0)
    (previousZero : ∀ firstWord, TraceWitness.remapRamAddress layout start = some firstWord →
      firstWord ≤ address → previous = 0) :
    TraceWitness.overlayRamBytes layout start trimmed address previous =
      TraceWitness.overlayRamBytes layout start bytes address previous := by
  -- both arrays read the same byte everywhere, missing bytes as 0
  have sameBytes : (fun i : Nat => trimmed[i]?.getD 0) = (fun i : Nat => bytes[i]?.getD 0) := by
    funext i
    by_cases kept : i < trimmed.size
    · rw [prefixSame i kept]
    · by_cases inBytes : i < bytes.size
      · rw [zerosAfter i (by omega) inBytes, Array.getElem?_eq_none (by omega)]
        rfl
      · rw [Array.getElem?_eq_none (by omega), Array.getElem?_eq_none (by omega)]
  unfold TraceWitness.overlayRamBytes
  split
  · rfl
  · rename_i firstWord remapped
    by_cases inTrimmed : firstWord ≤ address ∧ (address - firstWord) * 8 < trimmed.size
    · -- inside the kept bytes, both read the same bytes
      rw [if_pos inTrimmed, if_pos ⟨inTrimmed.1, by omega⟩, sameBytes]
    · rw [if_neg inTrimmed]
      by_cases inBytes : firstWord ≤ address ∧ (address - firstWord) * 8 < bytes.size
      · -- past the kept bytes, the word underneath and the zero bytes are both 0
        rw [if_pos inBytes, previousZero firstWord remapped inBytes.1, ← sameBytes]
        symm
        apply ramImageWord_zero
        intro offset _
        have past : trimmed.size ≤ (address - firstWord) * 8 + offset := by omega
        rw [Array.getElem?_eq_none past]
        rfl
      · rw [if_neg inBytes]

/-- `q` counts words from the output start; word `q` holds output bytes `8*q`
through `8*q+7`, with missing bytes read as zero.
When the configured output region has at least two words, a three-byte output
occupies the low three bytes of word zero and leaves word one zero. -/
theorem ramPublicIoWord_output (config : MemoryConfig) (layout : MemoryLayout)
    (built : MemoryLayout.new config = some layout)
    (io : JoltDevice) (sameLayout : io.memory_layout = layout)
    (inputsFit : io.inputs.size ≤ layout.max_input_size.toNat)
    (q : Nat) (inOutput : q < layout.max_output_size.toNat / 8) :
    ramPublicIoWord io ((layout.output_start.toNat - ramLowestAddress layout) / 8 + q) =
      TraceWitness.ramImageWord (fun i => io.outputs[i]?.getD 0) (8 * q) := by
  obtain ⟨lowLeInput, _, _, _, _⟩ := new_io_ordered config layout built
  rw [MemoryLayout.get_lowest_address_toNat] at lowLeInput
  obtain ⟨outputAfterInput, inputMultiple⟩ := new_outputs_after_inputs config layout built
  obtain ⟨panicAfterOutput, outputMultiple, terminationAfterPanic, _, _⟩ :=
    new_io_geometry config layout built
  have inputWordAligned := new_input_word_aligned config layout built
  rw [MemoryLayout.get_lowest_address_toNat] at inputWordAligned
  let low := ramLowestAddress layout
  change (layout.input_start.toNat - low) % 8 = 0 at inputWordAligned
  let inputFirst := (layout.input_start.toNat - low) / 8
  let outputFirst := (layout.output_start.toNat - low) / 8
  let panicFirst := (layout.panic.toNat - low) / 8
  let terminationFirst := (layout.termination.toNat - low) / 8
  change ramPublicIoWord io (outputFirst + q) =
    TraceWitness.ramImageWord (fun i => io.outputs[i]?.getD 0) (8 * q)
  have outputWordAligned : (layout.output_start.toNat - low) % 8 = 0 := by
    have outputSub : layout.output_start.toNat - low =
        (layout.input_start.toNat - low) + layout.max_input_size.toNat := by
      dsimp only [low, ramLowestAddress] at *
      omega
    rw [outputSub]
    omega
  have panicWordAligned : (layout.panic.toNat - low) % 8 = 0 := by
    have panicSub : layout.panic.toNat - low =
        (layout.output_start.toNat - low) + layout.max_output_size.toNat := by
      dsimp only [low, ramLowestAddress] at *
      omega
    rw [panicSub]
    omega
  have outputIndex : low + 8 * outputFirst = layout.output_start.toNat := by
    dsimp only [outputFirst, low, ramLowestAddress] at *
    omega
  have inputBeforeOutput : inputFirst + layout.max_input_size.toNat / 8 =
      outputFirst := by
    dsimp only [inputFirst, outputFirst, low, ramLowestAddress] at *
    omega
  have outputBeforePanic : outputFirst + layout.max_output_size.toNat / 8 =
      panicFirst := by
    dsimp only [outputFirst, panicFirst, low, ramLowestAddress] at *
    omega
  have terminationAfter : terminationFirst = panicFirst + 1 := by
    dsimp only [terminationFirst, panicFirst, low, ramLowestAddress] at *
    omega
  have lowPos := new_lowest_address_pos config layout built
  rw [MemoryLayout.get_lowest_address_toNat] at lowPos
  have remapInput : TraceWitness.remapRamAddress layout layout.input_start =
      some inputFirst := by
    unfold TraceWitness.remapRamAddress
    rw [if_neg (by dsimp only [low, ramLowestAddress] at *; omega)]
    rfl
  have remapOutput : TraceWitness.remapRamAddress layout layout.output_start =
      some outputFirst := by
    unfold TraceWitness.remapRamAddress
    rw [if_neg (by dsimp only [low, ramLowestAddress] at *; omega)]
    rfl
  have remapPanic : TraceWitness.remapRamAddress layout layout.panic =
      some panicFirst := by
    unfold TraceWitness.remapRamAddress
    rw [if_neg (by dsimp only [low, ramLowestAddress] at *; omega)]
    rfl
  have remapTermination : TraceWitness.remapRamAddress layout layout.termination =
      some terminationFirst := by
    unfold TraceWitness.remapRamAddress
    rw [if_neg (by dsimp only [low, ramLowestAddress] at *; omega)]
    rfl
  have inputZero : TraceWitness.overlayRamBytes layout layout.input_start
      io.inputs (outputFirst + q) 0 = 0 := by
    unfold TraceWitness.overlayRamBytes
    rw [remapInput]
    dsimp only
    have hInputNot : ¬ (inputFirst ≤ outputFirst + q ∧
        (outputFirst + q - inputFirst) * 8 < io.inputs.size) := by
      intro h
      have : (outputFirst + q - inputFirst) * 8 ≥ layout.max_input_size.toNat := by
        omega
      omega
    rw [if_neg hInputNot]
  have outputPacked : TraceWitness.overlayRamBytes layout layout.output_start
      io.outputs (outputFirst + q) 0 =
        TraceWitness.ramImageWord (fun i => io.outputs[i]?.getD 0) (8 * q) := by
    unfold TraceWitness.overlayRamBytes
    rw [remapOutput]
    dsimp only
    by_cases within : 8 * q < io.outputs.size
    · rw [if_pos (by omega)]
      congr 1
      omega
    · rw [if_neg (by omega)]
      symm
      apply ramImageWord_zero
      intro offset offsetLt
      rw [Array.getElem?_eq_none (by omega)]
      rfl
  have beforePanic : outputFirst + q < panicFirst := by omega
  have beforeTermination : outputFirst + q < terminationFirst := by omega
  unfold ramPublicIoWord
  rw [sameLayout, remapPanic, remapTermination]
  simp only [show (some terminationFirst == some (outputFirst + q)) = false by
    simp [Nat.ne_of_gt beforeTermination]]
  rw [inputZero, outputPacked]
  simp [show panicFirst ≠ outputFirst + q by omega]

/-- The word at the panic address encodes the device's panic flag as zero or one. -/
theorem ramPublicIoWord_panic (config : MemoryConfig) (layout : MemoryLayout)
    (built : MemoryLayout.new config = some layout)
    (io : JoltDevice) (sameLayout : io.memory_layout = layout) :
    ramPublicIoWord io ((layout.panic.toNat - ramLowestAddress layout) / 8) =
      if io.panic then 1 else 0 := by
  obtain ⟨lowLeInput, _, _, _, _⟩ := new_io_ordered config layout built
  rw [MemoryLayout.get_lowest_address_toNat] at lowLeInput
  obtain ⟨outputAfterInput, inputMultiple⟩ := new_outputs_after_inputs config layout built
  obtain ⟨panicAfterOutput, outputMultiple, terminationAfterPanic, _, _⟩ :=
    new_io_geometry config layout built
  have inputWordAligned := new_input_word_aligned config layout built
  rw [MemoryLayout.get_lowest_address_toNat] at inputWordAligned
  let low := ramLowestAddress layout
  change (layout.input_start.toNat - low) % 8 = 0 at inputWordAligned
  let panicFirst := (layout.panic.toNat - low) / 8
  let terminationFirst := (layout.termination.toNat - low) / 8
  change ramPublicIoWord io panicFirst = if io.panic then 1 else 0
  have panicWordAligned : (layout.panic.toNat - low) % 8 = 0 := by
    have outputSub : layout.output_start.toNat - low =
        (layout.input_start.toNat - low) + layout.max_input_size.toNat := by
      dsimp only [low, ramLowestAddress] at *
      omega
    have panicSub : layout.panic.toNat - low =
        (layout.output_start.toNat - low) + layout.max_output_size.toNat := by
      dsimp only [low, ramLowestAddress] at *
      omega
    rw [panicSub, outputSub]
    omega
  have terminationAfter : terminationFirst = panicFirst + 1 := by
    dsimp only [terminationFirst, panicFirst, low, ramLowestAddress] at *
    omega
  have lowPos := new_lowest_address_pos config layout built
  rw [MemoryLayout.get_lowest_address_toNat] at lowPos
  have remapPanic : TraceWitness.remapRamAddress layout layout.panic =
      some panicFirst := by
    unfold TraceWitness.remapRamAddress
    rw [if_neg (by dsimp only [low, ramLowestAddress] at *; omega)]
    rfl
  have remapTermination : TraceWitness.remapRamAddress layout layout.termination =
      some terminationFirst := by
    unfold TraceWitness.remapRamAddress
    rw [if_neg (by dsimp only [low, ramLowestAddress] at *; omega)]
    rfl
  unfold ramPublicIoWord
  rw [sameLayout, remapPanic, remapTermination]
  simp [show terminationFirst ≠ panicFirst by omega]

-- The verifier's public I/O word is the run's: they share the layout, inputs and panic
-- flag, and the verifier's outputs are the run's without their trailing zero bytes.
-- Past those bytes both read 0: the outputs start after the inputs' whole region.
theorem ramPublicIoWord_trimmed (io run : JoltDevice) (config : MemoryConfig)
    (built : MemoryLayout.new config = some run.memory_layout)
    (inputsFit : run.inputs.size ≤ run.memory_layout.max_input_size.toNat)
    (sameLayout : io.memory_layout = run.memory_layout)
    (sameInputs : io.inputs = run.inputs)
    (samePanic : io.panic = run.panic)
    (trimmedOutputs : io.outputs = trimTrailingZeros run.outputs)
    (address : Nat) :
    ramPublicIoWord io address = ramPublicIoWord run address := by
  obtain ⟨shorter, prefixSame, zerosAfter⟩ := trimTrailingZeros_spec run.outputs
  obtain ⟨outputsAfter, inputMultiple⟩ := new_outputs_after_inputs config run.memory_layout built
  have inputAligned := new_input_word_aligned config run.memory_layout built
  rw [MemoryLayout.get_lowest_address_toNat] at inputAligned
  unfold ramPublicIoWord
  rw [sameLayout, sameInputs, samePanic, trimmedOutputs]
  dsimp only
  rw [overlayRamBytes_trailing_zeros _ _ run.outputs _ _ _ shorter prefixSame zerosAfter ?_]
  -- the inputs' overlay is 0 from the outputs on: the inputs fit below them
  intro outputFirst outputRemapped above
  unfold TraceWitness.overlayRamBytes
  split
  · rfl
  · rename_i inputFirst inputRemapped
    rw [if_neg]
    rintro ⟨_, inInputs⟩
    unfold TraceWitness.remapRamAddress at outputRemapped inputRemapped
    dsimp only at outputRemapped inputRemapped
    split at outputRemapped
    · cases outputRemapped
    split at inputRemapped
    · cases inputRemapped
    cases outputRemapped
    cases inputRemapped
    omega

end JoltConstraints
