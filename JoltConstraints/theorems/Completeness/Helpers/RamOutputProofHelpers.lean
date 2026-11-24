import JoltConstraints.translation.Constraints.RamOutputEqPublicIo
import JoltConstraints.theorems.Completeness.Helpers.IOSetupFrame
import JoltConstraints.theorems.witness_domain
import JoltConstraints.theorems.SharedMemoryInitialization

open LeanRV64D

set_option autoImplicit false

namespace JoltConstraints

open scoped BigOperators

/-- Public bytes and halt claim extracted from an honest shared-memory run.
For example, an untouched output window supplies its full capacity of zero bytes. -/
noncomputable def _root_.HonestTrace.publicIo {inst : JoltInstance SourceInstruction}
    {inputs : JoltPrivateInputs} (trace : HonestTrace inst inputs) : JoltPublicIo :=
  let final := TraceWitness.finalTraceState trace
  { memory_layout := final.jolt_device.memory_layout
    inputs := inst.inputs
    outputs := final.jolt_device.outputsOf final.sail.mem
    panic := final.jolt_device.panic }

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
    · rw [Array.getElem?_replicate, ite_eq_left (by omega), Array.getElem?_eq_none (by omega)]
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
      rw [ite_eq_left inTrimmed, ite_eq_left ⟨inTrimmed.1, by omega⟩, sameBytes]
    · rw [ite_eq_right inTrimmed]
      by_cases inBytes : firstWord ≤ address ∧ (address - firstWord) * 8 < bytes.size
      · -- past the kept bytes, the word underneath and the zero bytes are both 0
        rw [ite_eq_left inBytes, previousZero firstWord remapped inBytes.1, ← sameBytes]
        symm
        apply ramImageWord_zero
        intro offset _
        have past : trimmed.size ≤ (address - firstWord) * 8 + offset := by omega
        rw [Array.getElem?_eq_none past]
        rfl
      · rw [ite_eq_right inBytes]

/-- An overlay starting at word `first` packs bytes `8*q` through `8*q+7`
at word `first + q`, with zero for missing bytes; for example, a short buffer
contributes zero at the next full word. -/
theorem overlayRamBytes_at_word (layout : MemoryLayout) (start : BitVec 64)
    (bytes : Array (BitVec 8)) (first q : Nat)
    (remapped : TraceWitness.remapRamAddress layout start = some first) :
    TraceWitness.overlayRamBytes layout start bytes (first + q) 0 =
      TraceWitness.ramImageWord (fun i => bytes[i]?.getD 0) (8 * q) := by
  unfold TraceWitness.overlayRamBytes
  rw [remapped]
  dsimp only
  by_cases within : 8 * q < bytes.size
  · rw [ite_eq_left (by omega)]
    congr 1
    omega
  · rw [ite_eq_right (by omega)]
    symm
    apply ramImageWord_zero
    intro offset _
    rw [Array.getElem?_eq_none (by omega)]
    rfl

/-- Two packed words agree when their eight constituent bytes agree.
For example, a shared-memory output word equals its extracted output-buffer word. -/
theorem ramImageWord_congr (f g : Nat → BitVec 8) (a b : Nat)
    (same : ∀ k < 8, f (a + k) = g (b + k)) :
    TraceWitness.ramImageWord f a = TraceWitness.ramImageWord g b := by
  unfold TraceWitness.ramImageWord
  rw [same 7 (by decide), same 6 (by decide), same 5 (by decide),
    same 4 (by decide), same 3 (by decide), same 2 (by decide), same 1 (by decide)]
  have zero := same 0 (by decide)
  simpa only [Nat.add_zero] using congrArg
    (fun x => g (b + 7) ++ g (b + 6) ++ g (b + 5) ++ g (b + 4) ++
      g (b + 3) ++ g (b + 2) ++ g (b + 1) ++ x) zero

/-- Extracting an in-capacity output byte reads that byte directly from shared memory.
For example, byte three is read at `output_start + 3`. -/
theorem outputsOf_get? (device : JoltDevice) (mem : Std.ExtHashMap Nat (BitVec 8))
    (i : Nat) (inside : i < device.memory_layout.max_output_size.toNat) :
    (device.outputsOf mem)[i]? =
      some ((mem.get? (device.memory_layout.output_start.toNat + i)).getD 0) := by
  simp [JoltDevice.outputsOf, inside]

/-- Every output word in the shared final image is the corresponding extracted
output word; for example, word one contains output bytes eight through fifteen. -/
theorem finalRamWord_output (trace : Trace) (config : MemoryConfig) (layout : MemoryLayout)
    (built : MemoryLayout.new config = some layout)
    (initialLayout : trace.initialState.jolt_device.memory_layout = layout)
    (finalLayout : (TraceWitness.finalTraceState trace).jolt_device.memory_layout = layout)
    (q : Nat) (inOutput : q < layout.max_output_size.toNat / 8) :
    TraceWitness.finalRamWord trace ((layout.output_start.toNat - ramLowestAddress layout) / 8 + q) =
      TraceWitness.ramImageWord (fun i =>
        ((TraceWitness.finalTraceState trace).jolt_device.outputsOf
          (TraceWitness.finalTraceState trace).sail.mem)[i]?.getD 0) (8 * q) := by
  have aligned := new_input_word_aligned config layout built
  obtain ⟨afterInput, inputMultiple⟩ := new_outputs_after_inputs config layout built
  have low := (new_io_ordered config layout built).1
  rw [MemoryLayout.get_lowest_address_toNat] at aligned low
  have startEq : ramLowestAddress layout +
      8 * ((layout.output_start.toNat - ramLowestAddress layout) / 8 + q) =
      layout.output_start.toNat + 8 * q := by
    unfold ramLowestAddress at *
    omega
  unfold TraceWitness.finalRamWord
  rw [initialLayout, MemoryLayout.get_lowest_address_toNat]
  change TraceWitness.ramImageWord _
    (ramLowestAddress layout + 8 * ((layout.output_start.toNat - ramLowestAddress layout) / 8 + q)) = _
  rw [startEq]
  apply ramImageWord_congr
  intro k hk
  rw [outputsOf_get? _ _ (8 * q + k) (by rw [finalLayout]; omega), Option.getD_some]
  rw [finalLayout]
  congr 2
  omega

/-- `q` counts words from the output start; word `q` holds output bytes `8*q`
through `8*q+7`, with missing bytes read as zero.
When the configured output region has at least two words, a three-byte output
occupies the low three bytes of word zero and leaves word one zero. -/
theorem ramPublicIoWord_output (config : MemoryConfig) (layout : MemoryLayout)
    (built : MemoryLayout.new config = some layout)
    (io : JoltPublicIo) (sameLayout : io.memory_layout = layout)
    (inputsFit : io.inputs.size ≤ layout.max_input_size.toNat)
    (q : Nat) (inOutput : q < layout.max_output_size.toNat / 8) :
    ramPublicIoWord io ((layout.output_start.toNat - ramLowestAddress layout) / 8 + q) =
      TraceWitness.ramImageWord (fun i => io.outputs[i]?.getD 0) (8 * q) := by
  obtain ⟨lowLeInput, _, _, _, _⟩ := new_io_ordered config layout built
  rw [MemoryLayout.get_lowest_address_toNat] at lowLeInput
  obtain ⟨outputAfterInput, inputMultiple⟩ := new_outputs_after_inputs config layout built
  have inputWordAligned := new_input_word_aligned config layout built
  rw [MemoryLayout.get_lowest_address_toNat] at inputWordAligned
  let low := ramLowestAddress layout
  change (layout.input_start.toNat - low) % 8 = 0 at inputWordAligned
  let inputFirst := (layout.input_start.toNat - low) / 8
  let outputFirst := (layout.output_start.toNat - low) / 8
  change ramPublicIoWord io (outputFirst + q) =
    TraceWitness.ramImageWord (fun i => io.outputs[i]?.getD 0) (8 * q)
  have outputWordAligned : (layout.output_start.toNat - low) % 8 = 0 := by
    have outputSub : layout.output_start.toNat - low =
        (layout.input_start.toNat - low) + layout.max_input_size.toNat := by
      dsimp only [low, ramLowestAddress] at *
      omega
    rw [outputSub]
    omega
  have outputIndex : low + 8 * outputFirst = layout.output_start.toNat := by
    dsimp only [outputFirst, low, ramLowestAddress] at *
    omega
  have inputBeforeOutput : inputFirst + layout.max_input_size.toNat / 8 =
      outputFirst := by
    dsimp only [inputFirst, outputFirst, low, ramLowestAddress] at *
    omega
  have lowPos := new_lowest_address_pos config layout built
  rw [MemoryLayout.get_lowest_address_toNat] at lowPos
  have remapInput : TraceWitness.remapRamAddress layout layout.input_start =
      some inputFirst := by
    unfold TraceWitness.remapRamAddress
    rw [ite_eq_right (by dsimp only [low, ramLowestAddress] at *; omega)]
    rfl
  have remapOutput : TraceWitness.remapRamAddress layout layout.output_start =
      some outputFirst := by
    unfold TraceWitness.remapRamAddress
    rw [ite_eq_right (by dsimp only [low, ramLowestAddress] at *; omega)]
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
    rw [ite_eq_right hInputNot]
  have outputPacked := overlayRamBytes_at_word layout layout.output_start io.outputs
    outputFirst q remapOutput
  unfold ramPublicIoWord
  rw [sameLayout, inputZero]
  exact outputPacked

/-- Input words of the public statement contain the supplied bytes and zero padding.
For example, the first input word packs input bytes zero through seven. -/
theorem ramPublicIoWord_input (config : MemoryConfig) (layout : MemoryLayout)
    (built : MemoryLayout.new config = some layout)
    (io : JoltPublicIo) (sameLayout : io.memory_layout = layout)
    (q : Nat) (inInput : q < layout.max_input_size.toNat / 8) :
    ramPublicIoWord io ((layout.input_start.toNat - ramLowestAddress layout) / 8 + q) =
      TraceWitness.ramImageWord (fun i => io.inputs[i]?.getD 0) (8 * q) := by
  have lowPos := new_lowest_address_pos config layout built
  have lowLeInput := (new_io_ordered config layout built).1
  have outputAfterInput := (new_io_word_geometry config layout built).1
  rw [MemoryLayout.get_lowest_address_toNat] at lowPos lowLeInput outputAfterInput
  let inputFirst := (layout.input_start.toNat - ramLowestAddress layout) / 8
  let outputFirst := (layout.output_start.toNat - ramLowestAddress layout) / 8
  have lowLeOutput : ramLowestAddress layout ≤ layout.output_start.toNat := by
    have ordered := (new_io_ordered config layout built).2.1
    unfold ramLowestAddress
    omega
  have remapInput : TraceWitness.remapRamAddress layout layout.input_start = some inputFirst := by
    unfold TraceWitness.remapRamAddress
    dsimp only
    rw [ite_eq_right (by omega)]
    rfl
  have remapOutput : TraceWitness.remapRamAddress layout layout.output_start = some outputFirst := by
    unfold TraceWitness.remapRamAddress
    dsimp only
    rw [ite_eq_right (by unfold ramLowestAddress at lowLeOutput; omega)]
    rfl
  have outputEmpty (previous : BitVec 64) : TraceWitness.overlayRamBytes layout layout.output_start
      io.outputs (inputFirst + q) previous = previous := by
    unfold TraceWitness.overlayRamBytes
    rw [remapOutput]
    dsimp only
    rw [ite_eq_right (by change ¬ (outputFirst ≤ inputFirst + q ∧ _); dsimp only [inputFirst, outputFirst, ramLowestAddress] at *; omega)]
  unfold ramPublicIoWord
  rw [sameLayout]
  dsimp only
  rw [outputEmpty]
  exact overlayRamBytes_at_word layout layout.input_start io.inputs inputFirst q remapInput

/-- Every byte in an aligned input-capacity region is protected by the MMU.
For example, a padded zero byte after the supplied input remains immutable. -/
theorem input_byte_protected (state : SailJoltState) (config : MemoryConfig)
    (built : MemoryLayout.new config = some state.jolt_device.memory_layout)
    (a : Nat) (lower : state.jolt_device.memory_layout.input_start.toNat ≤ a)
    (upper : a < state.jolt_device.memory_layout.output_start.toNat) :
    JoltISA.Mmu.protected_byte state a = true := by
  have relative := new_input_word_aligned config _ built
  have aligned := new_lowest_address_aligned config _ built
  have low := (new_io_ordered config _ built).1
  have inputEnd := new_input_end_eq_output_start config _ built
  have input : state.jolt_device.is_input (a / 8 * 8) = true := by
    simp only [JoltDevice.is_input, Bool.and_eq_true, decide_eq_true_eq]
    rw [inputEnd]
    constructor <;> omega
  simp only [JoltISA.Mmu.protected_byte, input, Bool.or_true, Bool.true_or]

/-- The final shared input word equals its initialized public bytes.
For example, a protected same-value store cannot alter input word one. -/
theorem finalRamWord_input {inst : JoltInstance SourceInstruction} {inputs : JoltPrivateInputs}
    (trace : HonestTrace inst inputs) (q : Nat)
    (inside : q < trace.initialState.jolt_device.memory_layout.max_input_size.toNat / 8) :
    TraceWitness.finalRamWord trace
      ((trace.initialState.jolt_device.memory_layout.input_start.toNat -
        ramLowestAddress trace.initialState.jolt_device.memory_layout) / 8 + q) =
      TraceWitness.ramImageWord (fun i => inst.inputs[i]?.getD 0) (8 * q) := by
  let layout := trace.initialState.jolt_device.memory_layout
  have built := (initial_state_device inst inputs trace.initialState trace.initialized).1
  unfold JoltInstance.memory_layout at built
  have aligned := new_input_word_aligned _ _ built
  have low := (new_io_ordered _ _ built).1
  obtain ⟨outputAfter, inputMultiple⟩ := new_outputs_after_inputs _ _ built
  rw [MemoryLayout.get_lowest_address_toNat] at aligned low
  have startEq : layout.get_lowest_address.toNat +
      8 * ((layout.input_start.toNat - ramLowestAddress layout) / 8 + q) =
      layout.input_start.toNat + 8 * q := by
    rw [MemoryLayout.get_lowest_address_toNat]
    dsimp only [layout, ramLowestAddress] at *
    omega
  unfold TraceWitness.finalRamWord
  change TraceWitness.ramImageWord _ (layout.get_lowest_address.toNat +
      8 * ((layout.input_start.toNat - ramLowestAddress layout) / 8 + q)) = _
  rw [startEq]
  apply ramImageWord_congr
  intro k hk
  let a := layout.input_start.toNat + 8 * q + k
  have lower : layout.input_start.toNat ≤ a := by dsimp only [a]; omega
  have upper : a < layout.output_start.toNat := by dsimp only [a, layout] at *; omega
  have kept := trace.final_protected_memory.bytes a
    (input_byte_protected trace.initialState _ built a lower upper)
  change JoltISA.Mmu.ram_byte (TraceWitness.finalTraceState trace).sail.mem a = _
  rw [kept]
  unfold JoltISA.Mmu.ram_byte
  rw [initial_state_input_get? inst inputs trace.initialState trace.initialized a lower upper,
    Option.getD_some]
  congr 2
  dsimp only [a, layout, ramLowestAddress] at *
  omega

-- The verifier's public I/O word is the run's: they share the layout and inputs,
-- and the verifier's outputs are the run's without their trailing zero bytes.
-- Past those bytes both read 0: the outputs start after the inputs' whole region.
theorem ramPublicIoWord_trimmed (io run : JoltPublicIo) (config : MemoryConfig)
    (built : MemoryLayout.new config = some run.memory_layout)
    (inputsFit : run.inputs.size ≤ run.memory_layout.max_input_size.toNat)
    (sameLayout : io.memory_layout = run.memory_layout)
    (sameInputs : io.inputs = run.inputs)
    (trimmedOutputs : io.outputs = trimTrailingZeros run.outputs)
    (address : Nat) :
    ramPublicIoWord io address = ramPublicIoWord run address := by
  obtain ⟨shorter, prefixSame, zerosAfter⟩ := trimTrailingZeros_spec run.outputs
  obtain ⟨outputsAfter, inputMultiple⟩ := new_outputs_after_inputs config run.memory_layout built
  have inputAligned := new_input_word_aligned config run.memory_layout built
  rw [MemoryLayout.get_lowest_address_toNat] at inputAligned
  unfold ramPublicIoWord
  rw [sameLayout, sameInputs, trimmedOutputs]
  dsimp only
  rw [overlayRamBytes_trailing_zeros _ _ run.outputs _ _ _ shorter prefixSame zerosAfter ?_]
  -- the inputs' overlay is 0 from the outputs on: the inputs fit below them
  intro outputFirst outputRemapped above
  unfold TraceWitness.overlayRamBytes
  split
  · rfl
  · rename_i inputFirst inputRemapped
    rw [ite_eq_right]
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
