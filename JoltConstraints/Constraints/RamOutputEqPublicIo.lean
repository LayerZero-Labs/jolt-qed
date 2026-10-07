import JoltConstraints.Constraints.IOSetupFrame
import JoltConstraints.Constraints.MemoryLayout

set_option autoImplicit false

namespace JoltConstraints

open scoped BigOperators

/-- Constraint (26) in `constraints.md`:
On the public I/O interval, the final RAM value equals the supplied public I/O word.
Rust: https://github.com/abiswas3/jolt/tree/main/crates/jolt-claims/src/protocols/jolt/relations/ram/output_check.rs#L115-L128 -/
def ramOutputEqPublicIo {F : Type} [Field F] {params : WitnessParams}
    (io : JoltDevice) (witness : WitnessType F params) : Prop :=
  ∀ address : Fin params.ramSize,
    ramPublicIoMask io address.val *
      (witness.RamValFinal address - ((ramPublicIoWord io address.val).toNat : F)) = 0

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
    HonestWitness.overlayRamBytes layout start bytes address previous = previous := by
  unfold ramLowestAddress at inputWordAligned above
  unfold HonestWitness.overlayRamBytes HonestWitness.remapRamAddress
  dsimp only
  by_cases hnone : start.toNat = 0 ∨
      start.toNat < min layout.trusted_advice_start.toNat layout.untrusted_advice_start.toNat
  · rw [if_pos hnone]
  · rw [if_neg hnone]
    dsimp only
    rw [if_neg]
    omega

/-- On the public I/O interval, the honest final RAM word is the public I/O word.
Below `RAM_START_ADDRESS` the RAM image is zero, and both advice overlays end
before the input's first word, so only the public overlays remain. -/
theorem finalRamWord_eq_ramPublicIoWord {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (adviceBelowInput : trace.initialState.jolt_device.AdviceBelowInput)
    (address : Nat)
    (lower : (trace.initialState.jolt_device.memory_layout.input_start.toNat -
      ramLowestAddress trace.initialState.jolt_device.memory_layout) / 8 ≤ address)
    (upper : address <
      (JoltISA.RAM_START_ADDRESS - ramLowestAddress trace.initialState.jolt_device.memory_layout) / 8) :
    HonestWitness.finalRamWord trace address =
      ramPublicIoWord (HonestWitness.finalTraceState trace).jolt_device address := by
  obtain ⟨hlayout, htrusted, huntrusted, _⟩ := finalTraceState_ioSame trace
  have hram : ¬ JoltISA.RAM_START_ADDRESS ≤
      min trace.initialState.jolt_device.memory_layout.trusted_advice_start.toNat
        trace.initialState.jolt_device.memory_layout.untrusted_advice_start.toNat + 8 * address := by
    unfold ramLowestAddress at upper
    omega
  have htrustedOverlay := overlayRamBytes_below_input _
    trace.initialState.jolt_device.memory_layout.trusted_advice_start trace.initialState.jolt_device.trusted_advice
    adviceBelowInput.inputWordAligned adviceBelowInput.trustedAdviceBelowInput address lower
  have huntrustedOverlay := overlayRamBytes_below_input _
    trace.initialState.jolt_device.memory_layout.untrusted_advice_start trace.initialState.jolt_device.untrusted_advice
    adviceBelowInput.inputWordAligned adviceBelowInput.untrustedAdviceBelowInput address lower
  unfold HonestWitness.finalRamWord ramPublicIoWord
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

-- Eight zero bytes make the zero word.
theorem ramImageWord_zero (byte : Nat → BitVec 8) (start : Nat)
    (allZero : ∀ offset < 8, byte (start + offset) = 0) :
    HonestWitness.ramImageWord byte start = 0 := by
  unfold HonestWitness.ramImageWord
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
    (previousZero : ∀ firstWord, HonestWitness.remapRamAddress layout start = some firstWord →
      firstWord ≤ address → previous = 0) :
    HonestWitness.overlayRamBytes layout start trimmed address previous =
      HonestWitness.overlayRamBytes layout start bytes address previous := by
  -- both arrays read the same byte everywhere, missing bytes as 0
  have sameBytes : (fun i : Nat => trimmed[i]?.getD 0) = (fun i : Nat => bytes[i]?.getD 0) := by
    funext i
    by_cases kept : i < trimmed.size
    · rw [prefixSame i kept]
    · by_cases inBytes : i < bytes.size
      · rw [zerosAfter i (by omega) inBytes, Array.getElem?_eq_none (by omega)]
        rfl
      · rw [Array.getElem?_eq_none (by omega), Array.getElem?_eq_none (by omega)]
  unfold HonestWitness.overlayRamBytes
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
  unfold HonestWitness.overlayRamBytes
  split
  · rfl
  · rename_i inputFirst inputRemapped
    rw [if_neg]
    rintro ⟨_, inInputs⟩
    unfold HonestWitness.remapRamAddress at outputRemapped inputRemapped
    dsimp only at outputRemapped inputRemapped
    split at outputRemapped
    · cases outputRemapped
    split at inputRemapped
    · cases inputRemapped
    cases outputRemapped
    cases inputRemapped
    omega

end JoltConstraints
