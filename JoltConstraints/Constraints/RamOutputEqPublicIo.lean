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
  obtain ⟨hlayout, htrusted, huntrusted⟩ := finalTraceState_ioSame trace
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

end JoltConstraints
