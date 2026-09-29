import JoltConstraints.Constraints.IOSetupFrame
import JoltConstraints.Constraints.MemoryLayout

set_option autoImplicit false

namespace JoltConstraints

open scoped BigOperators

/-- Constraint (26) in `constraints.md`:
On the public I/O interval, the final RAM value equals the supplied public I/O word.
Rust: https://github.com/abiswas3/jolt/tree/main/crates/jolt-claims/src/protocols/jolt/relations/ram/output_check.rs#L115-L128 -/
def ramOutputEqPublicIo {F : Type} [Field F] {params : WitnessParams}
    (io : JoltIOState) (witness : WitnessType F params) : Prop :=
  ∀ address : Fin params.ramSize,
    ramPublicIoMask io address.val *
      (witness.RamValFinal address - ((ramPublicIoWord io address.val).toNat : F)) = 0

/-- An overlay whose bytes end at or below `input_start` leaves every word from
the input's first remapped word onward unchanged. The overlay start need not be
aligned: remapping rounds it down, which only moves the bytes lower. -/
theorem overlayRamBytes_below_input (layout : JoltIOLayout)
    (start : BitVec 64) (bytes : Array (BitVec 8))
    (inputWordAligned : (layout.input.1.toNat - ramLowestAddress layout) % 8 = 0)
    (fits : start.toNat + bytes.size ≤ layout.input.1.toNat)
    (address : Nat)
    (above : (layout.input.1.toNat - ramLowestAddress layout) / 8 ≤ address)
    (previous : BitVec 64) :
    HonestWitness.overlayRamBytes layout start bytes address previous = previous := by
  unfold ramLowestAddress at inputWordAligned above
  unfold HonestWitness.overlayRamBytes HonestWitness.remapRamAddress
  dsimp only
  by_cases hnone : start.toNat = 0 ∨
      start.toNat < min layout.trustedAdvice.1.toNat layout.untrustedAdvice.1.toNat
  · rw [if_pos hnone]
  · rw [if_neg hnone]
    dsimp only
    rw [if_neg]
    omega

/-- On the public I/O interval, the honest final RAM word is the public I/O word.
Below `RAM_START_ADDRESS` the RAM image is zero, and both advice overlays end
before the input's first word, so only the public overlays remain. -/
theorem finalRamWord_eq_ramPublicIoWord {program : JoltProgram} (trace : JoltTrace program)
    (adviceBelowInput : program.initialState.io.AdviceBelowInput)
    (address : Nat)
    (lower : (program.initialState.io.layout.input.1.toNat -
      ramLowestAddress program.initialState.io.layout) / 8 ≤ address)
    (upper : address <
      (JoltISA.ramStartAddress - ramLowestAddress program.initialState.io.layout) / 8) :
    HonestWitness.finalRamWord trace address =
      ramPublicIoWord (HonestWitness.finalTraceState trace).io address := by
  obtain ⟨hlayout, htrusted, huntrusted⟩ := finalTraceState_ioSame trace
  have hram : ¬ JoltISA.ramStartAddress ≤
      min program.initialState.io.layout.trustedAdvice.1.toNat
        program.initialState.io.layout.untrustedAdvice.1.toNat + 8 * address := by
    unfold ramLowestAddress at upper
    omega
  have htrustedOverlay := overlayRamBytes_below_input _
    program.initialState.io.layout.trustedAdvice.1 program.initialState.io.trustedAdvice
    adviceBelowInput.inputWordAligned adviceBelowInput.trustedAdviceBelowInput address lower
  have huntrustedOverlay := overlayRamBytes_below_input _
    program.initialState.io.layout.untrustedAdvice.1 program.initialState.io.untrustedAdvice
    adviceBelowInput.inputWordAligned adviceBelowInput.untrustedAdviceBelowInput address lower
  unfold HonestWitness.finalRamWord ramPublicIoWord
  dsimp only
  rw [hlayout, htrusted, huntrusted, if_neg hram, htrustedOverlay, huntrustedOverlay]

/-- Completeness of constraint (26) for the honest witness.

The final device is the last recorded post-state's device. Execution preserves
the layout and both advice buffers (`finalTraceState_ioSame`), so the final
RAM image and the public I/O array share the input, output, panic, and
termination overlays. They differ only below the input: the zero RAM image
below `RAM_START_ADDRESS` and the advice buffers. `adviceBelowInput` keeps the
advice buffers out of the public interval; `AdviceBelowInput.of_memoryLayout`
proves that every Rust-constructed device satisfies it. Output growth needs no
premise here: both sides overlay the same final output buffer. -/
theorem honestWitness_ramOutputEqPublicIo
    {F : Type} [Field F] (params : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program)
    (ramFits : params.RamFits trace)
    (traceFits : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor program.expandedBytecode.size)
    (adviceBelowInput : program.initialState.io.AdviceBelowInput)
    : ramOutputEqPublicIo (HonestWitness.finalTraceState trace).io
      (JoltProgram.honestWitness (F := F) params trace ramFits traceFits bytecodeDomain) := by
  intro address
  change ramPublicIoMask (HonestWitness.finalTraceState trace).io address.val *
    (HonestWitness.RamValFinal (F := F) params trace address -
      ((ramPublicIoWord (HonestWitness.finalTraceState trace).io address.val).toNat : F)) = 0
  have hlayout := (finalTraceState_ioSame trace).1
  unfold ramPublicIoMask
  dsimp only
  rw [hlayout]
  split_ifs with hmask
  · rw [HonestWitness.RamValFinal,
      finalRamWord_eq_ramPublicIoWord trace adviceBelowInput address.val hmask.1 hmask.2,
      sub_self, mul_zero]
  · rw [zero_mul]

end JoltConstraints
