import JoltConstraints.Constraints.RamOutputEqPublicIo
import JoltConstraints.Constraints.IOSetupFrame
import JoltConstraints.Constraints.MemoryLayout

set_option autoImplicit false

namespace JoltConstraints

open scoped BigOperators

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
    (adviceBelowInput : program.initialState.jolt_device.AdviceBelowInput)
    : ramOutputEqPublicIo (HonestWitness.finalTraceState trace).jolt_device
      (JoltProgram.honestWitness (F := F) params trace ramFits traceFits bytecodeDomain) := by
  intro address
  change ramPublicIoMask (HonestWitness.finalTraceState trace).jolt_device address.val *
    (HonestWitness.RamValFinal (F := F) params trace address -
      ((ramPublicIoWord (HonestWitness.finalTraceState trace).jolt_device address.val).toNat : F)) = 0
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
