import JoltConstraints.translation.Constraints.RamReadData

open LeanRV64D

set_option autoImplicit false

open JoltConstraints

/-- Both advice buffers of a device lie below `input_start`, and `input_start`
is a whole number of words above the lowest RAM address. These are the only
layout facts the public-output constraint (26) needs: together they keep every
advice byte out of the public I/O interval.

Every starting device has them: `initial_state_advice_below_input`
(`theorems/layout_facts.lean`) proves them for the device that
`JoltInstance.initial_state` builds. -/
structure JoltDevice.AdviceBelowInput (io : JoltDevice) : Prop where
  inputWordAligned : (io.memory_layout.input_start.toNat - ramLowestAddress io.memory_layout) % 8 = 0
  trustedAdviceBelowInput :
    io.memory_layout.trusted_advice_start.toNat + io.trusted_advice.size ≤ io.memory_layout.input_start.toNat
  untrustedAdviceBelowInput :
    io.memory_layout.untrusted_advice_start.toNat + io.untrusted_advice.size ≤ io.memory_layout.input_start.toNat
