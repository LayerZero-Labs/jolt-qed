+++
status = "fixed-upstream"
reproduced_at = "unknown"
fixed_by = "a16z/jolt#2415"
upstream = ""
registry = []
note = "A Lean check, not a Jolt run; the Jolt revision it modelled is not recorded. The premise it motivated, RamRegionFits, is gone at ff6fc6568."
+++

# The padded RAM region can pass 2^64

`layout_check.lean` shows that `MemoryLayout.new` and the verifier's maximum-domain check alone do not give `lowest + 8 * maxRamSize ≤ 2^64`.
It builds a layout with a `2^63`-byte heap whose padded RAM domain holds a doubleword at byte address `2^64`.
It is a counterexample to a derivation, not a witness for `AllConstraints` and not a run of Jolt.
The soundness theorem took the bound as the premise `RamRegionFits` because of it.

At `ff6fc6568` Jolt rejects such a layout: `MemoryLayout::max_ram_k` rejects a padded region past `2^64` (Jolt at ff6fc6568: `common/src/jolt_device.rs` (`max_ram_k`), from a16z/jolt#2415).
`JoltInstance.ramRegionFits` (`JoltConstraints/theorems/Soundness/Layer3/Layout.lean`) proves the bound, and the premise is gone.

`layout_check.lean` is outside the build.
It uses `decide +kernel`, which the repository no longer accepts, and the `lake env lean` command at its top does not work in every setup.
It has not been checked against the current model.
