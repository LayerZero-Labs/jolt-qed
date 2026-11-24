import JoltConstraints.translation.program
import JoltConstraints.translation.witness
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option autoImplicit false

namespace JoltConstraints

open scoped BigOperators

/-- The code-word interval computed from each source instruction's last expanded row.
For example, a compressed instruction at a word's last halfword protects that word only.
The last row carries the source compression bit; other rows of its expansion do not.
Jolt at `ff6fc6568`: `crates/jolt-program/src/preprocess/ram.rs` (`code_region`). -/
def ramCodeRegion (bytecode : Array JoltInstructionRow) (layout : MemoryLayout) : Nat × Nat :=
  (JoltISA.codeRegionOf layout
    ((bytecode.toList.filter fun row => row.virtual_sequence_remaining.getD 0 == 0).map
      fun row => (row.address, row.is_compressed))).getD (0, 0)

/-- Public mask C on remapped words: code, input, advice and canary words.
For example, an output word has mask zero and a word overlapping the canary has mask one.
Jolt at `ff6fc6568`: `crates/jolt-program/src/preprocess/ram.rs`
(`write_protected_word_intervals`). -/
def ramWriteProtectedMask {F : Type} [Field F] (bytecode : Array JoltInstructionRow)
    (layout : MemoryLayout) (k : Nat) : F :=
  let lowest := layout.get_lowest_address.toNat
  let region := ramCodeRegion bytecode layout
  let overlaps (start stop : Nat) :=
    start < stop ∧ (start - lowest) / 8 ≤ k ∧ k < (stop - lowest + 7) / 8
  if (region.1 ≤ k ∧ k < region.2) ∨
      overlaps layout.input_start.toNat layout.input_end.toNat ∨
      overlaps layout.trusted_advice_start.toNat layout.trusted_advice_end.toNat ∨
      overlaps layout.untrusted_advice_start.toNat layout.untrusted_advice_end.toNat ∨
      overlaps layout.stack_end.toNat (layout.stack_end.toNat + JoltISA.STACK_CANARY_SIZE)
  then 1 else 0

/-- Protected words have zero selector-weighted increment at every cycle.
For example, a same-value store in the input segment contributes zero.
Jolt at `ff6fc6568`: `crates/jolt-claims/src/protocols/jolt/relations/ram/read_write_checking.rs`
(`unbatched_relation`, third claim). -/
def ramWriteProtected {F : Type} [Field F] {params : WitnessParams}
    (mask : Fin params.ramSize → F) (witness : WitnessType F params) : Prop :=
  ∀ t : Fin params.traceLength,
    0 = ∑ k : Fin params.ramSize, mask k * (witness.RamRa k t * witness.RamInc t)

end JoltConstraints
