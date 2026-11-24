import JoltConstraints.theorems.Soundness.Layer3.State
import JoltConstraints.theorems.witness_domain

open LeanRV64D

/-! The initial witness reads its words directly from the initialized shared byte map.
Program, input and advice initialization all use that map; an overlay ending
before a selected word cannot change it.
Jolt at `ff6fc6568`: `crates/jolt-witness/src/backend/trace/ram.rs`
(`initial_ram_state` and `populate_ram_bytes`). -/

set_option autoImplicit false

namespace JoltConstraints.Soundness

open JoltISA

/-- A byte buffer ending before a RAM word leaves that word's previous value
unchanged under the image overlay; for example, an input buffer below ordinary
RAM cannot overwrite its first word. -/
theorem overlayRamBytes_below_word (layout : MemoryLayout)
    (start : BitVec 64) (bytes : Array (BitVec 8)) (index : Nat) (previous : BitVec 64)
    (fits : start.toNat + bytes.size ≤ ramLowestAddress layout + 8 * index) :
    TraceWitness.overlayRamBytes layout start bytes index previous = previous := by
  unfold TraceWitness.overlayRamBytes
  cases hr : TraceWitness.remapRamAddress layout start with
  | none => rfl
  | some firstWord =>
    have hnot : ¬(firstWord ≤ index ∧ (index - firstWord) * 8 < bytes.size) := by
      intro ⟨hindex, hbytes⟩
      unfold TraceWitness.remapRamAddress at hr
      dsimp only at hr
      split_ifs at hr with hbad
      have hfirst := Option.some.inj hr
      unfold ramLowestAddress at fits hfirst
      omega
    simp only [hnot, ↓reduceIte]

/-- At every shared-memory index, the initialized image is the shared byte-map word.
For example, the first program word is read directly from initialized memory. -/
theorem initialRamWord_eq_ram_doubleword
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    {params : WitnessParams} (context : ConstraintContext joltInstance privateInputs params)
    {state : SailJoltState} (built : joltInstance.initial_state privateInputs = some state)
    (index : Nat) :
    TraceWitness.initialRamWordFromState state index =
      Mmu.ram_doubleword state.sail.mem (ramLowestAddress context.io.memory_layout + 8 * index) := by
  have layoutIs := initial_state_memory_layout context built
  unfold TraceWitness.initialRamWordFromState
  rw [layoutIs]
  dsimp only
  rw [MemoryLayout.get_lowest_address_toNat]
  rfl

end JoltConstraints.Soundness
