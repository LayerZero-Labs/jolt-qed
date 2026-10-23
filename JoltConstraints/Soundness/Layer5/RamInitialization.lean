import JoltConstraints.Soundness.Layer3.State
import JoltConstraints.Soundness.Layer5.PowerOfTwo

/-! Ordinary RAM in the initial witness is the interpreter's byte map, which
contains the program image and reads absent bytes as zero. Advice and input
overlays cannot reach it: their size checks and the checked layout place their
bytes below RAM_START_ADDRESS.
At public pin 8bbb2357:
See : jolt/common/src/jolt_device.rs:381-497
See : jolt/crates/jolt-witness/src/backend/trace/ram.rs:87-129
See : jolt/crates/jolt-witness/src/backend/trace/ram.rs:287-303 -/

set_option autoImplicit false

namespace JoltConstraints.Soundness

open JoltISA

private theorem adviceRegions_input_below_ram
    {trusted untrusted padded ts te us ue input : Nat}
    (placed : MemoryLayout.adviceRegions trusted untrusted padded = some (ts, te, us, ue))
    (fits : trusted + untrusted + input ≤ padded) :
    max ue te + input ≤ RAM_START_ADDRESS := by
  obtain ⟨teIs, ueIs, adjacent, first, _, _⟩ := adviceRegions_some placed
  unfold MemoryLayout.adviceRegions at placed
  obtain ⟨start, subtracted, _⟩ := Option.bind_eq_some_iff.mp placed
  have bounded := (checkedSub_some subtracted).2
  omega

private theorem new_input_below_ram (config : MemoryConfig) (layout : MemoryLayout)
    (built : MemoryLayout.new config = some layout) :
    layout.input_start.toNat + layout.max_input_size.toNat ≤ RAM_START_ADDRESS := by
  unfold MemoryLayout.new at built
  rw [bind_some_iff] at built
  obtain ⟨_, _, built⟩ := built
  rw [bind_some_iff] at built
  obtain ⟨trusted, trustedRounded, built⟩ := built
  rw [bind_some_iff] at built
  obtain ⟨untrusted, untrustedRounded, built⟩ := built
  rw [bind_some_iff] at built
  obtain ⟨input, inputRounded, built⟩ := built
  rw [bind_some_iff] at built
  obtain ⟨output, outputRounded, built⟩ := built
  rw [bind_some_iff] at built
  obtain ⟨_, _, built⟩ := built
  rw [bind_some_iff] at built
  obtain ⟨_, _, built⟩ := built
  rw [bind_some_iff] at built
  obtain ⟨_, _, built⟩ := built
  rw [bind_some_iff] at built
  obtain ⟨_, _, built⟩ := built
  rw [bind_some_iff] at built
  obtain ⟨total, summed, built⟩ := built
  rw [bind_some_iff] at built
  obtain ⟨padded, multiplied, built⟩ := built
  rw [bind_some_iff] at built
  obtain ⟨⟨ts, te, us, ue⟩, placed, built⟩ := built
  rw [bind_some_iff] at built
  obtain ⟨inputEnd, inputAdded, built⟩ := built
  repeat' (rw [bind_some_iff] at built; obtain ⟨_, _, built⟩ := built)
  cases built
  rw [bind_some_iff] at summed
  obtain ⟨a, addedA, summed⟩ := summed
  rw [bind_some_iff] at addedA
  obtain ⟨b, addedB, addedA⟩ := addedA
  rw [bind_some_iff] at addedB
  obtain ⟨c, addedC, addedB⟩ := addedB
  have ca := (checkedAdd_some addedC).1
  have cb := (checkedAdd_some addedB).1
  have cc := (checkedAdd_some addedA).1
  have cd := (checkedAdd_some summed).1
  have trustedEight := (alignUp8_some trustedRounded).2
  have untrustedEight := (alignUp8_some untrustedRounded).2
  have inputEight := (alignUp8_some inputRounded).2
  have outputEight := (alignUp8_some outputRounded).2
  have padding := checkedMul_some multiplied
  have roundedUp := nextPowerOfTwo_ge (total / 8)
  have fits : trusted + untrusted + input ≤ padded := by omega
  have below := adviceRegions_input_below_ram placed fits
  have inputFits := (checkedAdd_some inputAdded).2
  dsimp only
  simp only [BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := max ue te) (by omega),
    Nat.mod_eq_of_lt (a := input) (by omega)]
  exact below

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

/-- At every ordinary-RAM index, the initialized witness image is the actual
byte-map word. Input/advice overlays are proved disjoint from this region. -/
theorem initialRamWord_eq_ram_doubleword
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    {params : WitnessParams} (context : ConstraintContext joltInstance privateInputs params)
    {state : SailJoltState} (built : joltInstance.initial_state privateInputs = some state)
    (index : Nat) (inRam : RAM_START_ADDRESS ≤ ramLowestAddress context.io.memory_layout + 8 * index) :
    TraceWitness.initialRamWordFromState state index =
      Mmu.ram_doubleword state.sail.mem (ramLowestAddress context.io.memory_layout + 8 * index) := by
  have layoutIs := initial_state_memory_layout context built
  obtain ⟨layoutBuilt, _, _, _, _⟩ := initial_state_device joltInstance privateInputs state built
  have below := new_input_below_ram _ _ layoutBuilt
  obtain ⟨_, trustedBelow, untrustedBelow⟩ :=
    initial_state_advice_below_input joltInstance privateInputs state built
  have inputsIs := initial_state_inputs joltInstance privateInputs state built
  have valid := context.validInputs
  unfold JoltInstance.validate_inputs at valid
  rw [layoutBuilt] at valid
  simp only [Bool.and_eq_true, decide_eq_true_eq] at valid
  have inputsFit := valid.1.2
  rw [← layoutIs] at inRam ⊢
  have trusted (previous : BitVec 64) := overlayRamBytes_below_word state.jolt_device.memory_layout
    state.jolt_device.memory_layout.trusted_advice_start state.jolt_device.trusted_advice index
    previous (by omega)
  have untrusted (previous : BitVec 64) := overlayRamBytes_below_word state.jolt_device.memory_layout
    state.jolt_device.memory_layout.untrusted_advice_start state.jolt_device.untrusted_advice index
    previous (by omega)
  have inputs (previous : BitVec 64) := overlayRamBytes_below_word state.jolt_device.memory_layout
    state.jolt_device.memory_layout.input_start state.jolt_device.inputs index previous (by
      rw [inputsIs]; omega)
  unfold TraceWitness.initialRamWordFromState
  dsimp only
  rw [inputs, untrusted, trusted]
  change (if RAM_START_ADDRESS ≤ ramLowestAddress state.jolt_device.memory_layout + 8 * index
    then _ else _) = _
  rw [if_pos inRam]
  rfl

end JoltConstraints.Soundness
