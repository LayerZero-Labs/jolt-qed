/-
Facts about the memory layout: where Rust's MemoryLayout::new puts the advice regions
and the inputs. Each one is proved from MemoryLayout.new in JoltDevice.lean and the
instance's initial state in program.lean.
-/
import JoltConstraints.program

set_option autoImplicit false

-- An Option step succeeds exactly when its first part does and the rest succeeds from
-- that result. Rewriting with it walks a do-block one line at a time.
theorem bind_some_iff {Value Result : Type} (first : Option Value)
    (next : Value → Option Result) (result : Result) :
    (first >>= next) = some result ↔ ∃ value, first = some value ∧ next value = some result :=
  Option.bind_eq_some_iff

-- A checked addition that succeeds gives the sum, and the sum fits in 64 bits.
theorem checkedAdd_some {first second total : Nat}
    (added : MemoryLayout.checkedAdd first second = some total) :
    total = first + second ∧ first + second < 2 ^ 64 := by
  unfold MemoryLayout.checkedAdd at added
  split at added
  · rename_i fits
    cases added
    exact ⟨rfl, fits⟩
  · cases added

-- A checked subtraction that succeeds gives the difference, without going below 0.
theorem checkedSub_some {first second total : Nat}
    (subtracted : MemoryLayout.checkedSub first second = some total) :
    total = first - second ∧ second ≤ first := by
  unfold MemoryLayout.checkedSub at subtracted
  split at subtracted
  · rename_i fits
    cases subtracted
    exact ⟨rfl, fits⟩
  · cases subtracted

-- A checked multiplication that succeeds gives the product.
theorem checkedMul_some {first second total : Nat}
    (multiplied : MemoryLayout.checkedMul first second = some total) :
    total = first * second := by
  unfold MemoryLayout.checkedMul at multiplied
  split at multiplied
  · cases multiplied
    rfl
  · cases multiplied

-- Rounding up to a multiple of 8 gives a multiple of 8, never smaller than the start.
theorem alignUp8_some {value aligned : Nat}
    (rounded : MemoryLayout.alignUp8 value = some aligned) :
    value ≤ aligned ∧ aligned % 8 = 0 := by
  unfold MemoryLayout.alignUp8 at rounded
  split at rounded
  · rename_i multiple
    cases rounded
    exact ⟨Nat.le_refl _, multiple⟩
  · obtain ⟨total, _⟩ := checkedAdd_some rounded
    omega

-- Each advice region is as long as its size, the two sit next to each other, the first
-- starts io_bytes below RAM, and both end below 2^64.
-- See : jolt/common/src/jolt_device.rs:402-429
theorem adviceRegions_some {trustedSize untrustedSize ioBytes : Nat}
    {trustedStart trustedEnd untrustedStart untrustedEnd : Nat}
    (placed : MemoryLayout.adviceRegions trustedSize untrustedSize ioBytes =
      some (trustedStart, trustedEnd, untrustedStart, untrustedEnd)) :
    trustedEnd = trustedStart + trustedSize ∧
    untrustedEnd = untrustedStart + untrustedSize ∧
    (untrustedStart = trustedEnd ∨ trustedStart = untrustedEnd) ∧
    (trustedStart = JoltISA.RAM_START_ADDRESS - ioBytes ∨
      untrustedStart = JoltISA.RAM_START_ADDRESS - ioBytes) ∧
    trustedEnd < 2 ^ 64 ∧ untrustedEnd < 2 ^ 64 := by
  unfold MemoryLayout.adviceRegions at placed
  split at placed
  · -- trusted goes first, untrusted starts where it ends
    rw [bind_some_iff] at placed
    obtain ⟨start, subtracted, placed⟩ := placed
    rw [bind_some_iff] at placed
    obtain ⟨trustedTop, trustedAdded, placed⟩ := placed
    rw [bind_some_iff] at placed
    obtain ⟨untrustedTop, untrustedAdded, placed⟩ := placed
    cases placed
    obtain ⟨trustedTopIs, trustedTopFits⟩ := checkedAdd_some trustedAdded
    obtain ⟨untrustedTopIs, untrustedTopFits⟩ := checkedAdd_some untrustedAdded
    obtain ⟨startIs, _⟩ := checkedSub_some subtracted
    omega
  · -- untrusted goes first, trusted starts where it ends
    rw [bind_some_iff] at placed
    obtain ⟨start, subtracted, placed⟩ := placed
    rw [bind_some_iff] at placed
    obtain ⟨untrustedTop, untrustedAdded, placed⟩ := placed
    rw [bind_some_iff] at placed
    obtain ⟨trustedTop, trustedAdded, placed⟩ := placed
    cases placed
    obtain ⟨trustedTopIs, trustedTopFits⟩ := checkedAdd_some trustedAdded
    obtain ⟨untrustedTopIs, untrustedTopFits⟩ := checkedAdd_some untrustedAdded
    obtain ⟨startIs, _⟩ := checkedSub_some subtracted
    omega

-- What Rust's layout says about the advice regions and the inputs: each advice size is
-- its configured maximum rounded up to a multiple of 8, each advice region is as long as
-- its size, the two sit next to each other, both start at multiples of 8, and the inputs
-- start where the higher one ends.
-- See : jolt/common/src/jolt_device.rs:348-484 (MemoryLayout::new)
theorem new_advice_regions (config : MemoryConfig) (layout : MemoryLayout)
    (built : MemoryLayout.new config = some layout) :
    config.max_trusted_advice_size.toNat ≤ layout.max_trusted_advice_size.toNat ∧
    layout.max_trusted_advice_size.toNat % 8 = 0 ∧
    config.max_untrusted_advice_size.toNat ≤ layout.max_untrusted_advice_size.toNat ∧
    layout.max_untrusted_advice_size.toNat % 8 = 0 ∧
    layout.trusted_advice_end.toNat =
      layout.trusted_advice_start.toNat + layout.max_trusted_advice_size.toNat ∧
    layout.untrusted_advice_end.toNat =
      layout.untrusted_advice_start.toNat + layout.max_untrusted_advice_size.toNat ∧
    (layout.untrusted_advice_start.toNat = layout.trusted_advice_end.toNat ∨
      layout.trusted_advice_start.toNat = layout.untrusted_advice_end.toNat) ∧
    layout.trusted_advice_start.toNat % 8 = 0 ∧
    layout.untrusted_advice_start.toNat % 8 = 0 ∧
    layout.input_start.toNat =
      max layout.untrusted_advice_end.toNat layout.trusted_advice_end.toNat := by
  unfold MemoryLayout.new at built
  -- program size
  rw [bind_some_iff] at built
  obtain ⟨_, _, built⟩ := built
  -- the six sizes, rounded up to multiples of 8
  rw [bind_some_iff] at built
  obtain ⟨trusted, trustedRounded, built⟩ := built
  rw [bind_some_iff] at built
  obtain ⟨untrusted, untrustedRounded, built⟩ := built
  rw [bind_some_iff] at built
  obtain ⟨_, _, built⟩ := built
  rw [bind_some_iff] at built
  obtain ⟨_, _, built⟩ := built
  rw [bind_some_iff] at built
  obtain ⟨_, _, built⟩ := built
  rw [bind_some_iff] at built
  obtain ⟨_, _, built⟩ := built
  -- the two power-of-two checks
  rw [bind_some_iff] at built
  obtain ⟨_, _, built⟩ := built
  rw [bind_some_iff] at built
  obtain ⟨_, _, built⟩ := built
  -- the size of the I/O region
  rw [bind_some_iff] at built
  obtain ⟨_, _, built⟩ := built
  rw [bind_some_iff] at built
  obtain ⟨ioBytes, ioBytesMultiplied, built⟩ := built
  -- the advice regions
  rw [bind_some_iff] at built
  obtain ⟨⟨trustedStart, trustedEnd, untrustedStart, untrustedEnd⟩, placed, built⟩ := built
  -- input end, output end, termination, I/O end, stack end, stack start, heap end
  rw [bind_some_iff] at built
  obtain ⟨_, _, built⟩ := built
  rw [bind_some_iff] at built
  obtain ⟨_, _, built⟩ := built
  rw [bind_some_iff] at built
  obtain ⟨_, _, built⟩ := built
  rw [bind_some_iff] at built
  obtain ⟨_, _, built⟩ := built
  rw [bind_some_iff] at built
  obtain ⟨_, _, built⟩ := built
  rw [bind_some_iff] at built
  obtain ⟨_, _, built⟩ := built
  rw [bind_some_iff] at built
  obtain ⟨_, _, built⟩ := built
  -- the layout itself
  cases built
  obtain ⟨trustedAtLeast, trustedMultiple⟩ := alignUp8_some trustedRounded
  obtain ⟨untrustedAtLeast, untrustedMultiple⟩ := alignUp8_some untrustedRounded
  obtain ⟨trustedEndIs, untrustedEndIs, adjacent, firstStart, trustedEndFits,
    untrustedEndFits⟩ := adviceRegions_some placed
  -- io_bytes is a whole number of 8-byte units, and RAM starts at a multiple of 8
  have ioBytesIs := checkedMul_some ioBytesMultiplied
  have ramStart : JoltISA.RAM_START_ADDRESS = 0x80000000 := rfl
  -- every value fits in 64 bits, so reading it back as a BitVec gives it unchanged
  simp only [BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := trusted) (by omega), Nat.mod_eq_of_lt (a := untrusted) (by omega),
    Nat.mod_eq_of_lt (a := trustedStart) (by omega), Nat.mod_eq_of_lt (a := trustedEnd) (by omega),
    Nat.mod_eq_of_lt (a := untrustedStart) (by omega),
    Nat.mod_eq_of_lt (a := untrustedEnd) (by omega),
    Nat.mod_eq_of_lt (a := max untrustedEnd trustedEnd) (by omega)]
  omega

-- Each advice region, holding at most its configured maximum, ends at or before the
-- inputs start: the advice bytes never reach the public inputs.
-- See : jolt/common/src/jolt_device.rs:348-484 (MemoryLayout::new)
--       jolt/tracer/src/lib.rs:379-390 (create_emulator checks the advice sizes)
theorem new_advice_below_input (config : MemoryConfig) (layout : MemoryLayout)
    (built : MemoryLayout.new config = some layout) (trustedSize untrustedSize : Nat)
    (trustedFits : trustedSize ≤ config.max_trusted_advice_size.toNat)
    (untrustedFits : untrustedSize ≤ config.max_untrusted_advice_size.toNat) :
    layout.trusted_advice_start.toNat + trustedSize ≤ layout.input_start.toNat ∧
    layout.untrusted_advice_start.toNat + untrustedSize ≤ layout.input_start.toNat := by
  obtain ⟨_, _, _, _, trustedEnd, untrustedEnd, _, _, _, inputStart⟩ :=
    new_advice_regions config layout built
  omega

-- The inputs start a whole number of 64-bit words above the lowest address.
-- See : jolt/common/src/jolt_device.rs:486-488 (get_lowest_address)
theorem new_input_word_aligned (config : MemoryConfig) (layout : MemoryLayout)
    (built : MemoryLayout.new config = some layout) :
    (layout.input_start.toNat - layout.get_lowest_address.toNat) % 8 = 0 := by
  obtain ⟨_, trustedMultiple, _, untrustedMultiple, trustedEnd, untrustedEnd, adjacent, _, _,
    inputStart⟩ := new_advice_regions config layout built
  unfold MemoryLayout.get_lowest_address
  split <;> omega

-- The lowest address, where the advice regions begin, is a multiple of 8.
-- See : jolt/common/src/jolt_device.rs:486-488 (get_lowest_address)
theorem new_lowest_address_aligned (config : MemoryConfig) (layout : MemoryLayout)
    (built : MemoryLayout.new config = some layout) :
    layout.get_lowest_address.toNat % 8 = 0 := by
  obtain ⟨_, _, _, _, _, _, _, trustedStart, untrustedStart, _⟩ :=
    new_advice_regions config layout built
  unfold MemoryLayout.get_lowest_address
  split
  · exact trustedStart
  · exact untrustedStart

-- The I/O regions sit in order above the advice regions: the inputs start at or above
-- the lowest address, then the outputs, the panic word, the termination word, and the
-- end of I/O.
-- See : jolt/common/src/jolt_device.rs:348-484 (MemoryLayout::new)
theorem new_io_ordered (config : MemoryConfig) (layout : MemoryLayout)
    (built : MemoryLayout.new config = some layout) :
    layout.get_lowest_address.toNat ≤ layout.input_start.toNat ∧
    layout.input_start.toNat ≤ layout.output_start.toNat ∧
    layout.output_start.toNat ≤ layout.panic.toNat ∧
    layout.panic.toNat ≤ layout.termination.toNat ∧
    layout.termination.toNat ≤ layout.io_end.toNat := by
  obtain ⟨_, _, _, _, trustedEnd, untrustedEnd, _, _, _, inputStart⟩ :=
    new_advice_regions config layout built
  have lowestBelow : layout.get_lowest_address.toNat ≤ layout.input_start.toNat := by
    unfold MemoryLayout.get_lowest_address
    split <;> omega
  unfold MemoryLayout.new at built
  -- program size
  rw [bind_some_iff] at built
  obtain ⟨_, _, built⟩ := built
  -- the six sizes, rounded up to multiples of 8
  rw [bind_some_iff] at built
  obtain ⟨_, _, built⟩ := built
  rw [bind_some_iff] at built
  obtain ⟨_, _, built⟩ := built
  rw [bind_some_iff] at built
  obtain ⟨_, _, built⟩ := built
  rw [bind_some_iff] at built
  obtain ⟨_, _, built⟩ := built
  rw [bind_some_iff] at built
  obtain ⟨_, _, built⟩ := built
  rw [bind_some_iff] at built
  obtain ⟨_, _, built⟩ := built
  -- the two power-of-two checks
  rw [bind_some_iff] at built
  obtain ⟨_, _, built⟩ := built
  rw [bind_some_iff] at built
  obtain ⟨_, _, built⟩ := built
  -- the size of the I/O region
  rw [bind_some_iff] at built
  obtain ⟨_, _, built⟩ := built
  rw [bind_some_iff] at built
  obtain ⟨_, _, built⟩ := built
  -- the advice regions
  rw [bind_some_iff] at built
  obtain ⟨⟨trustedStart, trustedTop, untrustedStart, untrustedTop⟩, placed, built⟩ := built
  -- input end, output end, termination, I/O end
  rw [bind_some_iff] at built
  obtain ⟨inputEnd, inputEndAdded, built⟩ := built
  rw [bind_some_iff] at built
  obtain ⟨outputEnd, outputEndAdded, built⟩ := built
  rw [bind_some_iff] at built
  obtain ⟨termination, terminationAdded, built⟩ := built
  rw [bind_some_iff] at built
  obtain ⟨ioEnd, ioEndAdded, built⟩ := built
  -- stack end, stack start, heap end
  rw [bind_some_iff] at built
  obtain ⟨_, _, built⟩ := built
  rw [bind_some_iff] at built
  obtain ⟨_, _, built⟩ := built
  rw [bind_some_iff] at built
  obtain ⟨_, _, built⟩ := built
  -- the layout itself
  cases built
  obtain ⟨_, _, _, _, trustedTopFits, untrustedTopFits⟩ := adviceRegions_some placed
  obtain ⟨inputEndIs, inputEndFits⟩ := checkedAdd_some inputEndAdded
  obtain ⟨outputEndIs, outputEndFits⟩ := checkedAdd_some outputEndAdded
  obtain ⟨terminationIs, terminationFits⟩ := checkedAdd_some terminationAdded
  obtain ⟨ioEndIs, ioEndFits⟩ := checkedAdd_some ioEndAdded
  -- every value fits in 64 bits, so reading it back as a BitVec gives it unchanged
  dsimp only at lowestBelow ⊢
  simp only [BitVec.toNat_ofNat] at lowestBelow ⊢
  rw [Nat.mod_eq_of_lt (a := max untrustedTop trustedTop) (by omega),
    Nat.mod_eq_of_lt (a := inputEnd) (by omega), Nat.mod_eq_of_lt (a := outputEnd) (by omega),
    Nat.mod_eq_of_lt (a := termination) (by omega), Nat.mod_eq_of_lt (a := ioEnd) (by omega)]
  rw [Nat.mod_eq_of_lt (a := max untrustedTop trustedTop) (by omega)] at lowestBelow
  omega

-- The outputs start right after the inputs' region, whose size is a multiple of 8.
-- See : jolt/common/src/jolt_device.rs:348-484 (MemoryLayout::new)
theorem new_outputs_after_inputs (config : MemoryConfig) (layout : MemoryLayout)
    (built : MemoryLayout.new config = some layout) :
    layout.output_start.toNat = layout.input_start.toNat + layout.max_input_size.toNat ∧
    layout.max_input_size.toNat % 8 = 0 := by
  unfold MemoryLayout.new at built
  -- program size
  rw [bind_some_iff] at built
  obtain ⟨_, _, built⟩ := built
  -- the six sizes, rounded up to multiples of 8
  rw [bind_some_iff] at built
  obtain ⟨_, _, built⟩ := built
  rw [bind_some_iff] at built
  obtain ⟨_, _, built⟩ := built
  rw [bind_some_iff] at built
  obtain ⟨input, inputRounded, built⟩ := built
  rw [bind_some_iff] at built
  obtain ⟨_, _, built⟩ := built
  rw [bind_some_iff] at built
  obtain ⟨_, _, built⟩ := built
  rw [bind_some_iff] at built
  obtain ⟨_, _, built⟩ := built
  -- the two power-of-two checks
  rw [bind_some_iff] at built
  obtain ⟨_, _, built⟩ := built
  rw [bind_some_iff] at built
  obtain ⟨_, _, built⟩ := built
  -- the size of the I/O region
  rw [bind_some_iff] at built
  obtain ⟨_, _, built⟩ := built
  rw [bind_some_iff] at built
  obtain ⟨_, _, built⟩ := built
  -- the advice regions
  rw [bind_some_iff] at built
  obtain ⟨⟨trustedStart, trustedTop, untrustedStart, untrustedTop⟩, placed, built⟩ := built
  -- input end
  rw [bind_some_iff] at built
  obtain ⟨inputEnd, inputEndAdded, built⟩ := built
  -- output end, termination, I/O end, stack end, stack start, heap end
  rw [bind_some_iff] at built
  obtain ⟨_, _, built⟩ := built
  rw [bind_some_iff] at built
  obtain ⟨_, _, built⟩ := built
  rw [bind_some_iff] at built
  obtain ⟨_, _, built⟩ := built
  rw [bind_some_iff] at built
  obtain ⟨_, _, built⟩ := built
  rw [bind_some_iff] at built
  obtain ⟨_, _, built⟩ := built
  rw [bind_some_iff] at built
  obtain ⟨_, _, built⟩ := built
  -- the layout itself
  cases built
  obtain ⟨_, _, _, _, trustedTopFits, untrustedTopFits⟩ := adviceRegions_some placed
  obtain ⟨inputEndIs, inputEndFits⟩ := checkedAdd_some inputEndAdded
  obtain ⟨_, inputMultiple⟩ := alignUp8_some inputRounded
  -- every value fits in 64 bits, so reading it back as a BitVec gives it unchanged
  dsimp only
  simp only [BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := max untrustedTop trustedTop) (by omega),
    Nat.mod_eq_of_lt (a := inputEnd) (by omega), Nat.mod_eq_of_lt (a := input) (by omega)]
  omega

-- With the lowest address above 8, as validate_inputs requires, no device region covers
-- an address below 8, and the I/O region ends above it.
-- See : jolt/crates/jolt-verifier/src/verifier.rs:992-1005 (validate_ram_remap_base)
theorem JoltDevice.low_address_free (device : JoltDevice) (config : MemoryConfig)
    (built : MemoryLayout.new config = some device.memory_layout)
    (aboveEight : 8 < device.memory_layout.get_lowest_address.toNat)
    (address : Nat) (low : address < 8) :
    device.is_input address = false ∧ device.is_trusted_advice address = false ∧
    device.is_untrusted_advice address = false ∧ device.is_output address = false ∧
    device.is_panic address = false ∧ device.is_termination address = false ∧
    address ≤ device.memory_layout.io_end.toNat := by
  obtain ⟨inputAbove, outputAbove, panicAbove, terminationAbove, ioEndAbove⟩ :=
    new_io_ordered config device.memory_layout built
  have trustedAbove : device.memory_layout.get_lowest_address.toNat ≤
      device.memory_layout.trusted_advice_start.toNat := by
    unfold MemoryLayout.get_lowest_address
    split <;> omega
  have untrustedAbove : device.memory_layout.get_lowest_address.toNat ≤
      device.memory_layout.untrusted_advice_start.toNat := by
    unfold MemoryLayout.get_lowest_address
    split <;> omega
  unfold JoltDevice.is_input JoltDevice.is_trusted_advice JoltDevice.is_untrusted_advice
    JoltDevice.is_output JoltDevice.is_panic JoltDevice.is_termination
  simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not, Nat.not_le]
  omega

-- The starting device is the one given to init_state, with no outputs and no panic yet.
theorem init_state_jolt_device (entryAddress : BitVec 64) (ram : Array (BitVec 8))
    (device : JoltDevice) (adviceTape : JoltAdviceTape) (hostIO : JoltHostIOConfig) :
    (init_state entryAddress ram device adviceTape hostIO).jolt_device =
      { device with outputs := #[], panic := false } :=
  rfl

-- The starting device holds the fixed trusted advice and the prover's untrusted
-- advice. create_emulator checks both against the configured maximums.
-- See : jolt/tracer/src/lib.rs:364-408 (create_emulator)
theorem initial_state_device {Source : Type} (joltInstance : JoltInstance Source)
    (privateInputs : JoltPrivateInputs) (initialState : SailJoltState)
    (built : joltInstance.initial_state privateInputs = some initialState) :
    joltInstance.memory_layout = some initialState.jolt_device.memory_layout ∧
    initialState.jolt_device.trusted_advice = joltInstance.trusted_advice ∧
    initialState.jolt_device.untrusted_advice = privateInputs.untrusted_advice ∧
    joltInstance.trusted_advice.size ≤
      joltInstance.memory_config.max_trusted_advice_size.toNat ∧
    privateInputs.untrusted_advice.size ≤
      joltInstance.memory_config.max_untrusted_advice_size.toNat := by
  unfold JoltInstance.initial_state at built
  rw [bind_some_iff] at built
  obtain ⟨layout, layoutBuilt, built⟩ := built
  dsimp only at built
  -- create_emulator's three size checks: trusted advice, untrusted advice, inputs
  split at built
  · cases built
  rename_i trustedTooLong
  rw [bind_some_iff] at built
  obtain ⟨_, _, built⟩ := built
  split at built
  · cases built
  rename_i untrustedTooLong
  rw [bind_some_iff] at built
  obtain ⟨_, _, built⟩ := built
  split at built
  · cases built
  rw [bind_some_iff] at built
  obtain ⟨_, _, built⟩ := built
  -- the device holds the layout and the two specified advice buffers
  cases built
  rw [init_state_jolt_device]
  exact ⟨layoutBuilt, rfl, rfl, Nat.le_of_not_lt trustedTooLong,
    Nat.le_of_not_lt untrustedTooLong⟩

-- The starting device holds the instance's inputs.
-- See : jolt/tracer/src/lib.rs:398-399 (create_emulator)
theorem initial_state_inputs {Source : Type} (joltInstance : JoltInstance Source)
    (privateInputs : JoltPrivateInputs) (initialState : SailJoltState)
    (built : joltInstance.initial_state privateInputs = some initialState) :
    initialState.jolt_device.inputs = joltInstance.inputs := by
  unfold JoltInstance.initial_state at built
  rw [bind_some_iff] at built
  obtain ⟨layout, _, built⟩ := built
  dsimp only at built
  -- create_emulator's three size checks: trusted advice, untrusted advice, inputs
  split at built
  · cases built
  rw [bind_some_iff] at built
  obtain ⟨_, _, built⟩ := built
  split at built
  · cases built
  rw [bind_some_iff] at built
  obtain ⟨_, _, built⟩ := built
  split at built
  · cases built
  rw [bind_some_iff] at built
  obtain ⟨_, _, built⟩ := built
  -- the device holds the inputs
  cases built
  rw [init_state_jolt_device]

-- In the instance's starting device, each advice region, holding the prover's advice,
-- ends at or before the inputs start, and the inputs start a multiple of 8 bytes above
-- the lowest address.
theorem initial_state_advice_below_input {Source : Type} (joltInstance : JoltInstance Source)
    (privateInputs : JoltPrivateInputs) (initialState : SailJoltState)
    (built : joltInstance.initial_state privateInputs = some initialState) :
    (initialState.jolt_device.memory_layout.input_start.toNat -
        initialState.jolt_device.memory_layout.get_lowest_address.toNat) % 8 = 0 ∧
    initialState.jolt_device.memory_layout.trusted_advice_start.toNat +
        initialState.jolt_device.trusted_advice.size ≤
      initialState.jolt_device.memory_layout.input_start.toNat ∧
    initialState.jolt_device.memory_layout.untrusted_advice_start.toNat +
        initialState.jolt_device.untrusted_advice.size ≤
      initialState.jolt_device.memory_layout.input_start.toNat := by
  obtain ⟨layoutBuilt, trustedIs, untrustedIs, trustedFits, untrustedFits⟩ :=
    initial_state_device joltInstance privateInputs initialState built
  unfold JoltInstance.memory_layout at layoutBuilt
  rw [trustedIs, untrustedIs]
  obtain ⟨trustedBelow, untrustedBelow⟩ :=
    new_advice_below_input _ _ layoutBuilt _ _ trustedFits untrustedFits
  exact ⟨new_input_word_aligned _ _ layoutBuilt, trustedBelow, untrustedBelow⟩

-- In the instance's starting device, the lowest address is a multiple of 8.
theorem initial_state_lowest_address_aligned {Source : Type} (joltInstance : JoltInstance Source)
    (privateInputs : JoltPrivateInputs) (initialState : SailJoltState)
    (built : joltInstance.initial_state privateInputs = some initialState) :
    initialState.jolt_device.memory_layout.get_lowest_address.toNat % 8 = 0 := by
  obtain ⟨layoutBuilt, _⟩ := initial_state_device joltInstance privateInputs initialState built
  unfold JoltInstance.memory_layout at layoutBuilt
  exact new_lowest_address_aligned _ _ layoutBuilt
