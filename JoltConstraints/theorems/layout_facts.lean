/-
Facts about the memory layout: where Rust's MemoryLayout::try_new puts the advice regions
and the inputs. Each one is proved from MemoryLayout.new in JoltDevice.lean and the
instance's initial state in program.lean.
Layout source at public pin ff6fc6568:
https://github.com/a16z/jolt/blob/ff6fc656813d950565c9f6e1258b78bdaf0e60e8/common/src/jolt_device.rs#L488-L772
-/
import JoltConstraints.translation.program
import JoltConstraints.theorems.DeviceFrame
import JoltConstraints.theorems.Soundness.Layer5.PowerOfTwo

open LeanRV64D

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

/-- Rounding a 64-bit value up to a multiple of 8 stays below `2^64` when it succeeds.
For example, `alignUp8 9 = some 16`. -/
theorem alignUp8_lt {value aligned : Nat}
    (rounded : MemoryLayout.alignUp8 value = some aligned) (small : value < 2 ^ 64) :
    aligned < 2 ^ 64 := by
  unfold MemoryLayout.alignUp8 at rounded
  split at rounded
  · cases rounded
    exact small
  · obtain ⟨rfl, fits⟩ := checkedAdd_some rounded
    exact fits

/-- **The raw configured capacity and the capacity Jolt checks.** Jolt's `align_up` rounds each
configured maximum up to a multiple of 8: raw sizes 0, 1, 7, 8 and 9 give 0, 8, 8, 8 and 16.
Jolt at ff6fc6568: `common/src/jolt_device.rs` (`MemoryLayout::try_new`, `align_up`). -/
example : MemoryLayout.alignUp8 0 = some 0 := by decide
example : MemoryLayout.alignUp8 1 = some 8 := by decide
example : MemoryLayout.alignUp8 7 = some 8 := by decide
example : MemoryLayout.alignUp8 8 = some 8 := by decide
example : MemoryLayout.alignUp8 9 = some 16 := by decide

-- Each advice region is as long as its size, the two sit next to each other, the first
-- starts io_bytes below RAM, and both end below 2^64.
-- See : jolt/common/src/jolt_device.rs:532-574
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
  rw [bind_some_iff] at placed
  obtain ⟨start, subtracted, placed⟩ := placed
  split at placed
  · cases placed
  obtain ⟨startIs, _⟩ := checkedSub_some subtracted
  split at placed
  · -- trusted goes first, untrusted starts where it ends
    rw [bind_some_iff] at placed
    obtain ⟨trustedTop, trustedAdded, placed⟩ := placed
    rw [bind_some_iff] at placed
    obtain ⟨untrustedTop, untrustedAdded, placed⟩ := placed
    cases placed
    obtain ⟨trustedTopIs, trustedTopFits⟩ := checkedAdd_some trustedAdded
    obtain ⟨untrustedTopIs, untrustedTopFits⟩ := checkedAdd_some untrustedAdded
    omega
  · -- untrusted goes first, trusted starts where it ends
    rw [bind_some_iff] at placed
    obtain ⟨untrustedTop, untrustedAdded, placed⟩ := placed
    rw [bind_some_iff] at placed
    obtain ⟨trustedTop, trustedAdded, placed⟩ := placed
    cases placed
    obtain ⟨trustedTopIs, trustedTopFits⟩ := checkedAdd_some trustedAdded
    obtain ⟨untrustedTopIs, untrustedTopFits⟩ := checkedAdd_some untrustedAdded
    omega

-- The checked padded start excludes zero in either advice ordering.
theorem adviceRegions_starts_pos {trustedSize untrustedSize ioBytes : Nat}
    {trustedStart trustedEnd untrustedStart untrustedEnd : Nat}
    (placed : MemoryLayout.adviceRegions trustedSize untrustedSize ioBytes =
      some (trustedStart, trustedEnd, untrustedStart, untrustedEnd)) :
    0 < trustedStart ∧ 0 < untrustedStart := by
  unfold MemoryLayout.adviceRegions at placed
  rw [bind_some_iff] at placed
  obtain ⟨start, _, placed⟩ := placed
  split at placed
  · cases placed
  rename_i nonzero
  split at placed <;>
    rw [bind_some_iff] at placed <;>
    obtain ⟨firstEnd, firstAdded, placed⟩ := placed <;>
    rw [bind_some_iff] at placed <;>
    obtain ⟨_, _, placed⟩ := placed <;>
    cases placed <;>
    obtain ⟨_, _⟩ := checkedAdd_some firstAdded <;>
    omega

-- Construction alone ensures a positive lowest address; no verifier premise is needed.
theorem new_lowest_address_pos (config : MemoryConfig) (layout : MemoryLayout)
    (built : MemoryLayout.new config = some layout) :
    0 < layout.get_lowest_address.toNat := by
  unfold MemoryLayout.new at built
  repeat' (rw [bind_some_iff] at built; obtain ⟨_, _, built⟩ := built)
  cases built
  -- Use the placement step after discarding the other successful constructor steps.
  have positive := adviceRegions_starts_pos (by assumption)
  obtain ⟨_, _, _, _, _, _⟩ := adviceRegions_some (by assumption)
  unfold MemoryLayout.get_lowest_address
  split <;> simp only [BitVec.toNat_ofNat] <;> omega

/-- The smaller advice start is exactly the checked allocation start.
For example, swapping advice capacities changes their order but not this minimum. -/
private theorem adviceRegions_min_start {trusted untrusted bytes ts te us ue : Nat}
    (placed : MemoryLayout.adviceRegions trusted untrusted bytes = some (ts, te, us, ue)) :
    min ts us = JoltISA.RAM_START_ADDRESS - bytes := by
  unfold MemoryLayout.adviceRegions at placed
  rw [bind_some_iff] at placed
  obtain ⟨start, subtracted, placed⟩ := placed
  have startIs := (checkedSub_some subtracted).1
  split at placed
  · cases placed
  split at placed <;>
    rw [bind_some_iff] at placed <;>
    obtain ⟨middle, added, placed⟩ := placed <;>
    rw [bind_some_iff] at placed <;>
    obtain ⟨_, _, placed⟩ := placed <;>
    cases placed <;>
    obtain ⟨_, _⟩ := checkedAdd_some added <;>
    omega

/-- A checked power-of-two I/O allocation starts in the top half below RAM.
For example, the largest admitted I/O window begins at `0x40000000`, above
all unsupported emulator peripherals.
Jolt at `ff6fc6568`: `common/src/jolt_device.rs` (`MemoryLayout::try_new`). -/
private theorem adviceRegions_power_lower_bound (trusted untrusted total bytes : Nat)
    (ts te us ue : Nat)
    (multiplied : MemoryLayout.checkedMul (total / 8).nextPowerOfTwo 8 = some bytes)
    (placed : MemoryLayout.adviceRegions trusted untrusted bytes = some (ts, te, us, ue)) :
    0x40000000 ≤ ts ∧ 0x40000000 ≤ us := by
  obtain ⟨teIs, ueIs, adjacent, starts, _, _⟩ := adviceRegions_some placed
  obtain ⟨tsPositive, usPositive⟩ := adviceRegions_starts_pos placed
  have bytesIs := checkedMul_some multiplied
  obtain ⟨n, power⟩ := Nat.isPowerOfTwo_nextPowerOfTwo (total / 8)
  have bytesPower : bytes = 2 ^ (n + 3) := by
    rw [bytesIs, power, Nat.pow_add]
  have bytesSmall : bytes < 2 ^ 31 := by
    rcases starts with start | start <;> simp only [JoltISA.RAM_START_ADDRESS] at start <;> omega
  have exponent : n + 3 < 31 := by
    rw [bytesPower] at bytesSmall
    exact (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp bytesSmall
  have half : bytes ≤ 2 ^ 30 := by
    rw [bytesPower]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have minimum := adviceRegions_min_start placed
  simp only [JoltISA.RAM_START_ADDRESS] at minimum
  omega

/-- Every byte in a checked I/O layout is above emulator peripheral addresses.
For example, an input load cannot dispatch to the UART at `0x10000000`.
Jolt at `ff6fc6568`: `common/src/jolt_device.rs` (`MemoryLayout::try_new`). -/
theorem new_lowest_address_ge_half_ram (config : MemoryConfig) (layout : MemoryLayout)
    (built : MemoryLayout.new config = some layout) :
    0x40000000 ≤ layout.get_lowest_address.toNat := by
  unfold MemoryLayout.new at built
  repeat' (rw [bind_some_iff] at built; obtain ⟨_, _, built⟩ := built)
  cases built
  have bounds := adviceRegions_power_lower_bound _ _ _ _ _ _ _ _
    (by assumption) (by assumption)
  obtain ⟨_, _, _, _, _, _⟩ := adviceRegions_some (by assumption)
  unfold MemoryLayout.get_lowest_address
  split <;> simp only [BitVec.toNat_ofNat] <;> omega

-- What Rust's layout says about the advice regions and the inputs: each advice size is
-- its configured maximum rounded up to a multiple of 8, each advice region is as long as
-- its size, the two sit next to each other, both start at multiples of 8, and the inputs
-- start where the higher one ends.
-- See : jolt/common/src/jolt_device.rs:488-768 (MemoryLayout::try_new)
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
  -- Remaining geometry and padded-RAM admission.
  repeat' (rw [bind_some_iff] at built; obtain ⟨_, _, built⟩ := built)
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

/-- **The layout's capacities are the configured maxima rounded up to a multiple of 8**, as
`align_up` computes them. For example, `max_input_size = 1` gives a layout input capacity of 8.
Jolt at ff6fc6568: `common/src/jolt_device.rs` (`MemoryLayout::try_new`, `align_up`). -/
theorem new_capacities (config : MemoryConfig) (layout : MemoryLayout)
    (built : MemoryLayout.new config = some layout) :
    MemoryLayout.alignUp8 config.max_trusted_advice_size.toNat =
      some layout.max_trusted_advice_size.toNat ∧
    MemoryLayout.alignUp8 config.max_untrusted_advice_size.toNat =
      some layout.max_untrusted_advice_size.toNat ∧
    MemoryLayout.alignUp8 config.max_input_size.toNat = some layout.max_input_size.toNat := by
  unfold MemoryLayout.new at built
  rw [bind_some_iff] at built
  obtain ⟨_, _, built⟩ := built
  rw [bind_some_iff] at built
  obtain ⟨trusted, trustedRounded, built⟩ := built
  rw [bind_some_iff] at built
  obtain ⟨untrusted, untrustedRounded, built⟩ := built
  rw [bind_some_iff] at built
  obtain ⟨input, inputRounded, built⟩ := built
  repeat' (rw [bind_some_iff] at built; obtain ⟨_, _, built⟩ := built)
  cases built
  simp only [BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (alignUp8_lt trustedRounded (BitVec.isLt _)),
    Nat.mod_eq_of_lt (alignUp8_lt untrustedRounded (BitVec.isLt _)),
    Nat.mod_eq_of_lt (alignUp8_lt inputRounded (BitVec.isLt _))]
  exact ⟨trustedRounded, untrustedRounded, inputRounded⟩

-- Each advice region, holding at most its capacity, ends at or before the inputs start: the
-- advice bytes never reach the public inputs.
-- See : jolt/common/src/jolt_device.rs:488-768 (MemoryLayout::try_new)
--       jolt/common/src/jolt_device.rs:210-237 (JoltDevice::try_with_io checks the advice sizes)
theorem new_advice_below_input (config : MemoryConfig) (layout : MemoryLayout)
    (built : MemoryLayout.new config = some layout) (trustedSize untrustedSize : Nat)
    (trustedFits : trustedSize ≤ layout.max_trusted_advice_size.toNat)
    (untrustedFits : untrustedSize ≤ layout.max_untrusted_advice_size.toNat) :
    layout.trusted_advice_start.toNat + trustedSize ≤ layout.input_start.toNat ∧
    layout.untrusted_advice_start.toNat + untrustedSize ≤ layout.input_start.toNat := by
  obtain ⟨_, _, _, _, trustedEnd, untrustedEnd, _, _, _, inputStart⟩ :=
    new_advice_regions config layout built
  omega

-- The inputs start a whole number of 64-bit words above the lowest address.
-- See : jolt/common/src/jolt_device.rs:770-772 (get_lowest_address)
theorem new_input_word_aligned (config : MemoryConfig) (layout : MemoryLayout)
    (built : MemoryLayout.new config = some layout) :
    (layout.input_start.toNat - layout.get_lowest_address.toNat) % 8 = 0 := by
  obtain ⟨_, trustedMultiple, _, untrustedMultiple, trustedEnd, untrustedEnd, adjacent, _, _,
    inputStart⟩ := new_advice_regions config layout built
  unfold MemoryLayout.get_lowest_address
  split <;> omega

-- The lowest address, where the advice regions begin, is a multiple of 8.
-- See : jolt/common/src/jolt_device.rs:770-772 (get_lowest_address)
theorem new_lowest_address_aligned (config : MemoryConfig) (layout : MemoryLayout)
    (built : MemoryLayout.new config = some layout) :
    layout.get_lowest_address.toNat % 8 = 0 := by
  obtain ⟨_, _, _, _, _, _, _, trustedStart, untrustedStart, _⟩ :=
    new_advice_regions config layout built
  unfold MemoryLayout.get_lowest_address
  split
  · exact trustedStart
  · exact untrustedStart

/-- Outputs end at `io_end`, followed by the reserved I/O gap.
For example, a zero-capacity output still leaves eight bytes before RAM.
See : jolt/common/src/jolt_device.rs:488-768 (MemoryLayout::try_new). -/
theorem new_io_geometry (config : MemoryConfig) (layout : MemoryLayout)
    (built : MemoryLayout.new config = some layout) :
    layout.output_end.toNat = layout.output_start.toNat + layout.max_output_size.toNat ∧
    layout.max_output_size.toNat % 8 = 0 ∧
    layout.io_end = layout.output_end ∧
    layout.io_end.toNat + 8 ≤ JoltISA.RAM_START_ADDRESS := by
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
  rw [bind_some_iff] at built
  obtain ⟨outputEnd, outputAdded, built⟩ := built
  repeat' (rw [bind_some_iff] at built; obtain ⟨_, _, built⟩ := built)
  have layoutEq := Option.some.inj built
  rw [← layoutEq]
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
  have inputEight := (alignUp8_some inputRounded).2
  have outputEight := (alignUp8_some outputRounded).2
  have trustedEight := (alignUp8_some trustedRounded).2
  have untrustedEight := (alignUp8_some untrustedRounded).2
  have padding := checkedMul_some multiplied
  have roundedUp := JoltConstraints.Soundness.nextPowerOfTwo_ge (total / 8)
  have regions := adviceRegions_some placed
  have inputEndIs := checkedAdd_some inputAdded
  have outputEndIs := checkedAdd_some outputAdded
  have ioEndBound : outputEnd + 8 ≤ JoltISA.RAM_START_ADDRESS := by
    unfold MemoryLayout.adviceRegions at placed
    obtain ⟨_, subtracted, _⟩ := Option.bind_eq_some_iff.mp placed
    have startBound := checkedSub_some subtracted
    omega
  dsimp only
  simp only [BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := inputEnd) (by omega),
    Nat.mod_eq_of_lt (a := outputEnd) (by omega),
    Nat.mod_eq_of_lt (a := output) (by omega)]
  exact ⟨outputEndIs.1, outputEight, trivial, ioEndBound⟩

-- The outputs start right after the inputs' region, whose size is a multiple of 8.
-- See : jolt/common/src/jolt_device.rs:488-768 (MemoryLayout::try_new)
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
  repeat' (rw [bind_some_iff] at built; obtain ⟨_, _, built⟩ := built)
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

/-- A successful layout reserves at least the configured maximum number of input
bytes, rounding the reservation up to an eight-byte boundary.
For example, a configured maximum of nine bytes occupies sixteen layout bytes.
See jolt/common/src/jolt_device.rs (`MemoryLayout::try_new`) at ff6fc6568. -/
theorem new_input_size_bound (config : MemoryConfig) (layout : MemoryLayout)
    (built : MemoryLayout.new config = some layout) :
    config.max_input_size.toNat ≤ layout.max_input_size.toNat := by
  unfold MemoryLayout.new at built
  rw [bind_some_iff] at built
  obtain ⟨_, _, built⟩ := built
  rw [bind_some_iff] at built
  obtain ⟨_, _, built⟩ := built
  rw [bind_some_iff] at built
  obtain ⟨_, _, built⟩ := built
  rw [bind_some_iff] at built
  obtain ⟨input, inputRounded, built⟩ := built
  repeat' (rw [bind_some_iff] at built; obtain ⟨_, _, built⟩ := built)
  cases built
  have inputGe := (alignUp8_some inputRounded).1
  have inputLt : input < 2 ^ 64 := by
    unfold MemoryLayout.alignUp8 at inputRounded
    split at inputRounded
    · cases inputRounded
      exact BitVec.isLt _
    · obtain ⟨eq, bound⟩ := checkedAdd_some inputRounded
      omega
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt inputLt]
  exact inputGe

/-- The advice, input and output windows appear in order below RAM.
For example, `output_start` equals the end of the input reservation.
Jolt at `ff6fc6568`: `common/src/jolt_device.rs` (`MemoryLayout::try_new`). -/
theorem new_io_ordered (config : MemoryConfig) (layout : MemoryLayout)
    (built : MemoryLayout.new config = some layout) :
    layout.get_lowest_address.toNat ≤ layout.input_start.toNat ∧
    layout.input_start.toNat ≤ layout.output_start.toNat ∧
    layout.output_start.toNat ≤ layout.output_end.toNat ∧
    layout.output_end = layout.io_end ∧
    layout.io_end.toNat ≤ JoltISA.RAM_START_ADDRESS := by
  obtain ⟨_, _, _, _, trustedEnd, untrustedEnd, _, _, _, inputStart⟩ :=
    new_advice_regions config layout built
  obtain ⟨outputStart, _⟩ := new_outputs_after_inputs config layout built
  obtain ⟨outputEnd, _, ioEnd, bound⟩ := new_io_geometry config layout built
  have lowestBelow : layout.get_lowest_address.toNat ≤ layout.input_start.toNat := by
    unfold MemoryLayout.get_lowest_address
    split <;> omega
  exact ⟨lowestBelow, by omega, by omega, ioEnd.symm, by omega⟩

/-- The output segment begins at the input segment's exclusive end.
For example, consecutive input and output words leave no unmapped byte between them.
Jolt at `ff6fc6568`: `common/src/jolt_device.rs` (`MemoryLayout::try_new`). -/
theorem new_input_end_eq_output_start (config : MemoryConfig) (layout : MemoryLayout)
    (built : MemoryLayout.new config = some layout) : layout.input_end = layout.output_start := by
  unfold MemoryLayout.new at built
  repeat' (rw [bind_some_iff] at built; obtain ⟨_, _, built⟩ := built)
  cases built
  rfl

/-- Checked advice, input, output and gap intervals cover every byte from the
lowest I/O address to RAM.
For example, an unused byte after `output_end` is readable gap memory.
Jolt at `ff6fc6568`: `tracer/src/emulator/mmu.rs` (`device_readable`). -/
theorem JoltDevice.readable_of_layout (device : JoltDevice) (config : MemoryConfig)
    (built : MemoryLayout.new config = some device.memory_layout)
    (address : Nat) (lower : device.memory_layout.get_lowest_address.toNat ≤ address)
    (upper : address < JoltISA.RAM_START_ADDRESS) : device.readable address = true := by
  obtain ⟨_, _, _, _, trustedEnd, untrustedEnd, adjacent, _, _, inputStart⟩ :=
    new_advice_regions config device.memory_layout built
  obtain ⟨outputStart, _⟩ := new_outputs_after_inputs config device.memory_layout built
  obtain ⟨outputEnd, _, ioEnd, _⟩ := new_io_geometry config device.memory_layout built
  have inputEnd := congrArg BitVec.toNat (new_input_end_eq_output_start _ _ built)
  unfold JoltDevice.readable JoltDevice.is_input JoltDevice.is_trusted_advice
    JoltDevice.is_untrusted_advice JoltDevice.is_output JoltDevice.is_io_gap
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  rw [ioEnd] at *
  unfold MemoryLayout.get_lowest_address at lower
  split at lower <;> omega

/-- A word index counts 8-byte words up from the lowest address:
`(address - lowest) / 8`.
In a successful layout the output start and end word indices follow
from the input word index, and the output end word index is below the index of
`RAM_START_ADDRESS`.
See : jolt/common/src/jolt_device.rs:488-768 (MemoryLayout::try_new). -/
theorem new_io_word_geometry (config : MemoryConfig) (layout : MemoryLayout)
    (built : MemoryLayout.new config = some layout) :
    (layout.output_start.toNat - layout.get_lowest_address.toNat) / 8 =
      (layout.input_start.toNat - layout.get_lowest_address.toNat) / 8 +
        layout.max_input_size.toNat / 8 ∧
    (layout.output_end.toNat - layout.get_lowest_address.toNat) / 8 =
      (layout.output_start.toNat - layout.get_lowest_address.toNat) / 8 +
        layout.max_output_size.toNat / 8 ∧
    (layout.output_end.toNat - layout.get_lowest_address.toNat) / 8 <
      (JoltISA.RAM_START_ADDRESS - layout.get_lowest_address.toNat) / 8 := by
  obtain ⟨inputLower, _, _, _, _⟩ := new_io_ordered config layout built
  obtain ⟨outputStart, inputMultiple⟩ := new_outputs_after_inputs config layout built
  obtain ⟨outputEnd, outputMultiple, ioEndStart, ioEndBound⟩ :=
    new_io_geometry config layout built
  rw [ioEndStart] at ioEndBound
  omega

-- With the lowest address above 8, as validate_inputs requires, no device region covers
-- an address below 8, and the I/O region ends above it.
-- See : jolt/crates/jolt-verifier/src/verifier.rs:985-1002 (validate_ram_remap_base)
theorem JoltDevice.low_address_free (device : JoltDevice) (config : MemoryConfig)
    (built : MemoryLayout.new config = some device.memory_layout)
    (aboveEight : 8 < device.memory_layout.get_lowest_address.toNat)
    (address : Nat) (low : address < 8) :
    device.is_input address = false ∧ device.is_trusted_advice address = false ∧
    device.is_untrusted_advice address = false ∧ device.is_output address = false ∧
    address < device.memory_layout.io_end.toNat := by
  obtain ⟨inputAbove, outputAbove, outputEndAbove, ioEndEq, ioEndAbove⟩ :=
    new_io_ordered config device.memory_layout built
  have trustedAbove : device.memory_layout.get_lowest_address.toNat ≤
      device.memory_layout.trusted_advice_start.toNat := by
    unfold MemoryLayout.get_lowest_address
    split <;> omega
  have untrustedAbove : device.memory_layout.get_lowest_address.toNat ≤
      device.memory_layout.untrusted_advice_start.toNat := by
    unfold MemoryLayout.get_lowest_address
    split <;> omega
  have ioEndNat := congrArg BitVec.toNat ioEndEq
  unfold JoltDevice.is_input JoltDevice.is_trusted_advice JoltDevice.is_untrusted_advice
    JoltDevice.is_output
  simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not, Nat.not_le]
  omega

/-- A layout built by the tracer has a checked, nonoverflowing padded RAM domain.
For example, the final `try_new` admission rejects a wrapping domain end. -/
theorem new_max_ram_k (config : MemoryConfig) (layout : MemoryLayout)
    (built : MemoryLayout.new config = some layout) : layout.max_ram_k?.isSome := by
  unfold MemoryLayout.new at built
  repeat' (rw [bind_some_iff] at built; obtain ⟨_, _, built⟩ := built)
  cases built
  apply Option.isSome_iff_exists.mpr
  exact ⟨_, by assumption⟩

private theorem checked_ram_domain_spec (lowest heap : Nat) (segments : Bool) (k : Nat)
    (checked : (do
      guard (heap ≤ 2^64 - 8 && heap % 8 == 0)
      guard segments
      let total ← MemoryLayout.checkedSub heap lowest
      let words := (total / 8).nextPowerOfTwo
      guard (words < 2^64 && lowest + 8 * words ≤ 2^64)
      pure words : Option Nat) = some k) :
    heap % 8 = 0 ∧ lowest ≤ heap ∧
      k = ((heap - lowest) / 8).nextPowerOfTwo ∧ lowest + 8 * k ≤ 2^64 := by
  simp only [bind_some_iff] at checked
  obtain ⟨_, heapChecked, _, _, total, sub, _, domainChecked, result⟩ := checked
  have heapFacts := (Option.guard_eq_some' _).mp heapChecked
  have domainFacts := (Option.guard_eq_some' _).mp domainChecked
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at heapFacts domainFacts
  obtain ⟨rfl, lowBelow⟩ := checkedSub_some sub
  cases result
  exact ⟨heapFacts.2, lowBelow, rfl, domainFacts.2⟩

/-- An accepted maximum RAM domain has aligned heap bounds and a nonwrapping end.
For example, an end equal to `2^64` is allowed, while a larger end is rejected.
Jolt at `ff6fc6568`: `common/src/jolt_device.rs` (`MemoryLayout::max_ram_k`). -/
theorem max_ram_k_spec (layout : MemoryLayout) (k : Nat)
    (checked : layout.max_ram_k? = some k) :
    layout.heap_end.toNat % 8 = 0 ∧
      layout.get_lowest_address.toNat ≤ layout.heap_end.toNat ∧
      k = ((layout.heap_end.toNat - layout.get_lowest_address.toNat) / 8).nextPowerOfTwo ∧
      layout.get_lowest_address.toNat + 8 * k ≤ 2^64 :=
  checked_ram_domain_spec _ _ _ k checked

/-- An admitted layout ends its heap at least eight bytes below `2^64`.
For example, a heap end of `2^64 - 8` is admitted, while `2^64 - 7` is rejected.
Jolt at `ff6fc6568`: `common/src/jolt_device.rs` (`MemoryLayout::validate_heap_end`,
called first by `max_ram_k`). -/
theorem max_ram_k_heap_end_le (layout : MemoryLayout) (k : Nat)
    (checked : layout.max_ram_k? = some k) :
    layout.heap_end.toNat ≤ 2 ^ 64 - 8 := by
  unfold MemoryLayout.max_ram_k? at checked
  simp only [bind_some_iff] at checked
  obtain ⟨_, heapChecked, -⟩ := checked
  have heapFacts := (Option.guard_eq_some' _).mp heapChecked
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at heapFacts
  exact heapFacts.1

/-- Every layout `MemoryLayout.new` builds ends its heap at least eight bytes below
`2^64`, because `new` admits a layout only when `max_ram_k` does.
For example, a configuration whose heap would end at `2^64 - 1` builds no layout. -/
theorem new_heap_end_le (config : MemoryConfig) (layout : MemoryLayout)
    (built : MemoryLayout.new config = some layout) :
    layout.heap_end.toNat ≤ 2 ^ 64 - 8 := by
  obtain ⟨k, checked⟩ := Option.isSome_iff_exists.mp (new_max_ram_k config layout built)
  exact max_ram_k_heap_end_le layout k checked

-- The bootstrap device keeps its layout and starts with a false panic claim.
theorem init_state_jolt_device (entryAddress : BitVec 64) (ram : Array (BitVec 8))
    (device : JoltDevice) (adviceTape : JoltAdviceTape) (hostIO : JoltHostIOConfig) :
    (init_state entryAddress ram device adviceTape hostIO).jolt_device =
      { device with panic := false } :=
  rfl

/-- A successful shared-memory installation passed its three size checks, each against the
layout's capacity. For example, with a layout input capacity of 8, nine input bytes fail.
Jolt at ff6fc6568: `common/src/jolt_device.rs` (`JoltDevice::try_with_io`). -/
theorem initialState_fits (state after : SailJoltState) (sources : List (BitVec 64 × Bool))
    (inputs trusted untrusted : Array (BitVec 8))
    (built : JoltISA.initialState state sources inputs trusted untrusted = some after) :
    trusted.size ≤ state.jolt_device.memory_layout.max_trusted_advice_size.toNat ∧
    untrusted.size ≤ state.jolt_device.memory_layout.max_untrusted_advice_size.toNat ∧
    inputs.size ≤ state.jolt_device.memory_layout.max_input_size.toNat := by
  obtain ⟨_, _, _, memBuilt, _⟩ := JoltConstraints.initialState_shape _ _ _ _ _ _ built
  unfold JoltDevice.initialMem at memBuilt
  obtain ⟨admittedUnit, admitted, _⟩ := Option.bind_eq_some_iff.mp memBuilt
  have fits := (Option.guard_eq_some' admittedUnit).mp admitted
  simp only [Bool.and_eq_true, decide_eq_true_eq] at fits
  exact ⟨fits.1.2, fits.2, fits.1.1⟩

/-- A successful instance initialization built the checked layout, passed its three size
checks against the layout's capacities, and installed shared memory on the bootstrap
register/RAM state.
For example, its tape starts at position zero before I/O memory is installed. -/
theorem initial_state_build {Source : Type} (joltInstance : JoltInstance Source)
    (privateInputs : JoltPrivateInputs) (state : SailJoltState)
    (built : joltInstance.initial_state privateInputs = some state) :
    ∃ layout, joltInstance.memory_layout = some layout ∧
      joltInstance.trusted_advice.size ≤ layout.max_trusted_advice_size.toNat ∧
      privateInputs.untrusted_advice.size ≤ layout.max_untrusted_advice_size.toNat ∧
      joltInstance.inputs.size ≤ layout.max_input_size.toNat ∧
      JoltISA.initialState
        (init_state joltInstance.program.entry_address
          (initialRam layout joltInstance.program.memory_init)
          { panic := false, memory_layout := layout }
          { bytes := privateInputs.advice_tape, readPosition := 0 })
        (joltInstance.program.instructions.toList.map fun row => (row.address, row.is_compressed))
        joltInstance.inputs joltInstance.trusted_advice privateInputs.untrusted_advice = some state := by
  unfold JoltInstance.initial_state at built
  obtain ⟨layout, layoutBuilt, built⟩ := Option.bind_eq_some_iff.mp built
  obtain ⟨trustedFits, untrustedFits, inputsFit⟩ := initialState_fits _ _ _ _ _ _ built
  exact ⟨layout, layoutBuilt, trustedFits, untrustedFits, inputsFit, built⟩

/-- **Initialization fails exactly where Jolt's `create_emulator` does**: the checked layout
must exist, the code region of the program's rows must be valid, and each of the inputs, the
trusted advice and the untrusted advice must fit the layout's capacity, its configured maximum
rounded up to a multiple of 8. There is no check against the raw configured maximum.
For example, `max_input_size = 1` admits two input bytes (below).
Jolt at ff6fc6568: `tracer/src/lib.rs` (`create_emulator`) and `common/src/jolt_device.rs`
(`JoltDevice::try_with_io`). -/
theorem initial_state_isSome_iff {Source : Type} (joltInstance : JoltInstance Source)
    (privateInputs : JoltPrivateInputs) :
    (joltInstance.initial_state privateInputs).isSome ↔
      ∃ layout, joltInstance.memory_layout = some layout ∧
        (JoltISA.codeRegionOf layout (joltInstance.program.instructions.toList.map
          fun row => (row.address, row.is_compressed))).isSome ∧
        joltInstance.trusted_advice.size ≤ layout.max_trusted_advice_size.toNat ∧
        privateInputs.untrusted_advice.size ≤ layout.max_untrusted_advice_size.toNat ∧
        joltInstance.inputs.size ≤ layout.max_input_size.toNat := by
  constructor
  · intro initialized
    obtain ⟨state, built⟩ := Option.isSome_iff_exists.mp initialized
    obtain ⟨layout, layoutBuilt, trustedFits, untrustedFits, inputsFit, built⟩ :=
      initial_state_build joltInstance privateInputs state built
    obtain ⟨region, _, regionBuilt, _, _⟩ :=
      JoltConstraints.initialState_shape _ _ _ _ _ _ built
    exact ⟨layout, layoutBuilt, Option.isSome_iff_exists.mpr ⟨region, regionBuilt⟩,
      trustedFits, untrustedFits, inputsFit⟩
  · rintro ⟨layout, layoutBuilt, code, trustedFits, untrustedFits, inputsFit⟩
    obtain ⟨region, regionBuilt⟩ := Option.isSome_iff_exists.mp code
    unfold JoltInstance.initial_state
    simp only [layoutBuilt, Option.bind_eq_bind, Option.bind_some]
    unfold JoltISA.initialState JoltDevice.initialMem
    simp only [init_state_jolt_device]
    simp [regionBuilt, trustedFits, untrustedFits, inputsFit]

/-- With the raw `max_input_size = 1`, initialization admits two input bytes: the layout's
input capacity is 8. Before the fix, a raw-capacity guard rejected them, while Jolt's
`JoltDevice::try_with_io` accepts them. -/
example {Source : Type} (joltInstance : JoltInstance Source) (privateInputs : JoltPrivateInputs)
    (layout : MemoryLayout) (built : joltInstance.memory_layout = some layout)
    (raw : joltInstance.memory_config.max_input_size = 1)
    (code : (JoltISA.codeRegionOf layout (joltInstance.program.instructions.toList.map
      fun row => (row.address, row.is_compressed))).isSome)
    (twoInputs : joltInstance.inputs.size = 2) (noTrusted : joltInstance.trusted_advice.size = 0)
    (noUntrusted : privateInputs.untrusted_advice.size = 0) :
    (joltInstance.initial_state privateInputs).isSome := by
  have capacity := (new_capacities _ _ built).2.2
  simp only [raw] at capacity
  have eight : layout.max_input_size.toNat = 8 :=
    (Option.some.inj ((by decide : MemoryLayout.alignUp8 1 = some 8).symm.trans capacity)).symm
  exact (initial_state_isSome_iff _ _).mpr
    ⟨layout, built, code, by omega, by omega, by omega⟩

/-- With the raw `max_input_size = 1`, nine input bytes exceed the capacity 8 and
initialization fails, as `JoltDevice::try_with_io` fails. -/
example {Source : Type} (joltInstance : JoltInstance Source) (privateInputs : JoltPrivateInputs)
    (layout : MemoryLayout) (built : joltInstance.memory_layout = some layout)
    (raw : joltInstance.memory_config.max_input_size = 1)
    (nineInputs : joltInstance.inputs.size = 9) :
    joltInstance.initial_state privateInputs = none := by
  have capacity := (new_capacities _ _ built).2.2
  simp only [raw] at capacity
  have eight : layout.max_input_size.toNat = 8 :=
    (Option.some.inj ((by decide : MemoryLayout.alignUp8 1 = some 8).symm.trans capacity)).symm
  rw [← Option.not_isSome_iff_eq_none, initial_state_isSome_iff]
  rintro ⟨layout', built', -, -, -, fits⟩
  rw [built] at built'
  cases built'
  omega

/-- Initialization chooses a checked layout and enforces the tracer's advice limits, the
layout's capacities. Advice bytes are installed in shared memory; they are no longer device
fields.
For example, changing private advice cannot change the layout. -/
theorem initial_state_device {Source : Type} (joltInstance : JoltInstance Source)
    (privateInputs : JoltPrivateInputs) (initialState : SailJoltState)
    (built : joltInstance.initial_state privateInputs = some initialState) :
    joltInstance.memory_layout = some initialState.jolt_device.memory_layout ∧
    joltInstance.trusted_advice.size ≤
      initialState.jolt_device.memory_layout.max_trusted_advice_size.toNat ∧
    privateInputs.untrusted_advice.size ≤
      initialState.jolt_device.memory_layout.max_untrusted_advice_size.toNat := by
  obtain ⟨layout, layoutBuilt, trustedFits, untrustedFits, _, built⟩ :=
    initial_state_build joltInstance privateInputs initialState built
  obtain ⟨_, _, _, _, shape⟩ := JoltConstraints.initialState_shape _ _ _ _ _ _ built
  rw [shape]
  exact ⟨layoutBuilt, trustedFits, untrustedFits⟩

-- Successful initialization inherits the checked layout's exclusion of address zero.
theorem initial_state_lowest_address_pos {Source : Type} (joltInstance : JoltInstance Source)
    (privateInputs : JoltPrivateInputs) (initialState : SailJoltState)
    (built : joltInstance.initial_state privateInputs = some initialState) :
    0 < initialState.jolt_device.memory_layout.get_lowest_address.toNat := by
  have layoutBuilt := (initial_state_device joltInstance privateInputs initialState built).1
  exact new_lowest_address_pos _ _ layoutBuilt

-- In the instance's starting device, each advice region, holding the prover's advice,
-- ends at or before the inputs start, and the inputs start a multiple of 8 bytes above
-- the lowest address.
theorem initial_state_advice_below_input {Source : Type} (joltInstance : JoltInstance Source)
    (privateInputs : JoltPrivateInputs) (initialState : SailJoltState)
    (built : joltInstance.initial_state privateInputs = some initialState) :
    (initialState.jolt_device.memory_layout.input_start.toNat -
        initialState.jolt_device.memory_layout.get_lowest_address.toNat) % 8 = 0 ∧
    initialState.jolt_device.memory_layout.trusted_advice_start.toNat +
        joltInstance.trusted_advice.size ≤
      initialState.jolt_device.memory_layout.input_start.toNat ∧
    initialState.jolt_device.memory_layout.untrusted_advice_start.toNat +
        privateInputs.untrusted_advice.size ≤
      initialState.jolt_device.memory_layout.input_start.toNat := by
  obtain ⟨layoutBuilt, trustedFits, untrustedFits⟩ :=
    initial_state_device joltInstance privateInputs initialState built
  unfold JoltInstance.memory_layout at layoutBuilt
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
