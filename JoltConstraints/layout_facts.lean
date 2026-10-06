/-
Facts about the memory layout: where Rust's MemoryLayout::new puts the advice regions
and the inputs. Each one is proved from MemoryLayout.new in JoltDevice.lean.
-/
import JoltBytecode.JoltISA.JoltDevice

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

-- Each advice region is as long as its size, the two sit next to each other, and both
-- end below 2^64.
-- See : jolt/common/src/jolt_device.rs:402-429
theorem adviceRegions_some {trustedSize untrustedSize ioBytes : Nat}
    {trustedStart trustedEnd untrustedStart untrustedEnd : Nat}
    (placed : MemoryLayout.adviceRegions trustedSize untrustedSize ioBytes =
      some (trustedStart, trustedEnd, untrustedStart, untrustedEnd)) :
    trustedEnd = trustedStart + trustedSize ∧
    untrustedEnd = untrustedStart + untrustedSize ∧
    (untrustedStart = trustedEnd ∨ trustedStart = untrustedEnd) ∧
    trustedEnd < 2 ^ 64 ∧ untrustedEnd < 2 ^ 64 := by
  unfold MemoryLayout.adviceRegions at placed
  split at placed
  · -- trusted goes first, untrusted starts where it ends
    rw [bind_some_iff] at placed
    obtain ⟨start, _, placed⟩ := placed
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
    obtain ⟨start, _, placed⟩ := placed
    rw [bind_some_iff] at placed
    obtain ⟨untrustedTop, untrustedAdded, placed⟩ := placed
    rw [bind_some_iff] at placed
    obtain ⟨trustedTop, trustedAdded, placed⟩ := placed
    cases placed
    obtain ⟨trustedTopIs, trustedTopFits⟩ := checkedAdd_some trustedAdded
    obtain ⟨untrustedTopIs, untrustedTopFits⟩ := checkedAdd_some untrustedAdded
    omega

-- What Rust's layout says about the advice regions and the inputs: each advice size is
-- its configured maximum rounded up to a multiple of 8, each advice region is as long as
-- its size, the two sit next to each other, and the inputs start where the higher one ends.
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
  obtain ⟨_, _, built⟩ := built
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
  obtain ⟨trustedEndIs, untrustedEndIs, adjacent, trustedEndFits, untrustedEndFits⟩ :=
    adviceRegions_some placed
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
  obtain ⟨_, _, _, _, trustedEnd, untrustedEnd, _, inputStart⟩ :=
    new_advice_regions config layout built
  omega

-- The inputs start a whole number of 64-bit words above the lowest address.
-- See : jolt/common/src/jolt_device.rs:486-488 (get_lowest_address)
theorem new_input_word_aligned (config : MemoryConfig) (layout : MemoryLayout)
    (built : MemoryLayout.new config = some layout) :
    (layout.input_start.toNat - layout.get_lowest_address.toNat) % 8 = 0 := by
  obtain ⟨_, trustedMultiple, _, untrustedMultiple, trustedEnd, untrustedEnd, adjacent,
    inputStart⟩ := new_advice_regions config layout built
  unfold MemoryLayout.get_lowest_address
  split <;> omega
