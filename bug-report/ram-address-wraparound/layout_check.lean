import JoltConstraints.verifier_sizes

/-! A counterexample to deriving `lowest + 8 * maxRamSize ≤ 2^64` from
`MemoryLayout.new` and the maximum-domain check alone. This is not a satisfying
witness for `AllConstraints`, nor a reproduction against Jolt's verifier.
Run from the repository root with:
`lake env lean bug-report/ram-address-wraparound/layout_check.lean`. -/

set_option autoImplicit false

namespace RamAddressWraparound

def config : MemoryConfig := {
  max_input_size := 0, max_trusted_advice_size := 0,
  max_untrusted_advice_size := 0, max_output_size := 0,
  stack_size := 0, heap_size := BitVec.ofNat 64 (2 ^ 63), program_size := some 8 }

def observedBounds : Option (Nat × Nat × Nat) := do
  let layout ← MemoryLayout.new config
  let size ← JoltConstraints.VerifierSizes.maxRamSize layout
  pure (layout.get_lowest_address.toNat, layout.heap_end.toNat, size)

-- Kernel reduction is needed to unfold Nat.nextPowerOfTwo's private helper.
-- This uses neither native_decide nor a compiler-trust axiom.
private theorem layout_fields : (MemoryLayout.new config).map
    (fun layout => (layout.get_lowest_address.toNat, layout.heap_end.toNat)) =
    some (2 ^ 31 - 16, 2 ^ 63 + 2 ^ 31 + 136) := by decide +kernel

private theorem rounded_word_count : Nat.clog 2 (2 ^ 60 + 19) = 61 := by
  apply Nat.le_antisymm
  · exact Nat.clog_le_of_le_pow (by decide)
  · have lower := (Nat.lt_clog_iff_pow_lt (b := 2) (x := 2 ^ 60 + 19)
      (y := 60) (by decide)).mpr (by decide)
    omega

theorem observedBounds_eq : observedBounds =
    some (2 ^ 31 - 16, 2 ^ 63 + 2 ^ 31 + 136, 2 ^ 61) := by
  have fields := layout_fields
  cases built : MemoryLayout.new config with
  | none => simp [built] at fields
  | some layout =>
    simp only [built, Option.map_some, Option.some.injEq, Prod.mk.injEq] at fields
    simp only [observedBounds, built, Option.bind_eq_bind, Option.bind_some,
      JoltConstraints.VerifierSizes.maxRamSize, fields.1, fields.2]
    have rounding : Nat.clog 2 1152921504606846995 = 61 := rounded_word_count
    norm_num [MemoryLayout.checkedSub, JoltConstraints.VerifierSizes.checkedNextPowerOfTwo,
      rounding]

/-- The padded domain contains an aligned byte address of exactly `2^64`.
For example, a source value `2^64 - 8` and immediate 8 sum to this address,
whereas the machine's wrapped address is zero. Other constraints remain to be
checked before this can be called a soundness counterexample. -/
theorem padded_address_outside_word :
    ∃ index : Fin (2 ^ 61), (2 ^ 31 - 16) + 8 * index.val = 2 ^ 64 := by
  exact ⟨⟨(2 ^ 64 - (2 ^ 31 - 16)) / 8, by decide⟩, by decide⟩

#print axioms observedBounds_eq
#print axioms padded_address_outside_word

end RamAddressWraparound
