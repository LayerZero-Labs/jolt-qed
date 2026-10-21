import JoltConstraints.prover_config
import JoltConstraints.witness_params

set_option autoImplicit false

namespace ExecutionDimensions

private def BoundsFor (addresses : List Nat) : Option (Nat × Nat) → Prop
  | none => ∀ address ∈ addresses, address = 0
  | some (lo, hi) => lo ∈ addresses ∧ hi ∈ addresses ∧ lo ≠ 0 ∧ hi ≠ 0 ∧
      ∀ address ∈ addresses, address = 0 ∨ (lo ≤ address ∧ address ≤ hi)

private theorem boundsFor_observe (addresses : List Nat) (bounds : Option (Nat × Nat))
    (valid : BoundsFor addresses bounds) (address : Nat) :
    BoundsFor (addresses ++ [address]) (observe bounds address) := by
  by_cases zero : address = 0
  · subst address
    cases bounds with
    | none =>
      simp only [observe, BoundsFor, List.mem_append, List.mem_singleton]
      intro a member
      exact member.elim (valid a) id
    | some pair =>
      rcases pair with ⟨lo, hi⟩
      obtain ⟨loMem, hiMem, loNonzero, hiNonzero, bounded⟩ := valid
      simp only [observe, BoundsFor, List.mem_append, List.mem_singleton]
      refine ⟨Or.inl loMem, Or.inl hiMem, loNonzero, hiNonzero, ?_⟩
      intro a member
      exact member.elim (bounded a) Or.inl
  · cases bounds with
    | none =>
      simp only [BoundsFor] at valid
      simp only [observe, if_neg zero, BoundsFor, List.mem_append, List.mem_singleton]
      refine ⟨Or.inr trivial, Or.inr trivial, zero, zero, ?_⟩
      intro a member
      rcases member with member | rfl
      · exact Or.inl (valid a member)
      · exact Or.inr ⟨le_rfl, le_rfl⟩
    | some pair =>
      rcases pair with ⟨lo, hi⟩
      obtain ⟨loMem, hiMem, loNonzero, hiNonzero, bounded⟩ := valid
      simp only [observe, if_neg zero, BoundsFor, List.mem_append, List.mem_singleton]
      refine ⟨?_, ?_, by omega, by omega, ?_⟩
      · by_cases h : lo ≤ address
        · exact Or.inl (by simpa [min_eq_left h] using loMem)
        · exact Or.inr (min_eq_right (by omega))
      · by_cases h : hi ≤ address
        · exact Or.inr (max_eq_right h)
        · exact Or.inl (by simpa [max_eq_left (by omega : address ≤ hi)] using hiMem)
      · intro a member
        rcases member with member | rfl
        · rcases bounded a member with rfl | bounds
          · exact Or.inl rfl
          · exact Or.inr ⟨by omega, by omega⟩
        · exact Or.inr ⟨by omega, by omega⟩

private theorem boundsFor_fold (addresses : List Nat) :
    BoundsFor addresses (addresses.foldl observe none) := by
  induction addresses using List.reverseRecOn with
  | nil => simp [BoundsFor]
  | append_singleton addresses address ih =>
    simpa only [List.foldl_append, List.foldl_cons, List.foldl_nil] using
      boundsFor_observe addresses _ ih address

/-- The streaming bounds and the old address scan agree after checked remapping. -/
theorem checkedTouched_fold (addresses : List Nat) (layout : MemoryLayout) (touched : Nat)
    (checked : ProverConfig.checkedTouched (addresses.foldl observe none) layout = some touched) :
    (∀ address ∈ addresses, address = 0 ∨ layout.get_lowest_address.toNat ≤ address) ∧
    (addresses.filterMap (remap_address layout)).max?.getD 0 = touched := by
  have valid := boundsFor_fold addresses
  cases bounds : addresses.foldl observe none with
  | none =>
    rw [bounds] at valid checked
    simp only [BoundsFor] at valid
    cases checked
    refine ⟨fun a member => Or.inl (valid a member), ?_⟩
    have empty : addresses.filterMap (remap_address layout) = [] := by
      apply List.filterMap_eq_nil_iff.mpr
      intro a member
      simp [remap_address, valid a member]
    simp [empty]
  | some pair =>
    rcases pair with ⟨lo, hi⟩
    rw [bounds] at valid checked
    obtain ⟨_, hiMem, _, hiNonzero, bounded⟩ := valid
    simp only [ProverConfig.checkedTouched, bind_some_iff] at checked
    obtain ⟨loOffset, loChecked, hiOffset, hiChecked, result⟩ := checked
    obtain ⟨_, loAbove⟩ := checkedSub_some loChecked
    obtain ⟨rfl, _⟩ := checkedSub_some hiChecked
    cases result
    refine ⟨?_, ?_⟩
    · intro a member
      rcases bounded a member with rfl | bounds
      · exact Or.inl rfl
      · exact Or.inr (by omega)
    · have largest : (addresses.filterMap (remap_address layout)).max? =
          some ((hi - layout.get_lowest_address.toNat) / 8) := by
        apply List.max?_eq_some_iff.mpr
        refine ⟨?_, ?_⟩
        · exact List.mem_filterMap.mpr ⟨hi, hiMem, by simp [remap_address, hiNonzero]⟩
        · intro slot member
          obtain ⟨a, aMem, remapped⟩ := List.mem_filterMap.mp member
          unfold remap_address at remapped
          split at remapped
          · cases remapped
          · cases remapped
            have aBound := bounded a aMem
            apply Nat.div_le_div_right
            omega
      simp [largest]

end ExecutionDimensions

namespace ProverConfig

/-- Successful checked Rust padding equals the previous mathematical formula. -/
theorem checkedTraceLength_eq_padded (rows padded : Nat)
    (accepted : checkedTraceLength rows = some padded) :
    padded = padded_trace_length rows := by
  rw [checkedTraceLength_eq rows padded accepted]
  unfold padded_trace_length
  split
  · have exponent : Nat.clog 2 (rows + 1) ≤ 8 :=
      Nat.clog_le_of_le_pow (by omega)
    have rounded : 2 ^ Nat.clog 2 (rows + 1) ≤ 256 :=
      Nat.pow_le_pow_right (by decide) exponent
    exact max_eq_right rounded
  · have roundedUp := Nat.le_pow_clog (by decide : 1 < 2) (rows + 1)
    exact max_eq_left (by omega)

end ProverConfig

-- Jolt's prover accepts only traces whose nonzero RAM addresses are at or above the
-- lowest address.
private theorem HonestTrace.prover_config_addresses_ok
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (trace : HonestTrace joltInstance privateInputs) (config : ProverConfig)
    (accepted : trace.prover_config joltInstance = some config) :
    ∀ address ∈ trace.rows.toList.filterMap (·.ram_address), address = 0 ∨
      trace.initialState.jolt_device.memory_layout.get_lowest_address.toNat ≤ address := by
  have checked := (ProverConfig.deriveFromDimensions_sizes _ _ _ _ _ config accepted).2.2.1
  unfold ProverConfig.checkedRamSize at checked
  simp only [bind_some_iff] at checked
  obtain ⟨touched, touchChecked, _⟩ := checked
  exact (ExecutionDimensions.checkedTouched_fold
    (trace.rows.toList.filterMap (fun (row : TraceRow trace.bytecode) => row.ram_address))
      trace.initialState.jolt_device.memory_layout touched touchChecked).1

/-- If Jolt's prover accepts the honest trace, so does the corrected policy. Both
make the same last-jump, padded-length and address checks; they differ only in
the RAM size they pick. -/
theorem HonestTrace.corrected_prover_config_isSome
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (trace : HonestTrace joltInstance privateInputs) (config : ProverConfig)
    (accepted : trace.prover_config joltInstance = some config) :
    trace.corrected_prover_config.isSome := by
  obtain ⟨jump, lengthChecked, _, lengthBound⟩ :=
    ProverConfig.deriveFromDimensions_sizes _ _ _ _ _ config accepted
  have lengthIs := ProverConfig.checkedTraceLength_eq_padded _ _ lengthChecked
  change config.trace_length = padded_trace_length trace.rows.size at lengthIs
  have addressesOk := trace.prover_config_addresses_ok config accepted
  have lastJump : (trace.rows.back?.all fun last =>
      trace.bytecode[last.rowIndex].instruction.is_jump) = true := by
    rcases jump with empty | jump
    · change trace.rows.size = 0 at empty
      have emptyRows := Array.size_eq_zero_iff.mp empty
      rw [emptyRows]
      rfl
    · change (trace.rows.back?.any fun last =>
        trace.bytecode[last.rowIndex].instruction.is_jump) = true at jump
      cases last : trace.rows.back? with
      | none => rfl
      | some row => simpa only [last, Option.any_some, Option.all_some] using jump
  have addressCheck : (trace.rows.toList.filterMap (·.ram_address)).all
      (fun address => address == 0 ||
        trace.initialState.jolt_device.memory_layout.get_lowest_address.toNat ≤ address) = true := by
    apply List.all_eq_true.mpr
    intro a member
    simpa only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] using addressesOk a member
  have paddedBound : padded_trace_length trace.rows.size ≤
      joltInstance.max_padded_trace_length.toNat := by
    omega
  unfold HonestTrace.corrected_prover_config
  simp only [lastJump, addressCheck, guard, paddedBound, ↓reduceIte, pure_bind]
  rfl
