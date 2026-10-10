import JoltConstraints.Soundness.Layer1.Addresses

set_option autoImplicit false

namespace JoltConstraints.Soundness

open scoped BigOperators

variable {F : Type} [Field F]
  {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
  {params : WitnessParams} {witness : WitnessType F params}

private theorem ram_lowest_pos
    (context : ConstraintContext joltInstance privateInputs params) :
    0 < ramLowestAddress context.io.memory_layout := by
  have publicIo := context.publicIo
  unfold JoltInstance.public_io at publicIo
  obtain ⟨layout, hasLayout, sameIo⟩ := Option.bind_eq_some_iff.mp publicIo
  have valid := context.validInputs
  unfold JoltInstance.validate_inputs at valid
  rw [hasLayout] at valid
  simp only [Bool.and_eq_true, decide_eq_true_eq] at valid
  have lowest : 8 < layout.get_lowest_address.toNat := valid.1.1
  have layoutEq : layout = context.io.memory_layout :=
    congrArg JoltDevice.memory_layout (Option.some.inj sameIo)
  rw [← layoutEq]
  unfold ramLowestAddress MemoryLayout.get_lowest_address at *
  split at lowest <;> omega

/-- The loose address bound uses `WitnessParams.logRamK_lt_usizeBits`, the
modeled 64-bit host's domain-size bound, rather than an extra context premise. -/
theorem ram_address_value_lt_char (charAbove2pow127 : 2 ^ 127 < ringChar F)
    (layout : MemoryLayout) (address : Fin params.ramSize) :
    ramLowestAddress layout + 8 * address.val < ringChar F := by
  have lowest : ramLowestAddress layout < 2 ^ 64 :=
    lt_of_le_of_lt (Nat.min_le_left _ _) layout.trusted_advice_start.isLt
  have index : address.val < 2 ^ 63 := by
    have width := params.logRamK_lt_usizeBits
    exact address.isLt.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  have total : ramLowestAddress layout + 8 * address.val < 2 ^ 67 := by omega
  exact total.trans (lt_of_le_of_lt (by decide : 2 ^ 67 ≤ 2 ^ 127) charAbove2pow127)

private theorem ram_address_value_ne_zero (charAbove2pow127 : 2 ^ 127 < ringChar F)
    (context : ConstraintContext joltInstance privateInputs params)
    (address : Fin params.ramSize) :
    ((ramLowestAddress context.io.memory_layout + 8 * address.val : Nat) : F) ≠ 0 := by
  intro same
  have bounded := ram_address_value_lt_char (params := params) charAbove2pow127 context.io.memory_layout address
  have positive := ram_lowest_pos context
  have equal := natCast_injective_below_char bounded (by omega : 0 < ringChar F)
    (by simpa only [Nat.cast_zero] using same)
  omega

/-- A selected RAM address determines every read weighted by the full RAM selector. -/
theorem ram_read_of_selected (charAbove2pow127 : 2 ^ 127 < ringChar F)
    (context : ConstraintContext joltInstance privateInputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
    (t : Fin params.traceLength) (value : Fin params.ramSize → F)
    (chosen : Fin params.ramSize) (one : witness.RamRa chosen t = 1) :
    (∑ address, value address * witness.RamRa address t) = value chosen := by
  apply read_eq_selected (fun address => witness.RamRa address t) value
  · intro address
    rcases ramRa_zero_or_one context equations address t with zero | one
    · simp [zero]
    · simp [one]
  · exact one
  · exact fun address selected =>
      ramRa_at_most_one charAbove2pow127 context equations t address chosen selected one

/-- No in-domain RAM address is selected exactly when the raw RAM-address
column is zero. The verifier's positive remapping base and field bounds rule
out a selected address whose encoding is zero. -/
theorem ramRa_zero_iff_address_zero (charAbove2pow127 : 2 ^ 127 < ringChar F)
    (context : ConstraintContext joltInstance privateInputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
    (t : Fin params.traceLength) :
    (∀ address, witness.RamRa address t = 0) ↔ witness.RamAddress t = 0 := by
  constructor
  · intro zero
    rw [equations.ramAddressEqRamRaf t]
    simp [zero]
  · intro addressZero
    rcases ramRa_zero_or_unique charAbove2pow127 context equations t with zero | ⟨chosen, one, _⟩
    · exact zero
    · have address := equations.ramAddressEqRamRaf t
      rw [ram_read_of_selected charAbove2pow127 context equations t _ chosen one] at address
      exact False.elim (ram_address_value_ne_zero charAbove2pow127 context chosen
        (address.symm.trans addressZero))

/-- The all-zero selector alternative contributes no RAM read, write value,
or per-word increment. `RamInc` itself need not be zero. This describes the
RAM constraints; execution of a zero-address instruction is a later obligation. -/
theorem ram_zero_effects (charAbove2pow127 : 2 ^ 127 < ringChar F)
    (context : ConstraintContext joltInstance privateInputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
    (t : Fin params.traceLength) (addressZero : witness.RamAddress t = 0) :
    witness.RamReadValue t = 0 ∧ witness.RamWriteValue t = 0 ∧
      ∀ address, witness.RamRa address t * witness.RamInc t = 0 := by
  have zero := (ramRa_zero_iff_address_zero charAbove2pow127 context equations t).mpr addressZero
  refine ⟨?_, ?_, ?_⟩
  · rw [equations.ramReadValueEqRamRead t]
    simp [zero]
  · rw [equations.ramWriteValueEqRamReadWrite t]
    simp [zero]
  · intro address
    rw [zero address, zero_mul]

/-- Every nonzero raw RAM address has exactly one selected in-domain RAM index. -/
theorem ramRa_unique_of_address_ne_zero (charAbove2pow127 : 2 ^ 127 < ringChar F)
    (context : ConstraintContext joltInstance privateInputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
    (t : Fin params.traceLength) (nonzero : witness.RamAddress t ≠ 0) :
    ∃! address, witness.RamRa address t = 1 := by
  rcases ramRa_zero_or_unique charAbove2pow127 context equations t with zero | selected
  · exact False.elim (nonzero ((ramRa_zero_iff_address_zero charAbove2pow127 context equations t).mp zero))
  · exact selected

end JoltConstraints.Soundness
