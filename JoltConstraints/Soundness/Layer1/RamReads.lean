import JoltConstraints.Soundness.Layer1.Ram

/-! A selected RAM index determines the address, read, and write columns.
`ramRa_unique_of_address_ne_zero` supplies a selected index for nonzero
`RamAddress`; `ram_zero_effects` handles zero addresses. These are witness
column facts, before interpreting them as execution state. -/

set_option autoImplicit false

namespace JoltConstraints.Soundness

open scoped BigOperators

variable {F : Type} [Field F]
  {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
  {params : WitnessParams} {witness : WitnessType F params}

/-- A selected RAM index determines the raw byte-address column. -/
theorem ramAddress_of_selected (charAbove2pow127 : 2 ^ 127 < ringChar F)
    (context : ConstraintContext joltInstance privateInputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
    (t : Fin params.traceLength) (chosen : Fin params.ramSize)
    (selected : witness.RamRa chosen t = 1) :
    witness.RamAddress t =
      ((ramLowestAddress context.io.memory_layout + 8 * chosen.val : Nat) : F) := by
  rw [equations.ramAddressEqRamRaf t]
  exact ram_read_of_selected charAbove2pow127 context equations t _ chosen selected

/-- A selected RAM index reads its table value at the current cycle. -/
theorem ramReadValue_of_selected (charAbove2pow127 : 2 ^ 127 < ringChar F)
    (context : ConstraintContext joltInstance privateInputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
    (t : Fin params.traceLength) (chosen : Fin params.ramSize)
    (selected : witness.RamRa chosen t = 1) :
    witness.RamReadValue t = witness.RamVal chosen t := by
  rw [equations.ramReadValueEqRamRead t]
  simpa only [mul_comm] using
    ram_read_of_selected charAbove2pow127 context equations t (fun address => witness.RamVal address t)
      chosen selected

/-- A selected RAM index writes its current table value plus the cycle's increment. -/
theorem ramWriteValue_of_selected (charAbove2pow127 : 2 ^ 127 < ringChar F)
    (context : ConstraintContext joltInstance privateInputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
    (t : Fin params.traceLength) (chosen : Fin params.ramSize)
    (selected : witness.RamRa chosen t = 1) :
    witness.RamWriteValue t = witness.RamVal chosen t + witness.RamInc t := by
  rw [equations.ramWriteValueEqRamReadWrite t]
  simpa only [mul_comm] using
    ram_read_of_selected charAbove2pow127 context equations t
      (fun address => witness.RamVal address t + witness.RamInc t) chosen selected

end JoltConstraints.Soundness
