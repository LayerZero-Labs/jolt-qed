import JoltConstraints.Soundness.Layer1.BytecodeReads
import JoltConstraints.Soundness.Helpers.PrefixSum

/-! Register-table histories and reads for an arbitrary satisfying witness.
The prefix-sum constraint gives zero initialization and the single-cycle
increment. Bytecode selection then identifies each source and destination,
including absent operands and padding slots.

These are field-valued table facts. `Layer2/State.lean` connects initialization
to execution state, and `Layer2/ZeroRegister.lean` proves preservation of x0. -/

set_option autoImplicit false

namespace JoltConstraints.Soundness

open scoped BigOperators

variable {F : Type} [Field F] {params : WitnessParams} {witness : WitnessType F params}

/-- Every register-table entry starts at zero. The cycle domain is nonempty
because its length is `2^logT`. -/
theorem registersVal_zero (history : registersValEqPrefixRdInc witness)
    (register : Fin 128) :
    witness.RegistersVal register ⟨0, Nat.two_pow_pos _⟩ = 0 := by
  rw [history]
  simp

/-- Between two in-domain cycles, a register changes by its selected write
increment. There is no register-table column at cycle `traceLength`. -/
theorem registersVal_succ (history : registersValEqPrefixRdInc witness)
    (register : Fin 128) (t : Fin params.traceLength)
    (next : t.val + 1 < params.traceLength) :
    witness.RegistersVal register ⟨t.val + 1, next⟩ =
      witness.RegistersVal register t + witness.RdWa register t * witness.RdInc t := by
  rw [history register ⟨t.val + 1, next⟩, history register t]
  exact sum_before_succ (fun cycle => witness.RdWa register cycle * witness.RdInc cycle) t

private theorem sum_bytecodeRegisterSelector (bytecode : Array JoltInstructionRow)
    (operand : JoltISA.Instr → Option (Fin 128)) (address : Nat)
    (value : Fin 128 → F) :
    (∑ register : Fin 128, bytecodeRegisterSelector bytecode operand register address *
      value register) =
      match (bytecodeRow bytecode address).bind (fun row => operand row.instruction) with
      | none => 0
      | some register => value register := by
  classical
  cases rowIs : bytecodeRow bytecode address with
  | none => simp [bytecodeRegisterSelector, rowIs]
  | some row =>
    cases operandIs : operand row.instruction with
    | none => simp [bytecodeRegisterSelector, rowIs, operandIs]
    | some register => simp [bytecodeRegisterSelector, rowIs, operandIs]

variable {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}

/-- The first source reads its register-table entry. An absent source or a
padding slot reads zero; an explicit x0 reads the table entry at index zero. -/
theorem rs1Value_of_selected_bytecode (charAbove2pow127 : 2 ^ 127 < ringChar F)
    (context : ConstraintContext joltInstance privateInputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
    (t : Fin params.traceLength) (chosen : Fin (2 ^ params.logBytecodeK))
    (selected : bytecodeRa witness chosen t = 1) :
    witness.Rs1Value t =
      match (bytecodeRow context.bytecode chosen.val).bind
          (fun row => bytecodeRs1Register row.instruction) with
      | none => 0
      | some register => witness.RegistersVal register t := by
  rw [equations.rs1ValueEqRegistersRead t]
  simp_rw [rs1Ra_of_selected_bytecode charAbove2pow127 context equations _ t chosen selected]
  exact sum_bytecodeRegisterSelector context.bytecode bytecodeRs1Register chosen.val _

/-- The second source reads its register-table entry, with the same distinction
between an absent source and x0. -/
theorem rs2Value_of_selected_bytecode (charAbove2pow127 : 2 ^ 127 < ringChar F)
    (context : ConstraintContext joltInstance privateInputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
    (t : Fin params.traceLength) (chosen : Fin (2 ^ params.logBytecodeK))
    (selected : bytecodeRa witness chosen t = 1) :
    witness.Rs2Value t =
      match (bytecodeRow context.bytecode chosen.val).bind
          (fun row => bytecodeRs2Register row.instruction) with
      | none => 0
      | some register => witness.RegistersVal register t := by
  rw [equations.rs2ValueEqRegistersRead t]
  simp_rw [rs2Ra_of_selected_bytecode charAbove2pow127 context equations _ t chosen selected]
  exact sum_bytecodeRegisterSelector context.bytecode bytecodeRs2Register chosen.val _

/-- A destination's write value is its old table value plus `RdInc`.
With no destination, including padding, the write value is zero. -/
theorem rdWriteValue_of_selected_bytecode (charAbove2pow127 : 2 ^ 127 < ringChar F)
    (context : ConstraintContext joltInstance privateInputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
    (t : Fin params.traceLength) (chosen : Fin (2 ^ params.logBytecodeK))
    (selected : bytecodeRa witness chosen t = 1) :
    witness.RdWriteValue t =
      match (bytecodeRow context.bytecode chosen.val).bind
          (fun row => bytecodeRdRegister row.instruction) with
      | none => 0
      | some register => witness.RegistersVal register t + witness.RdInc t := by
  rw [equations.rdWriteValueEqRegistersReadWrite t]
  simp_rw [rdWa_of_selected_bytecode charAbove2pow127 context equations _ t chosen selected]
  exact sum_bytecodeRegisterSelector context.bytecode bytecodeRdRegister chosen.val _

/-- The next table replaces only the selected destination with `RdWriteValue`.
With no destination, every entry is unchanged. Selection is supplied by
`bytecodeRa_unique`; no execution or initial-state hypothesis is used. -/
theorem registersVal_succ_of_selected_bytecode (charAbove2pow127 : 2 ^ 127 < ringChar F)
    (context : ConstraintContext joltInstance privateInputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
    (register : Fin 128) (t : Fin params.traceLength)
    (next : t.val + 1 < params.traceLength) (chosen : Fin (2 ^ params.logBytecodeK))
    (selected : bytecodeRa witness chosen t = 1) :
    witness.RegistersVal register ⟨t.val + 1, next⟩ =
      match (bytecodeRow context.bytecode chosen.val).bind
          (fun row => bytecodeRdRegister row.instruction) with
      | none => witness.RegistersVal register t
      | some destination =>
          if register = destination then witness.RdWriteValue t
          else witness.RegistersVal register t := by
  rw [registersVal_succ equations.registersValEqPrefixRdInc register t next,
    rdWa_of_selected_bytecode charAbove2pow127 context equations register t chosen selected]
  have write := rdWriteValue_of_selected_bytecode charAbove2pow127 context equations t chosen selected
  cases rowIs : bytecodeRow context.bytecode chosen.val with
  | none => simp [bytecodeRegisterSelector, rowIs]
  | some row =>
    cases operandIs : bytecodeRdRegister row.instruction with
    | none => simp [bytecodeRegisterSelector, rowIs, operandIs]
    | some destination =>
      by_cases same : register = destination
      · subst register
        simpa [bytecodeRegisterSelector, rowIs, operandIs] using write.symm
      · simp [bytecodeRegisterSelector, rowIs, operandIs, same, Ne.symm same]

end JoltConstraints.Soundness
