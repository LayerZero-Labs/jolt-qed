import JoltConstraints.theorems.Soundness.Layer6.ExecutionPrefix
import JoltConstraints.theorems.Soundness.Layer6.BytecodePC
import JoltConstraints.theorems.Soundness.Layer6.SelectedRows

open LeanRV64D

set_option autoImplicit false

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail LeanRV64D LeanRV64D.Functions JoltISA

namespace JoltInstance

/-- A selected padding cycle has unexpanded address zero, as the no-op slots
have no source address; for example, the reserved no-op slot has address zero.
See jolt/crates/jolt-witness/src/witnesses/pc.rs (`UnexpandedPc::extract`)
at ff6fc6568. -/
theorem unexpanded_zero_of_padding
    {F : Type} [Field F] (joltField : JoltField F)
    (joltInstance : JoltInstance SourceInstruction)
    {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (equations : JoltConstraints.ConstraintEquations context.bytecode context.initialRam
      context.io context.entry witness)
    (cycle : Fin params.traceLength)
    (padding : witness.InstructionFlags .IsNoop cycle = 1) :
    witness.UnexpandedPC cycle = 0 := by
  obtain ⟨slot, selected, _⟩ := JoltConstraints.Soundness.bytecodeRa_unique
    (JoltConstraints.Soundness.two_pow_127_lt_char joltField) context equations cycle
  have flag := JoltConstraints.Soundness.instructionFlag_of_selected_bytecode
    (JoltConstraints.Soundness.two_pow_127_lt_char joltField)
    context equations .IsNoop cycle slot selected
  have noRow : JoltConstraints.bytecodeRow context.bytecode slot.val = none := by
    cases present : JoltConstraints.bytecodeRow context.bytecode slot.val with
    | none => rfl
    | some row =>
      simp [JoltConstraints.bytecodeInstructionFlag, present,
        JoltMetadata.instructionFlag, padding] at flag
  rw [JoltConstraints.Soundness.unexpandedPC_of_selected_bytecode
    (JoltConstraints.Soundness.two_pow_127_lt_char joltField)
    context equations cycle slot selected]
  simp [JoltConstraints.bytecodeAddress, noRow]

/-- A nonterminal virtual row cannot occupy the final witness cycle, because
constraint 18 advances its positive expanded slot while the final shift is
zero. For example, the first ECALL row cannot be the witness's last row. -/
theorem nonterminal_at_last_cycle_impossible
    {F : Type} [Field F] (joltField : JoltField F)
    (joltInstance : JoltInstance SourceInstruction)
    {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (equations : JoltConstraints.ConstraintEquations context.bytecode context.initialRam
      context.io context.entry witness)
    (run : JoltConstraints.Soundness.UntrustedAnswerRun joltInstance privateInputs)
    (bytecodeEq : run.bytecode = context.bytecode)
    (last : TraceRow run.bytecode)
    (cycle : Fin params.traceLength) (lastCycle : cycle.val + 1 = params.traceLength)
    (slot : Fin (2 ^ params.logBytecodeK))
    (slotIndex : slot.val = last.rowIndex.val + 1)
    (selected : JoltConstraints.bytecodeRa witness slot cycle = 1)
    (inlineNext : witness.NextPC cycle = witness.PC cycle + 1) : False := by
  have pcZero : witness.NextPC cycle = 0 := by
    rw [equations.nextPCEqShift cycle]
    simp [show ¬ cycle.val + 1 < params.traceLength by omega]
  have expandedPC := JoltConstraints.Soundness.pc_of_selected_bytecode
    (JoltConstraints.Soundness.two_pow_127_lt_char joltField)
    context equations cycle slot selected
  have castZero : ((last.rowIndex.val + 2 : Nat) : F) = 0 := by
    have h : ((last.rowIndex.val + 1 : Nat) : F) + 1 = 0 := by
      calc
        ((last.rowIndex.val + 1 : Nat) : F) + 1 = witness.PC cycle + 1 := by
          rw [expandedPC, slotIndex]
        _ = witness.NextPC cycle := inlineNext.symm
        _ = 0 := pcZero
    have natEq : last.rowIndex.val + 2 = (last.rowIndex.val + 1) + 1 := by omega
    rw [natEq]
    simpa only [Nat.cast_add, Nat.cast_one] using h
  have bound : last.rowIndex.val + 2 < ringChar F := by
    have fit := (show params.BytecodeDomainFor run.bytecode.size by
      simpa only [bytecodeEq] using context.bytecodeDomain).rowsFit
    have powBound : 2 ^ params.logBytecodeK ≤ 2 ^ 64 :=
      Nat.pow_le_pow_right (by decide : 0 < 2) params.logBytecodeK_lt_usizeBits.le
    have charBound := JoltConstraints.Soundness.two_pow_64_lt_char
      (JoltConstraints.Soundness.two_pow_127_lt_char joltField)
    omega
  have zero : last.rowIndex.val + 2 = 0 :=
    JoltConstraints.Soundness.natCast_injective_below_char (b := 0) bound
      (by
        have charBound := JoltConstraints.Soundness.two_pow_64_lt_char
          (JoltConstraints.Soundness.two_pow_127_lt_char joltField)
        omega) (by simpa using castZero)
  omega

/-- A selected terminal non-jump row has the ordinary update flags: Jump and
DoNotUpdateUnexpandedPC are zero, while IsCompressed records that row's length.
For example, a terminal compressed ADDI uses a two-byte successor. -/
theorem selected_terminal_nonjump_flags
    {F : Type} [Field F] (joltField : JoltField F)
    (joltInstance : JoltInstance SourceInstruction)
    {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (equations : JoltConstraints.ConstraintEquations context.bytecode context.initialRam
      context.io context.entry witness)
    (cycle : Fin params.traceLength) (slot : Fin (2 ^ params.logBytecodeK))
    (selected : JoltConstraints.bytecodeRa witness slot cycle = 1)
    (row : JoltInstructionRow)
    (rowIs : JoltConstraints.bytecodeRow context.bytecode slot.val = some row)
    (terminal : row.virtual_sequence_remaining.getD 0 = 0)
    (jumpFalse : JoltMetadata.opcodeFlag row.instruction .Jump = false) :
    witness.OpFlags .Jump cycle = 0 ∧
      witness.OpFlags .DoNotUpdateUnexpandedPC cycle = 0 ∧
      witness.OpFlags .IsCompressed cycle = (if row.is_compressed then (1 : F) else 0) := by
  have jumpZero : witness.OpFlags .Jump cycle = 0 := by
    rw [JoltConstraints.Soundness.opFlag_of_selected_bytecode
      (JoltConstraints.Soundness.two_pow_127_lt_char joltField)
      context equations .Jump cycle slot selected]
    rw [JoltConstraints.bytecodeCircuitFlag, rowIs]
    change (if JoltMetadata.opcodeFlag row.instruction .Jump = true
      then (1 : F) else 0) = 0
    rw [jumpFalse]
    rfl
  have doNotZero : witness.OpFlags .DoNotUpdateUnexpandedPC cycle = 0 := by
    rw [JoltConstraints.Soundness.opFlag_of_selected_bytecode
      (JoltConstraints.Soundness.two_pow_127_lt_char joltField)
      context equations .DoNotUpdateUnexpandedPC cycle slot selected]
    rw [JoltConstraints.bytecodeCircuitFlag, rowIs]
    change (if row.virtual_sequence_remaining.getD 0 != 0 then (1 : F) else 0) = 0
    simp
    exact terminal
  have compressed : witness.OpFlags .IsCompressed cycle =
      (if row.is_compressed then (1 : F) else 0) := by
    rw [JoltConstraints.Soundness.opFlag_of_selected_bytecode
      (JoltConstraints.Soundness.two_pow_127_lt_char joltField)
      context equations .IsCompressed cycle slot selected]
    simp [JoltConstraints.bytecodeCircuitFlag, rowIs, JoltMetadata.circuitFlag]
    -- the two sides differ only in their `Decidable` instances
    rfl
  exact ⟨jumpZero, doNotZero, compressed⟩

/-- The ordinary update equation advances a row whose branch, jump and
continuation flags are zero by its source length as a field sum.
For example, a compressed ADDI at address `a` advances to `a + 2`.
See jolt/crates/jolt-claims/src/protocols/composed/r1cs/rv64.rs
(`NEXT_UNEXP_PC_UPDATE_OTHERWISE`) at `ff6fc6568`. -/
theorem ordinary_row_next_pc_value
    {F : Type} [Field F]
    {params : WitnessParams} (witness : WitnessType F params)
    (address : BitVec 64) (isCompressed : Bool)
    (update : JoltConstraints.nextUnexpandedPCUpdateOtherwise witness)
    (cycle : Fin params.traceLength)
    (currentPC : witness.UnexpandedPC cycle = (address.toNat : F))
    (jumpZero : witness.OpFlags .Jump cycle = 0)
    (branchZero : witness.ShouldBranch cycle = 0)
    (doNotZero : witness.OpFlags .DoNotUpdateUnexpandedPC cycle = 0)
    (compressed : witness.OpFlags .IsCompressed cycle =
      if isCompressed then (1 : F) else 0) :
    witness.NextUnexpandedPC cycle =
      ((address.toNat + (if isCompressed then 2 else 4) : Nat) : F) := by
  have relation := update cycle
  rw [branchZero, jumpZero, currentPC, doNotZero, compressed] at relation
  cases h : isCompressed <;> simp [h] at relation ⊢ <;>
    linear_combination relation

/-- A nonterminal virtual row advances the expanded bytecode PC by one slot.
For example, the first row of an ECALL expansion selects the next ECALL row.
Constraint 18 gives the step because the virtual flag is one and the last-row
flag is zero.
Jolt at `ff6fc6568`: `crates/jolt-claims/src/protocols/composed/r1cs/rv64.rs`
(`NEXT_PC_EQ_PC_PLUS_ONE_IF_INLINE`). -/
theorem nonterminal_virtual_row_pc_plus_one
    {F : Type} [Field F] (joltField : JoltField F)
    (joltInstance : JoltInstance SourceInstruction)
    {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (equations : JoltConstraints.ConstraintEquations context.bytecode context.initialRam
      context.io context.entry witness)
    (cycle : Fin params.traceLength) (slot : Fin (2 ^ params.logBytecodeK))
    (selected : JoltConstraints.bytecodeRa witness slot cycle = 1)
    (row : JoltInstructionRow)
    (rowIs : JoltConstraints.bytecodeRow context.bytecode slot.val = some row)
    (nonterminal : row.virtual_sequence_remaining.getD 0 ≠ 0) :
    witness.NextPC cycle = witness.PC cycle + 1 := by
  have virtual : witness.OpFlags .VirtualInstruction cycle = 1 := by
    rw [JoltConstraints.Soundness.opFlag_of_selected_bytecode
      (JoltConstraints.Soundness.two_pow_127_lt_char joltField)
      context equations .VirtualInstruction cycle slot selected]
    have some : row.virtual_sequence_remaining.isSome = true := by
      cases h : row.virtual_sequence_remaining with
      | none =>
        have zero : row.virtual_sequence_remaining.getD 0 = 0 := by rw [h]; rfl
        exact False.elim (nonterminal zero)
      | some n => rfl
    rw [JoltConstraints.bytecodeCircuitFlag, rowIs]
    change (if row.virtual_sequence_remaining.isSome = true then (1 : F) else 0) = 1
    rw [some]
    rfl
  have nonlast : witness.OpFlags .IsLastInSequence cycle = 0 := by
    rw [JoltConstraints.Soundness.opFlag_of_selected_bytecode
      (JoltConstraints.Soundness.two_pow_127_lt_char joltField)
      context equations .IsLastInSequence cycle slot selected]
    have notLast : row.virtual_sequence_remaining ≠ some 0 := by
      intro h
      rw [h] at nonterminal
      exact nonterminal rfl
    rw [JoltConstraints.bytecodeCircuitFlag, rowIs]
    change (if row.virtual_sequence_remaining == some 0 then (1 : F) else 0) = 0
    split_ifs with equal
    · exact False.elim (notLast (beq_iff_eq.mp equal))
    · rfl
  have relation := equations.nextPCEqPCPlusOneIfInline cycle
  rw [virtual, nonlast] at relation
  linear_combination relation

end JoltInstance
