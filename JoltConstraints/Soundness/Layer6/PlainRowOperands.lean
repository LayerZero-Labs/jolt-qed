import JoltConstraints.Soundness.Layer5.Registers
import JoltConstraints.Completeness.Helpers.RegistersReadProofHelpers
import JoltConstraints.expansion_temp_liveness

/-! Operand observations shared by the plain-row instruction families. -/
set_option autoImplicit false
namespace JoltInstance
open JoltConstraints JoltConstraints.Soundness
open Sail PreSail LeanRV64D.Functions JoltISA

private theorem readSources_eq_operands (instruction : Instr) :
    ExpansionTempLiveness.readSources instruction =
      (rs1Operand? instruction).toList ++ (rs2Operand? instruction).toList := by
  cases instruction <;> rfl

private theorem operand_value {F : Type} [Field F] {params : WitnessParams}
    {witness : WitnessType F params} {t : Fin params.traceLength}
    {live : Fin 128 → Prop} {pre : SailJoltState}
    (agrees : RegisterAgreementOn live witness t pre) (operand : Option Src)
    (canonical : ∀ source ∈ operand, JoltRegisterEncoding.sourceIsCanonical source = true)
    (sourcesLive : ∀ source ∈ operand, live (TraceWitness.sourceRegisterAddress source)) :
    (match operand.map TraceWitness.sourceRegisterAddress with
      | none => 0 | some register => witness.RegistersVal register t) =
    (match (generalizing := false) operand with | some source => ((sourceValue source pre).toNat : F) | none => 0) := by
  cases operand with
  | none => rfl
  | some source => exact (agrees.read source (canonical source rfl) (sourcesLive source rfl)).2

/-- Live sources identify both selected operand values in the prepared state.
For example, AND reads two live sources, whereas LUI has two zero observations. -/
theorem row_operand_observations {F : Type} [Field F] {params : WitnessParams}
    (joltField : 2 ^ 128 < ringChar F) {witness : WitnessType F params} {live : Fin 128 → Prop}
    {inst : JoltInstance SourceInstruction} {inputs : JoltPrivateInputs}
    (context : ConstraintContext inst inputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
    {t : Fin params.traceLength} {slot : Fin (2 ^ params.logBytecodeK)}
    (selected : bytecodeRa witness slot t = 1)
    {row : JoltInstructionRow} (rowIs : bytecodeRow context.bytecode slot.val = some row)
    {pre : SailJoltState} (agrees : RegisterAgreementOn live witness t pre)
    (sourcesLive : ∀ source ∈ ExpansionTempLiveness.readSources row.instruction,
      live (TraceWitness.sourceRegisterAddress source)) :
    witness.Rs1Value t =
      (match rs1Operand? row.instruction with | some s => ((sourceValue s pre).toNat : F) | none => 0) ∧
    witness.Rs2Value t =
      (match rs2Operand? row.instruction with | some s => ((sourceValue s pre).toNat : F) | none => 0) := by
  have canonical := (bytecodeRow_rowOk context rowIs).canonical
  rw [readSources_eq_operands] at sourcesLive
  rw [rs1Value_of_selected_bytecode (two_pow_127_lt_char joltField) context equations t slot selected,
    rs2Value_of_selected_bytecode (two_pow_127_lt_char joltField) context equations t slot selected]
  simp only [rowIs, Option.bind_some, bytecodeRs1Register_eq_rs1Operand,
    bytecodeRs2Register_eq_rs2Operand]
  constructor
  · apply operand_value agrees
    · intro source member
      exact rs1Operand_canonical _ _ canonical member
    · intro source member
      exact sourcesLive source (List.mem_append_left _ (by simpa using member))
  · apply operand_value agrees
    · intro source member
      exact rs2Operand_canonical _ _ canonical member
    · intro source member
      exact sourcesLive source (List.mem_append_right _ (by simpa using member))

end JoltInstance
