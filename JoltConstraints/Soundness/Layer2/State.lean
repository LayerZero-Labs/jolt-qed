import JoltConstraints.Soundness.Layer2.Registers
import JoltConstraints.Soundness.Layer2.RegisterMap

/-! The register table's initial values agree with the actual initial state.
Preparing an instruction's PC leaves those register values unchanged. Neither
fact needs an honest trace or an instruction-execution premise. -/

set_option autoImplicit false

namespace JoltConstraints.Soundness

/-- Preparing PC and nextPC preserves every architectural and virtual source. -/
theorem sourceValue_advance_pc (source : JoltISA.Src)
    (address : BitVec 64) (compressed : Bool) (state : SailJoltState) :
    JoltISA.sourceValue source (advance_pc address compressed state) =
      JoltISA.sourceValue source state := by
  cases source with
  | vreg r => rfl
  | xreg r =>
    reg_cases r <;>
      simp_all only [JoltISA.sourceValue, advance_pc, Std.ExtDHashMap.get?_insert,
        beq_iff_eq, reduceCtorEq, ↓reduceDIte]

/-- Every register-table index agrees with the corresponding initial-state
word. The initialization equation is supplied by `context.initialized`. -/
theorem registersVal_initial_state
    {F : Type} [Field F] {params : WitnessParams} {witness : WitnessType F params}
    (history : registersValEqPrefixRdInc witness)
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    {initialState : SailJoltState}
    (built : joltInstance.initial_state privateInputs = some initialState)
    (register : Fin 128) :
    witness.RegistersVal register ⟨0, Nat.two_pow_pos _⟩ =
      ((JoltISA.sourceValue (JoltRegisterEncoding.source (BitVec.ofFin register))
        initialState).toNat : F) := by
  rw [registersVal_zero history,
    initial_state_sourceValue joltInstance privateInputs initialState built]
  simp

/-- The same table agrees with the initial state after preparing the first PC. -/
theorem registersVal_initial_advance_pc
    {F : Type} [Field F] {params : WitnessParams} {witness : WitnessType F params}
    (history : registersValEqPrefixRdInc witness)
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    {initialState : SailJoltState}
    (built : joltInstance.initial_state privateInputs = some initialState)
    (address : BitVec 64) (compressed : Bool) (register : Fin 128) :
    witness.RegistersVal register ⟨0, Nat.two_pow_pos _⟩ =
      ((JoltISA.sourceValue (JoltRegisterEncoding.source (BitVec.ofFin register))
        (advance_pc address compressed initialState)).toNat : F) := by
  rw [sourceValue_advance_pc]
  exact registersVal_initial_state history built register

end JoltConstraints.Soundness
