import JoltConstraints.Soundness.Layer3.History
import JoltConstraints.constraint_context
import JoltConstraints.honest_trace
import JoltConstraints.layout_facts

/-! The initial RAM table is the initializer's image, including both advice
buffers and public input. Preparing PC preserves the entire memory map and
device, hence any RAM encoding built from them. Relating device reads and writes
to the RAM history after execution remains a Layer 5b obligation. -/

set_option autoImplicit false

namespace JoltConstraints.Soundness

/-- Preparing PC preserves every observation of the memory map and Jolt device,
including their byte contents, layout, advice, output, and panic state. -/
theorem ramObservation_advance_pc {α : Sort _}
    (observe : Std.ExtHashMap Nat (BitVec 8) → JoltDevice → α)
    (address : BitVec 64) (compressed : Bool) (state : SailJoltState) :
    observe (advance_pc address compressed state).sail.mem
        (advance_pc address compressed state).jolt_device =
      observe state.sail.mem state.jolt_device := rfl

/-- The initial RAM-image encoding is unchanged by preparing PC. -/
theorem initialRamWordFromState_advance_pc
    (address : BitVec 64) (compressed : Bool) (state : SailJoltState) (index : Nat) :
    TraceWitness.initialRamWordFromState (advance_pc address compressed state) index =
      TraceWitness.initialRamWordFromState state index :=
  ramObservation_advance_pc
    (fun memory device => TraceWitness.initialRamWordFromState
      { state with sail := { state.sail with mem := memory }, jolt_device := device } index)
    address compressed state

/-- The actual initializer and the constraint context use the same RAM layout,
so their remapping bases and device regions agree. -/
theorem initial_state_memory_layout
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    {params : WitnessParams} (context : ConstraintContext joltInstance privateInputs params)
    {initialState : SailJoltState}
    (built : joltInstance.initial_state privateInputs = some initialState) :
    initialState.jolt_device.memory_layout = context.io.memory_layout := by
  have initialLayout := (initial_state_device joltInstance privateInputs initialState built).1
  have publicIo := context.publicIo
  unfold JoltInstance.public_io at publicIo
  obtain ⟨layout, hasLayout, sameIo⟩ := Option.bind_eq_some_iff.mp publicIo
  have publicLayout : layout = context.io.memory_layout :=
    congrArg JoltDevice.memory_layout (Option.some.inj sameIo)
  have same : layout = initialState.jolt_device.memory_layout :=
    Option.some.inj (hasLayout.symm.trans initialLayout)
  exact same.symm.trans publicLayout

/-- Every initial RAM-table entry agrees with the actual initial state.
The context binds its initial image to that same initialization computation. -/
theorem ramVal_initial_state
    {F : Type} [Field F] {params : WitnessParams} {witness : WitnessType F params}
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (context : ConstraintContext joltInstance privateInputs params)
    (history : ramValEqInitialPlusPrefixRamInc context.initialRam witness)
    {initialState : SailJoltState}
    (built : joltInstance.initial_state privateInputs = some initialState)
    (index : Fin params.ramSize) :
    witness.RamVal index ⟨0, Nat.two_pow_pos _⟩ =
      ((TraceWitness.initialRamWordFromState initialState index.val).toNat : F) := by
  obtain ⟨state, initialized, image⟩ := context.initialized
  have same : state = initialState := Option.some.inj (initialized.symm.trans built)
  subst state
  rw [ramVal_zero history, image]
  rfl

/-- Initial RAM agreement also holds after preparing the first instruction's PC. -/
theorem ramVal_initial_advance_pc
    {F : Type} [Field F] {params : WitnessParams} {witness : WitnessType F params}
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (context : ConstraintContext joltInstance privateInputs params)
    (history : ramValEqInitialPlusPrefixRamInc context.initialRam witness)
    {initialState : SailJoltState}
    (built : joltInstance.initial_state privateInputs = some initialState)
    (address : BitVec 64) (compressed : Bool) (index : Fin params.ramSize) :
    witness.RamVal index ⟨0, Nat.two_pow_pos _⟩ =
      ((TraceWitness.initialRamWordFromState
        (advance_pc address compressed initialState) index.val).toNat : F) := by
  rw [initialRamWordFromState_advance_pc]
  exact ramVal_initial_state context history built index

end JoltConstraints.Soundness
