/-
The immediate obligations below `JoltInstance.soundness`. Each unfinished helper
has a name and a concrete statement so the main theorem can be assembled without
adding premises. See `JoltConstraints/model_review.md`, "Proofs owed".
-/
import JoltConstraints.Constraints.All
import JoltConstraints.Soundness.Assumptions
import JoltConstraints.language
import JoltConstraints.witness_helpers.pc
import JoltConstraints.witness_helpers.rs1_value
import JoltConstraints.witness_helpers.rs2_value
import JoltConstraints.witness_helpers.ram_address

set_option autoImplicit false

namespace JoltInstance

/-- The execution tape reconstructed from the witness's advice rows. The bytecode
identifies those rows; the extraction itself is still an obligation. -/
noncomputable def soundnessWitnessTape {F : Type} [Field F] {params : WitnessParams}
    (bytecode : Array JoltInstructionRow) (witness : WitnessType F params) :
    Array (BitVec 8) := by
  sorry

/-- The witness observations needed at the top of soundness. Row equalities apply
to actual trace cycles; padding positions need no correspondence. `finalRamWord`
includes the device overlays and the special panic and termination words. -/
structure Represents {F : Type} [Field F] {params : WitnessParams}
    (witness : WitnessType F params) (trace : Trace) : Prop where
  rowsBound : trace.rows.size ≤ params.traceLength
  pc : ∀ t : Fin params.traceLength, t.val < trace.rows.size →
    witness.PC t = TraceWitness.PC params trace t
  rs1 : ∀ t : Fin params.traceLength, t.val < trace.rows.size →
    witness.Rs1Value t = TraceWitness.Rs1Value params trace t
  rs2 : ∀ t : Fin params.traceLength, t.val < trace.rows.size →
    witness.Rs2Value t = TraceWitness.Rs2Value params trace t
  ramAddress : ∀ t : Fin params.traceLength, t.val < trace.rows.size →
    witness.RamAddress t = TraceWitness.RamAddress params trace t
  finalRam : ∀ address : Fin params.ramSize,
    witness.RamValFinal address = ((TraceWitness.finalRamWord trace address.val).toNat : F)

/-- A. Reconstruct a single honest run from the selected witness rows, using the
witness's advice answers as one fixed tape. This includes the execution prefix,
stopping, and the final-memory correspondence. The B6 stopping and panic cases
are excluded by `TemporaryRestrictions`; the fixed-tape argument is still owed. -/
theorem soundness_reconstruct_trace {F : Type} [Field F] (joltField : JoltField F)
    (joltInstance : JoltInstance SourceInstruction)
    (assumptions : joltInstance.SoundnessAssumptions)
    (restrictions : joltInstance.TemporaryRestrictions)
    {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (equations : JoltConstraints.ConstraintEquations context.bytecode context.initialRam
      context.io context.entry witness) :
    ∃ trace : HonestTrace joltInstance
        { privateInputs with advice_tape := soundnessWitnessTape context.bytecode witness },
      trace.bytecode = context.bytecode ∧ Represents witness trace := by
  sorry

/-- B. The final RAM words and constraint 26 give the public output and panic
claim. The comparison includes device words through `finalRamWord`. -/
theorem soundness_matches_outputs {F : Type} [Field F] (joltField : JoltField F)
    (joltInstance : JoltInstance SourceInstruction)
    {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (equations : JoltConstraints.ConstraintEquations context.bytecode context.initialRam
      context.io context.entry witness)
    (trace : HonestTrace joltInstance
      { privateInputs with advice_tape := soundnessWitnessTape context.bytecode witness })
    (represented : Represents witness trace) :
    trace.matches_outputs := by
  sorry

/-- C. The represented rows and verifier bounds give Jolt prover acceptance.
In particular this must establish the last-jump check and that padding the real
row count, with Jolt's 256-row minimum, fits the instance maximum. -/
theorem soundness_prover_accepts {F : Type} [Field F] (joltField : JoltField F)
    (joltInstance : JoltInstance SourceInstruction)
    {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (equations : JoltConstraints.ConstraintEquations context.bytecode context.initialRam
      context.io context.entry witness)
    (trace : HonestTrace joltInstance
      { privateInputs with advice_tape := soundnessWitnessTape context.bytecode witness })
    (bytecodeEq : trace.bytecode = context.bytecode)
    (represented : Represents witness trace) :
    trace.prover_config.isSome := by
  sorry

/-- D. Each executed spoil assert uses its row's pre-state operands. The row
observations and lookup constraints must rule out a failing assertion. -/
theorem soundness_spoil_asserts_pass {F : Type} [Field F] (joltField : JoltField F)
    (joltInstance : JoltInstance SourceInstruction)
    {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (equations : JoltConstraints.ConstraintEquations context.bytecode context.initialRam
      context.io context.entry witness)
    (trace : HonestTrace joltInstance
      { privateInputs with advice_tape := soundnessWitnessTape context.bytecode witness })
    (bytecodeEq : trace.bytecode = context.bytecode)
    (represented : Represents witness trace) :
    trace.SpoilAssertsPass := by
  sorry

end JoltInstance
