/-
The base completeness statement: for every instance and every honest trace that puts
it in Jolt's language, the witness Jolt's prover builds, at the sizes Jolt's prover
picks, satisfies every modeled constraint, under the instance assumptions below.
It inherits the sorrys listed in model_review.md (Proofs owed). Some of them are
false until Jolt bugs are fixed (a16z/jolt#1949, #1950 and #1951 items 1 and 4).
-/
import JoltConstraints.Completeness.All
import JoltConstraints.Completeness.Assumptions
import JoltConstraints.language
import JoltConstraints.advice_inputs

open LeanRV64D

set_option autoImplicit false

-- Jolt's preprocessing accepts the honest trace's bytecode: its rows pass the PC map
-- checks, since the trace's `accepted` field says Jolt accepts the program.
theorem HonestTrace.exists_preprocessed {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs) :
    ∃ slots, preprocess trace.bytecode = some slots := by
  have pcMapOk := accepted_pc_map_ok joltInstance trace.bytecode trace.expands trace.accepted
  unfold preprocess
  rw [if_pos pcMapOk]
  exact ⟨_, rfl⟩

-- Jolt's verifier finds the entry slot with get_first_pc. For the honest trace it is
-- the slot the witness starts at: the first row's slot.
-- See : jolt/crates/jolt-program/src/preprocess/bytecode.rs:218-226 (get_first_pc)
theorem HonestTrace.first_pc_eq_entry {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (slots : Array BytecodeSlot) (preprocessed : preprocess trace.bytecode = some slots) :
    get_first_pc slots joltInstance.program.entry_address =
      some (TraceWitness.bytecodePc trace 0) := by
  have nonempty := trace.nonempty
  have first := trace.starts_at_entry slots preprocessed (getElem trace.rows 0 nonempty)
    (Array.getElem?_eq_getElem nonempty)
  rw [TraceWitness.bytecodePc, dif_pos nonempty]
  exact first

/-- The witness's starting slot, `TraceWitness.bytecodePc trace 0`, lies in the bytecode
domain at Jolt's sizes: the slot is at most the number of rows, and the domain holds the
rows plus the NoOp.
For example, a 5-row bytecode has an 8-slot domain, and the starting slot is at most 5. -/
theorem HonestTrace.entry_lt_bytecode_domain {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (config : ProverConfig) (proverAccepts : trace.prover_config joltInstance = some config) :
    TraceWitness.bytecodePc trace 0 <
      2 ^ (trace.witness_params config proverAccepts).logBytecodeK := by
  have rowsFit := (trace.witness_params_bytecode_domain config proverAccepts).rowsFit
  unfold TraceWitness.bytecodePc
  split_ifs with nonempty
  · have inBytecode := (getElem trace.rows 0 nonempty).rowIndex.isLt
    omega
  · exact pow_pos (by decide : 0 < (2 : Nat)) _

-- Jolt's verifier has public I/O for the instance: the instance's memory layout
-- builds, since Jolt's tracer started from it.
theorem HonestTrace.exists_public_io {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs) :
    ∃ io, joltInstance.public_io = some io := by
  obtain ⟨layoutBuilt, _⟩ := initial_state_device joltInstance privateInputs trace.initialState
    trace.initialized
  unfold JoltInstance.public_io
  rw [layoutBuilt]
  exact ⟨_, rfl⟩

/-- Completeness of Jolt: the verifier accepts the table Jolt's prover builds, at the sizes
Jolt's prover picks.
For an instance `joltInstance` that meets `JoltInstance.CompletenessAssumptions`
(`Completeness/Assumptions.lean`), take any private inputs `privateInputs` and any honest
trace `trace` of the instance on them that meets the three conditions of
`JoltInstance.InLanguage`: it ends with the claimed outputs (`claimsRunOutputs`), no spoil
assert fails (`spoilAssertsPass`), and Jolt's prover accepts it with config `config`
(`proverAccepts`).
Then the honest witness at Jolt's witness sizes (`HonestTrace.witness_params`) satisfies
`AllConstraints` with the words of the untrusted-advice block of the run's initial RAM as
the committed advice (`JoltConstraints.adviceBlockWords`).
For example, a 300-row run that touches RAM word 1000 is accepted on a 512-cycle witness
with a 1024-word RAM table.
It inherits the gaps in `model_review.md` ("Proofs owed").
Jolt's prover and verifier RAM sizes include the fix of a16z/jolt#2250 (`touched + 1` and
`div_ceil(8)`), so Jolt's RAM table holds the highest touched word
(`HonestTrace.prover_config_holds_highest_slot`). -/
theorem JoltInstance.completeness {F : Type} [Field F]
    (joltInstance : JoltInstance SourceInstruction)
    (assumptions : joltInstance.CompletenessAssumptions)
    (privateInputs : JoltPrivateInputs)
    (trace : HonestTrace joltInstance privateInputs)
    (claimsRunOutputs : trace.matches_outputs joltInstance)
    (spoilAssertsPass : trace.SpoilAssertsPass)
    (config : ProverConfig)
    (proverAccepts : trace.prover_config joltInstance = some config) :
    JoltConstraints.AllConstraints joltInstance
      (JoltConstraints.adviceBlockWords trace.initialState.jolt_device.memory_layout
        (TraceWitness.initialRamWord trace))
      (HonestTrace.honestWitness (F := F) (trace.witness_params config proverAccepts) trace) := by
  obtain ⟨slots, preprocessed⟩ := trace.exists_preprocessed
  obtain ⟨io, publicIo⟩ := trace.exists_public_io
  obtain ⟨context, equations⟩ := trace.allConstraintsOnBytes_prover_sizes (F := F) config
    proverAccepts
    slots preprocessed
    ⟨TraceWitness.bytecodePc trace 0, trace.entry_lt_bytecode_domain config proverAccepts⟩
    (trace.first_pc_eq_entry slots preprocessed) spoilAssertsPass
    joltInstance.program.next_pc_no_wrap assumptions.imageNonempty claimsRunOutputs io publicIo
  have satisfied := JoltConstraints.allConstraints_of_onBytes context equations
  obtain ⟨state, initialized, ramIs⟩ := context.initialized
  have stateIs : state = trace.initialState :=
    Option.some.inj (initialized.symm.trans trace.initialized)
  rw [← JoltConstraints.Soundness.initial_state_memory_layout context initialized, ramIs, stateIs] at satisfied
  exact satisfied

/-- Completeness, existential form: every instance in Jolt's language
(`JoltInstance.InLanguage`) that meets `JoltInstance.CompletenessAssumptions` has committed
untrusted-advice words and a witness, at some sizes, that satisfy every constraint.
It follows from `JoltInstance.completeness` by unpacking `InLanguage`: the witness is the
honest one at Jolt's sizes.
For example, an instance whose program writes its claimed output and ends in `j .` has
the honest witness of that run as its witness. -/
theorem JoltInstance.completeness_someWitness {F : Type} [Field F]
    (joltInstance : JoltInstance SourceInstruction)
    (assumptions : joltInstance.CompletenessAssumptions)
    (inLanguage : joltInstance.InLanguage) :
    ∃ (untrustedAdvice : Nat → F) (params : WitnessParams)
      (witness : WitnessType F params),
      JoltConstraints.AllConstraints joltInstance untrustedAdvice witness := by
  obtain ⟨privateInputs, trace, claimsRunOutputs, proverAccepts, spoilAssertsPass⟩ :=
    inLanguage
  obtain ⟨config, accepted⟩ := Option.isSome_iff_exists.mp proverAccepts
  exact ⟨_, _, _, JoltInstance.completeness joltInstance assumptions privateInputs
    trace claimsRunOutputs spoilAssertsPass config accepted⟩
