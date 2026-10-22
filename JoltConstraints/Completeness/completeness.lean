/-
The base completeness statement: every instance in Jolt's language has private
inputs and a witness that satisfy every modeled constraint, under the instance
assumptions below.
It inherits the sorrys listed in model_review.md (Proofs owed). Two of them are
false until Jolt bugs are fixed (a16z/jolt#1951 items 1 and 4).
-/
import JoltConstraints.Completeness.All
import JoltConstraints.Completeness.Assumptions
import JoltConstraints.language

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

-- The witness's starting slot lies in the bytecode domain at the corrected sizes:
-- the slot is at most the number of rows, and the domain holds the rows plus the NoOp.
theorem HonestTrace.entry_lt_bytecode_domain {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (config : ProverConfig) (accepted : trace.corrected_prover_config = some config) :
    TraceWitness.bytecodePc trace 0 <
      2 ^ (trace.corrected_witness_params config accepted).logBytecodeK := by
  have rowsFit := (trace.corrected_witness_params_bytecode_domain config accepted).rowsFit
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

-- Completeness: every instance in Jolt's language has private inputs and a witness
-- that satisfy every constraint. The instance satisfies
-- `JoltInstance.CompletenessAssumptions` (Completeness/Assumptions.lean).
-- The witness is the one Jolt's prover builds from the honest trace, but at the
-- corrected sizes: Jolt's own RAM size is one slot too small for some traces
-- (a16z/jolt#1951 item 4; bug-report/ram-k-off-by-one).
theorem JoltInstance.completeness {F : Type} [Field F]
    (joltInstance : JoltInstance SourceInstruction)
    (assumptions : joltInstance.CompletenessAssumptions)
    (inLanguage : joltInstance.InLanguage) :
    ∃ (privateInputs : JoltPrivateInputs) (params : WitnessParams)
      (witness : WitnessType F params),
      JoltConstraints.AllConstraints joltInstance privateInputs witness := by
  obtain ⟨privateInputs, trace, claimsRunOutputs, proverAccepts, spoilAssertsPass⟩ :=
    inLanguage
  obtain ⟨rustConfig, rustSizes⟩ := Option.isSome_iff_exists.mp proverAccepts
  obtain ⟨config, accepted⟩ :=
    Option.isSome_iff_exists.mp (trace.corrected_prover_config_isSome rustConfig rustSizes)
  obtain ⟨slots, preprocessed⟩ := trace.exists_preprocessed
  obtain ⟨io, publicIo⟩ := trace.exists_public_io
  exact ⟨privateInputs, _, _, trace.allConstraints_corrected_sizes config accepted slots
    preprocessed ⟨TraceWitness.bytecodePc trace 0, trace.entry_lt_bytecode_domain config accepted⟩
    (trace.first_pc_eq_entry slots preprocessed) spoilAssertsPass assumptions.pcNoWrap
    assumptions.imageNonempty claimsRunOutputs io publicIo⟩
