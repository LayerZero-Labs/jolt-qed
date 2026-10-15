/-
The base completeness statement: when the honest trace shows the instance is in
Jolt's language, the witness Jolt's prover builds from it satisfies every modeled
constraint, under the premises below.
It inherits the sorrys listed in model_review.md (Proofs owed).
-/
import JoltConstraints.Completeness.All
import JoltConstraints.Completeness.Assumptions

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
-- the slot the witness starts at: the first row's slot, or the NoOp's slot 0 when the
-- trace is empty (the entry address is then 0).
-- See : jolt/crates/jolt-program/src/preprocess/bytecode.rs:218-226 (get_first_pc)
theorem HonestTrace.first_pc_eq_entry {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (slots : Array BytecodeSlot) (preprocessed : preprocess trace.bytecode = some slots) :
    get_first_pc slots joltInstance.program.entry_address =
      some (TraceWitness.bytecodePc trace 0) := by
  by_cases nonempty : 0 < trace.rows.size
  · -- the trace starts at the first row's slot
    have first := trace.starts_at_entry slots preprocessed (getElem trace.rows 0 nonempty)
      (Array.getElem?_eq_getElem nonempty)
    rw [TraceWitness.bytecodePc, dif_pos nonempty]
    exact first
  · -- with no rows the entry address is 0, which get_first_pc maps to the NoOp
    have zero : joltInstance.program.entry_address = 0 := by
      by_contra notZero
      exact nonempty (trace.nonempty notZero)
    rw [zero, TraceWitness.bytecodePc, dif_neg nonempty]
    unfold get_first_pc
    rw [if_pos rfl]

-- The witness's starting slot lies in the bytecode domain at Jolt's prover's sizes:
-- the slot is at most the number of rows, and the domain holds the rows plus the NoOp.
theorem HonestTrace.entry_lt_bytecode_domain {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (config : ProverConfig) (accepted : trace.prover_config = some config) :
    TraceWitness.bytecodePc trace 0 < 2 ^ (trace.witness_params config accepted).logBytecodeK := by
  have rowsFit : trace.bytecode.size + 1 ≤ 2 ^ Nat.clog 2 (trace.bytecode.size + 1) :=
    Nat.le_pow_clog (by decide) _
  have domainGrows : 2 ^ Nat.clog 2 (trace.bytecode.size + 1) ≤
      2 ^ (trace.witness_params config accepted).logBytecodeK :=
    Nat.pow_le_pow_right (by decide) (Nat.le_max_right _ _)
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

-- Completeness: if the honest trace shows the instance is in Jolt's language
-- (`claimsRunOutputs`) and Jolt's prover accepts it at the sizes in `config`, the
-- witness Jolt's prover builds satisfies every constraint. The instance satisfies
-- `JoltInstance.CompletenessAssumptions`; Completeness/Assumptions.lean has both
-- bundles.
theorem JoltInstance.completeness {F : Type} [Field F]
    (joltInstance : JoltInstance SourceInstruction)
    (assumptions : joltInstance.CompletenessAssumptions)
    (privateInputs : JoltPrivateInputs) (trace : HonestTrace joltInstance privateInputs)
    (claimsRunOutputs : trace.matches_outputs)
    (config : ProverConfig) (proverAccepts : trace.ProverAccepts config) :
    JoltConstraints.AllConstraints joltInstance privateInputs
      (trace.honestWitness (F := F) (trace.witness_params config proverAccepts.proverSizes)) := by
  obtain ⟨slots, preprocessed⟩ := trace.exists_preprocessed
  obtain ⟨io, publicIo⟩ := trace.exists_public_io
  exact trace.allConstraints_rust_sizes config proverAccepts.proverSizes
    proverAccepts.ramBoundary slots preprocessed
    ⟨TraceWitness.bytecodePc trace 0,
      trace.entry_lt_bytecode_domain config proverAccepts.proverSizes⟩
    (trace.first_pc_eq_entry slots preprocessed) proverAccepts.spoilAssertsPass
    assumptions.pcNoWrap assumptions.imageNonempty claimsRunOutputs io publicIo
