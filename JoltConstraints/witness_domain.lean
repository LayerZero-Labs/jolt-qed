import JoltConstraints.witness_helpers.ram_ra_chunk
import JoltConstraints.witness_params

set_option autoImplicit false

-- Rust: [remapped_ram_address](/Users/ari.biswas/Work-with-A16z/jolt/crates/jolt-witness/src/backend/trace/ram.rs:260).
-- Every nonzero RAM access must remap successfully and fit the chosen witness
-- domain. This includes device I/O. Rust treats raw address zero as no access;
-- a nonzero address below the layout's lowest address is an error, not padding.
-- This is a condition on witness parameters and the recorded execution, not an
-- extra ISA execution rule. It covers every actual row, before witness padding.
def WitnessParams.RamFits (p : WitnessParams) (trace : Trace) : Prop :=
  ∀ (i : Fin trace.rows.size),
    let row := getElem trace.rows i.val i.isLt
    let instruction :=
      (getElem trace.bytecode row.rowIndex.val row.rowIndex.isLt).instruction
    match TraceWitness.ramAccessAddress instruction row.preState with
    | none => True
    | some rawAddress =>
        rawAddress = 0 ∨ ∃ address : Nat,
          TraceWitness.remapRamAddress trace.initialState.jolt_device.memory_layout rawAddress = some address ∧
          address < p.ramSize

theorem WitnessParams.remappedRamAddress_lt (p : WitnessParams)
    (trace : Trace)
    (ramFits : p.RamFits trace) (t : Fin p.traceLength) (b : Nat)
    (hb : TraceWitness.remappedRamAddress trace t.val = some b) :
    b < p.ramSize := by
  unfold TraceWitness.remappedRamAddress at hb
  split_ifs at hb with ht
  · let row := getElem trace.rows t.val ht
    let instruction :=
      (getElem trace.bytecode row.rowIndex.val row.rowIndex.isLt).instruction
    have hf := ramFits ⟨t.val, ht⟩
    change (TraceWitness.ramAccessAddress instruction row.preState).bind
      (TraceWitness.remapRamAddress trace.initialState.jolt_device.memory_layout) = some b at hb
    change match TraceWitness.ramAccessAddress instruction row.preState with
      | none => True
      | some rawAddress =>
          rawAddress = 0 ∨ ∃ address : Nat,
            TraceWitness.remapRamAddress trace.initialState.jolt_device.memory_layout rawAddress =
              some address ∧ address < p.ramSize at hf
    cases ha : TraceWitness.ramAccessAddress instruction row.preState with
    | none => simp [ha] at hb
    | some raw =>
        simp only [ha, Option.bind_some] at hb
        simp only [ha] at hf
        rcases hf with hz | ⟨address, hremap, hlt⟩
        · subst raw
          simp [TraceWitness.remapRamAddress] at hb
        · rw [hremap] at hb
          cases Option.some.inj hb
          exact hlt

-- The witness's address of an LD or SD row is the honest trace's address of that row.
theorem TraceRow.ram_address_eq {bytecode : Array JoltInstructionRow}
    (row : TraceRow bytecode) :
    row.ram_address =
      (TraceWitness.ramAccessAddress bytecode[row.rowIndex].instruction row.preState).map
        BitVec.toNat := by
  unfold TraceRow.ram_address TraceWitness.ramAccessAddress
  cases bytecode[row.rowIndex].instruction <;> rfl

-- The lowest address is the lower of the two advice starts.
theorem MemoryLayout.get_lowest_address_toNat (layout : MemoryLayout) :
    layout.get_lowest_address.toNat =
      min layout.trusted_advice_start.toNat layout.untrusted_advice_start.toNat := by
  unfold MemoryLayout.get_lowest_address
  split <;> omega

-- An accepted run's RAM size is a power of two.
theorem HonestTrace.prover_config_ram_K_pow {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (config : ProverConfig) (accepted : trace.prover_config = some config) :
    ∃ log, config.ram_K = 2 ^ log := by
  unfold HonestTrace.prover_config at accepted
  -- the jump check, the length check and the address check
  rw [bind_some_iff] at accepted
  obtain ⟨_, _, accepted⟩ := accepted
  rw [bind_some_iff] at accepted
  obtain ⟨_, _, accepted⟩ := accepted
  rw [bind_some_iff] at accepted
  obtain ⟨_, _, accepted⟩ := accepted
  -- the config itself
  cases accepted
  exact ⟨_, rfl⟩

-- Rust's witness sizes hold every RAM access of an accepted run: each LD or SD
-- address is 0 or has a slot below ram_K (HonestTrace.prover_config_ram_fits).
theorem HonestTrace.witness_params_ram_fits {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (config : ProverConfig) (accepted : trace.prover_config = some config) :
    (trace.witness_params config accepted).RamFits trace := by
  intro i
  dsimp only
  obtain ⟨log, isPower⟩ := trace.prover_config_ram_K_pow config accepted
  have ramSizeIs : (trace.witness_params config accepted).ramSize = config.ram_K := by
    unfold WitnessParams.ramSize HonestTrace.witness_params
    dsimp only
    rw [isPower, Nat.log2_two_pow]
  cases access : TraceWitness.ramAccessAddress
      trace.bytecode[trace.rows[i.val].rowIndex].instruction trace.rows[i.val].preState with
  | none => trivial
  | some rawAddress =>
    have touches : trace.rows[i.val].ram_address = some rawAddress.toNat := by
      rw [TraceRow.ram_address_eq, access, Option.map_some]
    have member : trace.rows[i.val] ∈ trace.rows := Array.getElem_mem i.isLt
    rcases trace.prover_config_ram_fits config accepted _ member _ touches with
      zero | ⟨above, slot, remapped, small⟩
    · -- address 0 means no access
      left
      exact BitVec.eq_of_toNat_eq zero
    · -- otherwise it has the same slot in both remaps, below ram_K
      right
      refine ⟨slot, ?_, by rw [ramSizeIs]; exact small⟩
      unfold remap_address at remapped
      unfold TraceWitness.remapRamAddress
      rw [MemoryLayout.get_lowest_address_toNat] at above remapped
      have notZero : rawAddress.toNat ≠ 0 := by
        intro isZero
        rw [if_pos isZero] at remapped
        cases remapped
      rw [if_neg notZero] at remapped
      rw [if_neg (by omega)]
      exact remapped

