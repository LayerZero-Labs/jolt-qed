import JoltConstraints.witness_helpers.ram_ra_chunk
import JoltConstraints.witness_params

open LeanRV64D

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

/-- When Jolt's prover accepts the honest trace (`proverAccepts`), its RAM size
`config.ram_K` is a power of two.
For example, a run touching word 1000 gets `ram_K = 1024 = 2^10`.
See jolt/crates/jolt-prover/src/config.rs (`ProverConfig::derive_from_dimensions`,
`ProverConfig::from_padded_dimensions`) at c97e9300. -/
theorem HonestTrace.prover_config_ram_K_pow {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (config : ProverConfig) (proverAccepts : trace.prover_config joltInstance = some config) :
    ∃ log, config.ram_K = 2 ^ log := by
  obtain ⟨_, _, _, sizeIs, _⟩ := trace.prover_config_ram_K config proverAccepts
  exact ⟨_, sizeIs⟩

/-- The RAM domain at Jolt's sizes, `2 ^ logRamK`, is Jolt's RAM size `config.ram_K`,
since that is a power of two.
For example, `ram_K = 1024` gives `logRamK = 10` and a 1024-word domain. -/
theorem HonestTrace.witness_params_ram_size {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (config : ProverConfig) (proverAccepts : trace.prover_config joltInstance = some config) :
    (trace.witness_params config proverAccepts).ramSize = config.ram_K := by
  obtain ⟨log, isPower⟩ := trace.prover_config_ram_K_pow config proverAccepts
  unfold WitnessParams.ramSize HonestTrace.witness_params
  dsimp only
  rw [isPower, Nat.log2_two_pow]

/-- Jolt's witness sizes hold every RAM access of the honest trace
(`WitnessParams.RamFits`): each LD, SD or floor-row address is 0 (no access) or remaps to
a word index below `config.ram_K` (`HonestTrace.prover_config_ram_fits`).
That bound uses `HonestTrace.prover_config_holds_highest_slot`, which holds under the
fix of a16z/jolt#1951 item 4 that Jolt's prover model follows.
For example, with lowest address `0x7fff8000`, an SD at `0x80000010` uses word 4098,
which must be below `config.ram_K`. -/
theorem HonestTrace.witness_params_ram_fits {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (config : ProverConfig) (proverAccepts : trace.prover_config joltInstance = some config) :
    (trace.witness_params config proverAccepts).RamFits trace := by
  intro i
  dsimp only
  cases access : TraceWitness.ramAccessAddress
      trace.bytecode[trace.rows[i.val].rowIndex].instruction trace.rows[i.val].preState with
  | none => trivial
  | some rawAddress =>
    have touches : trace.rows[i.val].ram_address = some rawAddress.toNat := by
      rw [TraceRow.ram_address_eq, access, Option.map_some]
    have member : trace.rows[i.val] ∈ trace.rows := Array.getElem_mem i.isLt
    rcases trace.prover_config_ram_fits config proverAccepts _ member _ touches with
      zero | ⟨above, slot, remapped, small⟩
    · -- address 0 means no access
      left
      exact BitVec.eq_of_toNat_eq zero
    · -- otherwise it has the same slot in both remaps, below ram_K
      right
      refine ⟨slot, ?_, by rw [trace.witness_params_ram_size config proverAccepts]; exact small⟩
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
