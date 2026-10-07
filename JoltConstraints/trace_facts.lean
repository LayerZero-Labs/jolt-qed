/-
Facts about the honest trace as a whole: how its rows sit in the program's bytecode.
Each one is proved from honest_trace.lean and the program facts.
-/
import JoltConstraints.program_facts
import JoltConstraints.honest_trace
import JoltConstraints.execution_facts
import JoltConstraints.layout_facts

set_option autoImplicit false

-- The trace starts at the slot Rust's get_first_pc picks for the entry address: one
-- past the first row's position, since the NoOp takes slot 0.
-- See : jolt/crates/jolt-program/src/preprocess/bytecode.rs:218-226 (get_first_pc)
theorem HonestTrace.starts_at_entry {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (slots : Array BytecodeSlot) (preprocessed : preprocess trace.bytecode = some slots)
    (first : HonestTraceRow trace.bytecode) (firstRow : trace.rows[0]? = some first) :
    get_first_pc slots joltInstance.program.entry_address = some (first.rowIndex.val + 1) := by
  obtain ⟨entryAddress, entryStarts, _⟩ := trace.starts first firstRow
  have accepted := accepted_pc_map_ok joltInstance trace.bytecode trace.expands trace.accepted
  obtain ⟨noopFirst, rowsAfter, _, _⟩ := preprocess_slots trace.bytecode slots preprocessed
  -- the entry address is a row's address, so it is at least RAM_START_ADDRESS, not 0
  have addressOk := pc_map_ok_addresses trace.bytecode accepted first.rowIndex first.rowIndex.isLt
  have notZero : joltInstance.program.entry_address ≠ 0 := by
    intro zero
    rw [Fin.getElem_fin] at entryAddress
    rw [entryAddress, zero] at addressOk
    unfold bytecode_address_ok JoltISA.RAM_START_ADDRESS at addressOk
    simp only [Bool.and_eq_true, decide_eq_true_eq] at addressOk
    have zeroValue : (0 : BitVec 64).toNat = 0 := rfl
    omega
  -- get_first_pc searches the slots for the first row at the entry address
  unfold get_first_pc
  rw [if_neg notZero, Array.findIdx?_eq_some_iff_getElem]
  obtain ⟨inSlots, slotIsRow⟩ := Array.getElem?_eq_some_iff.mp (rowsAfter _ first.rowIndex.isLt)
  refine ⟨inSlots, ?_, ?_⟩
  · -- the first row's slot holds a row at the entry address
    rw [slotIsRow]
    simp only [beq_iff_eq]
    exact entryAddress
  · -- no earlier slot does: slot 0 is the NoOp, and no earlier row has that address
    intro slot before
    cases slot with
    | zero =>
      obtain ⟨_, slotIsNoop⟩ := Array.getElem?_eq_some_iff.mp noopFirst
      rw [slotIsNoop]
      dsimp only
      exact Bool.false_ne_true
    | succ position =>
      obtain ⟨_, slotIsEarlier⟩ :=
        Array.getElem?_eq_some_iff.mp (rowsAfter position (by omega))
      rw [slotIsEarlier]
      simp only [beq_iff_eq]
      intro sameAddress
      rw [Fin.getElem_fin] at entryAddress entryStarts
      have later := expand_program_first_of_address joltInstance.program trace.bytecode
        trace.expands accepted position first.rowIndex (by omega) first.rowIndex.isLt
        (sameAddress.trans entryAddress.symm) entryStarts
      omega

-- In an honest trace, every LD reads from a whole number of 64-bit units above the
-- lowest address, as Rust's witness needs to place it in its RAM table.
-- See : jolt/crates/jolt-witness/src/backend/trace/ram.rs:260 (remapped_ram_address)
theorem HonestTrace.load_offset_aligned {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (row : HonestTraceRow trace.bytecode) (faultClass : JoltISA.LoadFaultClass)
    (dst : JoltISA.Dst) (base : JoltISA.Src) (imm : BitVec 64)
    (isLoad : trace.bytecode[row.rowIndex].instruction = .LD faultClass dst base imm) :
    ((JoltISA.sourceValue base row.preState + imm).toNat -
      trace.initialState.jolt_device.memory_layout.get_lowest_address.toNat) % 8 = 0 := by
  have address := row.load_aligned faultClass dst base imm isLoad
  have lowest := initial_state_lowest_address_aligned joltInstance privateInputs
    trace.initialState trace.initialized
  omega

-- In an honest trace, every SD writes to a whole number of 64-bit units above the
-- lowest address, as Rust's witness needs to place it in its RAM table.
-- See : jolt/crates/jolt-witness/src/backend/trace/ram.rs:260 (remapped_ram_address)
theorem HonestTrace.store_offset_aligned {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (row : HonestTraceRow trace.bytecode) (base value : JoltISA.Src) (imm : BitVec 64)
    (isStore : trace.bytecode[row.rowIndex].instruction = .SD base value imm) :
    ((JoltISA.sourceValue base row.preState + imm).toNat -
      trace.initialState.jolt_device.memory_layout.get_lowest_address.toNat) % 8 = 0 := by
  have address := row.store_aligned base value imm isStore
  have lowest := initial_state_lowest_address_aligned joltInstance privateInputs
    trace.initialState trace.initialized
  omega

-- Rust's padded length is a power of two, at least 256, and larger than the run, so
-- the witness always ends with at least one padding row.
-- See : jolt/crates/jolt-prover/src/config.rs:118-122
theorem padded_trace_length_spec (rows : Nat) :
    rows < padded_trace_length rows ∧ 256 ≤ padded_trace_length rows ∧
    ∃ log, padded_trace_length rows = 2 ^ log := by
  unfold padded_trace_length
  split
  · -- a short run pads to 256 = 2^8
    exact ⟨by omega, Nat.le_refl _, 8, rfl⟩
  · -- a longer run pads to the power of two that holds it plus one
    have holds := Nat.le_pow_clog (by decide : 1 < 2) (rows + 1)
    exact ⟨by omega, by omega, _, rfl⟩

-- A guard that passes had a true condition.
theorem guard_some {condition : Prop} [Decidable condition] {passed : Unit}
    (checked : (guard condition : Option Unit) = some passed) : condition := by
  unfold guard at checked
  split at checked
  · assumption
  · cases checked

-- When Rust's prover accepts a run, its trace length is the padded length, and that
-- length is within the instance's maximum.
-- See : jolt/crates/jolt-prover/src/config.rs:118-128
theorem HonestTrace.prover_config_trace_length {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (config : ProverConfig) (accepted : trace.prover_config = some config) :
    config.trace_length = padded_trace_length trace.rows.size ∧
    config.trace_length ≤ joltInstance.max_padded_trace_length.toNat := by
  unfold HonestTrace.prover_config at accepted
  -- the jump check
  rw [bind_some_iff] at accepted
  obtain ⟨_, _, accepted⟩ := accepted
  -- the length check
  rw [bind_some_iff] at accepted
  obtain ⟨_, lengthChecked, accepted⟩ := accepted
  -- the address check
  rw [bind_some_iff] at accepted
  obtain ⟨_, _, accepted⟩ := accepted
  -- the config itself
  cases accepted
  exact ⟨rfl, guard_some lengthChecked⟩

-- When Rust's prover accepts a run, its last row is a jump (a16z/jolt#1968).
-- See : jolt/crates/jolt-prover/src/config.rs:122-126 at upstream 629ed77b
theorem HonestTrace.prover_config_last_jump {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (config : ProverConfig) (accepted : trace.prover_config = some config) :
    (trace.rows.back?.all fun last => trace.bytecode[last.rowIndex].instruction.is_jump) = true := by
  unfold HonestTrace.prover_config at accepted
  -- the jump check
  rw [bind_some_iff] at accepted
  obtain ⟨_, jumpChecked, _⟩ := accepted
  exact guard_some jumpChecked

-- A slot at most the highest touched slot is below ram_K: rounding up a number past
-- the highest slot gives a power of two above it.
theorem slot_below_ram_K (slot touched imageEnd : Nat) (atMost : slot ≤ touched) :
    slot < 2 ^ Nat.clog 2 (max (touched + 1) imageEnd) := by
  have roundedUp := Nat.le_pow_clog (by decide : 1 < 2) (max (touched + 1) imageEnd)
  omega

-- When Rust's prover accepts a run, every memory address a row touches is 0 (no
-- access), or is at or above the lowest address and has a slot below ram_K.
-- See : jolt/crates/jolt-prover/src/config.rs:125-143, 183-195
--       jolt/crates/jolt-witness/src/backend/trace/ram.rs:260-283 (the slot must be below ram_K)
theorem HonestTrace.prover_config_ram_fits {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (config : ProverConfig) (accepted : trace.prover_config = some config)
    (row : HonestTraceRow trace.bytecode) (inTrace : row ∈ trace.rows) (address : Nat)
    (touches : row.ram_address = some address) :
    address = 0 ∨
      (trace.initialState.jolt_device.memory_layout.get_lowest_address.toNat ≤ address ∧
        ∃ slot, remap_address trace.initialState.jolt_device.memory_layout address = some slot ∧
          slot < config.ram_K) := by
  unfold HonestTrace.prover_config at accepted
  -- the jump check
  rw [bind_some_iff] at accepted
  obtain ⟨_, _, accepted⟩ := accepted
  -- the length check
  rw [bind_some_iff] at accepted
  obtain ⟨_, _, accepted⟩ := accepted
  -- the address check
  rw [bind_some_iff] at accepted
  obtain ⟨_, addressesChecked, accepted⟩ := accepted
  -- the config itself
  cases accepted
  dsimp only
  -- the address is one of the run's addresses, so it passed the address check
  have member : address ∈ trace.rows.toList.filterMap (·.ram_address) :=
    List.mem_filterMap.mpr ⟨row, Array.mem_toList_iff.mpr inTrace, touches⟩
  have checked := List.all_eq_true.mp (guard_some addressesChecked) address member
  simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at checked
  by_cases zero : address = 0
  · exact Or.inl zero
  · obtain zero' | above := checked
    · exact absurd zero' zero
    -- its slot is at most the highest touched slot, which is below ram_K
    have slotIs : remap_address trace.initialState.jolt_device.memory_layout address =
        some ((address - trace.initialState.jolt_device.memory_layout.get_lowest_address.toNat) / 8) := by
      unfold remap_address
      rw [if_neg zero]
    have atMost := List.le_max?_getD_of_mem (k := 0)
      (List.mem_filterMap.mpr ⟨address, member, slotIs⟩)
    exact Or.inr ⟨above, _, slotIs, slot_below_ram_K _ _ _ atMost⟩

-- The program image spans at least one 64-bit slot.
theorem program_image_len_words_pos (memory_init : List (BitVec 64 × BitVec 8)) :
    1 ≤ program_image_len_words memory_init := by
  unfold program_image_len_words
  dsimp only
  omega

-- When Rust's prover accepts a run, its RAM table has at least 2 slots, since the
-- program image ends at slot 2 or later. So a RAM slot number splits into at least
-- one chunk.
-- See : jolt/crates/jolt-prover/src/config.rs:140-143
theorem HonestTrace.prover_config_ram_K_ge_two {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (config : ProverConfig) (accepted : trace.prover_config = some config) :
    2 ≤ config.ram_K := by
  unfold HonestTrace.prover_config at accepted
  -- the jump check
  rw [bind_some_iff] at accepted
  obtain ⟨_, _, accepted⟩ := accepted
  -- the length check
  rw [bind_some_iff] at accepted
  obtain ⟨_, _, accepted⟩ := accepted
  -- the address check
  rw [bind_some_iff] at accepted
  obtain ⟨_, _, accepted⟩ := accepted
  -- the config itself
  cases accepted
  dsimp only
  have imageWords := program_image_len_words_pos joltInstance.program.memory_init
  exact (by omega : 2 ≤ max _ _).trans (Nat.le_pow_clog (by decide : 1 < 2) _)
