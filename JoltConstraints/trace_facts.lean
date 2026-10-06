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
