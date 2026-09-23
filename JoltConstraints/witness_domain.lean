import JoltConstraints.witness_helpers.ram_ra_chunk

set_option autoImplicit false

-- Rust: [remapped_ram_address](/Users/ari.biswas/Work-with-A16z/jolt/crates/jolt-witness/src/backend/trace/ram.rs:260).
-- Every nonzero RAM access must remap successfully and fit the chosen witness
-- domain. This includes device I/O. Rust treats raw address zero as no access;
-- a nonzero address below the layout's lowest address is an error, not padding.
-- This is a condition on witness parameters and the recorded execution, not an
-- extra ISA execution rule. It covers every actual row, before witness padding.
def WitnessParams.RamFits (p : WitnessParams) {program : JoltProgram}
    (trace : JoltTrace program) : Prop :=
  ∀ (i : Fin trace.rows.size),
    let row := getElem trace.rows i.val i.isLt
    let instruction :=
      (getElem program.expandedBytecode row.rowIndex.val row.rowIndex.isLt).instruction
    match HonestWitness.ramAccessAddress instruction row.preState with
    | none => True
    | some rawAddress =>
        rawAddress = 0 ∨ ∃ address : Nat,
          HonestWitness.remapRamAddress program.initialState.io.layout rawAddress = some address ∧
          address < p.ramSize

theorem WitnessParams.remappedRamAddress_lt (p : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program)
    (ramFits : p.RamFits trace) (t : Fin p.traceLength) (b : Nat)
    (hb : HonestWitness.remappedRamAddress trace t.val = some b) :
    b < p.ramSize := by
  unfold HonestWitness.remappedRamAddress at hb
  split_ifs at hb with ht
  · let row := getElem trace.rows t.val ht
    let instruction :=
      (getElem program.expandedBytecode row.rowIndex.val row.rowIndex.isLt).instruction
    have hf := ramFits ⟨t.val, ht⟩
    change (HonestWitness.ramAccessAddress instruction row.preState).bind
      (HonestWitness.remapRamAddress program.initialState.io.layout) = some b at hb
    change match HonestWitness.ramAccessAddress instruction row.preState with
      | none => True
      | some rawAddress =>
          rawAddress = 0 ∨ ∃ address : Nat,
            HonestWitness.remapRamAddress program.initialState.io.layout rawAddress =
              some address ∧ address < p.ramSize at hf
    cases ha : HonestWitness.ramAccessAddress instruction row.preState with
    | none => simp [ha] at hb
    | some raw =>
        simp only [ha, Option.bind_some] at hb
        simp only [ha] at hf
        rcases hf with hz | ⟨address, hremap, hlt⟩
        · subst raw
          simp [HonestWitness.remapRamAddress] at hb
        · rw [hremap] at hb
          cases Option.some.inj hb
          exact hlt
