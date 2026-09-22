import JoltConstraints.witness_helpers.rd_wa
import JoltConstraints.witness_helpers.rd_write_value

set_option autoImplicit false

namespace HonestWitness

-- Rust: [RegistersVal materialization](/Users/ari.biswas/Work-with-A16z/jolt/crates/jolt-witness/src/backend/trace/registers.rs:26).
-- The witness register array starts at zero, including virtual registers. Each
-- column records its contents BEFORE that cycle's captured destination write.
-- Apply only preceding writes; padding retains the last accumulated value.
-- A one-hot write bit replaces value by RdWriteValue; a zero bit preserves it.
noncomputable def RegistersVal {F : Type} [Field F] (p : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program) :
    Fin 128 → Fin p.traceLength → F :=
  fun register t =>
    (List.finRange t.val).foldl (fun value i =>
      let cycle : Fin p.traceLength := ⟨i.val, Nat.lt_trans i.isLt t.isLt⟩
      value + RdWa p trace register cycle * (RdWriteValue p trace cycle - value)) 0

end HonestWitness
