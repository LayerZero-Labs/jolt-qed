import JoltConstraints.witness_helpers.rd_wa
import JoltConstraints.witness_helpers.rd_write_value

set_option autoImplicit false

namespace TraceWitness

-- Rust: [RegistersVal materialization](https://github.com/a16z/jolt/blob/8bbb2357890928d8f83b00ca542879077c4d3d28/crates/jolt-witness/src/backend/trace/registers.rs#L4-L68).
-- The witness register array starts at zero, including virtual registers. Each
-- column records its contents BEFORE that cycle's encoded destination write.
-- Apply only preceding writes; padding retains the last accumulated value.
-- A one-hot write bit replaces value by RdWriteValue; a zero bit preserves it.
noncomputable def RegistersVal {F : Type} [Field F] (p : WitnessParams)
    (trace : Trace) :
    Fin 128 → Fin p.traceLength → F :=
  fun register t =>
    -- RegVal[reg. t] = RegVal[reg, t -1] + RdWa[reg,
    (List.finRange t.val).foldl (fun value i =>
      let cycle : Fin p.traceLength := ⟨i.val, Nat.lt_trans i.isLt t.isLt⟩
      value + RdWa p trace register cycle * (RdWriteValue p trace cycle - value)) 0

end TraceWitness
