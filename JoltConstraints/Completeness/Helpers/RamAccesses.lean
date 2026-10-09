import JoltConstraints.Constraints.RamReadData

set_option autoImplicit false

namespace JoltConstraints

/-- Actual RAM accesses are word-aligned relative to the layout.
RamFits separately supplies successful remapping and the RAM-domain bound.
This is a condition on the recorded accesses, not an ISA execution rule, and
only completeness uses it, so it lives here rather than in the relation. -/
def ramAccessesValid (trace : Trace) : Prop :=
  ∀ i : Fin trace.rows.size,
    let row := getElem trace.rows i.val i.isLt
    let instruction := trace.bytecode[row.rowIndex].instruction
    match TraceWitness.ramAccessAddress instruction row.preState with
    | none => True
    | some address =>
        (address.toNat - ramLowestAddress trace.initialState.jolt_device.memory_layout) % 8 = 0

end JoltConstraints
