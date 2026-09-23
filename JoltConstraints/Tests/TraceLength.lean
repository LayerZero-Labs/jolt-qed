import JoltConstraints.honest_witness

set_option autoImplicit false

namespace TraceLengthChecks

-- A physical trace can be used only when every row has a witness cycle.
noncomputable example {F : Type} [Field F] (p : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program)
    (ramFits : p.RamFits trace) (traceFits : trace.rows.size ≤ p.traceLength) :
    WitnessType F p :=
  JoltProgram.honestWitness (F := F) p trace ramFits traceFits

-- Two physical rows cannot fit into a one-cycle domain.
example (p : WitnessParams) {program : JoltProgram} (trace : JoltTrace program)
    (oneCycle : p.logT = 0) (twoRows : trace.rows.size = 2) :
    ¬ trace.rows.size ≤ p.traceLength := by
  simp [WitnessParams.traceLength, oneCycle, twoRows]

end TraceLengthChecks
