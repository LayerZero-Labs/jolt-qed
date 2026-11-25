import JoltConstraints.translation.honest_witness
import JoltConstraints.translation.Constraints.HaltEndRule
import JoltConstraints.theorems.HaltFlags
import JoltConstraints.theorems.execution_conditions

open LeanRV64D

set_option autoImplicit false

namespace JoltConstraints

/-- The honest witness satisfies row 21 under its actual final panic claim.
For example, either halt kind may fill the final witness row exactly or be
followed by padding; earlier real rows are not halts.
Jolt at `ff6fc6568`: `rv64_trace_constraints` and `Cpu::halt`. -/
theorem honestWitness_haltEndRule {F : Type} [Field F] (params : WitnessParams)
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (trace : HonestTrace joltInstance privateInputs)
    (traceFits : params.ProverPaddedFor trace.rows.size) :
    haltEndRule (TraceWitness.finalTraceState trace).jolt_device.panic
      (HonestTrace.honestWitness (F := F) params trace) := by
  intro t
  change 2 * (TraceWitness.NextIsNoop params trace t -
      TraceWitness.InstructionFlags params trace .IsNoop t) =
    (2 - (if (TraceWitness.finalTraceState trace).jolt_device.panic then 1 else 0)) *
      TraceWitness.OpFlags params trace .Halt t +
      TraceWitness.OpFlags params trace .HaltPanic t
  by_cases real : t.val < trace.rows.size
  · have current : TraceWitness.InstructionFlags (F := F) params trace .IsNoop t = 0 := by
      simp [TraceWitness.InstructionFlags, real, JoltMetadata.instructionFlag]
    rw [current]
    have flags := JoltMetadata.haltFlags trace.bytecode[trace.rows[t.val].rowIndex.val].instruction
    by_cases nextReal : t.val + 1 < trace.rows.size
    · have nextBound : t.val + 1 < params.traceLength := nextReal.trans_le traceFits.2
      have next : TraceWitness.NextIsNoop (F := F) params trace t = 0 := by
        simp [TraceWitness.NextIsNoop, nextBound, TraceWitness.InstructionFlags,
          nextReal, JoltMetadata.instructionFlag]
      have noHalt := trace.runs_until_stop t.val _ _
        (Array.getElem?_eq_getElem real) (Array.getElem?_eq_getElem nextReal)
      have noKind : trace.bytecode[trace.rows[t.val].rowIndex.val].instruction.haltKind? = none :=
        Option.not_isSome_iff_eq_none.mp noHalt
      simp [next, TraceWitness.OpFlags, real, JoltMetadata.circuitFlag,
        flags.1, flags.2, noKind]
    · have lastIndex : trace.rows.size - 1 = t.val := by omega
      have back : trace.rows.back? = some trace.rows[t.val] := by
        rw [Array.back?_eq_getElem?, lastIndex, Array.getElem?_eq_getElem real]
      have halts := trace.stops _ back
      obtain ⟨_, _, kind, kindIs, _, panicIs⟩ := trace.halt_row t.val real halts
      change trace.bytecode[trace.rows[t.val].rowIndex.val].instruction.haltKind? = some kind
        at kindIs
      have final : TraceWitness.finalTraceState trace = trace.rows[t.val].postState := by
        simp [TraceWitness.finalTraceState, trace.nonempty, lastIndex]
      have next : TraceWitness.NextIsNoop (F := F) params trace t = 1 := by
        simp [TraceWitness.NextIsNoop, TraceWitness.InstructionFlags, nextReal]
      rw [next, final, panicIs]
      simp only [TraceWitness.OpFlags, dite_eq_left real, JoltMetadata.circuitFlag,
        flags.1, flags.2, kindIs]
      cases kind <;> simp
  · have nextOutside : ¬t.val + 1 < trace.rows.size := by omega
    simp [TraceWitness.NextIsNoop, TraceWitness.InstructionFlags, TraceWitness.OpFlags,
      real, nextOutside]

end JoltConstraints
