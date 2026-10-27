import JoltConstraints.honest_trace

set_option autoImplicit false

/-- Rust's source-level stopping rule: the completed source instruction jumps
to its own address and would do so on re-execution.
See : a16z/jolt PR #2109, merge commit 0249591a, `Cpu::tick`. -/
structure HonestTrace.Terminated {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs) :
    Prop where
  nonempty : 0 < trace.rows.size
  atSourceEnd : trace.bytecode[
    (trace.rows[trace.rows.size - 1]'(by omega)).rowIndex].continues = false
  repeatedPC : (trace.rows[trace.rows.size - 1]'(by omega)).postState.sail.regs.get?
      Register.nextPC =
    some trace.bytecode[(trace.rows[trace.rows.size - 1]'(by omega)).rowIndex].address
  selfJumpRepeats :
    trace.bytecode[(trace.rows[trace.rows.size - 1]'(by omega)).rowIndex].selfJumpRepeats = true

-- A nonempty honest trace stops as Rust's tracer does: its last row ends its source
-- instruction and leaves nextPC at that instruction's address (the trace's `stops`).
theorem HonestTrace.terminated {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (nonempty : 0 < trace.rows.size) : trace.Terminated := by
  have lastIsBack : trace.rows.back? = some (trace.rows[trace.rows.size - 1]'(by omega)) := by
    rw [Array.back?_eq_getElem?, Array.getElem?_eq_getElem (by omega)]
  obtain ⟨atEnd, samePC, repeats⟩ := trace.stops _ lastIsBack
  refine ⟨nonempty, ?_, samePC, repeats⟩
  unfold JoltInstructionRow.continues
  rw [atEnd]
  rfl
