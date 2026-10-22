import JoltConstraints.Soundness.Layer7.StallSuffix

/-! The next source address at a terminal row with a real successor. -/

set_option autoImplicit false

namespace JoltInstance

open JoltConstraints.Soundness

/-- At the final row of a source expansion, a real successor makes the witness's
next unexpanded PC equal Sail's post-state next PC.
`atCycle` identifies the run's final row, and `nextReal` excludes padding.
For example, an ADDI at `0x80000000` followed by a real instruction selects
Sail's `0x80000004` as the next source address.
See jolt/crates/jolt-witness/src/witnesses/pc.rs (`NextUnexpandedPc::extract`)
and jolt/crates/jolt-witness/src/witnesses/flags.rs (`ShouldJump::extract`)
at 5def437f. -/
theorem terminal_next_unexpanded_pc
    {F : Type} [Field F] (joltField : JoltField F)
    (joltInstance : JoltInstance SourceInstruction)
    (noWrap : joltInstance.program.NextPCNoWrap)
    {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (equations : JoltConstraints.ConstraintEquations context.bytecode context.initialRam
      context.io context.entry witness)
    (run : UntrustedAnswerRun joltInstance privateInputs)
    (bytecodeEq : run.bytecode = context.bytecode)
    (represented : RepresentsRows witness run.toTrace)
    (last : TraceRow run.bytecode) (atEnd : last ∈ run.rows.back?)
    (terminal : run.bytecode[last.rowIndex].virtual_sequence_remaining.getD 0 = 0)
    (cycle : Fin params.traceLength) (atCycle : cycle.val + 1 = run.rows.size)
    (nextBound : run.rows.size < params.traceLength)
    (nextReal : witness.InstructionFlags .IsNoop ⟨run.rows.size, nextBound⟩ ≠ 1)
    (address : BitVec 64)
    (postNext : last.postState.sail.regs.get? Register.nextPC = some address) :
    witness.NextUnexpandedPC cycle = (address.toNat : F) := by
  sorry

end JoltInstance
