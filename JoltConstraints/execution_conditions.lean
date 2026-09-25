import JoltConstraints.trace

set_option autoImplicit false

namespace JoltTrace

/-- Rust's source-level stopping rule: the completed source instruction leaves
PC at its own address. The opcode is unrestricted, so a taken self-branch is
included. This describes a complete tracer run, not satisfaction of a constraint.
Rust: https://github.com/abiswas3/jolt/tree/main/tracer/src/lib.rs#L329-L339 -/
structure Terminated {program : JoltProgram} (trace : JoltTrace program) : Prop where
  nonempty : 0 < trace.rows.size
  atSourceEnd : program.expandedBytecode[
    (trace.rows[trace.rows.size - 1]'(by omega)).rowIndex].continues = false
  repeatedPC : (trace.rows[trace.rows.size - 1]'(by omega)).postState.sail.regs.get? Register.nextPC =
    some program.expandedBytecode[(trace.rows[trace.rows.size - 1]'(by omega)).rowIndex].address

end JoltTrace
