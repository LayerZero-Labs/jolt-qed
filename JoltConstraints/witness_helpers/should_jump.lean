import JoltConstraints.witness_helpers.op_flags
import JoltConstraints.witness_helpers.instruction_flags

open LeanRV64D

set_option autoImplicit false

namespace TraceWitness

-- Rust: ShouldJump = Jump · (1 − NextIsNoop).
-- A jump followed by a padding row gives zero. At the final witness position
-- the missing successor counts as a no-op, as in `NextIsNoop`, so a final jump
-- gives zero too. That happens when the run fills its power-of-two domain.
-- Padding itself has Jump = 0.
-- See : jolt/crates/jolt-witness/src/witnesses/flags.rs:28-34, 116-128 at 3cc6e7bd1
noncomputable def ShouldJump {F : Type} [Field F] (p : WitnessParams)
    (trace : Trace) : Fin p.traceLength → F :=
  fun t =>
    OpFlags p trace .Jump t *
      (if nextInBounds : t.val + 1 < p.traceLength then
        1 - InstructionFlags p trace .IsNoop ⟨t.val + 1, nextInBounds⟩
      else 0)

end TraceWitness
