import JoltBytecode.JoltISA.Expansions.Mul
import JoltBytecode.InstructionEquivalence.ProofSupport.InstructionLemmas
import JoltBytecode.InstructionEquivalence.ProofSupport.ValueLemmas
import Mathlib

/-!
# M-extension expansion block semantics

These lemmas describe source-instruction inline blocks after they have been
lowered to real Jolt ISA rows.  In particular, nested `MULH` expansions must
use the scratch virtual registers allocated at the call site.
-/

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true
set_option linter.unusedVariables false

noncomputable section

namespace JoltISA

/-- Pure value computed by the lowered `MULH` block. -/
def mulhBlockValue (x y : BitVec 64) : BitVec 64 :=
  jolt_mulhu_value x y + jolt_movsign_value x * y + jolt_movsign_value y * x









end JoltISA

end
