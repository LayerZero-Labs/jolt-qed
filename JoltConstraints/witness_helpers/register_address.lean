import JoltBytecode.JoltISA.Instruction

set_option autoImplicit false

namespace HonestWitness

-- Rust: [register domain](/Users/ari.biswas/Work-with-A16z/jolt/common/src/constants.rs).
-- Architectural and virtual operands use the same 128-address witness domain.
-- An explicit x0 is address zero; it is not an absent operand.
def sourceRegisterAddress : JoltISA.Src → Fin 128
  | .vreg r => r.toFin
  | .xreg (.Regidx r) => (r.setWidth 7).toFin

def destinationRegisterAddress : JoltISA.Dst → Fin 128
  | .vreg r => r.toFin
  | .xreg (.Regidx r) => (r.setWidth 7).toFin

end HonestWitness
