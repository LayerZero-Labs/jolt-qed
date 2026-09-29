import JoltBytecode.JoltISA.RegisterAccess

set_option autoImplicit false

namespace HonestWitness

def capturedDestination (_instruction : JoltISA.Instr) (dst : JoltISA.Dst) : JoltISA.Dst :=
  dst

def capturedDestinationValue (instruction : JoltISA.Instr) (dst : JoltISA.Dst)
    (state : SailJoltState) : BitVec 64 :=
  match capturedDestination instruction dst with
  | .xreg r => JoltISA.sourceValue (.xreg r) state
  | .vreg r => JoltISA.sourceValue (.vreg r) state

end HonestWitness
