import JoltBytecode.JoltISA.RegisterAccess

set_option autoImplicit false

namespace TraceWitness

def capturedDestination (dst : JoltISA.Dst) : JoltISA.Dst :=
  dst

def capturedDestinationValue (dst : JoltISA.Dst) (state : SailJoltState) : BitVec 64 :=
  match capturedDestination dst with
  | .xreg r => JoltISA.sourceValue (.xreg r) state
  | .vreg r => JoltISA.sourceValue (.vreg r) state

end TraceWitness
