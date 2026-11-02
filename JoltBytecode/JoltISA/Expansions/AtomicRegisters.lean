import JoltBytecode.JoltISA.Instruction
import JoltBytecode.JoltISA.VirtualRegisters

/-!
# Legacy AMO register selectors used by protected-register proofs

These selectors name scratch registers in the retained legacy AMO programs.
For example, `amoOldVRegFor rd` selects slot zero, or slot one when rewriting
an architectural zero destination consumes the first temporary.
-/

open Sail PreSail LeanRV64D.Functions

namespace JoltISA

/-- Rust AMO scratch slot `n`, shifted when `rd = x0` consumes the first
temporary. -/
def amoVRegFor (rd : regidx) (n : Nat) : VReg :=
  if isX0 rd then inlineTmp (n + 1) else inlineTmp n

def amoOldVRegFor (rd : regidx) : VReg := amoVRegFor rd 0
def amoNewVRegFor (rd : regidx) : VReg := amoVRegFor rd 1
def amoTmpVRegFor (rd : regidx) : VReg := amoVRegFor rd 2
def amoMaskVRegFor (rd : regidx) : VReg := amoVRegFor rd 2
def amoDwordVRegFor (rd : regidx) : VReg := amoVRegFor rd 3
def amoShiftVRegFor (rd : regidx) : VReg := amoVRegFor rd 4
def amoInlineTmpVRegFor (rd : regidx) : VReg := amoVRegFor rd 5

def amoDoubleBinopNewVRegFor (rd : regidx) : VReg := amoVRegFor rd 0
def amoDoubleBinopOldVRegFor (rd : regidx) : VReg := amoVRegFor rd 1

def amoWordSelectOldVRegFor (rd : regidx) : VReg := amoVRegFor rd 0
def amoWordSelectDwordVRegFor (rd : regidx) : VReg := amoVRegFor rd 1
def amoWordSelectShiftVRegFor (rd : regidx) : VReg := amoVRegFor rd 2
def amoWordSelectNewVRegFor (rd : regidx) : VReg := amoVRegFor rd 3
def amoWordSelectMaskVRegFor (rd : regidx) : VReg := amoVRegFor rd 4
def amoWordSelectInlineTmpVRegFor (rd : regidx) : VReg := amoVRegFor rd 5

end JoltISA
