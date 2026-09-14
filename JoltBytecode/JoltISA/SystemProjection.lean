/-
Copyright (c) 2026 Ari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ari 
-/
import JoltBytecode.JoltISA.VirtualRegisters

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace System

/-- As the control status registers are present in both the virtual register 
file and the sail hash map.
Simply killing of vregs does not suffice for equivalence. 
A jolt program could write to virutal registers, which result in writing of 
the sail control status registers.
TODO: (Ari) In the future, I might re-design this component by having definitional 
equality between the two objects as an axiom, and it might make my life easier.
For now this works.
-/
def systemProject (js : SailJoltState) : SailState :=
  { js.sail with
    regs :=
      ((((((js.sail.regs
        |>.insert Register.mtvec (js.vregs JoltISA.trapHandlerVReg))
        |>.insert Register.mscratch (js.vregs JoltISA.mscratchVReg))
        |>.insert Register.mepc (js.vregs JoltISA.mepcVReg))
        |>.insert Register.mcause (js.vregs JoltISA.mcauseVReg))
        |>.insert Register.mtval (js.vregs JoltISA.mtvalVReg))
        |>.insert Register.mstatus (js.vregs JoltISA.mstatusVReg)) }

/-- Given the post execution result of Jolt computation, 
Get the post execution result of the Sail part of that computation.
-/
def systemProjectResult
    (r : EStateM.Result (Error exception) SailJoltState α) :
    EStateM.Result (Error exception) SailState α :=
  match r with
  | .ok a js' => .ok a (systemProject js')
  | .error e js' => .error e (systemProject js')

end System

end
