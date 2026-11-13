/-
Copyright (c) 2026 Ari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ari 
-/
import JoltBytecode.JoltISA.VirtualRegisters

open LeanRV64D

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail LeanRV64D LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace System

/-- The reservation width Sail holds for Jolt's reservation registers: none,
a word, or a doubleword.
For example, equal nonzero word and doubleword addresses give width 8. -/
def reservationWidth (w d : BitVec 64) : Int :=
  if w = 0#64 then 0 else if d = w then 8 else 4

/-- The Sail state represented by Jolt's persistent system virtual registers.
The six CSRs come from v34 through v39, with `mstatus.MPP` forced to Machine.
The reservation comes from v32 and v33; for example, two zero values project
to an invalid reservation with address and width zero. -/
def systemProject (js : SailJoltState) : SailState :=
  { js.sail with
    regs :=
      js.sail.regs
        |>.insert Register.mtvec (js.vregs JoltISA.trapHandlerVReg)
        |>.insert Register.mscratch (js.vregs JoltISA.mscratchVReg)
        |>.insert Register.mepc (js.vregs JoltISA.mepcVReg)
        |>.insert Register.mcause (js.vregs JoltISA.mcauseVReg)
        |>.insert Register.mtval (js.vregs JoltISA.mtvalVReg)
        |>.insert Register.mstatus (js.vregs JoltISA.mstatusVReg ||| 0x1800#64)
        |>.insert Register.reservation_valid (js.vregs JoltISA.reservationWReg != 0#64)
        |>.insert Register.reservation_addr (js.vregs JoltISA.reservationWReg)
        |>.insert Register.reservation_width
          (reservationWidth (js.vregs JoltISA.reservationWReg) (js.vregs JoltISA.reservationDReg)) }

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
