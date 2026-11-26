import JoltBytecode.Bundles
import JoltBytecode.InstructionEquivalence.Instructions.System.Reservation
import JoltBytecode.InstructionEquivalence.Instructions.System.Sc

open LeanRV64D

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail LeanRV64D LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace System

/-! ## Main theorems for LR.W, LR.D, SC.W and SC.D -/

def lrwProgramEqSailStatement (rd rs1 : regidx) (aq rl : Bool) (js : SailJoltState)
    (_h : ReservationReadEqAssumptions false rs1 js) : Prop :=
  systemProjectResult ((JoltISA.execProgram (JoltISA.lrwProgramAuto rd rs1)).run js) =
    (execute_LOADRES aq rl rs1 4 rd).run (systemProject js)

theorem lrwProgram_eq_sail_projected (rd rs1 : regidx) (aq rl : Bool) (js : SailJoltState)
    (h : ReservationReadEqAssumptions false rs1 js) :
    lrwProgramEqSailStatement rd rs1 aq rl js h :=
  SystemProofs.lrRows_eq_execute false aq rl rd rs1 js h

def lrdProgramEqSailStatement (rd rs1 : regidx) (aq rl : Bool) (js : SailJoltState)
    (_h : ReservationReadEqAssumptions true rs1 js) : Prop :=
  systemProjectResult ((JoltISA.execProgram (JoltISA.lrdProgramAuto rd rs1)).run js) =
    (execute_LOADRES aq rl rs1 8 rd).run (systemProject js)

theorem lrdProgram_eq_sail_projected (rd rs1 : regidx) (aq rl : Bool) (js : SailJoltState)
    (h : ReservationReadEqAssumptions true rs1 js) :
    lrdProgramEqSailStatement rd rs1 aq rl js h :=
  SystemProofs.lrRows_eq_execute true aq rl rd rs1 js h

def scwProgramEqSailStatement (rd rs1 rs2 : regidx) (aq rl : Bool) (js : SailJoltState)
    (_h : ReservationStoreEqAssumptions false rs2 rs1 js) : Prop :=
  systemProjectResult ((JoltISA.execProgram (JoltISA.scwProgramAuto rd rs1 rs2)).run js) =
    (execute_STORECON aq rl rs2 rs1 4 rd).run (systemProject js)

theorem scwProgram_eq_sail_projected (rd rs1 rs2 : regidx) (aq rl : Bool) (js : SailJoltState)
    (h : ReservationStoreEqAssumptions false rs2 rs1 js) :
    scwProgramEqSailStatement rd rs1 rs2 aq rl js h :=
  SystemProofs.scRows_eq_execute false aq rl rd rs1 rs2 js h

def scdProgramEqSailStatement (rd rs1 rs2 : regidx) (aq rl : Bool) (js : SailJoltState)
    (_h : ReservationStoreEqAssumptions true rs2 rs1 js) : Prop :=
  systemProjectResult ((JoltISA.execProgram (JoltISA.scdProgramAuto rd rs1 rs2)).run js) =
    (execute_STORECON aq rl rs2 rs1 8 rd).run (systemProject js)

theorem scdProgram_eq_sail_projected (rd rs1 rs2 : regidx) (aq rl : Bool) (js : SailJoltState)
    (h : ReservationStoreEqAssumptions true rs2 rs1 js) :
    scdProgramEqSailStatement rd rs1 rs2 aq rl js h :=
  SystemProofs.scRows_eq_execute true aq rl rd rs1 rs2 js h

end System

end
