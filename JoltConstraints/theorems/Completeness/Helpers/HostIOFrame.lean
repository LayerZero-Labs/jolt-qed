import JoltConstraints.theorems.nextpc_frame
import JoltConstraints.theorems.execution_facts

open LeanRV64D

-- HostIO changes no Sail state: it either leaves the state unchanged or only
-- appends to the advice tape (`execHostIO_keeps_state`).

set_option autoImplicit false

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail LeanRV64D LeanRV64D.Functions

namespace JoltHostFrame

def Preserves {α : Type} (m : JoltMonad α) : Prop :=
  ∀ (s t : SailJoltState) (v : α), m s = .ok v t → t.sail = s.sail

theorem execHostIO_frame : Preserves (JoltISA.execHostIO) :=
  fun s t v h => (execHostIO_keeps_state s t v h).1

end JoltHostFrame

namespace JoltNextPCFrame

theorem hostIOFrame_of_exec (instr : JoltISA.Instr) (s t : SailJoltState)
    (hexec : JoltISA.execInstr instr s = .ok (.Retire_Success ()) t) :
    HostIOFrame instr s t := by
  cases instr with
  | VirtualHostIO =>
    have hsail := JoltHostFrame.execHostIO_frame s t (.Retire_Success ()) hexec
    exact congrArg (fun sail : SailState => sail.regs.get? Register.nextPC) hsail
  | _ => trivial

theorem row {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (i : Fin trace.rows.size)
    (hjump : JoltMetadata.opcodeFlag
      (trace.bytecode[trace.rows[i].rowIndex].instruction.withRuntimeAdvice
        trace.rows[i].runtimeAdvice) .Jump = false)
    (hnot : BranchTaken
      (trace.bytecode[trace.rows[i].rowIndex].instruction.withRuntimeAdvice
        trace.rows[i].runtimeAdvice) trace.rows[i].preState = false) :
    trace.rows[i].postState.sail.regs.get? Register.nextPC =
      trace.rows[i].preState.sail.regs.get? Register.nextPC := by
  apply instruction _ _ _ hjump hnot _ (trace.row i (by omega)).executes
  exact hostIOFrame_of_exec _ _ _ (trace.row i (by omega)).executes

end JoltNextPCFrame
