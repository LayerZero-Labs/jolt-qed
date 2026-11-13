import JoltConstraints.Completeness.Helpers.TracePCProofHelpers
import JoltConstraints.nextpc_frame

open LeanRV64D

-- HostIO changes no Sail state: its byte reads go through Jolt's MMU, which
-- changes nothing, and it otherwise only appends to the advice tape.

set_option autoImplicit false

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail LeanRV64D LeanRV64D.Functions

namespace JoltHostFrame

def Preserves {α : Type} (m : JoltMonad α) : Prop :=
  ∀ (s t : SailJoltState) (v : α), m s = .ok v t → t.sail = s.sail

theorem pure_rule {α : Type} (v : α) : Preserves (pure v) := by
  intro s t x h
  cases h
  rfl

theorem bind_rule {α β : Type} {m : JoltMonad α} {f : α → JoltMonad β}
    (hm : Preserves m) (hf : ∀ x, Preserves (f x)) : Preserves (m >>= f) := by
  intro s t v h
  cases hr : m s with
  | error e s' => simp only [bind, EStateM.bind, hr] at h; cases h
  | ok x s' =>
    simp only [bind, EStateM.bind, hr] at h
    exact (hf x s' t v h).trans (hm s s' x hr)

theorem read_rule (src : JoltISA.Src) : Preserves (JoltISA.readSrc src) := by
  intro s t v h
  obtain ⟨rfl, _⟩ := lookup_readSrc_value src s t v h
  rfl

theorem get_rule : Preserves (get : JoltMonad SailJoltState) := by
  intro s t v h
  cases h
  rfl

theorem throw_rule {α : Type} (e : Error exception) :
    Preserves (throw e : JoltMonad α) := by
  intro s t v h
  cases h

theorem modifyAdvice_rule
    (f : SailJoltState → SailJoltState)
    (hf : ∀ s, (f s).sail = s.sail) :
    Preserves (modify f : JoltMonad Unit) := by
  intro s t v h
  cases h
  exact hf s

theorem loadByte_rule (addr : BitVec 64) : Preserves (JoltISA.Mmu.load addr) := by
  intro s t v h
  rw [JoltISA.Mmu.load_state h]

theorem hostLoad_rule (addr : BitVec 64) : Preserves (JoltISA.Mmu.hostLoad addr) := by
  intro s t v h
  cases h
  rfl

theorem readHostBytes_frame {width : Nat}
    (pointer : BitVec width) (n : Nat) (bytes : Array (BitVec 8)) :
    Preserves (JoltISA.readHostBytes JoltISA.Mmu.hostLoad pointer n bytes) := by
  induction n generalizing pointer bytes with
  | zero => exact pure_rule _
  | succ n ih =>
  dsimp only [JoltISA.readHostBytes]
  refine bind_rule (hostLoad_rule _) (fun result => ?_)
  cases result with
  | none => exact pure_rule _
  | some byte => exact ih _ _

theorem execHostIO_frame : Preserves JoltISA.execHostIO := by
  unfold JoltISA.execHostIO JoltISA.execHostIOWith JoltISA.readHostRange
  refine bind_rule (read_rule _) fun _ => ?_
  split
  · refine bind_rule (read_rule _) fun _ => ?_
    refine bind_rule (read_rule _) fun _ => ?_
    refine bind_rule ?_ fun result => ?_
    · split
      · exact readHostBytes_frame _ _ _
      · exact (pure_rule _)
    · cases result with
      | none => exact (pure_rule _)
      | some _ => exact bind_rule (modifyAdvice_rule _ (by intro s; rfl)) fun _ => (pure_rule _)
  · split
    · refine bind_rule (read_rule _) fun _ => ?_
      refine bind_rule (read_rule _) fun _ => ?_
      refine bind_rule (read_rule _) fun _ => ?_
      refine bind_rule get_rule fun _ => ?_
      split
      · refine bind_rule ?_ fun _ => (pure_rule _)
        split
        · exact readHostBytes_frame _ _ _
        · exact (pure_rule _)
      · exact (pure_rule _)
    · exact (pure_rule _)

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
