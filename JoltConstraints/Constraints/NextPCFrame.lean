import JoltConstraints.Constraints.TracePCProofHelpers
import JoltConstraints.metadata

/-!
Instruction-level nextPC frames. Ordinary instructions, untaken branches, and
word memory operations preserve nextPC. HostIO's frame is proved in
`HostIOFrame.lean` and supplies the remaining case.
-/

set_option autoImplicit false

open Sail PreSail LeanRV64D.Functions

namespace SailNextPCFrame

def Preserves {α : Type} (m : SailM α) : Prop :=
  ∀ (s t : SailState) (v : α), m s = .ok v t →
    t.regs.get? Register.nextPC = s.regs.get? Register.nextPC

theorem pure_rule {α : Type} (v : α) : Preserves (pure v) := by
  intro s t x h
  cases h
  rfl

theorem bind_rule {α β : Type} {m : SailM α} {f : α → SailM β}
    (hm : Preserves m) (hf : ∀ x, Preserves (f x)) : Preserves (m >>= f) := by
  intro s t v h
  cases hr : m s with
  | error e s' => simp only [bind, EStateM.bind, hr] at h; cases h
  | ok x s' =>
    simp only [bind, EStateM.bind, hr] at h
    exact (hf x s' t v h).trans (hm s s' x hr)

theorem read_rule (r : Register) : Preserves (Sail.readReg r) := by
  intro s t v h
  cases readReg_pure r s v t h
  rfl

theorem write_rule (r : Register) (v : RegisterType r)
    (hne : r ≠ Register.nextPC) : Preserves (Sail.writeReg r v) := by
  intro s t x h
  cases h
  simp only [Std.ExtDHashMap.get?_insert, beq_iff_eq, hne, ↓reduceDIte]

end SailNextPCFrame

namespace JoltNextPCFrame
open JoltISA

def Preserves {α : Type} (m : JoltMonad α) : Prop :=
  ∀ (s t : SailJoltState) (v : α), m s = .ok v t →
    t.sail.regs.get? Register.nextPC = s.sail.regs.get? Register.nextPC

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

theorem lift_rule {α : Type} {m : SailM α} (hm : SailNextPCFrame.Preserves m) :
    Preserves (liftSail m) := by
  intro s t v h
  cases hr : m s.sail with
  | error e s' => simp only [liftSail, hr] at h; cases h
  | ok x s' =>
    simp only [liftSail, hr] at h
    cases h
    exact hm s.sail _ _ hr

theorem read_rule (src : Src) : Preserves (readSrc src) := by
  intro s t v h
  obtain ⟨rfl, _⟩ := lookup_readSrc_value src s t v h
  rfl

theorem write_rule (dst : Dst) (value : BitVec 64) : Preserves (writeDst dst value) := by
  cases dst with
  | xreg rd =>
    intro s t v h
    simp only [writeDst, liftSail, wX_bits_stateAfterWrite] at h
    cases h
    reg_cases rd <;>
      simp_all only [stateAfterWrite, wX_update_regs, regval_into_reg,
        Std.ExtDHashMap.get?_insert, beq_iff_eq, reduceCtorEq, ↓reduceDIte]
  | vreg vr =>
    intro s t v h
    by_cases hw : vr.toNat < 32
    · simp only [writeDst, writeVReg, hw, ↓reduceIte, throw, throwThe] at h
      cases h
    · simp only [writeDst, writeVReg, hw, ↓reduceIte] at h
      cases h
      rfl

theorem throw_rule {α : Type} (e : Error exception) :
    Preserves (throw e : JoltMonad α) := by
  intro s t x h
  cases h

theorem get_rule : Preserves (get : JoltMonad SailJoltState) := by
  intro s t x h
  cases h
  rfl

theorem modify_rule (f : SailJoltState → SailJoltState)
    (hf : ∀ s, (f s).sail.regs.get? Register.nextPC =
      s.sail.regs.get? Register.nextPC) :
    Preserves (modify f : JoltMonad Unit) := by
  intro s t x h
  cases h
  exact hf s

macro "jolt_nextpc_auto" : tactic => `(tactic|
  repeat' first
  | exact read_rule _
  | exact write_rule _ _
  | exact pure_rule _
  | exact throw_rule _
  | exact get_rule
  | exact modify_rule _ (by intro s; rfl)
  | exact lift_rule (SailNextPCFrame.read_rule _)
  | exact lift_rule (SailNextPCFrame.write_rule _ _ (by decide))
  | fail_if_no_progress dsimp only [get_arch_pc, get_next_pc]
  | split
  | refine bind_rule ?_ (fun x => ?_))

theorem ordinary_instruction (instr : Instr)
    (hload : ∀ fault dst base imm, instr ≠ .LD fault dst base imm)
    (hstore : ∀ base value imm, instr ≠ .SD base value imm)
    (hhost : ∀ dst src imm, instr ≠ .VirtualHostIO dst src imm)
    (hcontrol : JoltMetadata.opcodeFlag instr .Jump = false ∧
      JoltMetadata.instructionFlag instr .Branch = false) :
    Preserves (execInstr instr) := by
  cases instr
  case VirtualAdviceLoad dst byteCount =>
    intro s t v h
    simp only [execInstr] at h
    cases hr : readAdviceTape s.adviceTape byteCount with
    | none => simp only [hr] at h; cases h
    | some pair =>
      obtain ⟨value, tape⟩ := pair
      simp only [hr] at h
      exact (bind_rule (write_rule dst value) (fun _ => pure_rule _))
        { s with adviceTape := tape } t v h
  all_goals try exact False.elim (hload _ _ _ _ rfl)
  all_goals try exact False.elim (hstore _ _ _ rfl)
  all_goals try exact False.elim (hhost _ _ _ rfl)
  all_goals try (simp [JoltMetadata.opcodeFlag, JoltMetadata.instructionFlag] at hcontrol)
  all_goals simp only [execInstr]
  all_goals try jolt_nextpc_auto

def BranchTaken (instr : Instr) (s : SailJoltState) : Bool :=
  match instr with
  | .BEQ lhs rhs _ | .BNE lhs rhs _ | .BLT lhs rhs _
  | .BGE lhs rhs _ | .BLTU lhs rhs _ | .BGEU lhs rhs _ =>
      branchDecisionPure instr (sourceValue lhs s) (sourceValue rhs s)
  | _ => false

theorem readHostBytes_frame
    (loadByte : BitVec 64 → JoltMonad (Result (BitVec 8) ExecutionResult))
    (hload : ∀ address, Preserves (loadByte address))
    (overflowChecks incrementAfterLast : Bool) {width : Nat}
    (pointer : BitVec width) (n : Nat) (bytes : Array (BitVec 8)) :
    Preserves (readHostBytes loadByte overflowChecks incrementAfterLast pointer n bytes) := by
  induction n generalizing pointer bytes with
  | zero =>
    exact pure_rule _
  | succ n ih =>
    dsimp only [readHostBytes]
    refine bind_rule (hload _) (fun result => ?_)
    cases result with
    | Err e => exact pure_rule _
    | Ok byte =>
      split_ifs with h
      · exact bind_rule (throw_rule _) (fun _ => ih _ _)
      · exact bind_rule (pure_rule _) (fun _ => ih _ _)

theorem execHostIOWith_frame
    (loadByte : BitVec 64 → JoltMonad (Result (BitVec 8) ExecutionResult))
    (hload : ∀ address, Preserves (loadByte address)) :
    Preserves (execHostIOWith loadByte) := by
  unfold execHostIOWith
  refine bind_rule get_rule (fun config => ?_)
  dsimp only
  split
  · exact pure_rule _
  · refine bind_rule (pure_rule _) (fun _ => ?_)
    refine bind_rule (read_rule _) (fun callId => ?_)
    repeat' first
      | exact readHostBytes_frame loadByte hload _ _ _ _ _
      | exact read_rule _
      | exact pure_rule _
      | exact throw_rule _
      | exact modify_rule _ (by intro s; rfl)
      | split
      | refine bind_rule ?_ (fun x => ?_)

theorem branch_not_taken (instr : Instr) (s t : SailJoltState)
    (hbranch : JoltMetadata.instructionFlag instr .Branch = true)
    (hnot : BranchTaken instr s = false)
    (hexec : execInstr instr s = .ok (.Retire_Success ()) t) : t = s := by
  cases instr <;> try (simp [JoltMetadata.instructionFlag] at hbranch)
  all_goals
    simp only [execInstr] at hexec
    have hleft := lookup_read_bind _ _ _ _ _ hexec
    have hright := lookup_read_bind _ _ _ _ _ hleft
    simp only [BranchTaken] at hnot
    simp only [hnot, pure] at hright
    cases hright
    rfl

theorem memory_write {addr data : BitVec 64} {s t : SailJoltState}
    {v : Result Bool ExecutionResult}
    (hr : Mmu.store_doubleword addr data s = .ok v t) :
    t.sail.regs.get? Register.nextPC = s.sail.regs.get? Register.nextPC := by
  rw [(Mmu.store_doubleword_regs hr).1]

theorem load_instruction (fault : LoadFaultClass) (dst : Dst) (base : Src)
    (imm : BitVec 64) (s t : SailJoltState)
    (hexec : execInstr (.LD fault dst base imm) s = .ok (.Retire_Success ()) t) :
    t.sail.regs.get? Register.nextPC = s.sail.regs.get? Register.nextPC := by
  have hx := lookup_read_bind base _ _ _ _ hexec
  by_cases halign : (sourceValue base s + imm) &&& 7 = 0
  · simp only [halign, ↓reduceIte] at hx
    cases hr : Mmu.load_doubleword (sourceValue base s + imm) s with
    | error e s' => simp only [bind, EStateM.bind, hr] at hx; cases hx
    | ok v s' =>
      have hstate := Mmu.load_doubleword_state hr
      subst s'
      simp only [bind, EStateM.bind, hr] at hx
      cases v with
      | Ok value =>
        exact (bind_rule (write_rule dst value) (fun _ => pure_rule _)) s t _ hx
      | Err e => cases hx; rfl
  · simp only [halign, ↓reduceIte, pure, EStateM.pure] at hx
    cases hx

theorem store_instruction (base value : Src) (imm : BitVec 64)
    (s t : SailJoltState)
    (hexec : execInstr (.SD base value imm) s = .ok (.Retire_Success ()) t) :
    t.sail.regs.get? Register.nextPC = s.sail.regs.get? Register.nextPC := by
  have hx := lookup_read_bind base _ _ _ _ hexec
  have hx := lookup_read_bind value _ _ _ _ hx
  by_cases halign : (sourceValue base s + imm) &&& 7 = 0
  · simp only [halign, ↓reduceIte] at hx
    cases hr : Mmu.store_doubleword (sourceValue base s + imm) (sourceValue value s) s with
    | error e s' => simp only [bind, EStateM.bind, hr] at hx; cases hx
    | ok v s' =>
      have hp := memory_write hr
      simp only [bind, EStateM.bind, hr] at hx
      cases v <;> cases hx <;> exact hp
  · simp only [halign, ↓reduceIte, pure, EStateM.pure] at hx
    cases hx

def HostIOFrame (instr : Instr) (s t : SailJoltState) : Prop :=
  match instr with
  | .VirtualHostIO .. =>
      t.sail.regs.get? Register.nextPC = s.sail.regs.get? Register.nextPC
  | _ => True

theorem instruction (instr : Instr) (s t : SailJoltState)
    (hjump : JoltMetadata.opcodeFlag instr .Jump = false)
    (hnot : BranchTaken instr s = false)
    (hhost : HostIOFrame instr s t)
    (hexec : execInstr instr s = .ok (.Retire_Success ()) t) :
    t.sail.regs.get? Register.nextPC = s.sail.regs.get? Register.nextPC := by
  cases instr
  case LD fault dst base imm =>
    exact load_instruction fault dst base imm s t hexec
  case SD base value imm =>
    exact store_instruction base value imm s t hexec
  case VirtualHostIO dst src imm =>
    exact hhost
  all_goals try (simp [JoltMetadata.opcodeFlag] at hjump)
  all_goals try
    (have hstate := branch_not_taken _ s t (by rfl) hnot hexec
     subst t
     rfl)
  all_goals
    exact ordinary_instruction _
      (by intros; intro h; cases h) (by intros; intro h; cases h)
      (by intros; intro h; cases h)
      ⟨by rfl, by rfl⟩ s t _ hexec

end JoltNextPCFrame
