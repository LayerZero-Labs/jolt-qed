import JoltConstraints.Constraints.LookupWriteProofHelpers
import JoltBytecode.InstructionEquivalence.ProofSupport.Memory.Write
import JoltBytecode.InstructionEquivalence.ProofSupport.Memory.Read
open Sail PreSail LeanRV64D.Functions
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 400000

namespace PCFrame

def Preserves {α : Type} (m : SailM α) : Prop :=
  ∀ (s t : SailState) (v : α), m s = .ok v t →
    t.regs.get? Register.PC = s.regs.get? Register.PC

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
    (hne : r ≠ Register.PC) : Preserves (Sail.writeReg r v) := by
  intro s t x h
  cases h
  simp only [Std.ExtDHashMap.get?_insert, beq_iff_eq, hne, ↓reduceDIte]

theorem jump_rule (target : BitVec 64) : Preserves (jump_to target) := by
  intro s t v h
  unfold jump_to ext_control_check_pc at h
  simp only [SailME.run, PreSail.PreSailME.run, ExceptT.run, ExceptT.mk,
    ExceptT.bind, ExceptT.bindCont, ExceptT.pure, ExceptT.lift,
    liftM, monadLift, MonadLift.monadLift, Functor.map, EStateM.map,
    bind, EStateM.bind, pure, EStateM.pure, Sail.assert, PreSail.assert] at h
  by_cases hbit : (BitVec.access target 0 == 0#1) = true
  · simp only [hbit, ↓reduceIte, pure, EStateM.pure, bind, EStateM.bind,
      ExceptT.bindCont, liftM, monadLift, MonadLift.monadLift, ExceptT.lift,
      ExceptT.mk, EStateM.map, Functor.map] at h
    have hzca : Preserves (currentlyEnabled extension.Ext_Zca) := by
      unfold currentlyEnabled
      apply bind_rule
      · unfold currentlyEnabled
        exact bind_rule (read_rule Register.misa) (fun _ => pure_rule _)
      · intro zca
        exact pure_rule _
    cases hz : currentlyEnabled extension.Ext_Zca s with
    | error e s' => simp only [hz] at h; cases h
    | ok zca s' =>
      have hp := hzca s s' zca hz
      by_cases halign : bit_to_bool (BitVec.access target 1) = true ∧
          LeanRV64D.Functions.not zca = true
      all_goals
        simp only [hz, ExceptT.bindCont, liftM, monadLift, MonadLift.monadLift,
          ExceptT.lift, ExceptT.mk, EStateM.map, Functor.map,
          Bool.and_eq_true, halign, ↓reduceIte,
          set_next_pc, Sail.writeReg, bind, EStateM.bind, pure, EStateM.pure] at h
        cases h
        simpa only [Std.ExtDHashMap.get?_insert, beq_iff_eq,
          reduceCtorEq, ↓reduceDIte] using hp
  · simp only [hbit, ↓reduceIte, throw, throwThe] at h
    cases h

end PCFrame

namespace JoltPCFrame
open JoltISA

def Preserves {α : Type} (m : JoltMonad α) : Prop :=
  ∀ (s t : SailJoltState) (v : α), m s = .ok v t →
    t.sail.regs.get? Register.PC = s.sail.regs.get? Register.PC

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

theorem lift_rule {α : Type} {m : SailM α} (hm : PCFrame.Preserves m) :
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

macro "jolt_pc_auto" : tactic => `(tactic|
  repeat' first
  | exact read_rule _
  | exact write_rule _ _
  | exact pure_rule _
  | exact throw_rule _
  | exact get_rule
  | exact lift_rule (PCFrame.read_rule _)
  | exact lift_rule (PCFrame.write_rule _ _ (by decide))
  | exact lift_rule (PCFrame.jump_rule _)
  | fail_if_no_progress dsimp only [get_arch_pc, get_next_pc]
  | split
  | refine bind_rule ?_ (fun x => ?_))

theorem ordinary_instruction (instr : Instr)
    (hload : ∀ fault dst base imm, instr ≠ .LD fault dst base imm)
    (hstore : ∀ base value imm, instr ≠ .SD base value imm)
    (hhost : ∀ dst src imm, instr ≠ .VirtualHostIO dst src imm) :
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
  all_goals simp only [execInstr]
  all_goals try jolt_pc_auto

end JoltPCFrame

namespace JoltPCFrame
open JoltISA

theorem aligned_access (addr : BitVec 64) (h : addr &&& 7 = 0) :
    AlignedDwordAccess addr :=
  { misalign := access_misaligned_8_aligned_false addr h
    split := split_misaligned_aligned_8 addr h
    align := h
    no_ovf := aligned_addr_no_ovf_of_align addr h }

theorem memory_read (s : SailJoltState) (ops : AssumptionOperands)
    (ha : all_assumptions s ops) (addr : BitVec 64)
    (halign : addr &&& 7 = 0)
    (hwindow : ramStartAddress ≤ addr.toNat → ops.memoryWindows addr)
    (t : SailJoltState) (v : Result (BitVec 64) ExecutionResult)
    (hr : readMemoryWord addr s = .ok v t) : t = s := by
  by_cases hram : ramStartAddress ≤ addr.toNat
  · obtain ⟨hbytes, hpmp, _, _, _, _, _, hmmio, _⟩ :=
      ha.2.2.2.2.1 addr (hwindow hram)
    have hread := vmem_read_addr_dword_reduces addr s.sail
      ha.curPrivilege ha.mstatusMprv (aligned_access addr halign)
      hbytes.memBytesPresentAt hpmp hmmio
    rw [readMemoryWord_ram addr hram] at hr
    simp only [liftSail, hread] at hr
    cases hr
    rfl
  · simp only [readMemoryWord, Nat.lt_of_not_ge hram, ↓reduceIte] at hr
    split at hr <;> cases hr <;> rfl

theorem memory_write (s : SailJoltState) (ops : AssumptionOperands)
    (ha : all_assumptions s ops) (addr data : BitVec 64)
    (halign : addr &&& 7 = 0)
    (hwindow : ramStartAddress ≤ addr.toNat → ops.memoryWindows addr)
    (t : SailJoltState) (v : Result Bool ExecutionResult)
    (hr : writeMemoryWord addr data s = .ok v t) :
    t.sail.regs.get? Register.PC = s.sail.regs.get? Register.PC := by
  by_cases hram : ramStartAddress ≤ addr.toNat
  · obtain ⟨_, _, _, hpmp, _, _, _, _, _, hmmio, _⟩ :=
      ha.2.2.2.2.1 addr (hwindow hram)
    have hwrite := vmem_write_addr_dword_store_reduces addr data s.sail
      ha.curPrivilege ha.mstatusMprv (aligned_access addr halign).toAlignedAccess
      hpmp hmmio
    rw [writeMemoryWord_ram addr data hram] at hr
    simp only [liftSail, hwrite] at hr
    cases hr
    rfl
  · simp only [writeMemoryWord, Nat.lt_of_not_ge hram, ↓reduceIte] at hr
    split at hr <;> cases hr <;> rfl

theorem load_instruction (fault : LoadFaultClass) (dst : Dst) (base : Src)
    (imm : BitVec 64) (s t : SailJoltState) (ops : AssumptionOperands)
    (ha : all_assumptions s ops)
    (hwindow : ramStartAddress ≤ (sourceValue base s + imm).toNat →
      ops.memoryWindows (sourceValue base s + imm))
    (hexec : execInstr (.LD fault dst base imm) s = .ok (.Retire_Success ()) t) :
    t.sail.regs.get? Register.PC = s.sail.regs.get? Register.PC := by
  have hx := lookup_read_bind base _ _ _ _ hexec
  by_cases halign : (sourceValue base s + imm) &&& 7 = 0
  · simp only [halign, ↓reduceIte] at hx
    cases hr : readMemoryWord (sourceValue base s + imm) s with
    | error e s' => simp only [bind, EStateM.bind, hr] at hx; cases hx
    | ok v s' =>
      have hstate := memory_read s ops ha _ halign hwindow s' v hr
      subst s'
      simp only [bind, EStateM.bind, hr] at hx
      cases v with
      | Ok value =>
        exact (bind_rule (write_rule dst value) (fun _ => pure_rule _)) s t _ hx
      | Err e => cases hx; rfl
  · simp only [halign, ↓reduceIte, pure, EStateM.pure] at hx
    cases hx

theorem store_instruction (base value : Src) (imm : BitVec 64)
    (s t : SailJoltState) (ops : AssumptionOperands)
    (ha : all_assumptions s ops)
    (hwindow : ramStartAddress ≤ (sourceValue base s + imm).toNat →
      ops.memoryWindows (sourceValue base s + imm))
    (hexec : execInstr (.SD base value imm) s = .ok (.Retire_Success ()) t) :
    t.sail.regs.get? Register.PC = s.sail.regs.get? Register.PC := by
  have hx := lookup_read_bind base _ _ _ _ hexec
  have hx := lookup_read_bind value _ _ _ _ hx
  by_cases halign : (sourceValue base s + imm) &&& 7 = 0
  · simp only [halign, ↓reduceIte] at hx
    cases hr : writeMemoryWord (sourceValue base s + imm) (sourceValue value s) s with
    | error e s' => simp only [bind, EStateM.bind, hr] at hx; cases hx
    | ok v s' =>
      have hp := memory_write s ops ha _ _ halign hwindow s' v hr
      simp only [bind, EStateM.bind, hr] at hx
      cases v <;> cases hx <;> exact hp
  · simp only [halign, ↓reduceIte, pure, EStateM.pure] at hx
    cases hx

end JoltPCFrame

namespace JoltPCFrame
open JoltISA

def MemoryWindowsCovered (instr : Instr) (s : SailJoltState)
    (ops : AssumptionOperands) : Prop :=
  match instr with
  | .LD _ _ base imm | .SD base _ imm =>
    ramStartAddress ≤ (sourceValue base s + imm).toNat →
      ops.memoryWindows (sourceValue base s + imm)
  | _ => True

theorem instruction (instr : Instr) (s t : SailJoltState)
    (ops : AssumptionOperands) (ha : all_assumptions s ops)
    (hwindow : MemoryWindowsCovered instr s ops)
    (hhost : instr.HostIOPCFrame s t)
    (hexec : execInstr instr s = .ok (.Retire_Success ()) t) :
    t.sail.regs.get? Register.PC = s.sail.regs.get? Register.PC := by
  cases instr with
  | LD fault dst base imm => exact load_instruction fault dst base imm s t ops ha hwindow hexec
  | SD base value imm => exact store_instruction base value imm s t ops ha hwindow hexec
  | VirtualHostIO _ _ _ => exact hhost
  | _ =>
    exact ordinary_instruction _
      (by intros; intro h; cases h) (by intros; intro h; cases h)
      (by intros; intro h; cases h) s t _ hexec

theorem hostIOPCFrame_withRuntimeAdvice (instr : Instr) (advice : instr.RuntimeAdvice)
    (s t : SailJoltState) :
    (instr.withRuntimeAdvice advice).HostIOPCFrame s t = instr.HostIOPCFrame s t := by
  cases instr <;> rfl

theorem memoryWindows_withRuntimeAdvice (instr : Instr) (advice : instr.RuntimeAdvice)
    (s : SailJoltState) (ops : AssumptionOperands) :
    MemoryWindowsCovered (instr.withRuntimeAdvice advice) s ops =
      MemoryWindowsCovered instr s ops := by
  cases instr <;> rfl

theorem row {program : JoltProgram} (trace : JoltTrace program)
    (i : Fin trace.rows.size) :
    trace.rows[i].postState.sail.regs.get? Register.PC =
      trace.rows[i].preState.sail.regs.get? Register.PC := by
  apply instruction _ _ _ (trace.assumptionOperands i) (trace.allAssumptions i)
    _ _ trace.rows[i].executes
  · rw [memoryWindows_withRuntimeAdvice]
    exact trace.ramAccessAssumed i
  · rw [hostIOPCFrame_withRuntimeAdvice]
    exact trace.rows[i].hostIOPreservesPC

end JoltPCFrame

theorem lookup_prepareSource_PC (program : JoltProgram)
    (layout : program.SequenceLayout) (i : Fin program.expandedBytecode.size)
    (state : SailJoltState) :
    (program.prepareSource layout i state).sail.regs.get? Register.PC =
      some program.expandedBytecode[i].address := by
  simp only [JoltProgram.prepareSource, Std.ExtDHashMap.get?_insert,
    beq_iff_eq, reduceCtorEq, ↓reduceDIte, cast_eq]

theorem lookup_trace_PC {program : JoltProgram} (trace : JoltTrace program)
    (n : Nat) (hn : n < trace.rows.size) :
    trace.rows[n].preState.sail.regs.get? Register.PC =
      some program.expandedBytecode[trace.rows[n].rowIndex].address := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero =>
      rw [trace.startsAtInitial hn]
      exact lookup_prepareSource_PC program trace.sequenceLayout _ _
    | succ m =>
      have hm : m < trace.rows.size := by omega
      have hp := ih m (by omega) hm
      have hlink := trace.linked m hm hn
      let prev := trace.rows[m]
      let curr := trace.rows[m + 1]
      by_cases hc : program.expandedBytecode[prev.rowIndex].continues = true
      · change program.expandedBytecode[trace.rows[m].rowIndex].continues = true at hc
        have hsucc := trace.successor m hm hn
        simp only [hc, ↓reduceIte] at hlink hsucc
        obtain ⟨haddr, _, _, _⟩ :=
          trace.sequenceLayout.next prev.rowIndex curr.rowIndex hsucc hc
        have hpres := JoltPCFrame.row trace ⟨m, hm⟩
        change trace.rows[m].postState.sail.regs.get? Register.PC =
          trace.rows[m].preState.sail.regs.get? Register.PC at hpres
        change curr.preState.sail.regs.get? Register.PC = _
        rw [hlink, hpres, hp]
        exact congrArg some haddr.symm
      · change ¬ program.expandedBytecode[trace.rows[m].rowIndex].continues = true at hc
        simp only [if_neg hc] at hlink
        change curr.preState.sail.regs.get? Register.PC = _
        rw [hlink]
        exact lookup_prepareSource_PC program trace.sequenceLayout curr.rowIndex _
