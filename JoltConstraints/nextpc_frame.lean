import JoltConstraints.metadata
import JoltBytecode.InstructionEquivalence.ProofSupport.Preservation
import JoltBytecode.InstructionEquivalence.ProofSupport.RegisterAccess
import JoltBytecode.InstructionEquivalence.ProofSupport.BundleLemmas
import JoltBytecode.InstructionEquivalence.ProofSupport.Memory.Write
import JoltBytecode.InstructionEquivalence.ProofSupport.Memory.Read

open LeanRV64D

/-!
Instruction-level nextPC frames. Ordinary instructions, untaken branches, and
word memory operations preserve nextPC. HostIO's frame is proved in
`HostIOFrame.lean` and supplies the remaining case.
-/

set_option autoImplicit false

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail LeanRV64D LeanRV64D.Functions

-- Operand reads, moved here from LookupWriteProofHelpers.lean so the frame lemmas
-- below can sit under trace_interface.lean.
private theorem readReg_get (reg : Register) (s : SailState)
    (v : RegisterType reg) (s' : SailState)
    (h : (LeanRV64D.readReg reg : SailM (RegisterType reg)) s = .ok v s') :
    s.regs.get? reg = some v := by
  unfold LeanRV64D.readReg Sail.ConcurrencyInterfaceV1.PreSail.readReg at h
  simp only [bind, EStateM.bind, get, MonadStateOf.get, getThe, EStateM.get,
    pure] at h
  cases hg : s.regs.get? reg with
  | none => simp only [hg] at h; change EStateM.Result.error Error.Unreachable s = .ok v s' at h; cases h
  | some value => simp [hg] at h; cases h; rfl

theorem lookup_readSrc_value (src : JoltISA.Src) (state state' : SailJoltState)
    (value : BitVec 64)
    (hread : JoltISA.readSrc src state = .ok value state') :
    state' = state ∧ value = JoltISA.sourceValue src state := by
  cases src with
  | vreg vr =>
      simp only [JoltISA.readSrc_vreg, readVReg_run] at hread
      cases hread
      exact ⟨rfl, rfl⟩
  | xreg rd =>
      change liftSail (rX_bits rd) state = .ok value state' at hread
      unfold liftSail at hread
      cases h : rX_bits rd state.sail with
      | error e s =>
          rw [h] at hread
          cases hread
      | ok v s =>
          rw [h] at hread
          have hs : s = state.sail := rX_bits_pure rd state.sail v s h
          subst s
          cases hread
          constructor
          · rfl
          · reg_cases rd
            all_goals
              simp_all only [JoltISA.sourceValue, rX_bits, rX,
                regval_from_reg, Sail.BitVec.toNatInt, Int.ofNat_eq_natCast,
                Int.toNat_natCast, zero_reg, zeros]
              first
              | simp only [bind, EStateM.bind, pure, EStateM.pure] at h
                cases h
                rfl
              | simp only [bind, EStateM.bind, pure, EStateM.pure] at h
                generalize hread : LeanRV64D.readReg _ state.sail = result at h
                cases result with
                | error e s => cases h
                | ok v s =>
                    have hg := readReg_get _ _ _ _ hread
                    simp only [hg, Option.getD_some]
                    cases h
                    rfl

/-- Successful operand reads can be replaced by the pure witness calculation. -/
theorem lookup_read_bind {α : Type} (src : JoltISA.Src)
    (f : BitVec 64 → JoltMonad α) (pre post : SailJoltState) (result : α)
    (hexec : (JoltISA.readSrc src >>= f) pre = .ok result post) :
    f (JoltISA.sourceValue src pre) pre = .ok result post := by
  cases hr : JoltISA.readSrc src pre with
  | error e s => simp only [bind, EStateM.bind, hr] at hexec; cases hexec
  | ok v s =>
    obtain ⟨rfl, rfl⟩ := lookup_readSrc_value src pre s v hr
    simpa only [bind, EStateM.bind, hr] using hexec

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

theorem read_rule (r : Register) : Preserves (LeanRV64D.readReg r) := by
  intro s t v h
  cases readReg_pure r s v t h
  rfl

theorem write_rule (r : Register) (v : RegisterType r)
    (hne : r ≠ Register.nextPC) : Preserves (LeanRV64D.writeReg r v) := by
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

/-- A non-memory, non-host row with neither a jump nor a branch flag preserves
Sail's nextPC register for every successful computation result.
For example, ADD writes its destination without changing nextPC.
The load/store flags exclude both native and floor rows, which `instruction`
handles separately; Jolt's tracer uses the memory rows in
`tracer/src/instruction/floor_access.rs` (`load`, `store`) at `c6703570`. -/
theorem ordinary_instruction (instr : Instr)
    (hload : JoltMetadata.opcodeFlag instr .Load = false)
    (hstore : JoltMetadata.opcodeFlag instr .Store = false)
    (hhost : instr ≠ .VirtualHostIO)
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
  all_goals try (simp only [JoltMetadata.opcodeFlag, Bool.true_eq_false] at hload hstore)
  all_goals try exact False.elim (hhost rfl)
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

/-- A doubleword load preserves nextPC, even when it returns an MMU error.
For example, loading the containing doubleword at address 8 cannot change nextPC.
Jolt's tracer: `tracer/src/emulator/mmu.rs` (`Mmu::load_doubleword`) at `c6703570`. -/
theorem load_doubleword_rule (address : BitVec 64) :
    Preserves (Mmu.load_doubleword address) := by
  intro s t result runs
  rw [Mmu.load_doubleword_state runs]

/-- A doubleword store preserves nextPC while updating memory or device state.
For example, storing a merged byte lane at address 8 cannot change nextPC.
Jolt's tracer: `tracer/src/emulator/mmu.rs` (`Mmu::store_doubleword`) at `c6703570`. -/
theorem store_doubleword_rule (address value : BitVec 64) :
    Preserves (Mmu.store_doubleword address value) := by
  intro s t result runs
  rw [(Mmu.store_doubleword_regs runs).1]

/-- A retired LD preserves nextPC; for example, LD into x5 changes x5 but
leaves Sail's nextPC register intact.
Jolt's tracer: `tracer/src/instruction/ld.rs` (`LD::exec`) at `c6703570`. -/
theorem load_instruction (fault : LoadFaultClass) (dst : Dst) (base : Src)
    (imm : BitVec 64) (s t : SailJoltState)
    (hexec : execInstr (.LD fault dst base imm) s = .ok (.Retire_Success ()) t) :
    t.sail.regs.get? Register.nextPC = s.sail.regs.get? Register.nextPC := by
  have keeps : Preserves (execInstr (.LD fault dst base imm)) := by
    simp only [execInstr]
    preservation_auto [read_rule _, write_rule _ _, pure_rule _,
      load_doubleword_rule _] using bind_rule
  exact keeps s t _ hexec

/-- A retired SD preserves nextPC; for example, writing a doubleword to RAM
changes its bytes but leaves Sail's nextPC register intact.
Jolt's tracer: `tracer/src/instruction/sd.rs` (`SD::exec`) at `c6703570`. -/
theorem store_instruction (base value : Src) (imm : BitVec 64)
    (s t : SailJoltState)
    (hexec : execInstr (.SD base value imm) s = .ok (.Retire_Success ()) t) :
    t.sail.regs.get? Register.nextPC = s.sail.regs.get? Register.nextPC := by
  have keeps : Preserves (execInstr (.SD base value imm)) := by
    simp only [execInstr]
    preservation_auto [read_rule _, pure_rule _, store_doubleword_rule _ _] using bind_rule
  exact keeps s t _ hexec

/-- Each floor load preserves nextPC, for all three width classes and all
successful computation results, including modeled memory exceptions.
For example, VirtualLoadH at effective address 10 loads from 8 without changing nextPC.
Jolt's tracer: `tracer/src/instruction/floor_access.rs` (`load`) at `c6703570`. -/
theorem floor_load_instruction (instr : Instr) (faultClass : LoadFaultClass)
    (dst : Dst) (base : Src) (imm : BitVec 64) (fault : ExceptionType)
    (selected : instr = .VirtualLoadB faultClass dst base imm fault ∨
      instr = .VirtualLoadH faultClass dst base imm fault ∨
      instr = .VirtualLoadW faultClass dst base imm fault) :
    Preserves (execInstr instr) := by
  rcases selected with rfl | rfl | rfl <;> simp only [execInstr]
  all_goals preservation_auto [read_rule _, write_rule _ _, pure_rule _,
    load_doubleword_rule _] using bind_rule

/-- Each floor store preserves nextPC, for all three width classes and all
successful computation results, including modeled memory exceptions.
For example, VirtualStoreW at effective address 12 writes to 8 without changing nextPC.
Jolt's tracer: `tracer/src/instruction/floor_access.rs` (`store`) at `c6703570`. -/
theorem floor_store_instruction (instr : Instr) (base value : Src)
    (imm : BitVec 64) (fault : ExceptionType)
    (selected : instr = .VirtualStoreB base value imm fault ∨
      instr = .VirtualStoreH base value imm fault ∨
      instr = .VirtualStoreW base value imm fault) :
    Preserves (execInstr instr) := by
  rcases selected with rfl | rfl | rfl <;> simp only [execInstr]
  all_goals preservation_auto [read_rule _, pure_rule _, store_doubleword_rule _ _]
    using bind_rule

def HostIOFrame (instr : Instr) (s t : SailJoltState) : Prop :=
  match instr with
  | .VirtualHostIO .. =>
      t.sail.regs.get? Register.nextPC = s.sail.regs.get? Register.nextPC
  | _ => True

/-- A retired non-jump row preserves nextPC when its branch is not taken and
its host-call frame holds; for example, a floor load needs no extra premise.
Memory rows are classified once by their flags and use shared MMU frame rules.
Jolt's tracer: `tracer/src/instruction/floor_access.rs` (`load`, `store`)
at `c6703570`. -/
theorem instruction (instr : Instr) (s t : SailJoltState)
    (hjump : JoltMetadata.opcodeFlag instr .Jump = false)
    (hnot : BranchTaken instr s = false)
    (hhost : HostIOFrame instr s t)
    (hexec : execInstr instr s = .ok (.Retire_Success ()) t) :
    t.sail.regs.get? Register.nextPC = s.sail.regs.get? Register.nextPC := by
  by_cases hload : JoltMetadata.opcodeFlag instr .Load = true
  · obtain ⟨faultClass, dst, base, imm, selected⟩ := JoltMetadata.opcodeFlag_load_cases instr hload
    rcases selected with rfl | ⟨fault, selected⟩
    · exact load_instruction faultClass dst base imm s t hexec
    · exact floor_load_instruction instr faultClass dst base imm fault selected s t _ hexec
  by_cases hstore : JoltMetadata.opcodeFlag instr .Store = true
  · obtain ⟨base, value, imm, selected⟩ := JoltMetadata.opcodeFlag_store_cases instr hstore
    rcases selected with rfl | ⟨fault, selected⟩
    · exact store_instruction base value imm s t hexec
    · exact floor_store_instruction instr base value imm fault selected s t _ hexec
  by_cases host : instr = .VirtualHostIO
  · subst instr
    exact hhost
  by_cases branch : JoltMetadata.instructionFlag instr .Branch = true
  · rw [branch_not_taken instr s t branch hnot hexec]
  exact ordinary_instruction instr (by simpa using hload) (by simpa using hstore)
    host ⟨hjump, by simpa using branch⟩ s t _ hexec

end JoltNextPCFrame
