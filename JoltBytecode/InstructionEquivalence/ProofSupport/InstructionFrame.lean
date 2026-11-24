import JoltBytecode.JoltISA.Semantics
import JoltBytecode.InstructionEquivalence.ProofSupport.Preservation
import Batteries.Data.Array.Lemmas
import JoltBytecode.InstructionEquivalence.ProofSupport.RegisterAccess
import JoltBytecode.InstructionEquivalence.ProofSupport.Memory.MmuJolt

open LeanRV64D

/-! A shared frame for Jolt instructions, parameterized by a state relation.
Sail register effects must preserve memory, and store effects must satisfy the
checked MMU's doubleword-store relation. This supports both static setup and
protected shared-memory invariants at Jolt `ff6fc6568`.
See `tracer/src/emulator/mmu.rs` (`store_raw`, `assert_write_protected_store`)
and `tracer/src/emulator/cpu.rs` (`Cpu::halt`, `Cpu::tick`). -/

set_option autoImplicit false

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail LeanRV64D LeanRV64D.Functions JoltISA

namespace InstructionFrame

/-- Primitive preservation obligations for a reflexive, transitive state relation.
`sail` permits memory-preserving Sail effects, `vreg` permits a virtual-register
write, `store` requires checked MMU doubleword stores to preserve the relation, and `append` permits adding
bytes to the advice tape without moving its cursor.
For example, preserving protected shared-memory bytes fits these rules.
Tape reads are supplied separately for the instruction being executed. -/
structure Rules (relation : SailJoltState → SailJoltState → Prop) : Prop where
  refl : ∀ state, relation state state
  trans : ∀ before middle after, relation before middle → relation middle after →
    relation before after
  sail : ∀ (state : SailJoltState) (after : SailState), after.mem = state.sail.mem → relation state { state with sail := after }
  vreg : ∀ state vr value, relation state
    { state with vregs := fun r => if r = vr then value else state.vregs r }
  store : ∀ address value,
    StatePreservation.Preserves relation (Mmu.store_doubleword address value)
  halt : ∀ state kind, relation state (recordHalt kind state)
  append : ∀ state bytes, relation state
    { state with adviceTape :=
      { state.adviceTape with bytes := state.adviceTape.bytes ++ bytes } }

/-- Preservation obligations for primitives other than device stores and tape reads.
For example, preserving protected shared-memory bytes permits register effects
and tape appends; checked stores provide a separate obligation.
See `tracer/src/emulator/cpu.rs` (`Cpu::tick`) at `ff6fc6568`. -/
structure NonStoreRules (relation : SailJoltState → SailJoltState → Prop) : Prop where
  refl : ∀ state, relation state state
  trans : ∀ before middle after, relation before middle → relation middle after →
    relation before after
  sail : ∀ (state : SailJoltState) (after : SailState), after.mem = state.sail.mem → relation state { state with sail := after }
  vreg : ∀ state vr value, relation state
    { state with vregs := fun r => if r = vr then value else state.vregs r }
  halt : ∀ state kind, relation state (recordHalt kind state)
  append : ∀ state bytes, relation state
    { state with adviceTape :=
      { state.adviceTape with bytes := state.adviceTape.bytes ++ bytes } }

private theorem Rules.nonStore {relation : SailJoltState → SailJoltState → Prop}
    (rules : Rules relation) : NonStoreRules relation :=
  ⟨rules.refl, rules.trans, rules.sail, rules.vreg, rules.halt, rules.append⟩

private theorem NonStoreRules.withStore {relation : SailJoltState → SailJoltState → Prop}
    (rules : NonStoreRules relation)
    (store : ∀ address value,
      StatePreservation.Preserves relation (Mmu.store_doubleword address value)) : Rules relation :=
  ⟨rules.refl, rules.trans, rules.sail, rules.vreg, store, rules.halt, rules.append⟩

/-- Writing a destination preserves any relation that permits Sail replacement
and virtual-register writes.
For example, writing register x5 or virtual register 40 preserves input memory
and leaves the advice tape unchanged. -/
theorem writeDst_rule (relation : SailJoltState → SailJoltState → Prop)
    (sail : ∀ (state : SailJoltState) (after : SailState), after.mem = state.sail.mem → relation state { state with sail := after })
    (vreg : ∀ state vr value, relation state
      { state with vregs := fun r => if r = vr then value else state.vregs r })
    (dst : Dst) (value : BitVec 64) :
    StatePreservation.Preserves relation (writeDst dst value) := by
  cases dst with
  | vreg vr =>
    intro s t result runs
    simp only [writeDst, writeVReg] at runs
    split at runs
    · cases runs
    · cases runs
      exact vreg _ _ _
  | xreg rd =>
    apply StatePreservation.liftSail_rule (sailRelation := fun s t => t.mem = s.mem)
      (fun state after h => sail state after h)
    intro s t result runs
    cases result
    rw [wX_eq_modify_regs rd value s t runs]

variable {relation : SailJoltState → SailJoltState → Prop}

private def SailMemory {α : Type} (step : SailM α) : Prop :=
  StatePreservation.Preserves (fun s t => t.mem = s.mem) step

private theorem mem_pure {α : Type} (a : α) : SailMemory (pure a) :=
  StatePreservation.pure_rule
    (relation := fun (s t : SailState) => t.mem = s.mem) (fun _ => rfl) _

private theorem mem_bind {α β : Type} {m : SailM α} {f : α → SailM β}
    (hm : SailMemory m) (hf : ∀ a, SailMemory (f a)) : SailMemory (m >>= f) :=
  StatePreservation.bind_rule (fun _ _ _ h h' => h'.trans h) hm hf

private theorem mem_read (r : Register) : SailMemory (LeanRV64D.readReg r) := by
  intro s t a h
  rw [readReg_pure r s a t h]

private theorem mem_write (r : Register) (v : RegisterType r) :
    SailMemory (LeanRV64D.writeReg r v) := by
  intro s t a h
  simp only [LeanRV64D.writeReg, Sail.ConcurrencyInterfaceV1.PreSail.writeReg,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet] at h
  cases h
  rfl

private theorem mem_and {m n : SailM Bool} (hm : SailMemory m) (hn : SailMemory n) :
    SailMemory (m <&&> n) := by
  unfold _root_.andM
  refine mem_bind hm (fun b => ?_)
  cases b
  · exact mem_pure _
  · exact hn

private theorem mem_liftE {ε α : Type} {m : SailM α} (hm : SailMemory m) :
    SailMemory (ExceptT.run (monadLift m : SailME ε α)) := by
  intro s t a h
  simp only [ExceptT.run, monadLift, MonadLift.monadLift, ExceptT.lift,
    ExceptT.mk, Functor.map, EStateM.map] at h
  cases hr : m s with
  | error e u => rw [hr] at h; cases h
  | ok b u =>
    rw [hr] at h
    cases h
    exact hm s _ b hr

private theorem mem_bindE {ε α β : Type} {m : SailME ε α} {f : α → SailME ε β}
    (hm : SailMemory (ExceptT.run m)) (hf : ∀ a, SailMemory (ExceptT.run (f a))) :
    SailMemory (ExceptT.run (m >>= f)) := by
  simp only [bind, ExceptT.bind, ExceptT.run, ExceptT.mk, ExceptT.bindCont]
  refine mem_bind hm (fun a => ?_)
  cases a
  · exact mem_pure _
  · exact hf _

private theorem mem_andE {ε : Type} {m n : SailME ε Bool}
    (hm : SailMemory (ExceptT.run m)) (hn : SailMemory (ExceptT.run n)) :
    SailMemory (ExceptT.run (m <&&> n)) := by
  unfold _root_.andM
  refine mem_bindE hm (fun b => ?_)
  cases b
  · exact mem_pure _
  · exact hn

private theorem mem_runE {ε : Type} {m : SailME ε ε}
    (hm : SailMemory (ExceptT.run m)) : SailMemory (SailME.run m) := by
  unfold SailME.run PreSailME.run
  refine mem_bind hm (fun a => ?_)
  cases a with
  | ok value => exact mem_pure _
  | error e =>
    cases e with
    | inl e => exact StatePreservation.throw_rule _ _
    | inr value => exact mem_pure _

private theorem mem_jump (target : BitVec 64) : SailMemory (jump_to target) := by
  have henabled : SailMemory (currentlyEnabled extension.Ext_Zca) := by
    simp only [currentlyEnabled]
    exact mem_and (mem_pure _) (mem_bind
      (mem_and (mem_pure _) (mem_bind (mem_read _) (fun _ => mem_pure _)))
      (fun _ => mem_pure _))
  have hassert (b : Bool) (msg : String) : SailMemory (LeanRV64D.sail_assert b msg) := by
    cases b
    · exact StatePreservation.throw_rule _ _
    · exact mem_pure _
  unfold jump_to ext_control_check_pc
  apply mem_runE
  refine mem_bindE (mem_liftE (hassert _ _)) (fun _ => ?_)
  refine mem_bindE (mem_andE (mem_pure _)
    (mem_bindE (mem_liftE henabled) (fun _ => mem_pure _))) (fun b => ?_)
  cases b
  · refine mem_bindE (mem_liftE ?_) (fun _ => mem_pure _)
    unfold set_next_pc
    exact mem_bind (mem_write _ _) (fun _ => mem_pure _)
  · exact mem_pure _

private theorem lift_rule (rules : NonStoreRules relation) {α : Type} (step : SailM α)
    (hmem : SailMemory step) : StatePreservation.Preserves relation (liftSail step) :=
  StatePreservation.liftSail_rule rules.sail hmem

private theorem readSrc_rule (rules : NonStoreRules relation) (src : Src) :
    StatePreservation.Preserves relation (readSrc src) := by
  cases src with
  | vreg vr =>
    intro s t v h
    simp only [readSrc, readVReg, bind, EStateM.bind, get, getThe,
      MonadStateOf.get, EStateM.get, pure, EStateM.pure] at h
    cases h
    exact rules.refl _
  | xreg rs =>
    apply lift_rule rules _
    intro s t value runs
    rw [rX_bits_pure rs s value t runs]

/-- A successful raw byte store preserves the relation using the Sail rule for
RAM and the device-store rule for I/O.
For example, storing one byte to RAM changes only Sail memory. -/
theorem storeRaw_rule
    (sail : ∀ state after, relation state { state with sail := after })
    (store : ∀ state device address value,
      JoltDevice.store? state.jolt_device state.sail.mem address value = some device →
      relation state { state with sail := { state.sail with mem := device } })
    (s s' : SailJoltState)
    (address : Nat) (value : BitVec 8)
    (stored : Mmu.store_raw? s address value = some s') : relation s s' := by
  simp only [Mmu.store_raw?] at stored
  repeat' split at stored
  all_goals first
    | (cases stored; exact sail _ _)
    | cases stored
    | (cases deviceStore : s.jolt_device.store? s.sail.mem address value with
        | none => simp [deviceStore] at stored
        | some device =>
          simp only [deviceStore, Option.map_some] at stored
          cases stored
          exact sail _ _)

/-- A byte-store fold preserves a relation from its original state when each
listed offset preserves that relation for every reachable intermediate state.
For example, eight accepted byte stores preserve the protected canary bytes.
See `tracer/src/emulator/mmu.rs` (`Mmu::store_doubleword_raw`) at `ff6fc6568`. -/
theorem storeFold_rule_of_step (address : Nat) (value : BitVec 64)
    (s0 : SailJoltState) (offsets : List Nat)
    (step : ∀ k ∈ offsets, ∀ s s', relation s0 s →
      Mmu.store_raw? s (address + k) (value.extractLsb' (8 * k) 8) = some s' →
      relation s0 s') (start : Option SailJoltState)
    (hstart : ∀ s, start = some s → relation s0 s) (s' : SailJoltState)
    (stored : offsets.foldl (fun current k => current.bind fun s =>
      Mmu.store_raw? s (address + k) (value.extractLsb' (8 * k) 8)) start = some s') :
    relation s0 s' := by
  induction offsets generalizing start with
  | nil => exact hstart s' stored
  | cons k offsets ih =>
    refine ih (fun k member => step k (List.mem_cons_of_mem _ member)) _ ?_ stored
    intro s hs
    cases hst : start with
    | none => rw [hst] at hs; cases hs
    | some e =>
      rw [hst] at hs
      exact step k List.mem_cons_self e s (hstart e hst) hs

private theorem loadDoubleword_rule (rules : NonStoreRules relation) (address : BitVec 64) :
    StatePreservation.Preserves relation (Mmu.load_doubleword address) := by
  intro s t v h
  simp only [Mmu.load_doubleword] at h
  repeat' split at h
  all_goals first | (cases h; exact rules.refl _) | cases h

private theorem storeDoubleword_rule (rules : Rules relation) (address value : BitVec 64) :
    StatePreservation.Preserves relation (Mmu.store_doubleword address value) :=
  rules.store address value

private theorem execHostIO_rule (rules : NonStoreRules relation) :
    StatePreservation.Preserves relation execHostIO := by
  unfold execHostIO execHostIOWith
  preservation_auto [StatePreservation.get_rule rules.refl,
    StatePreservation.pure_rule rules.refl _,
    StatePreservation.modify_rule _ (fun state => rules.append state _)]
    using (StatePreservation.bind_rule rules.trans)

/-- Every successful instruction preserves a relation satisfying the non-store
primitive rules, its tape-read obligation, and checked-store obligations for SD and
the floor-addressed VirtualStoreB, VirtualStoreH, and VirtualStoreW rows.
For example, input memory is preserved by all four store kinds.
Each uses `Mmu.store_doubleword`, as in the tracer's `SD::exec` in
`tracer/src/instruction/sd.rs` and `store` in `tracer/src/instruction/floor_access.rs`.
For example, a device relation permits every tape read; tape growth uses this
theorem only when `instr` is not an advice load, making `read` vacuous.
The read obligation describes only consuming the tape; destination writes use
the same register-write rule as other instructions. -/
theorem execInstr_rule_of_store (rules : NonStoreRules relation) (instr : Instr)
    (store : ∀ base source imm, instr = .SD base source imm →
      ∀ address value, StatePreservation.Preserves relation (Mmu.store_doubleword address value))
    (floorStore : ∀ base source imm fault,
      (instr = .VirtualStoreB base source imm fault ∨
       instr = .VirtualStoreH base source imm fault ∨
       instr = .VirtualStoreW base source imm fault) →
      ∀ address value, StatePreservation.Preserves relation (Mmu.store_doubleword address value))
    (read : ∀ dst width, instr = .VirtualAdviceLoad dst width →
      ∀ state value tape, readAdviceTape state.adviceTape width = some (value, tape) →
        relation state { state with adviceTape := tape }) :
    StatePreservation.Preserves relation (execInstr instr) := by
  cases instr
  case VirtualAdviceLoad dst width =>
    intro s t v h
    simp only [execInstr] at h
    cases hr : readAdviceTape s.adviceTape width with
    | none => simp only [hr] at h; cases h
    | some pair =>
      obtain ⟨value, tape⟩ := pair
      simp only [hr] at h
      exact rules.trans _ _ _ (read dst width rfl s value tape hr)
        ((StatePreservation.bind_rule rules.trans
          (writeDst_rule relation rules.sail rules.vreg dst value)
          (fun _ => StatePreservation.pure_rule rules.refl _))
          { s with adviceTape := tape } t v h)
  case AUIPC dst imm =>
    simp only [execInstr]
    refine StatePreservation.bind_rule rules.trans ?_ (fun pc => ?_)
    · apply lift_rule rules
      simpa only [get_arch_pc] using mem_read Register.PC
    · exact StatePreservation.bind_rule rules.trans
        (writeDst_rule relation rules.sail rules.vreg dst _)
        (fun _ => StatePreservation.pure_rule rules.refl _)
  all_goals simp only [execInstr, execHalt]
  all_goals preservation_auto [readSrc_rule rules _,
    writeDst_rule relation rules.sail rules.vreg _ _,
    StatePreservation.pure_rule rules.refl _, StatePreservation.throw_rule relation _,
    StatePreservation.get_rule rules.refl,
    lift_rule rules (LeanRV64D.readReg _) (mem_read _),
    lift_rule rules (LeanRV64D.writeReg _ _) (mem_write _ _),
    lift_rule rules (get_arch_pc ()) (mem_read Register.PC),
    lift_rule rules (jump_to _) (mem_jump _), loadDoubleword_rule rules _,
    StatePreservation.modify_rule _ (fun state => rules.halt state _),
    storeDoubleword_rule (rules.withStore (store _ _ _ rfl)) _ _, execHostIO_rule rules]
    using (StatePreservation.bind_rule rules.trans)
  all_goals exact storeDoubleword_rule (rules.withStore
    (floorStore _ _ _ _ (by
      first
      | exact Or.inl rfl
      | exact Or.inr (Or.inl rfl)
      | exact Or.inr (Or.inr rfl)))) _ _


/-- Every successful instruction preserves a relation satisfying `rules` and
its instruction-specific tape-read obligation `read`.
For example, a device relation permits every tape read; tape growth uses this
theorem only when `instr` is not an advice load, making `read` vacuous.
The read obligation describes only consuming the tape; destination writes use
the same register-write rule as other instructions. -/
theorem execInstr_rule (rules : Rules relation) (instr : Instr)
    (read : ∀ dst width, instr = .VirtualAdviceLoad dst width →
      ∀ state value tape, readAdviceTape state.adviceTape width = some (value, tape) →
        relation state { state with adviceTape := tape }) :
    StatePreservation.Preserves relation (execInstr instr) := by
  exact execInstr_rule_of_store rules.nonStore instr
    (fun _ _ _ _ => rules.store) (fun _ _ _ _ _ => rules.store) read

end InstructionFrame
