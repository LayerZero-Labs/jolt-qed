/-
Step f: the code bytes stay intact through the run.

Jolt fetches instructions from the committed bytecode, never from RAM, while Sail's model fetches
from memory. The two agree only while the bytes of the instruction rows in memory are the image's.
This file states that as a Jolt-side invariant (`JoltCodeIntact`), shows that it gives the Sail-side
`CodeIntact` that `block_simulates_decoded` needs (`CodeIntact.of_related`), that it holds at the
start of every honest trace (`JoltCodeIntact.initial`), and that a block keeps it unless its
instruction stores into a code byte (`NoCodeStore`, `JoltCodeIntact.of_block`).
`docs/riscv-alignment.md` section 2 records this as a documented deviation of the model.
-/
import JoltConstraints.WholeRun.Decoded
import JoltConstraints.WholeRun.RunInv
import JoltConstraints.WholeRun.SystemBlocks

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail
  LeanRV64D LeanRV64D.Functions

set_option autoImplicit false
noncomputable section
namespace RiscvInstruction

/-- The first byte of the doubleword that Jolt's rows write when `i` stores, on the state `js`;
none for an instruction that does not store.
The narrow stores SB, SH and SW rewrite the aligned doubleword of their effective address,
SD writes the doubleword at its effective address (aligned whenever the row retires),
word atomics and SC.W the aligned doubleword of `rs1`, and doubleword atomics and SC.D the
doubleword at `rs1`.
For example, `SB` with `rs1 + imm = 0x80000003` has base `0x80000000`, and `AMOADD.D` with
`rs1 = 0x80000008` has base `0x80000008`.
These are the addresses of `Mmu::store_doubleword` in `tracer/src/emulator/mmu.rs`, which
every store, SC and AMO of the tracer reaches. -/
def storeBase : RiscvInstruction → SailJoltState → Option (BitVec 64)
  | .SB _ rs1 imm, js | .SH _ rs1 imm, js | .SW _ rs1 imm, js =>
      some (compute_aligned_dword_base_address (JoltISA.sourceValue (.xreg rs1) js) imm)
  | .SD _ rs1 imm, js => some (load_effective_address (JoltISA.sourceValue (.xreg rs1) js) imm)
  | .SC_W _ rs1 _ _ _, js
  | .AMOSWAP_W _ rs1 _ _ _, js | .AMOADD_W _ rs1 _ _ _, js
  | .AMOXOR_W _ rs1 _ _ _, js | .AMOAND_W _ rs1 _ _ _, js
  | .AMOOR_W _ rs1 _ _ _, js | .AMOMIN_W _ rs1 _ _ _, js
  | .AMOMAX_W _ rs1 _ _ _, js | .AMOMINU_W _ rs1 _ _ _, js
  | .AMOMAXU_W _ rs1 _ _ _, js => some (amoWordBase (JoltISA.sourceValue (.xreg rs1) js))
  | .SC_D _ rs1 _ _ _, js
  | .AMOSWAP_D _ rs1 _ _ _, js | .AMOADD_D _ rs1 _ _ _, js
  | .AMOXOR_D _ rs1 _ _ _, js | .AMOAND_D _ rs1 _ _ _, js
  | .AMOOR_D _ rs1 _ _ _, js | .AMOMIN_D _ rs1 _ _ _, js
  | .AMOMAX_D _ rs1 _ _ _, js | .AMOMINU_D _ rs1 _ _ _, js
  | .AMOMAXU_D _ rs1 _ _ _, js => some (JoltISA.sourceValue (.xreg rs1) js)
  | _, _ => none

end RiscvInstruction

/-- The first byte of the doubleword that Jolt's rows write when a RISC-V source instruction
stores; none for an instruction that does not store, and none for a custom instruction or a
registered inline, which the whole-run theorem leaves out of scope (`BlockConforms.riscv`).
For example, the custom instruction `AdviceLD` has none, and `SW` has its aligned doubleword. -/
def SourceInstruction.storeBase : SourceInstruction → SailJoltState → Option (BitVec 64)
  | .riscv i, js => i.storeBase js
  | .jolt _, _ => none
  | .inline .., _ => none

namespace WholeRun

-- Reuse the established implementation lemmas without changing their modules.
open private NoStoreRow NoStoreProgram ScratchRow AccessKind accessAddress storeRow StorePlan
  bind_success scratchRow_frozen sourceValue_regs reservation_store_plan csrrw_noStore csrBit_noStore
  csrrwi_noStore csrImmediateBit_noStore layout_memLow
  from JoltConstraints.WholeRun.Bundles
open private blockInstrs_eq expandedInstrs from JoltConstraints.WholeRun.Bridge

/-! ### One doubleword store changes only its own eight bytes -/

private theorem foldl_insert_get? (ea : Nat) (g : Nat → BitVec 8) (l : List Nat)
    (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) (h : ∀ k ∈ l, ea + k ≠ a) :
    (l.foldl (fun m k => m.insert (ea + k) (g k)) mem).get? a = mem.get? a := by
  induction l generalizing mem with
  | nil => rfl
  | cons k l ih =>
    rw [List.foldl_cons, ih _ (fun k' hk' => h k' (List.mem_cons_of_mem _ hk'))]
    have : ¬ (ea + k == a) = true := by
      simpa only [beq_iff_eq] using h k List.mem_cons_self
    simp only [Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.getElem?_insert, this,
      Bool.false_eq_true, ↓reduceIte]

private theorem store_raw_mem (s s' : SailJoltState) (ea : Nat) (v : BitVec 8) (a : Nat)
    (ha : a ≠ ea) (h : JoltISA.Mmu.store_raw? s ea v = some s') :
    s'.sail.mem.get? a = s.sail.mem.get? a := by
  unfold JoltISA.Mmu.store_raw? at h
  split at h
  · split at h
    · cases h
      have : ¬ (ea == a) = true := by simpa only [beq_iff_eq] using ha.symm
      simp only [Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.getElem?_insert, this,
        Bool.false_eq_true, ↓reduceIte]
    · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · obtain ⟨device, _, h⟩ := Option.map_eq_some_iff.mp h
        cases h
        rfl

private theorem store_bytes_mem (s0 : SailJoltState) (address : Nat) (v : BitVec 64) (a : Nat)
    (ks : List Nat) (hk : ∀ k ∈ ks, address + k ≠ a) (current : Option SailJoltState)
    (hc : ∀ s, current = some s → s.sail.mem.get? a = s0.sail.mem.get? a) :
    ∀ s, ks.foldl (fun state k => state.bind fun s =>
      JoltISA.Mmu.store_raw? s (address + k) (v.extractLsb' (8 * k) 8)) current = some s →
      s.sail.mem.get? a = s0.sail.mem.get? a := by
  induction ks generalizing current with
  | nil => exact hc
  | cons k ks ih =>
    apply ih (fun k' hk' => hk k' (List.mem_cons_of_mem _ hk'))
    intro next hnext
    cases hcur : current with
    | none => simp [hcur] at hnext
    | some before =>
      simp only [hcur, Option.bind_some] at hnext
      exact (store_raw_mem before next _ _ _ (hk k List.mem_cons_self).symm hnext).trans
        (hc before hcur)

/-- The bytes of the doubleword that starts at `base`.
For example, `InDword 0x80000008 0x8000000f` holds and `InDword 0x80000008 0x80000010` does not. -/
def InDword (base : BitVec 64) (a : Nat) : Prop :=
  base.toNat ≤ a ∧ a < base.toNat + 8

/-- A successful doubleword store writes no byte of Sail's memory map outside its own eight bytes;
a store to the I/O window writes none. -/
private theorem store_doubleword_mem (address value : BitVec 64) (s t : SailJoltState)
    (r : Result Bool ExecutionResult)
    (h : JoltISA.Mmu.store_doubleword address value s = .ok r t) (a : Nat)
    (ha : ¬ InDword address a) : t.sail.mem.get? a = s.sail.mem.get? a := by
  have hk : ∀ k ∈ List.range 8, address.toNat + k ≠ a := by
    intro k hk heq
    exact ha ⟨by omega, by have := List.mem_range.mp hk; omega⟩
  unfold JoltISA.Mmu.store_doubleword at h
  dsimp only at h
  split at h
  · cases h
  · split at h
    · split at h
      · cases h
        exact foldl_insert_get? _ (fun k => value.extractLsb' (8 * k) 8) _ _ _ hk
      · cases h
    · split at h
      · rename_i s' hs'
        have ht : s' = t := (EStateM.Result.ok.inj h).2
        exact ht ▸ store_bytes_mem s address.toNat value a (List.range 8) hk (some s)
          (fun s1 hs1 => by cases hs1; rfl) s' hs'
      · cases h


/-! ### Rows that do not store leave the memory map alone -/

private def MKeep (s t : SailJoltState) : Prop := t.sail.mem = s.sail.mem

private theorem mkeep_refl (s : SailJoltState) : MKeep s s := rfl

private theorem mkeep_trans (a b c : SailJoltState) (h : MKeep a b) (h' : MKeep b c) :
    MKeep a c := h'.trans h

private def SKeep (s t : SailState) : Prop := t.mem = s.mem

private theorem skeep_trans (a b c : SailState) (h : SKeep a b) (h' : SKeep b c) :
    SKeep a c := h'.trans h

private abbrev SKeeps {α : Type} (m : SailM α) : Prop := StatePreservation.Preserves SKeep m

private abbrev MKeeps {α : Type} (m : JoltMonad α) : Prop := StatePreservation.Preserves MKeep m

private theorem skeeps_pure {α : Type} (a : α) : SKeeps (pure a : SailM α) :=
  StatePreservation.pure_rule (relation := SKeep) (fun _ => rfl) a

private theorem skeeps_bind {α β : Type} {m : SailM α} {f : α → SailM β}
    (hm : SKeeps m) (hf : ∀ a, SKeeps (f a)) : SKeeps (m >>= f) :=
  StatePreservation.bind_rule skeep_trans hm hf

private theorem skeeps_ite {α : Type} {c : Prop} [Decidable c] {m n : SailM α}
    (hm : SKeeps m) (hn : SKeeps n) : SKeeps (if c then m else n) := by
  split <;> assumption

private theorem skeeps_throw {α : Type} (e : Error exception) : SKeeps (throw e : SailM α) :=
  StatePreservation.throw_rule SKeep e

private theorem skeeps_readReg (r : Register) :
    SKeeps (LeanRV64D.readReg r : SailM (RegisterType r)) := by
  intro s t v h
  cases hg : s.regs.get? r with
  | none => rw [Step.readReg_eq_of_get?_none r _ hg] at h; cases h
  | some w => rw [readReg_eq_of_get? r _ w hg] at h; cases h; rfl

private theorem skeeps_writeReg (r : Register) (v : RegisterType r) :
    SKeeps (LeanRV64D.writeReg r v : SailM Unit) := by
  intro s t u h
  rw [Step.writeReg_run] at h
  cases h
  rfl

private theorem skeeps_assert (b : Bool) (msg : String) :
    SKeeps (LeanRV64D.sail_assert b msg) := by
  intro s t u h
  cases b
  · cases h
  · cases h; rfl

private theorem skeeps_andM {m n : SailM Bool} (hm : SKeeps m) (hn : SKeeps n) :
    SKeeps (m <&&> n) := by
  unfold _root_.andM
  refine skeeps_bind hm fun b => ?_
  cases b
  · exact skeeps_pure _
  · exact hn

private theorem skeeps_map {α β : Type} (f : α → β) {m : SailM α} (hm : SKeeps m) :
    SKeeps (f <$> m) := by
  have h : f <$> m = m >>= fun a => pure (f a) := by
    funext s
    cases m s <;> rfl
  rw [h]
  exact skeeps_bind hm fun _ => skeeps_pure _

private theorem skeeps_set_next_pc (pc : BitVec 64) : SKeeps (set_next_pc pc) := by
  unfold set_next_pc
  exact skeeps_bind (skeeps_writeReg _ _) fun _ => skeeps_pure _

private theorem skeeps_enabled : SKeeps (currentlyEnabled extension.Ext_Zca) := by
  simp only [currentlyEnabled]
  refine skeeps_andM (skeeps_pure _) ?_
  refine skeeps_bind ?_ fun _ => skeeps_pure _
  exact skeeps_andM (skeeps_pure _) (skeeps_bind (skeeps_readReg _) fun _ => skeeps_pure _)

local macro "sail_keeps" : tactic =>
  `(tactic| repeat' (first
    | exact skeeps_readReg _
    | exact skeeps_writeReg _ _
    | exact skeeps_assert _ _
    | exact skeeps_pure _
    | apply skeeps_andM
    | apply skeeps_ite
    | apply skeeps_bind
    | split
    | intro _))

private theorem skeeps_rX (r : regidx) : SKeeps (rX_bits r) := by
  unfold rX_bits rX
  sail_keeps

private theorem skeeps_wX (r : regidx) (v : BitVec 64) : SKeeps (wX_bits r v) := by
  unfold wX_bits wX xreg_write_callback
  sail_keeps

private abbrev SEKeeps {ε α : Type} (m : SailME ε α) : Prop := SKeeps (ExceptT.run m)

private theorem sekeeps_pure {ε α : Type} (a : α) : SEKeeps (pure a : SailME ε α) :=
  skeeps_pure (Except.ok (ε := Error exception ⊕ ε) a)

private theorem sekeeps_bind {ε α β : Type} {m : SailME ε α} {f : α → SailME ε β}
    (hm : SEKeeps m) (hf : ∀ a, SEKeeps (f a)) : SEKeeps (m >>= f) := by
  change SKeeps (ExceptT.run m >>= ExceptT.bindCont f)
  refine skeeps_bind hm fun result => ?_
  cases result with
  | error e => exact skeeps_pure _
  | ok a => exact hf a

private theorem sekeeps_lift {ε α : Type} {m : SailM α} (hm : SKeeps m) :
    SEKeeps (liftM m : SailME ε α) := skeeps_map Except.ok hm

private theorem sekeeps_andM {ε : Type} {m n : SailME ε Bool}
    (hm : SEKeeps m) (hn : SEKeeps n) : SEKeeps (m <&&> n) := by
  unfold _root_.andM
  refine sekeeps_bind hm fun b => ?_
  cases b
  · exact sekeeps_pure _
  · exact hn

private theorem sekeeps_ite {ε α : Type} {c : Prop} [Decidable c] {m n : SailME ε α}
    (hm : SEKeeps m) (hn : SEKeeps n) : SEKeeps (if c then m else n) := by
  split <;> assumption

private theorem sekeeps_run {α : Type} {m : SailME α α} (hm : SEKeeps m) :
    SKeeps (SailME.run m) := by
  unfold SailME.run Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.run
  refine skeeps_bind hm fun result => ?_
  cases result with
  | ok a => exact skeeps_pure _
  | error e =>
    cases e with
    | inl e => exact skeeps_throw e
    | inr a => exact skeeps_pure _

private theorem skeeps_jump_to (target : BitVec 64) : SKeeps (jump_to target) := by
  unfold jump_to ext_control_check_pc
  apply sekeeps_run
  refine sekeeps_bind (sekeeps_lift (skeeps_assert _ _)) fun _ => ?_
  refine sekeeps_bind ?_ fun b => ?_
  · refine sekeeps_andM (sekeeps_pure _) ?_
    exact sekeeps_bind (sekeeps_lift skeeps_enabled) fun _ => sekeeps_pure _
  · exact sekeeps_ite (sekeeps_pure _)
      (sekeeps_bind (sekeeps_lift (skeeps_set_next_pc _)) fun _ => sekeeps_pure _)

private theorem mkeeps_lift {α : Type} {m : SailM α} (hm : SKeeps m) : MKeeps (liftSail m) :=
  StatePreservation.liftSail_rule (relation := MKeep) (sailRelation := SKeep)
    (fun _ _ h => h) hm

private theorem mkeeps_pure {α : Type} (a : α) : MKeeps (pure a : JoltMonad α) :=
  StatePreservation.pure_rule (relation := MKeep) mkeep_refl a

private theorem mkeeps_bind {α β : Type} {m : JoltMonad α} {f : α → JoltMonad β}
    (hm : MKeeps m) (hf : ∀ a, MKeeps (f a)) : MKeeps (m >>= f) :=
  StatePreservation.bind_rule mkeep_trans hm hf

private theorem mkeeps_ite {α : Type} {c : Prop} [Decidable c] {m n : JoltMonad α}
    (hm : MKeeps m) (hn : MKeeps n) : MKeeps (if c then m else n) := by
  split <;> assumption

private theorem mkeeps_throw {α : Type} (e : Error exception) : MKeeps (throw e : JoltMonad α) :=
  StatePreservation.throw_rule MKeep e

private theorem mkeeps_get : MKeeps (get : JoltMonad SailJoltState) :=
  StatePreservation.get_rule mkeep_refl

private theorem mkeeps_modify (f : SailJoltState → SailJoltState)
    (hf : ∀ js, (f js).sail.mem = js.sail.mem) : MKeeps (modify f) :=
  StatePreservation.modify_rule (relation := MKeep) f hf

private theorem mkeeps_readSrc (src : JoltISA.Src) : MKeeps (JoltISA.readSrc src) := by
  cases src with
  | xreg r => exact mkeeps_lift (skeeps_rX r)
  | vreg r =>
    unfold JoltISA.readSrc readVReg
    exact mkeeps_bind mkeeps_get fun _ => mkeeps_pure _

private theorem mkeeps_writeDst (dst : JoltISA.Dst) (v : BitVec 64) :
    MKeeps (JoltISA.writeDst dst v) := by
  cases dst with
  | xreg r => exact mkeeps_lift (skeeps_wX r v)
  | vreg r =>
    unfold JoltISA.writeDst writeVReg
    exact mkeeps_ite (mkeeps_throw _) (mkeeps_modify _ fun _ => rfl)

private theorem mkeeps_load (address : BitVec 64) : MKeeps (JoltISA.Mmu.load address) := by
  intro s t v h
  simp only [JoltISA.Mmu.load] at h
  repeat' split at h
  all_goals first | (cases h; exact mkeep_refl _) | cases h

private theorem mkeeps_load_doubleword (address : BitVec 64) :
    MKeeps (JoltISA.Mmu.load_doubleword address) := by
  intro s t v h
  simp only [JoltISA.Mmu.load_doubleword] at h
  repeat' split at h
  all_goals first | (cases h; exact mkeep_refl _) | cases h

private theorem mkeeps_hostLoad (address : BitVec 64) :
    MKeeps (JoltISA.Mmu.hostLoad address) := by
  intro s t v h
  cases h
  exact mkeep_refl _

private theorem mkeeps_readHostBytes {width : Nat}
    (pointer : BitVec width) (n : Nat) (bytes : Array (BitVec 8)) :
    MKeeps (JoltISA.readHostBytes JoltISA.Mmu.hostLoad pointer n bytes) := by
  induction n generalizing pointer bytes with
  | zero => exact mkeeps_pure _
  | succ n ih =>
    dsimp only [JoltISA.readHostBytes]
    refine mkeeps_bind (mkeeps_hostLoad _) (fun result => ?_)
    cases result with
    | none => exact mkeeps_pure _
    | some byte => exact ih _ _

private theorem mkeeps_hostIO : MKeeps JoltISA.execHostIO := by
  unfold JoltISA.execHostIO JoltISA.execHostIOWith JoltISA.readHostRange
  preservation_auto [mkeeps_readHostBytes _ _ _, mkeeps_readSrc _,
    mkeeps_pure _, mkeeps_get, mkeeps_modify _ (fun _ => rfl)]
    using (StatePreservation.bind_rule mkeep_trans)

local macro "jolt_keep" : tactic =>
  `(tactic| repeat' (first
    | exact mkeeps_readSrc _
    | exact mkeeps_writeDst _ _
    | exact mkeeps_pure _
    | exact mkeeps_throw _
    | exact mkeeps_get
    | exact mkeeps_modify _ (fun _ => rfl)
    | apply mkeeps_ite
    | refine mkeeps_bind ?_ (fun _ => ?_)
    | exact mkeeps_lift (skeeps_jump_to _)
    | exact mkeeps_lift (skeeps_set_next_pc _)
    | exact mkeeps_lift (skeeps_readReg _)
    | exact mkeeps_lift (skeeps_writeReg _ _)
    | exact mkeeps_load _
    | exact mkeeps_load_doubleword _
    | split))

/-- A row that is not a store leaves Jolt's memory map alone. -/
private theorem mkeeps_execInstr (i : JoltISA.Instr) (hi : NoStoreRow i) :
    MKeeps (JoltISA.execInstr i) := by
  cases i
  case VirtualAdviceLoad dst width =>
    intro s t v h
    simp only [JoltISA.execInstr] at h
    cases hr : JoltISA.readAdviceTape s.adviceTape width with
    | none => simp only [hr] at h; cases h
    | some pair =>
      obtain ⟨value, tape⟩ := pair
      simp only [hr] at h
      exact (mkeeps_bind (mkeeps_writeDst dst value) (fun _ => mkeeps_pure _)
        { s with adviceTape := tape } t v h)
  case VirtualHostIO => exact mkeeps_hostIO
  case SD => exact False.elim hi
  case VirtualStoreB => exact False.elim hi
  case VirtualStoreH => exact False.elim hi
  case VirtualStoreW => exact False.elim hi
  all_goals simp only [JoltISA.execInstr]
  all_goals jolt_keep

private theorem mkeeps_execProgram (p : JoltISA.Program) (hp : NoStoreProgram p) :
    MKeeps (JoltISA.execProgram p) := by
  induction p with
  | done _ => exact mkeeps_pure _
  | instr i rest ih =>
    simp only [JoltISA.execProgram]
    refine mkeeps_bind (mkeeps_execInstr i hp.1) fun result => ?_
    split
    · exact ih hp.2
    · exact mkeeps_pure _

private theorem scratchRow_noStore (i : JoltISA.Instr) (hi : ScratchRow i) : NoStoreRow i := by
  cases i <;> trivial

private theorem store_body_mem (addr value : BitVec 64) (s t : SailJoltState)
    (hrun : (do
      match ← JoltISA.Mmu.store_doubleword addr value with
      | .Ok _ => pure RETIRE_SUCCESS
      | .Err e => pure e : JoltMonad ExecutionResult) s = .ok RETIRE_SUCCESS t)
    (a : Nat) (ha : ¬ InDword addr a) : t.sail.mem.get? a = s.sail.mem.get? a := by
  obtain ⟨r, u, hm, ht⟩ := bind_success _ _ s t RETIRE_SUCCESS hrun
  have htu : t = u := by
    cases r <;> (simp only [pure, EStateM.pure] at ht; exact (EStateM.Result.ok.inj ht).2.symm)
  subst htu
  exact store_doubleword_mem addr value s t _ hm a ha

private theorem storeRow_mem (kind : AccessKind) (rs : regidx) (value : JoltISA.Src)
    (imm : BitVec 64) (s t : SailJoltState)
    (hrun : JoltISA.execInstr (storeRow kind rs value imm) s = .ok RETIRE_SUCCESS t)
    (a : Nat) (ha : ¬ InDword (accessAddress kind (JoltISA.sourceValue (.xreg rs) s) imm) a) :
    t.sail.mem.get? a = s.sail.mem.get? a := by
  cases kind
  all_goals simp only [storeRow, JoltISA.execInstr] at hrun
  all_goals have hbase := lookup_read_bind (.xreg rs) _ s t RETIRE_SUCCESS hrun
  case dword =>
    have hv := lookup_read_bind value _ s t RETIRE_SUCCESS hbase
    split at hv
    · exact store_body_mem _ _ s t hv a ha
    · cases hv
  case byte =>
    have hv := lookup_read_bind value _ s t RETIRE_SUCCESS hbase
    exact store_body_mem _ _ s t hv a ha
  all_goals split at hbase
  all_goals first
    | cases hbase
    | exact store_body_mem _ _ s t
        (lookup_read_bind value _ s t RETIRE_SUCCESS hbase) a ha

private theorem storePlan_mem (kind : AccessKind) (rs : regidx) (imm : BitVec 64)
    (p : JoltISA.Program) (hp : StorePlan kind rs imm p) (s t : SailJoltState)
    (hrun : JoltISA.execProgram p s = .ok RETIRE_SUCCESS t) (a : Nat)
    (ha : ¬ InDword (accessAddress kind (JoltISA.sourceValue (.xreg rs) s) imm) a) :
    t.sail.mem.get? a = s.sail.mem.get? a := by
  induction hp generalizing s t with
  | store value rest htail =>
    obtain ⟨u, hrow, hrest⟩ := JoltISA.execProgram_instr_run_retire_inv _ _ s t hrun
    rw [mkeeps_execProgram rest htail u t _ hrest]
    exact storeRow_mem kind rs value imm s u hrow a ha
  | scratch row rest hrow htail ih =>
    obtain ⟨u, hstep, hrest⟩ := JoltISA.execProgram_instr_run_retire_inv _ _ s t hrun
    obtain ⟨hregs, -⟩ := scratchRow_frozen row hrow s u _ hstep
    have heq := sourceValue_regs rs s u hregs
    rw [ih u t hrest (by rw [heq]; exact ha),
      mkeeps_execInstr row (scratchRow_noStore row hrow) s u _ hstep]


private theorem accessAddress_word_zero (v : BitVec 64) :
    accessAddress AccessKind.word v 0 = amoWordBase v := by
  simp [accessAddress, amoWordBase]

private theorem accessAddress_dword_zero (v : BitVec 64) :
    accessAddress AccessKind.dword v 0 = v := by
  simp [accessAddress]

private theorem get_of_keep {s t : SailJoltState} (h : MKeep s t) (a : Nat) :
    t.sail.mem.get? a = s.sail.mem.get? a := by
  rw [show t.sail.mem = s.sail.mem from h]

private theorem sc_mem (double : Bool) (rd rs1 rs2 : regidx) (s t : SailJoltState)
    (hrun : JoltISA.execProgram (SystemProofs.scRows double rd rs1 rs2) s = .ok RETIRE_SUCCESS t)
    (a : Nat)
    (ha : ¬ InDword (SystemProofs.reservationBase double (JoltISA.sourceValue (.xreg rs1) s)) a) :
    t.sail.mem.get? a = s.sail.mem.get? a := by
  have heq : accessAddress (if double then AccessKind.dword else AccessKind.word)
      (JoltISA.sourceValue (.xreg rs1) s) 0#64 =
      SystemProofs.reservationBase double (JoltISA.sourceValue (.xreg rs1) s) := by
    cases double <;> simp [accessAddress, SystemProofs.reservationBase, amoWordBase]
  exact storePlan_mem _ rs1 0#64 _ (reservation_store_plan double rd rs1 rs2) s t hrun a
    (by rw [heq]; exact ha)

private theorem lr_mem (double : Bool) (rd rs1 rs2 : regidx) (s t : SailJoltState)
    (hrun : JoltISA.execProgram (SystemProofs.lrRows double rd rs1 rs2) s = .ok RETIRE_SUCCESS t)
    (a : Nat) : t.sail.mem.get? a = s.sail.mem.get? a := by
  refine get_of_keep (mkeeps_execProgram _ ?_ s t _ hrun) a
  cases double
  all_goals simp only [SystemProofs.lrRows, Bool.false_eq_true, ite_true, ite_false,
    JoltISA.lrwProgramAuto, JoltISA.lrdProgramAuto]
  all_goals split <;> simp [NoStoreProgram, NoStoreRow]

/-- **Frame lemma for one source instruction.** If the rows of `i`, with honest advice, retire
from `s` to `t`, Jolt's memory map has the same byte in `t` as in `s` at every address outside
the doubleword that `i.storeBase s` names. -/
private theorem joltRun_mem (i : RiscvInstruction) (s t : SailJoltState)
    (hrun : RiscvInstruction.joltRun (honestInstr i s) s = .ok RETIRE_SUCCESS t) (a : Nat)
    (ha : ∀ base, i.storeBase s = some base → ¬ InDword base a) :
    t.sail.mem.get? a = s.sail.mem.get? a := by
  cases i
  case LB rd rs1 imm =>
    simp only [honestInstr, RiscvInstruction.joltRun, JoltISA.lbProgramAuto] at hrun
    split at hrun <;> exact get_of_keep (mkeeps_execProgram _
      (by simp [NoStoreProgram, NoStoreRow]) s t _ hrun) a
  case LBU rd rs1 imm =>
    simp only [honestInstr, RiscvInstruction.joltRun, JoltISA.lbuProgramAuto] at hrun
    split at hrun <;> exact get_of_keep (mkeeps_execProgram _
      (by simp [NoStoreProgram, NoStoreRow]) s t _ hrun) a
  case LH rd rs1 imm =>
    simp only [honestInstr, RiscvInstruction.joltRun, JoltISA.lhProgramAuto] at hrun
    split at hrun <;> exact get_of_keep (mkeeps_execProgram _
      (by simp [NoStoreProgram, NoStoreRow]) s t _ hrun) a
  case LHU rd rs1 imm =>
    simp only [honestInstr, RiscvInstruction.joltRun, JoltISA.lhuProgramAuto] at hrun
    split at hrun <;> exact get_of_keep (mkeeps_execProgram _
      (by simp [NoStoreProgram, NoStoreRow]) s t _ hrun) a
  case LW rd rs1 imm =>
    simp only [honestInstr, RiscvInstruction.joltRun, JoltISA.lwProgramAuto] at hrun
    split at hrun <;> exact get_of_keep (mkeeps_execProgram _
      (by simp [NoStoreProgram, NoStoreRow]) s t _ hrun) a
  case LWU rd rs1 imm =>
    simp only [honestInstr, RiscvInstruction.joltRun, JoltISA.lwuProgramAuto] at hrun
    split at hrun <;> exact get_of_keep (mkeeps_execProgram _
      (by simp [NoStoreProgram, NoStoreRow]) s t _ hrun) a
  case LD rd rs1 imm =>
    exact get_of_keep (mkeeps_execInstr (JoltISA.ldNativeInstr rd rs1 imm)
      (by simp [NoStoreRow, JoltISA.ldNativeInstr]) s t _ hrun) a
  case SD rs2 rs1 imm =>
    exact storeRow_mem AccessKind.dword rs1 (.xreg rs2) _ s t hrun a (ha _ rfl)
  case SB rs2 rs1 imm =>
    exact storePlan_mem AccessKind.byte rs1 (sign_extend (m := 64) imm) _
      (by
        simp only [JoltISA.sbProgramAuto]
        repeat' first
          | exact StorePlan.store _ _ (by simp [NoStoreProgram])
          | apply StorePlan.scratch _ _ (by simp [ScratchRow])) s t hrun a (ha _ rfl)
  case SH rs2 rs1 imm =>
    exact storePlan_mem AccessKind.halfword rs1 (sign_extend (m := 64) imm) _
      (by
        simp only [JoltISA.shProgramAuto]
        repeat' first
          | exact StorePlan.store _ _ (by simp [NoStoreProgram])
          | apply StorePlan.scratch _ _ (by simp [ScratchRow])) s t hrun a (ha _ rfl)
  case SW rs2 rs1 imm =>
    exact storePlan_mem AccessKind.word rs1 (sign_extend (m := 64) imm) _
      (by
        simp only [JoltISA.swProgramAuto]
        repeat' first
          | exact StorePlan.store _ _ (by simp [NoStoreProgram])
          | apply StorePlan.scratch _ _ (by simp [ScratchRow])) s t hrun a (ha _ rfl)
  case AMOSWAP_W rd rs1 rs2 aq rl =>
    refine storePlan_mem AccessKind.word rs1 0 _
      (by
        simp only [JoltISA.amoswapwProgramAuto]
        split <;> repeat' first
          | exact StorePlan.store _ _ (by simp [NoStoreProgram, NoStoreRow])
          | apply StorePlan.scratch _ _ (by simp [ScratchRow])) s t hrun a ?_
    rw [accessAddress_word_zero]
    exact ha _ rfl
  case AMOADD_W rd rs1 rs2 aq rl =>
    refine storePlan_mem AccessKind.word rs1 0 _
      (by
        simp only [JoltISA.amoaddwProgramAuto]
        split <;> repeat' first
          | exact StorePlan.store _ _ (by simp [NoStoreProgram, NoStoreRow])
          | apply StorePlan.scratch _ _ (by simp [ScratchRow])) s t hrun a ?_
    rw [accessAddress_word_zero]
    exact ha _ rfl
  case AMOXOR_W rd rs1 rs2 aq rl =>
    refine storePlan_mem AccessKind.word rs1 0 _
      (by
        simp only [JoltISA.amoxorwProgramAuto]
        split <;> repeat' first
          | exact StorePlan.store _ _ (by simp [NoStoreProgram, NoStoreRow])
          | apply StorePlan.scratch _ _ (by simp [ScratchRow])) s t hrun a ?_
    rw [accessAddress_word_zero]
    exact ha _ rfl
  case AMOAND_W rd rs1 rs2 aq rl =>
    refine storePlan_mem AccessKind.word rs1 0 _
      (by
        simp only [JoltISA.amoandwProgramAuto]
        split <;> repeat' first
          | exact StorePlan.store _ _ (by simp [NoStoreProgram, NoStoreRow])
          | apply StorePlan.scratch _ _ (by simp [ScratchRow])) s t hrun a ?_
    rw [accessAddress_word_zero]
    exact ha _ rfl
  case AMOOR_W rd rs1 rs2 aq rl =>
    refine storePlan_mem AccessKind.word rs1 0 _
      (by
        simp only [JoltISA.amoorwProgramAuto]
        split <;> repeat' first
          | exact StorePlan.store _ _ (by simp [NoStoreProgram, NoStoreRow])
          | apply StorePlan.scratch _ _ (by simp [ScratchRow])) s t hrun a ?_
    rw [accessAddress_word_zero]
    exact ha _ rfl
  case AMOMIN_W rd rs1 rs2 aq rl =>
    refine storePlan_mem AccessKind.word rs1 0 _
      (by
        simp only [JoltISA.amominwProgramAuto]
        split <;> repeat' first
          | exact StorePlan.store _ _ (by simp [NoStoreProgram, NoStoreRow])
          | apply StorePlan.scratch _ _ (by simp [ScratchRow])) s t hrun a ?_
    rw [accessAddress_word_zero]
    exact ha _ rfl
  case AMOMAX_W rd rs1 rs2 aq rl =>
    refine storePlan_mem AccessKind.word rs1 0 _
      (by
        simp only [JoltISA.amomaxwProgramAuto]
        split <;> repeat' first
          | exact StorePlan.store _ _ (by simp [NoStoreProgram, NoStoreRow])
          | apply StorePlan.scratch _ _ (by simp [ScratchRow])) s t hrun a ?_
    rw [accessAddress_word_zero]
    exact ha _ rfl
  case AMOMINU_W rd rs1 rs2 aq rl =>
    refine storePlan_mem AccessKind.word rs1 0 _
      (by
        simp only [JoltISA.amominuwProgramAuto]
        split <;> repeat' first
          | exact StorePlan.store _ _ (by simp [NoStoreProgram, NoStoreRow])
          | apply StorePlan.scratch _ _ (by simp [ScratchRow])) s t hrun a ?_
    rw [accessAddress_word_zero]
    exact ha _ rfl
  case AMOMAXU_W rd rs1 rs2 aq rl =>
    refine storePlan_mem AccessKind.word rs1 0 _
      (by
        simp only [JoltISA.amomaxuwProgramAuto]
        split <;> repeat' first
          | exact StorePlan.store _ _ (by simp [NoStoreProgram, NoStoreRow])
          | apply StorePlan.scratch _ _ (by simp [ScratchRow])) s t hrun a ?_
    rw [accessAddress_word_zero]
    exact ha _ rfl
  case AMOSWAP_D rd rs1 rs2 aq rl =>
    refine storePlan_mem AccessKind.dword rs1 0 _
      (by
        simp only [JoltISA.amoswapdProgramAuto]
        split <;> repeat' first
          | exact StorePlan.store _ _ (by simp [NoStoreProgram, NoStoreRow])
          | apply StorePlan.scratch _ _ (by simp [ScratchRow])) s t hrun a ?_
    rw [accessAddress_dword_zero]
    exact ha _ rfl
  case AMOADD_D rd rs1 rs2 aq rl =>
    refine storePlan_mem AccessKind.dword rs1 0 _
      (by
        simp only [JoltISA.amoadddProgramAuto]
        split <;> repeat' first
          | exact StorePlan.store _ _ (by simp [NoStoreProgram, NoStoreRow])
          | apply StorePlan.scratch _ _ (by simp [ScratchRow])) s t hrun a ?_
    rw [accessAddress_dword_zero]
    exact ha _ rfl
  case AMOXOR_D rd rs1 rs2 aq rl =>
    refine storePlan_mem AccessKind.dword rs1 0 _
      (by
        simp only [JoltISA.amoxordProgramAuto]
        split <;> repeat' first
          | exact StorePlan.store _ _ (by simp [NoStoreProgram, NoStoreRow])
          | apply StorePlan.scratch _ _ (by simp [ScratchRow])) s t hrun a ?_
    rw [accessAddress_dword_zero]
    exact ha _ rfl
  case AMOAND_D rd rs1 rs2 aq rl =>
    refine storePlan_mem AccessKind.dword rs1 0 _
      (by
        simp only [JoltISA.amoanddProgramAuto]
        split <;> repeat' first
          | exact StorePlan.store _ _ (by simp [NoStoreProgram, NoStoreRow])
          | apply StorePlan.scratch _ _ (by simp [ScratchRow])) s t hrun a ?_
    rw [accessAddress_dword_zero]
    exact ha _ rfl
  case AMOOR_D rd rs1 rs2 aq rl =>
    refine storePlan_mem AccessKind.dword rs1 0 _
      (by
        simp only [JoltISA.amoordProgramAuto]
        split <;> repeat' first
          | exact StorePlan.store _ _ (by simp [NoStoreProgram, NoStoreRow])
          | apply StorePlan.scratch _ _ (by simp [ScratchRow])) s t hrun a ?_
    rw [accessAddress_dword_zero]
    exact ha _ rfl
  case AMOMIN_D rd rs1 rs2 aq rl =>
    refine storePlan_mem AccessKind.dword rs1 0 _
      (by
        simp only [JoltISA.amomindProgramAuto]
        split <;> repeat' first
          | exact StorePlan.store _ _ (by simp [NoStoreProgram, NoStoreRow])
          | apply StorePlan.scratch _ _ (by simp [ScratchRow])) s t hrun a ?_
    rw [accessAddress_dword_zero]
    exact ha _ rfl
  case AMOMAX_D rd rs1 rs2 aq rl =>
    refine storePlan_mem AccessKind.dword rs1 0 _
      (by
        simp only [JoltISA.amomaxdProgramAuto]
        split <;> repeat' first
          | exact StorePlan.store _ _ (by simp [NoStoreProgram, NoStoreRow])
          | apply StorePlan.scratch _ _ (by simp [ScratchRow])) s t hrun a ?_
    rw [accessAddress_dword_zero]
    exact ha _ rfl
  case AMOMINU_D rd rs1 rs2 aq rl =>
    refine storePlan_mem AccessKind.dword rs1 0 _
      (by
        simp only [JoltISA.amominudProgramAuto]
        split <;> repeat' first
          | exact StorePlan.store _ _ (by simp [NoStoreProgram, NoStoreRow])
          | apply StorePlan.scratch _ _ (by simp [ScratchRow])) s t hrun a ?_
    rw [accessAddress_dword_zero]
    exact ha _ rfl
  case AMOMAXU_D rd rs1 rs2 aq rl =>
    refine storePlan_mem AccessKind.dword rs1 0 _
      (by
        simp only [JoltISA.amomaxudProgramAuto]
        split <;> repeat' first
          | exact StorePlan.store _ _ (by simp [NoStoreProgram, NoStoreRow])
          | apply StorePlan.scratch _ _ (by simp [ScratchRow])) s t hrun a ?_
    rw [accessAddress_dword_zero]
    exact ha _ rfl
  case LR_W rd rs1 aq rl => exact lr_mem false rd rs1 (regidx.Regidx 0) s t hrun a
  case LR_D rd rs1 aq rl => exact lr_mem true rd rs1 (regidx.Regidx 0) s t hrun a
  case SC_W rd rs1 rs2 aq rl => exact sc_mem false rd rs1 rs2 s t hrun a (ha _ rfl)
  case SC_D rd rs1 rs2 aq rl => exact sc_mem true rd rs1 rs2 s t hrun a (ha _ rfl)
  case ECALL =>
    exact get_of_keep (mkeeps_execProgram _ (by simp [JoltISA.ecallProgram, NoStoreProgram, NoStoreRow]) s t _ hrun) a
  case EBREAK =>
    exact get_of_keep (mkeeps_execProgram _ (by simp [JoltISA.ebreakProgram, NoStoreProgram, NoStoreRow]) s t _ hrun) a
  case MRET => exact get_of_keep (mkeeps_execProgram _ (by trivial) s t _ hrun) a
  case CSRRW => exact get_of_keep (mkeeps_execProgram _ (csrrw_noStore _ _ _) s t _ hrun) a
  case CSRRS => exact get_of_keep (mkeeps_execProgram _ (csrBit_noStore false _ _ _) s t _ hrun) a
  case CSRRC => exact get_of_keep (mkeeps_execProgram _ (csrBit_noStore true _ _ _) s t _ hrun) a
  case CSRRWI => exact get_of_keep (mkeeps_execProgram _ (csrrwi_noStore _ _ _) s t _ hrun) a
  case CSRRSI =>
    exact get_of_keep (mkeeps_execProgram _ (csrImmediateBit_noStore false _ _ _) s t _ hrun) a
  case CSRRCI =>
    exact get_of_keep (mkeeps_execProgram _ (csrImmediateBit_noStore true _ _ _) s t _ hrun) a
  all_goals
    simp only [honestInstr, RiscvInstruction.joltRun, JoltISA.execLUI] at hrun
    first
    | refine get_of_keep (mkeeps_execInstr _ ?_ s t _ hrun) a
      first
      | (unfold JoltISA.pureWritebackNativeInstr; split_ifs <;> trivial)
      | (unfold JoltISA.Instr.rewriteNative; trivial)
      | trivial
    | refine get_of_keep (mkeeps_execProgram _ ?_ s t _ hrun) a
      simp only [JoltISA.slliProgramAuto,
          JoltISA.srliProgramAuto,
          JoltISA.sraiProgramAuto,
          JoltISA.sllProgramAuto,
          JoltISA.srlProgramAuto,
          JoltISA.sraProgramAuto,
          JoltISA.slliwProgramAuto,
          JoltISA.srliwProgramAuto,
          JoltISA.sraiwProgramAuto,
          JoltISA.sllwProgramAuto,
          JoltISA.srlwProgramAuto,
          JoltISA.srawProgramAuto,
          JoltISA.mulhProgramAuto,
          JoltISA.mulhsuProgramAuto,
          JoltISA.divProgramAuto,
          JoltISA.divuProgramAuto,
          JoltISA.remProgramAuto,
          JoltISA.remuProgramAuto,
          JoltISA.divwProgramAuto,
          JoltISA.divuwProgramAuto,
          JoltISA.remwProgramAuto,
          JoltISA.remuwProgramAuto ]
      split <;> simp [NoStoreProgram, NoStoreRow]

private theorem patchAdvice_noStore (l : List JoltISA.Instr) (h : ∀ i ∈ l, NoStoreRow i)
    (vals : List (BitVec 64)) : ∀ i ∈ patchAdvice vals l, NoStoreRow i := by
  induction l generalizing vals with
  | nil => intro i hi; simp [patchAdvice] at hi
  | cons x rest ih =>
    have hrest := ih (fun i hi => h i (List.mem_cons_of_mem _ hi))
    cases x
    case VirtualAdvice dst placeholder imm =>
      intro i hi
      simp only [patchAdvice, List.mem_cons] at hi
      rcases hi with rfl | hi
      · trivial
      · exact hrest _ i hi
    all_goals
      intro i hi
      simp only [patchAdvice, List.mem_cons] at hi
      rcases hi with rfl | hi
      · exact h _ List.mem_cons_self
      · exact hrest _ i hi

private theorem seq_noStore (l : List JoltISA.Instr) (h : ∀ i ∈ l, NoStoreRow i) :
    NoStoreProgram (JoltISA.Program.seq l) := by
  induction l with
  | nil => trivial
  | cons x rest ih =>
    exact ⟨h x List.mem_cons_self, ih (fun i hi => h i (List.mem_cons_of_mem _ hi))⟩

private theorem rewriteNative_noStore (i : JoltISA.Instr) (h : NoStoreRow i) :
    NoStoreRow i.rewriteNative := by
  unfold JoltISA.Instr.rewriteNative
  repeat' (first | exact h | trivial | split)

private theorem jolt_rows_noStore (j : JoltCustomInstruction) (e : ExpandedSource)
    (he : (SourceInstruction.jolt j).expand = some e) :
    ∀ i ∈ expandedInstrs e, NoStoreRow i := by
  cases j <;> simp only [SourceInstruction.expand, Option.some.injEq] at he <;> subst he
  all_goals first
    | (simp only [JoltISA.advicelbProgramAuto, JoltISA.advicelhProgramAuto,
        JoltISA.advicelwProgramAuto, JoltISA.adviceldProgramAuto]
       split <;> simp [expandedInstrs, ExpandedSource.ofProgram, JoltISA.Program.instrs,
         NoStoreRow])
    | (simp only [expandedInstrs, ExpandedSource.ofNative, List.mem_singleton, forall_eq]
       exact rewriteNative_noStore _ (by trivial))

/-- **Frame lemma for one block.** A block that runs, and is not a registered inline, changes no
byte of Jolt's memory map outside the doubleword that its instruction stores into. Inline rows
store to several doublewords, which `storeBase` does not describe. -/
private theorem block_mem {program : Rv64ProgramImage SourceInstruction} {b : Block}
    (hruns : b.Runs program)
    (hinline : ∀ key rs1 rs2 rd, b.row.instruction ≠ .inline key rs1 rs2 rd) (a : Nat)
    (ha : ∀ base, b.row.instruction.storeBase b.start = some base → ¬ InDword base a) :
    b.post.sail.mem.get? a = b.pre.sail.mem.get? a := by
  obtain ⟨instrs, hblock, hrun⟩ := hruns.executes_plain hinline
  suffices h : b.post.sail.mem.get? a = b.start.sail.mem.get? a from h
  cases hi : b.row.instruction with
  | riscv i =>
    have hraw := blockInstrs_run i b.row.address b.row.is_compressed b.start instrs
      (by simpa only [← hi] using hblock)
    exact joltRun_mem i b.start b.post (hraw.symm.trans hrun) a
      (fun base hb => ha base (by rw [hi]; exact hb))
  | jolt j =>
    obtain ⟨e, he⟩ : ∃ e, b.row.instruction.expand = some e := by
      rw [hi]; cases j <;> exact ⟨_, rfl⟩
    have hnos : NoStoreProgram (JoltISA.Program.seq instrs) := by
      rw [blockInstrs_eq he hblock]
      exact seq_noStore _ (patchAdvice_noStore _ (jolt_rows_noStore j e (hi ▸ he)) _)
    exact get_of_keep (mkeeps_execProgram _ hnos _ _ _ hrun) a
  | inline key rs1 rs2 rd => exact absurd hi (hinline key rs1 rs2 rd)

/-- The bytes of the program's instruction rows: each row covers two bytes if compressed and four
otherwise.
For example, a 4-byte row at `0x80000000` covers `0x80000000` to `0x80000003`. -/
def IsCodeByte (program : Rv64ProgramImage SourceInstruction) (a : Nat) : Prop :=
  ∃ row ∈ program.instructions, ∃ k, k < (if row.is_compressed then 2 else 4) ∧
    a = row.address.toNat + k

/-- **The code lies in Jolt's memory unchanged.** Jolt's memory map `jt.sail.mem` holds the
image byte (`imageByte?`) at every byte of every instruction row, and the image ends at or below
the heap end, so that the code is inside the range Sail's memory holds (`Related.present`).
This is the Jolt-side version of `CodeIntact`: `CodeIntact.of_related` carries it to Sail.
For example, at the start of a run Jolt's loader has written the ELF's bytes at their addresses
(`JoltCodeIntact.initial`), and a store into an instruction row's bytes falsifies it. -/
def JoltCodeIntact (program : Rv64ProgramImage SourceInstruction) (jt : SailJoltState) : Prop :=
  program.program_end.toNat ≤ jt.jolt_device.memory_layout.heap_end.toNat ∧
  ∀ row ∈ program.instructions, ∀ k, k < (if row.is_compressed then 2 else 4) →
    ∀ b, imageByte? program (row.address.toNat + k) = some b →
      jt.sail.mem.get? (row.address.toNat + k) = some b

/-- **Documented deviation (docs/riscv-alignment.md §2): Sail's model fetches coherently from
memory, while Jolt fetches from the committed bytecode; without Zifencei the specification permits
either.**
The block's instruction stores into no byte of any instruction row of the program.
The footprint is the whole doubleword that Jolt's rows write, not only the bytes stored: Jolt's
narrow stores rewrite their aligned doubleword (`Mmu::store_doubleword`), and rewriting a byte
with its own value is harmless but needs this footprint in the frame lemma. It is
`SourceInstruction.storeBase`, which covers SB, SH, SW, SD, SC and every AMO and is empty for
every other instruction.
For example, `SB` at `0x80000003` violates it for a program with a row at `0x80000000`, and
`SB` at `0x80100003` does not. -/
def NoCodeStore (program : Rv64ProgramImage SourceInstruction) (b : Block) : Prop :=
  ∀ base, b.row.instruction.storeBase b.start = some base →
    ∀ k, k < 8 → ¬ IsCodeByte program (base.toNat + k)

/-- **Sail's memory holds the code too.** If Jolt's memory holds the image's code and Sail's state
is related to Jolt's, Sail's memory holds it: Sail has a byte at every address up to the end of the
heap, and where it does it is Jolt's. -/
theorem CodeIntact.of_related {program : Rv64ProgramImage SourceInstruction}
    {jt : SailJoltState} {s : SailState} (hrel : Related jt s) (h : JoltCodeIntact program jt) :
    CodeIntact program s := by
  intro row hrow k hk b hb
  obtain ⟨hR, hend⟩ := imageByte?_bounds program hb
  have hjt := h.2 row hrow k hk b hb
  have hlow := layout_memLow jt hrel.layout
  obtain ⟨b', hb'⟩ := hrel.present (row.address.toNat + k) (by omega)
    (by unfold memHigh; have := h.1; omega)
  have hram := hrel.ram _ hR
  simp only [JoltISA.Mmu.ram_byte, hb', hjt, Option.getD_some] at hram
  rw [hb', hram]

/-- **A block that stores outside the code keeps the code.** The block must not be a registered
inline, whose stores `NoCodeStore` does not describe. -/
theorem JoltCodeIntact.of_block {program : Rv64ProgramImage SourceInstruction} {b : Block}
    (hruns : b.Runs program)
    (hinline : ∀ key rs1 rs2 rd, b.row.instruction ≠ .inline key rs1 rs2 rd)
    (hno : NoCodeStore program b)
    (h : JoltCodeIntact program b.pre) : JoltCodeIntact program b.post := by
  refine ⟨by rw [hruns.layout_eq]; exact h.1, ?_⟩
  intro row hrow k hk b' hb'
  have hmem : b.post.sail.mem.get? (row.address.toNat + k) =
      b.pre.sail.mem.get? (row.address.toNat + k) := by
    refine block_mem hruns hinline _ fun base hbase hin => ?_
    exact hno base hbase ((row.address.toNat + k) - base.toNat) (by have := hin.2; omega)
      ⟨row, hrow, k, hk, by have := hin.1; omega⟩
  rw [hmem]
  exact h.2 row hrow k hk b' hb'

/-- The loader writes the image into Jolt's memory map: every image byte is present in the initial
memory map, and the image ends below the heap end. -/
private theorem initial_image_facts (joltInstance : JoltInstance SourceInstruction)
    (privateInputs : JoltPrivateInputs) (jt : SailJoltState)
    (built : joltInstance.initial_state privateInputs = some jt) :
    joltInstance.program.program_end.toNat ≤ jt.jolt_device.memory_layout.heap_end.toNat ∧
    ∀ (a : Nat) (b : BitVec 8), imageByte? joltInstance.program a = some b →
      jt.sail.mem.get? a = some b := by
  obtain ⟨device, tape, hlayout, hjt⟩ := initial_state_ram joltInstance privateInputs jt built
  unfold JoltInstance.memory_layout at hlayout
  obtain ⟨psize, hpsize, hheap⟩ := new_heap_end_ge _ _ hlayout
  have hpsize' : psize = joltInstance.program.program_size := by
    simpa using hpsize.symm
  subst hpsize'
  have hend_le := joltInstance.program.program_end.isLt
  have hge := joltInstance.program.program_end_ge_ram_start
  have hpsize_nat : joltInstance.program.program_size.toNat =
      joltInstance.program.program_end.toNat - JoltISA.RAM_START_ADDRESS := by
    have hR64 : (BitVec.ofNat 64 JoltISA.RAM_START_ADDRESS).toNat = JoltISA.RAM_START_ADDRESS := by
      simp [JoltISA.RAM_START_ADDRESS]
    unfold Rv64ProgramImage.program_size
    rw [BitVec.toNat_sub_of_le (by
      rw [BitVec.le_def, hR64]; exact joltInstance.program.program_end_ge_ram_start), hR64]
  have hdev : jt.jolt_device.memory_layout = device.memory_layout := by subst hjt; rfl
  refine ⟨?_, ?_⟩
  · rw [hdev]
    simp only [JoltISA.STACK_CANARY_SIZE] at hheap
    omega
  · intro a b h
    obtain ⟨hR, hend⟩ := imageByte?_bounds joltInstance.program h
    have hbacking := heap_end_le_ram_backing_end device
    unfold JoltISA.Mmu.ram_backing_end at hbacking
    have hsize := initialRam_size device.memory_layout joltInstance.program.memory_init
    have ho : a - JoltISA.RAM_START_ADDRESS < (initialRam device.memory_layout
        joltInstance.program.memory_init).size := by
      rw [hsize]
      simp only [JoltISA.STACK_CANARY_SIZE] at hheap
      omega
    have := init_state_mem_get? joltInstance.program.entry_address
      (initialRam device.memory_layout joltInstance.program.memory_init) device tape
      (a - JoltISA.RAM_START_ADDRESS)
    rw [← hjt, Nat.add_sub_cancel' hR] at this
    rw [this]
    have ho' : a - JoltISA.RAM_START_ADDRESS < (Array.replicate
        (8 * ((device.memory_layout.get_total_memory_size.toNat + 7) / 8)) (0 : BitVec 8)).size := by
      rw [Array.size_replicate]
      rw [hsize] at ho
      exact ho
    have key := initialRam_fold_getElem? joltInstance.program.memory_init
      (Array.replicate (8 * ((device.memory_layout.get_total_memory_size.toNat + 7) / 8)) 0)
      (a - JoltISA.RAM_START_ADDRESS) ho'
    unfold initialRam
    rw [Nat.add_sub_cancel' hR] at key
    have h' : lastByte joltInstance.program.memory_init a = some b := h
    refine key.trans ?_
    rw [h']
    rfl

/-- **The code starts intact.** In the initial state of every honest trace, Jolt's memory map
holds the image's bytes, and the image ends below the heap end. -/
theorem JoltCodeIntact.initial {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs) :
    JoltCodeIntact joltInstance.program trace.initialState := by
  obtain ⟨hend, hbytes⟩ := initial_image_facts joltInstance privateInputs _ trace.initialized
  exact ⟨hend, fun _ _ _ _ b hb => hbytes _ b hb⟩

end WholeRun
