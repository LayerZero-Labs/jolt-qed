import JoltBytecode.JoltISA.Semantics
import JoltBytecode.InstructionEquivalence.ProofSupport.Preservation
import Batteries.Data.Array.Lemmas

/-! A shared frame for Jolt instructions, parameterized by a state relation.
The state-changing primitives are Sail updates, virtual-register writes, device
stores, tape appends, and tape reads.
See `jolt/tracer/src/emulator/mmu.rs:644-667`,
`jolt/tracer/src/emulator/cpu.rs:24-60,1244-1333`, and
`jolt/tracer/src/instruction/virtual_advice_load.rs:20-27` at 8bbb2357. -/

set_option autoImplicit false

open Sail PreSail LeanRV64D.Functions JoltISA

namespace InstructionFrame

/-- Primitive preservation obligations for a reflexive, transitive state relation.
`sail` permits replacing the Sail component, `vreg` permits a virtual-register
write, `store` permits a successful device byte store, and `append` permits adding
bytes to the advice tape without moving its cursor.
For example, preserving device inputs and allowing only tape growth both fit.
Tape reads are supplied separately for the instruction being executed. -/
structure Rules (relation : SailJoltState → SailJoltState → Prop) : Prop where
  refl : ∀ state, relation state state
  trans : ∀ before middle after, relation before middle → relation middle after →
    relation before after
  sail : ∀ state after, relation state { state with sail := after }
  vreg : ∀ state vr value, relation state
    { state with vregs := fun r => if r = vr then value else state.vregs r }
  store : ∀ state device address value,
    JoltDevice.store? state.jolt_device address value = some device →
    relation state { state with jolt_device := device }
  append : ∀ state bytes, relation state
    { state with adviceTape :=
      { state.adviceTape with bytes := state.adviceTape.bytes ++ bytes } }

/-- Writing a destination preserves any relation that permits Sail replacement
and virtual-register writes.
For example, writing register x5 or virtual register 40 preserves device inputs
and leaves the advice tape unchanged. -/
theorem writeDst_rule (relation : SailJoltState → SailJoltState → Prop)
    (sail : ∀ state after, relation state { state with sail := after })
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
    exact StatePreservation.liftSail_rule (sailRelation := fun _ _ => True)
      (fun state after _ => sail state after) (fun _ _ _ _ => True.intro)

variable {relation : SailJoltState → SailJoltState → Prop}

private theorem lift_rule (rules : Rules relation) {α : Type} (step : SailM α) :
    StatePreservation.Preserves relation (liftSail step) :=
  StatePreservation.liftSail_rule (sailRelation := fun _ _ => True)
    (fun state after _ => rules.sail state after) (fun _ _ _ _ => True.intro)

private theorem readSrc_rule (rules : Rules relation) (src : Src) :
    StatePreservation.Preserves relation (readSrc src) := by
  cases src with
  | vreg vr =>
    intro s t v h
    simp only [readSrc, readVReg, bind, EStateM.bind, get, getThe,
      MonadStateOf.get, EStateM.get, pure, EStateM.pure] at h
    cases h
    exact rules.refl _
  | xreg rs => exact lift_rule rules _

/-- A successful raw byte store preserves the relation using the Sail rule for
RAM and the device-store rule for I/O.
For example, storing one byte to RAM changes only Sail memory. -/
theorem storeRaw_rule
    (sail : ∀ state after, relation state { state with sail := after })
    (store : ∀ state device address value,
      JoltDevice.store? state.jolt_device address value = some device →
      relation state { state with jolt_device := device })
    (s s' : SailJoltState)
    (address : Nat) (value : BitVec 8)
    (stored : Mmu.store_raw? s address value = some s') : relation s s' := by
  simp only [Mmu.store_raw?] at stored
  repeat' split at stored
  all_goals first
    | (cases stored; exact sail _ _)
    | cases stored
    | (cases deviceStore : s.jolt_device.store? address value with
        | none => simp [deviceStore] at stored
        | some device =>
          simp only [deviceStore, Option.map_some] at stored
          cases stored
          exact store _ _ _ _ deviceStore)

private theorem storeFold_rule (rules : Rules relation) (address : Nat)
    (value : BitVec 64) (s0 : SailJoltState) :
    ∀ (offsets : List Nat) (start : Option SailJoltState),
      (∀ s, start = some s → relation s0 s) →
      ∀ s', offsets.foldl (fun current k => current.bind fun s =>
        Mmu.store_raw? s (address + k) (value.extractLsb' (8 * k) 8)) start = some s' →
        relation s0 s' := by
  intro offsets
  induction offsets with
  | nil => intro start hstart s' hs'; exact hstart s' hs'
  | cons k offsets ih =>
    intro start hstart s' hs'
    refine ih _ ?_ s' hs'
    intro s hs
    cases hst : start with
    | none => rw [hst] at hs; cases hs
    | some e =>
      rw [hst] at hs
      exact rules.trans _ _ _ (hstart e hst)
        (storeRaw_rule rules.sail rules.store _ _ _ _ hs)

private theorem loadDoubleword_rule (rules : Rules relation) (address : BitVec 64) :
    StatePreservation.Preserves relation (Mmu.load_doubleword address) := by
  intro s t v h
  simp only [Mmu.load_doubleword] at h
  repeat' split at h
  all_goals first | (cases h; exact rules.refl _) | cases h

private theorem storeDoubleword_rule (rules : Rules relation) (address value : BitVec 64) :
    StatePreservation.Preserves relation (Mmu.store_doubleword address value) := by
  intro s t v h
  simp only [Mmu.store_doubleword] at h
  repeat' split at h
  all_goals first
    | (cases h; exact rules.sail _ _)
    | (rename_i heq
       cases h
       exact storeFold_rule rules _ value s _ (some s)
         (fun s1 hs1 => by cases hs1; exact rules.refl _) _ heq)
    | cases h

private theorem load_rule (rules : Rules relation) (address : BitVec 64) :
    StatePreservation.Preserves relation (Mmu.load address) := by
  intro s t v h
  simp only [Mmu.load] at h
  repeat' split at h
  all_goals first | (cases h; exact rules.refl _) | cases h

private theorem readHostBytes_rule (rules : Rules relation)
    (overflowChecks incrementAfterLast : Bool) {width : Nat}
    (pointer : BitVec width) (n : Nat) (bytes : Array (BitVec 8)) :
    StatePreservation.Preserves relation
      (readHostBytes Mmu.load overflowChecks incrementAfterLast pointer n bytes) := by
  induction n generalizing pointer bytes with
  | zero => exact StatePreservation.pure_rule rules.refl _
  | succ n ih =>
    dsimp only [readHostBytes]
    refine StatePreservation.bind_rule rules.trans (load_rule rules _) (fun result => ?_)
    cases result with
    | Err e => exact StatePreservation.pure_rule rules.refl _
    | Ok byte =>
      split_ifs
      · exact StatePreservation.bind_rule rules.trans
          (StatePreservation.throw_rule relation _) (fun _ => ih _ _)
      · exact StatePreservation.bind_rule rules.trans
          (StatePreservation.pure_rule rules.refl _) (fun _ => ih _ _)

private theorem execHostIO_rule (rules : Rules relation) :
    StatePreservation.Preserves relation execHostIO := by
  unfold execHostIO execHostIOWith
  refine StatePreservation.bind_rule rules.trans
    (StatePreservation.get_rule rules.refl) (fun config => ?_)
  dsimp only
  split
  · exact StatePreservation.pure_rule rules.refl _
  · refine StatePreservation.bind_rule rules.trans
      (StatePreservation.pure_rule rules.refl _) (fun _ => ?_)
    refine StatePreservation.bind_rule rules.trans (readSrc_rule rules _) (fun callId => ?_)
    preservation_auto [readHostBytes_rule rules _ _ _ _ _, readSrc_rule rules _,
      StatePreservation.pure_rule rules.refl _, StatePreservation.throw_rule relation _,
      StatePreservation.modify_rule _ (fun state => rules.append state _)]
      using (StatePreservation.bind_rule rules.trans)

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
  all_goals simp only [execInstr]
  all_goals preservation_auto [readSrc_rule rules _,
    writeDst_rule relation rules.sail rules.vreg _ _,
    StatePreservation.pure_rule rules.refl _, StatePreservation.throw_rule relation _,
    StatePreservation.get_rule rules.refl, lift_rule rules _, loadDoubleword_rule rules _,
    storeDoubleword_rule rules _ _, execHostIO_rule rules]
    using (StatePreservation.bind_rule rules.trans)

end InstructionFrame
