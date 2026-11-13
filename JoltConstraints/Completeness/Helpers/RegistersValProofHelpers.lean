import JoltConstraints.Completeness.Helpers.LookupWriteProofHelpers
import JoltBytecode.InstructionEquivalence.ProofSupport.Projection
import JoltConstraints.Completeness.Helpers.HostIOFrame
import JoltConstraints.Completeness.Helpers.FloorMemory

open LeanRV64D

/-!
Instruction-level register frames for the honest register-history witness.
Successful final rows preserve every register other than their destination.
The proofs use the trace's existing execution and memory assumptions.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail LeanRV64D LeanRV64D.Functions

theorem register42_prepareSource_preserves_sourceValue
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (trace : HonestTrace joltInstance privateInputs)
    (i : Fin trace.bytecode.size) (s : SailJoltState)
    (src : JoltISA.Src) :
    JoltISA.sourceValue src (prepareSource trace.bytecode i s) =
      JoltISA.sourceValue src s := by
  cases src with
  | vreg vr => rfl
  | xreg rd =>
      reg_cases rd <;>
        simp only [JoltISA.sourceValue, prepareSource,
          Std.ExtDHashMap.get?_insert, beq_iff_eq, reduceCtorEq,
          ↓reduceDIte]

theorem register42_xreg_write_preserves_other
    (rd rs : regidx) (value : BitVec 64) (s : SailJoltState)
    (hne : rd ≠ rs)
    (hready : Assumptions.XRegReadable rs s.sail) :
    JoltISA.sourceValue (.xreg rs)
        { s with sail := stateAfterWrite s.sail rd value } =
      JoltISA.sourceValue (.xreg rs) s := by
  obtain ⟨readValue, hread⟩ := hready.exists_value
  have hreadJ : JoltISA.readSrc (.xreg rs) s = .ok readValue s := by
    simp [JoltISA.readSrc, liftSail, hread]
  have hpre := (lookup_readSrc_value (.xreg rs) s s readValue hreadJ).2
  have hread' := rX_bits_stateAfterWrite_of_ne rd rs value readValue s.sail hne hread
  have hreadJ' :
      JoltISA.readSrc (.xreg rs)
        { s with sail := stateAfterWrite s.sail rd value } =
        .ok readValue { s with sail := stateAfterWrite s.sail rd value } := by
    simp [JoltISA.readSrc, liftSail, hread']
  have hpost := (lookup_readSrc_value (.xreg rs) _ _ readValue hreadJ').2
  exact hpost.symm.trans hpre

def register42_dstAsSrc : JoltISA.Dst → JoltISA.Src
  | .xreg rd => .xreg rd
  | .vreg vr => .vreg vr

theorem register42_writeDst_preserves_other
    (dst : JoltISA.Dst) (src : JoltISA.Src) (value : BitVec 64)
    (s t : SailJoltState)
    (hne : src ≠ register42_dstAsSrc dst)
    (hready : ∀ rd, Assumptions.XRegReadable rd s.sail)
    (hwrite : JoltISA.writeDst dst value s = .ok () t) :
    JoltISA.sourceValue src t = JoltISA.sourceValue src s := by
  cases dst with
  | xreg rd =>
      simp only [JoltISA.writeDst, liftSail,
        wX_bits_stateAfterWrite] at hwrite
      cases hwrite
      cases src with
      | vreg vr => rfl
      | xreg rs =>
          have hne' : rd ≠ rs := by
            intro heq
            subst heq
            exact hne rfl
          exact register42_xreg_write_preserves_other rd rs value s hne' (hready rs)
  | vreg vr =>
      by_cases hvalid : vr.toNat < 32
      · simp only [JoltISA.writeDst, writeVReg, hvalid, ↓reduceIte,
          throw, throwThe, MonadExceptOf.throw, EStateM.throw] at hwrite
        cases hwrite
      · simp only [JoltISA.writeDst, writeVReg, hvalid,
          ↓reduceIte, modify, modifyGet, MonadStateOf.modifyGet,
          EStateM.modifyGet] at hwrite
        cases hwrite
        cases src with
        | xreg rd => rfl
        | vreg vs =>
            have hne' : vs ≠ vr := by
              intro heq
              subst heq
              exact hne rfl
            simp [JoltISA.sourceValue, hne']

theorem register42_write_retire_preserves_other
    (dst : JoltISA.Dst) (src : JoltISA.Src) (value : BitVec 64)
    (s t : SailJoltState)
    (hne : src ≠ register42_dstAsSrc dst)
    (hready : ∀ rd, Assumptions.XRegReadable rd s.sail)
    (hexec : (do JoltISA.writeDst dst value; pure RETIRE_SUCCESS) s =
      .ok (.Retire_Success ()) t) :
    JoltISA.sourceValue src t = JoltISA.sourceValue src s := by
  cases hr : JoltISA.writeDst dst value s with
  | error e s' => simp only [bind, EStateM.bind, hr] at hexec; cases hexec
  | ok u s' =>
      cases u
      simp only [bind, EStateM.bind, hr, pure, EStateM.pure,
        EStateM.Result.ok.injEq] at hexec
      rw [← hexec.2]
      exact register42_writeDst_preserves_other dst src value s s' hne hready hr

theorem register42_unary_write_preserves_other
    (dst : JoltISA.Dst) (operand src : JoltISA.Src)
    (calculate : BitVec 64 → BitVec 64) (s t : SailJoltState)
    (hne : src ≠ register42_dstAsSrc dst)
    (hready : ∀ rd, Assumptions.XRegReadable rd s.sail)
    (hexec : (do
      let x ← JoltISA.readSrc operand
      JoltISA.writeDst dst (calculate x)
      pure RETIRE_SUCCESS) s = .ok (.Retire_Success ()) t) :
    JoltISA.sourceValue src t = JoltISA.sourceValue src s := by
  have h := lookup_read_bind operand _ s t _ hexec
  exact register42_write_retire_preserves_other dst src _ s t hne hready h

theorem register42_binary_write_preserves_other
    (dst : JoltISA.Dst) (lhs rhs src : JoltISA.Src)
    (calculate : BitVec 64 → BitVec 64 → BitVec 64)
    (s t : SailJoltState)
    (hne : src ≠ register42_dstAsSrc dst)
    (hready : ∀ rd, Assumptions.XRegReadable rd s.sail)
    (hexec : (do
      let x ← JoltISA.readSrc lhs
      let y ← JoltISA.readSrc rhs
      JoltISA.writeDst dst (calculate x y)
      pure RETIRE_SUCCESS) s = .ok (.Retire_Success ()) t) :
    JoltISA.sourceValue src t = JoltISA.sourceValue src s := by
  have h := lookup_read_bind lhs _ s t _ hexec
  have h := lookup_read_bind rhs _ s t _ h
  exact register42_write_retire_preserves_other dst src _ s t hne hready h

theorem register42_nextPC_preserves_sourceValue
    (src : JoltISA.Src) (value : BitVec 64) (s : SailJoltState) :
    JoltISA.sourceValue src
      { s with sail := { s.sail with regs := s.sail.regs.insert Register.nextPC value } } =
      JoltISA.sourceValue src s := by
  cases src with
  | vreg vr => rfl
  | xreg rd =>
      reg_cases rd <;>
        simp only [JoltISA.sourceValue, Std.ExtDHashMap.get?_insert,
          beq_iff_eq, reduceCtorEq, ↓reduceDIte]

theorem register42_lift_readReg_pure
    (reg : Register) (s t : SailJoltState)
    (value : RegisterType reg)
    (hread : liftSail (LeanRV64D.readReg reg) s = .ok value t) : t = s := by
  cases hr : LeanRV64D.readReg reg s.sail with
  | error e s' => simp only [liftSail, hr] at hread; cases hread
  | ok v s' =>
      have hs := readReg_pure reg s.sail v s' hr
      simp only [liftSail, hr] at hread
      cases hread
      cases hs
      rfl

theorem register42_nextPC_write_preserves_sourceValue
    (src : JoltISA.Src) (value : BitVec 64)
    (s t : SailJoltState)
    (hwrite : liftSail (LeanRV64D.writeReg Register.nextPC value) s = .ok () t) :
    JoltISA.sourceValue src t = JoltISA.sourceValue src s := by
  simp only [liftSail, LeanRV64D.writeReg, Sail.ConcurrencyInterfaceV1.PreSail.writeReg,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet] at hwrite
  cases hwrite
  exact register42_nextPC_preserves_sourceValue src value s

theorem register42_lift_readReg_bind {α : Type}
    (reg : Register) (f : RegisterType reg → JoltMonad α)
    (s t : SailJoltState) (result : α)
    (hexec : (liftSail (LeanRV64D.readReg reg) >>= f) s = .ok result t) :
    ∃ value, f value s = .ok result t := by
  cases hr : liftSail (LeanRV64D.readReg reg) s with
  | error e s' => simp only [bind, EStateM.bind, hr] at hexec; cases hexec
  | ok v s' =>
      have hs := register42_lift_readReg_pure reg s s' v hr
      subst s'
      simp only [bind, EStateM.bind, hr] at hexec
      exact ⟨v, hexec⟩

theorem register42_write_then_nextPC_preserves_other
    (dst : JoltISA.Dst) (src : JoltISA.Src)
    (written pc : BitVec 64) (s t : SailJoltState)
    (hne : src ≠ register42_dstAsSrc dst)
    (hready : ∀ rd, Assumptions.XRegReadable rd s.sail)
    (hexec : (do
      JoltISA.writeDst dst written
      liftSail (LeanRV64D.writeReg Register.nextPC pc)
      pure RETIRE_SUCCESS) s = .ok (.Retire_Success ()) t) :
    JoltISA.sourceValue src t = JoltISA.sourceValue src s := by
  cases hw : JoltISA.writeDst dst written s with
  | error e s' => simp only [bind, EStateM.bind, hw] at hexec; cases hexec
  | ok u mid =>
      cases u
      simp only [bind, EStateM.bind, hw] at hexec
      cases hp : liftSail (LeanRV64D.writeReg Register.nextPC pc) mid with
      | error e s' => simp only [hp] at hexec; cases hexec
      | ok u post =>
          cases u
          simp only [hp, pure, EStateM.pure,
            EStateM.Result.ok.injEq] at hexec
          rw [← hexec.2]
          exact (register42_nextPC_write_preserves_sourceValue src pc mid post hp).trans
            (register42_writeDst_preserves_other dst src written s mid hne hready hw)

theorem register42_jal_preserves_other
    (dst : JoltISA.Dst) (src : JoltISA.Src) (imm : BitVec 64)
    (s t : SailJoltState)
    (hne : src ≠ register42_dstAsSrc dst)
    (hready : ∀ rd, Assumptions.XRegReadable rd s.sail)
    (hexec : JoltISA.execInstr (.JAL dst imm) s =
      .ok (.Retire_Success ()) t) :
    JoltISA.sourceValue src t = JoltISA.sourceValue src s := by
  simp only [JoltISA.execInstr] at hexec
  obtain ⟨rustPC, h⟩ := register42_lift_readReg_bind Register.nextPC _ s t _ hexec
  obtain ⟨address, h⟩ := register42_lift_readReg_bind Register.PC _ s t _ h
  exact register42_write_then_nextPC_preserves_other dst src rustPC
    (address + imm) s t hne hready h

theorem register42_xreg_write_after_nextPC_preserves_other
    (rd : regidx) (src : JoltISA.Src)
    (written target : BitVec 64) (s : SailJoltState)
    (hne : src ≠ .xreg rd)
    (hready : ∀ rs, Assumptions.XRegReadable rs s.sail) :
    JoltISA.sourceValue src
      { s with sail := (stateAfterWrite
        { s.sail with regs := s.sail.regs.insert Register.nextPC target }
        rd written) } = JoltISA.sourceValue src s := by
  have hcomm :
      { s with sail := (stateAfterWrite
        { s.sail with regs := s.sail.regs.insert Register.nextPC target }
        rd written) } =
      { s with sail := { (stateAfterWrite s.sail rd written) with
        regs := (stateAfterWrite s.sail rd written).regs.insert
          Register.nextPC target } } := by
    exact congrArg (fun sail => { s with sail := sail })
      (by simpa only [System.setNextPCState] using
        (Projection.stateAfterWrite_setNextPCState s.sail rd written target))
  rw [hcomm]
  exact (register42_nextPC_preserves_sourceValue src target
    { s with sail := stateAfterWrite s.sail rd written }).trans
    (by cases src with
      | vreg vr => rfl
      | xreg rs =>
          have hne' : rd ≠ rs := by
            intro heq
            subst heq
            exact hne rfl
          exact register42_xreg_write_preserves_other rd rs written s hne'
            (hready rs))

theorem register42_writeDst_after_nextPC_preserves_other
    (dst : JoltISA.Dst) (src : JoltISA.Src)
    (written target : BitVec 64) (s t : SailJoltState)
    (hne : src ≠ register42_dstAsSrc dst)
    (hready : ∀ rs, Assumptions.XRegReadable rs s.sail)
    (hwrite : JoltISA.writeDst dst written
      { s with sail := { s.sail with
        regs := s.sail.regs.insert Register.nextPC target } } = .ok () t) :
    JoltISA.sourceValue src t = JoltISA.sourceValue src s := by
  cases dst with
  | xreg rd =>
      simp only [JoltISA.writeDst, liftSail,
        wX_bits_stateAfterWrite] at hwrite
      cases hwrite
      exact register42_xreg_write_after_nextPC_preserves_other rd src written
        target s hne hready
  | vreg vr =>
      by_cases hvalid : vr.toNat < 32
      · simp only [JoltISA.writeDst, writeVReg, hvalid, ↓reduceIte,
          throw, throwThe, MonadExceptOf.throw, EStateM.throw] at hwrite
        cases hwrite
      · simp only [JoltISA.writeDst, writeVReg, hvalid,
          ↓reduceIte, modify, modifyGet, MonadStateOf.modifyGet,
          EStateM.modifyGet] at hwrite
        cases hwrite
        cases src with
        | xreg rd =>
            exact register42_nextPC_preserves_sourceValue (.xreg rd) target s
        | vreg vs =>
            have hne' : vs ≠ vr := by
              intro heq
              subst heq
              exact hne rfl
            simp [JoltISA.sourceValue, hne']

theorem register42_nextPC_then_writeDst_preserves_other
    (dst : JoltISA.Dst) (src : JoltISA.Src)
    (written target : BitVec 64) (s t : SailJoltState)
    (hne : src ≠ register42_dstAsSrc dst)
    (hready : ∀ rs, Assumptions.XRegReadable rs s.sail)
    (hexec : (do
      liftSail (LeanRV64D.writeReg Register.nextPC target)
      JoltISA.writeDst dst written
      pure RETIRE_SUCCESS) s = .ok (.Retire_Success ()) t) :
    JoltISA.sourceValue src t = JoltISA.sourceValue src s := by
  have hpc : liftSail (LeanRV64D.writeReg Register.nextPC target) s =
      .ok () { s with sail := { s.sail with
        regs := s.sail.regs.insert Register.nextPC target } } := rfl
  simp only [bind, EStateM.bind, hpc] at hexec
  cases hw : JoltISA.writeDst dst written
      { s with sail := { s.sail with
        regs := s.sail.regs.insert Register.nextPC target } } with
  | error e s' => simp only [hw] at hexec; cases hexec
  | ok u post =>
      cases u
      simp only [hw, pure, EStateM.pure,
        EStateM.Result.ok.injEq] at hexec
      rw [← hexec.2]
      exact register42_writeDst_after_nextPC_preserves_other dst src written
        target s post hne hready hw

theorem register42_jalr_preserves_other
    (dst : JoltISA.Dst) (base src : JoltISA.Src) (imm : BitVec 64)
    (s t : SailJoltState)
    (hne : src ≠ register42_dstAsSrc dst)
    (hready : ∀ rd, Assumptions.XRegReadable rd s.sail)
    (hexec : JoltISA.execInstr (.JALR dst base imm) s =
      .ok (.Retire_Success ()) t) :
    JoltISA.sourceValue src t = JoltISA.sourceValue src s := by
  simp only [JoltISA.execInstr] at hexec
  obtain ⟨rustPC, h⟩ := register42_lift_readReg_bind Register.nextPC _ s t _ hexec
  have h := lookup_read_bind base _ s t _ h
  exact register42_nextPC_then_writeDst_preserves_other dst src rustPC
    (jolt_jalr_target64 (JoltISA.sourceValue base s) imm) s t hne hready h

namespace SailReadOnly

def Preserves {α : Type} (m : SailM α) : Prop :=
  ∀ (s t : SailState) (v : α), m s = .ok v t → t = s

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

theorem andM_rule {first second : SailM Bool}
    (keepsFirst : Preserves first) (keepsSecond : Preserves second) :
    Preserves (first <&&> second) :=
  bind_rule keepsFirst fun value => by
    cases value
    · exact pure_rule false
    · exact keepsSecond

end SailReadOnly

namespace Register42ReadOnly

def Preserves {α : Type} (m : JoltMonad α) : Prop :=
  ∀ (s t : SailJoltState) (result : α), m s = .ok result t → t = s

theorem pure_rule {α : Type} (v : α) : Preserves (pure v) := by
  intro s t result h
  cases h
  rfl

theorem bind_rule {α β : Type} {m : JoltMonad α} {f : α → JoltMonad β}
    (hm : Preserves m) (hf : ∀ x, Preserves (f x)) :
    Preserves (m >>= f) := by
  intro s t result h
  cases hr : m s with
  | error e s' => simp only [bind, EStateM.bind, hr] at h; cases h
  | ok v s' =>
      simp only [bind, EStateM.bind, hr] at h
      exact (hf v s' t result h).trans (hm s s' v hr)

theorem readSrc_rule (src : JoltISA.Src) : Preserves (JoltISA.readSrc src) := by
  intro s t value h
  exact (lookup_readSrc_value src s t value h).1

theorem liftReadReg_rule (reg : Register) :
    Preserves (liftSail (LeanRV64D.readReg reg)) := by
  intro s t value h
  exact register42_lift_readReg_pure reg s t value h

theorem throw_rule {α : Type} (e : Error exception) :
    Preserves (throw e : JoltMonad α) := by
  intro s t value h
  cases h

end Register42ReadOnly

macro "register42_readOnly_auto" : tactic => `(tactic|
  repeat' first
  | exact Register42ReadOnly.readSrc_rule _
  | exact Register42ReadOnly.liftReadReg_rule _
  | exact Register42ReadOnly.pure_rule _
  | exact Register42ReadOnly.throw_rule _
  | split
  | refine Register42ReadOnly.bind_rule ?_ (fun x => ?_))

theorem register42_currentlyEnabled_readOnly :
    SailReadOnly.Preserves (currentlyEnabled extension.Ext_Zca) := by
  simp only [currentlyEnabled]
  open SailReadOnly in
  exact andM_rule (pure_rule _)
    (bind_rule (andM_rule (pure_rule _)
      (bind_rule (read_rule Register.misa) fun _ => pure_rule _)) fun _ => pure_rule _)

theorem register42_jump_to_shape
    (target : BitVec 64) (s t : SailState)
    (result : ExecutionResult)
    (hjump : jump_to target s = .ok result t) :
    t = s ∨ t = System.setNextPCState s target := by
  unfold jump_to ext_control_check_pc at hjump
  simp only [SailME.run, Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.run, ExceptT.run, ExceptT.mk,
    ExceptT.bind, ExceptT.bindCont, ExceptT.pure, ExceptT.lift,
    liftM, monadLift, MonadLift.monadLift, Functor.map, EStateM.map,
    bind, EStateM.bind, pure, EStateM.pure,
    LeanRV64D.sail_assert, Sail.ConcurrencyInterfaceV1.PreSail.sail_assert] at hjump
  by_cases hbit : (BitVec.access target 0 == 0#1) = true
  · simp only [hbit, ↓reduceIte, pure, EStateM.pure, EStateM.bind,
      ExceptT.bindCont, EStateM.map] at hjump
    -- `<&&>` short-circuits: `Ext_Zca` is read only when bit 1 is set.
    cases bit1 : bit_to_bool (BitVec.access target 1)
    · simp only [andM, toBool, bit1, ExceptT.bindCont, EStateM.map, Bool.false_eq_true,
        ↓reduceIte, set_next_pc, LeanRV64D.writeReg, bind, EStateM.bind,
        pure, EStateM.pure] at hjump
      cases hjump
      first | exact Or.inl rfl | exact Or.inr rfl
    · simp only [andM, toBool, bit1, bind, EStateM.bind, pure, EStateM.pure,
        ExceptT.bind, ExceptT.bindCont, ExceptT.pure, ExceptT.mk, EStateM.map] at hjump
      cases hz : currentlyEnabled extension.Ext_Zca s with
      | error e s' => simp only [hz] at hjump; cases hjump
      | ok zca s' =>
        have hs' := register42_currentlyEnabled_readOnly s s' zca hz
        subst s'
        cases zca <;>
          simp only [hz, sail_not_true, sail_not_false, ExceptT.bindCont, EStateM.map,
            Bool.false_eq_true, ↓reduceIte, set_next_pc, LeanRV64D.writeReg, bind,
            EStateM.bind, pure, EStateM.pure] at hjump <;>
          cases hjump
        all_goals first | exact Or.inl rfl | exact Or.inr rfl
  · simp only [hbit, ↓reduceIte, throw, throwThe] at hjump
    cases hjump

theorem register42_jump_to_preserves_sourceValue
    (src : JoltISA.Src) (target : BitVec 64)
    (s t : SailJoltState) (result : ExecutionResult)
    (hjump : liftSail (jump_to target) s = .ok result t) :
    JoltISA.sourceValue src t = JoltISA.sourceValue src s := by
  cases hr : jump_to target s.sail with
  | error e sail => simp only [liftSail, hr] at hjump; cases hjump
  | ok value sail =>
      have hshape := register42_jump_to_shape target s.sail sail value hr
      simp only [liftSail, hr] at hjump
      cases hjump
      rcases hshape with hs | hs
      · subst sail
        rfl
      · subst sail
        simpa only [System.setNextPCState] using
          register42_nextPC_preserves_sourceValue src target s

theorem register42_branch_preserves_sourceValue
    (lhs rhs src : JoltISA.Src)
    (decision : BitVec 64 → BitVec 64 → Bool) (offset : BitVec 64)
    (s t : SailJoltState)
    (hexec : (do
      let x ← JoltISA.readSrc lhs
      let y ← JoltISA.readSrc rhs
      if decision x y then
        let pc ← liftSail (LeanRV64D.readReg Register.PC)
        liftSail (jump_to (pc + offset))
      else pure RETIRE_SUCCESS) s = .ok (.Retire_Success ()) t) :
    JoltISA.sourceValue src t = JoltISA.sourceValue src s := by
  have h := lookup_read_bind lhs _ s t _ hexec
  have h := lookup_read_bind rhs _ s t _ h
  split_ifs at h with hbranch
  · obtain ⟨pc, h⟩ := register42_lift_readReg_bind Register.PC _ s t _ h
    exact register42_jump_to_preserves_sourceValue src (pc + offset) s t _ h
  · cases h
    rfl

/-- Loading a doubleword and writing its destination preserves any other source
register; for example, loading x1 leaves x2 unchanged.
Jolt's tracer: `tracer/src/instruction/floor_access.rs` (`load`) at `c6703570`. -/
theorem register42_load_word_preserves_other
    (address : BitVec 64) (dst : JoltISA.Dst) (src : JoltISA.Src)
    (s t : SailJoltState) (hne : src ≠ register42_dstAsSrc dst)
    (hready : ∀ rd, Assumptions.XRegReadable rd s.sail)
    (runs : (do
      match ← JoltISA.Mmu.load_doubleword address with
      | .Ok value => JoltISA.writeDst dst value; pure RETIRE_SUCCESS
      | .Err error => pure error) s = .ok (.Retire_Success ()) t) :
    JoltISA.sourceValue src t = JoltISA.sourceValue src s := by
  cases hr : JoltISA.Mmu.load_doubleword address s with
  | error e state => simp only [bind, EStateM.bind, hr] at runs; cases runs
  | ok value state =>
      have unchanged := JoltISA.Mmu.load_doubleword_state hr
      subst state
      simp only [bind, EStateM.bind, hr] at runs
      cases value with
      | Ok word => exact register42_write_retire_preserves_other dst src word s t hne hready runs
      | Err error => cases runs; rfl

/-- LD preserves sources other than its destination; for example, LD into x1
leaves x2 unchanged when both registers are readable.
Jolt's tracer: `tracer/src/instruction/ld.rs` (`LD::exec`) at `c6703570`. -/
theorem register42_load_preserves_other
    (fault : JoltISA.LoadFaultClass) (dst : JoltISA.Dst)
    (base src : JoltISA.Src) (imm : BitVec 64)
    (s t : SailJoltState)
    (hne : src ≠ register42_dstAsSrc dst)
    (hready : ∀ rd, Assumptions.XRegReadable rd s.sail)
    (hexec : JoltISA.execInstr (.LD fault dst base imm) s =
      .ok (.Retire_Success ()) t) :
    JoltISA.sourceValue src t = JoltISA.sourceValue src s := by
  have h := lookup_read_bind base _ s t _ hexec
  by_cases halign : (JoltISA.sourceValue base s + imm) &&& 7 = 0
  · simp only [halign, ↓reduceIte] at h
    exact register42_load_word_preserves_other _ dst src s t hne hready h
  · simp only [halign, ↓reduceIte, pure, EStateM.pure] at h
    cases h

/-- A doubleword store preserves every register; for example, storing x1
changes memory but leaves the captured source x1 unchanged.
Jolt's tracer: `tracer/src/instruction/floor_access.rs` (`store`) at `c6703570`. -/
theorem register42_store_word_preserves_sourceValue
    (address value : BitVec 64) (src : JoltISA.Src) (s t : SailJoltState)
    (runs : (do
      match ← JoltISA.Mmu.store_doubleword address value with
      | .Ok _ => pure RETIRE_SUCCESS
      | .Err error => pure error) s = .ok (.Retire_Success ()) t) :
    JoltISA.sourceValue src t = JoltISA.sourceValue src s := by
  cases hr : JoltISA.Mmu.store_doubleword address value s with
  | error e state => simp only [bind, EStateM.bind, hr] at runs; cases runs
  | ok result state =>
      have frame : JoltISA.sourceValue src state = JoltISA.sourceValue src s := by
        obtain ⟨hregs, hvregs⟩ := JoltISA.Mmu.store_doubleword_regs hr
        simp only [JoltISA.sourceValue, hregs, hvregs]
      simp only [bind, EStateM.bind, hr] at runs
      cases result <;> cases runs <;> exact frame

/-- SD preserves every source register, such as its base x2 when storing x1.
Jolt's tracer: `tracer/src/instruction/sd.rs` (`SD::exec`) at `c6703570`. -/
theorem register42_store_preserves_sourceValue
    (base stored src : JoltISA.Src) (imm : BitVec 64)
    (s t : SailJoltState)
    (hexec : JoltISA.execInstr (.SD base stored imm) s =
      .ok (.Retire_Success ()) t) :
    JoltISA.sourceValue src t = JoltISA.sourceValue src s := by
  have h := lookup_read_bind base _ s t _ hexec
  have h := lookup_read_bind stored _ s t _ h
  by_cases halign : (JoltISA.sourceValue base s + imm) &&& 7 = 0
  · simp only [halign, ↓reduceIte] at h
    exact register42_store_word_preserves_sourceValue _ _ src s t h
  · simp only [halign, ↓reduceIte, pure, EStateM.pure] at h
    cases h

namespace Register42VRegs

def Preserves {α : Type} (m : JoltMonad α) : Prop :=
  ∀ (s t : SailJoltState) (v : α), m s = .ok v t → t.vregs = s.vregs

theorem pure_rule {α : Type} (v : α) : Preserves (pure v) := by
  intro s t result h
  cases h
  rfl

theorem bind_rule {α β : Type} {m : JoltMonad α} {f : α → JoltMonad β}
    (hm : Preserves m) (hf : ∀ x, Preserves (f x)) :
    Preserves (m >>= f) := by
  intro s t v h
  cases hr : m s with
  | error e state => simp only [bind, EStateM.bind, hr] at h; cases h
  | ok x state =>
      simp only [bind, EStateM.bind, hr] at h
      exact (hf x state t v h).trans (hm s state x hr)

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

theorem modifyAdvice_rule (f : SailJoltState → SailJoltState)
    (hf : ∀ s, (f s).vregs = s.vregs) :
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

end Register42VRegs

/-- A retired instruction preserves every readable source except its destination;
for example, a floor LoadH into x1 preserves x2, and StoreH preserves both.
Jolt's tracer: `tracer/src/instruction/floor_access.rs` (`load`, `store`)
at `c6703570`. -/
theorem register42_instruction_preserves_other
    (instr : JoltISA.Instr) (src : JoltISA.Src)
    (s t : SailJoltState)
    (hne : ∀ dst, instr.destination? = some dst →
      src ≠ register42_dstAsSrc dst)
    (hready : ∀ rd, Assumptions.XRegReadable rd s.sail)
    (hexec : JoltISA.execInstr instr s =
      .ok (.Retire_Success ()) t) :
    JoltISA.sourceValue src t = JoltISA.sourceValue src s := by
  cases instr
  case LD fault dst base imm =>
    exact register42_load_preserves_other fault dst base src imm s t
      (hne dst rfl) hready hexec
  case SD base stored imm =>
    exact register42_store_preserves_sourceValue base stored src imm s t hexec
  case VirtualLoadB faultClass dst base imm fault =>
    exact register42_load_word_preserves_other _ dst src s t (hne dst rfl) hready
      (JoltConstraints.floor_load_access _ faultClass dst base imm 0 fault
        (Or.inl ⟨rfl, rfl⟩) () s t hexec).2
  case VirtualStoreB base value imm fault =>
    exact register42_store_word_preserves_sourceValue _ _ src s t
      (JoltConstraints.floor_store_access _ base value imm 0 fault
        (Or.inl ⟨rfl, rfl⟩) () s t hexec).2
  case VirtualLoadH faultClass dst base imm fault =>
    exact register42_load_word_preserves_other _ dst src s t (hne dst rfl) hready
      (JoltConstraints.floor_load_access _ faultClass dst base imm 1 fault
        (Or.inr (Or.inl ⟨rfl, rfl⟩)) () s t hexec).2
  case VirtualStoreH base value imm fault =>
    exact register42_store_word_preserves_sourceValue _ _ src s t
      (JoltConstraints.floor_store_access _ base value imm 1 fault
        (Or.inr (Or.inl ⟨rfl, rfl⟩)) () s t hexec).2
  case VirtualLoadW faultClass dst base imm fault =>
    exact register42_load_word_preserves_other _ dst src s t (hne dst rfl) hready
      (JoltConstraints.floor_load_access _ faultClass dst base imm 3 fault
        (Or.inr (Or.inr ⟨rfl, rfl⟩)) () s t hexec).2
  case VirtualStoreW base value imm fault =>
    exact register42_store_word_preserves_sourceValue _ _ src s t
      (JoltConstraints.floor_store_access _ base value imm 3 fault
        (Or.inr (Or.inr ⟨rfl, rfl⟩)) () s t hexec).2
  case VirtualAdviceLoad dst byteCount =>
    cases hr : JoltISA.readAdviceTape s.adviceTape byteCount with
    | none => simp only [JoltISA.execInstr, hr] at hexec; cases hexec
    | some result =>
        obtain ⟨written, tape⟩ := result
        have h : (do JoltISA.writeDst dst written; pure RETIRE_SUCCESS)
            { s with adviceTape := tape } = .ok (.Retire_Success ()) t := by
          simpa only [JoltISA.execInstr, hr] using hexec
        have hp := register42_write_retire_preserves_other dst src written
          { s with adviceTape := tape } t (hne dst rfl) hready h
        exact hp.trans (by cases src <;> rfl)
  case VirtualHostIO =>
    have hrun : JoltISA.execHostIO s = .ok (.Retire_Success ()) t := by
      simpa only [JoltISA.execInstr] using hexec
    have hsail := JoltHostFrame.execHostIO_frame s t (.Retire_Success ()) hrun
    have hvregs := Register42VRegs.execHostIO_frame s t (.Retire_Success ()) hrun
    cases src with
    | xreg rd => simp only [JoltISA.sourceValue, hsail]
    | vreg vr => exact congrFun hvregs vr
  case AUIPC dst imm =>
    have h : (liftSail (LeanRV64D.readReg Register.PC) >>= fun pc => do
      JoltISA.writeDst dst (BitVec.ofNat 64 (JoltISA.addWide pc imm))
      pure RETIRE_SUCCESS) s = .ok (.Retire_Success ()) t := by
      simpa only [JoltISA.execInstr, get_arch_pc] using hexec
    obtain ⟨pc, h⟩ := register42_lift_readReg_bind Register.PC _ s t _ h
    exact register42_write_retire_preserves_other dst src _ s t
      (hne dst rfl) hready h
  case JAL dst imm =>
    exact register42_jal_preserves_other dst src imm s t
      (hne dst rfl) hready hexec
  case JALR dst base imm =>
    exact register42_jalr_preserves_other dst base src imm s t
      (hne dst rfl) hready hexec
  case FENCE =>
    simp only [JoltISA.execInstr, pure, EStateM.pure] at hexec
    cases hexec
    rfl
  all_goals simp only [JoltISA.Instr.destination?] at hne
  all_goals simp only [JoltISA.execInstr] at hexec
  all_goals try first
    | exact register42_write_retire_preserves_other _ src _ s t
        (hne _ rfl) hready hexec
    | exact register42_unary_write_preserves_other _ _ src _ s t
        (hne _ rfl) hready hexec
    | exact register42_binary_write_preserves_other _ _ _ src _ s t
        (hne _ rfl) hready hexec
  all_goals try
    (exact register42_branch_preserves_sourceValue _ _ src _ _ s t hexec)
  all_goals try
    (have hs : t = s := by
      apply (show Register42ReadOnly.Preserves _ from ?_) s t _ hexec
      register42_readOnly_auto
     subst t
     rfl)

/-- Canonical source for one Rust/Jolt register witness address. -/
def register42_srcOfAddress (address : Fin 128) : JoltISA.Src :=
  if address.val < 32 then
    .xreg (.Regidx (BitVec.ofNat 5 address.val))
  else
    .vreg (BitVec.ofNat 7 address.val)

theorem register42_srcOfAddress_address (address : Fin 128) :
    TraceWitness.sourceRegisterAddress (register42_srcOfAddress address) =
      address := by
  by_cases h : address.val < 32
  · simp only [register42_srcOfAddress, h, ↓reduceIte,
      TraceWitness.sourceRegisterAddress]
    apply Fin.ext
    simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]
  · simp only [register42_srcOfAddress, h, ↓reduceIte,
      TraceWitness.sourceRegisterAddress]
    apply Fin.ext
    simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt address.isLt]

theorem register42_canonical_vreg_ge32 (vr : JoltISA.VReg)
    (hcanon : JoltRegisterEncoding.destinationIsCanonical (.vreg vr) = true) :
    32 ≤ vr.toNat := by
  by_contra hlt
  have hn : vr.toNat ≤ 31 := by omega
  interval_cases h : vr.toNat <;>
    simp [JoltRegisterEncoding.destinationIsCanonical,
      JoltISA.joltRegisterSlot, h] at hcanon

theorem register42_srcOfDestinationAddress (dst : JoltISA.Dst)
    (hcanon : JoltRegisterEncoding.destinationIsCanonical dst = true) :
    register42_srcOfAddress (TraceWitness.destinationRegisterAddress dst) =
      register42_dstAsSrc dst := by
  cases dst with
  | xreg rd =>
      cases rd with
      | Regidx bits =>
          have hlt : bits.toNat < 32 := bits.isLt
          have haddr :
              (TraceWitness.destinationRegisterAddress
                (.xreg (.Regidx bits))).val = bits.toNat := by
            have hlt128 : bits.toNat < 128 := by omega
            simp [TraceWitness.destinationRegisterAddress,
              BitVec.toNat_setWidth, Nat.mod_eq_of_lt hlt128]
          simp [register42_srcOfAddress, haddr, hlt,
            register42_dstAsSrc]
  | vreg vr =>
      have hge := register42_canonical_vreg_ge32 vr hcanon
      simp [register42_srcOfAddress,
        TraceWitness.destinationRegisterAddress,
        register42_dstAsSrc, hge]

theorem register42_instruction_destination_canonical
    (instr : JoltISA.Instr) (dst : JoltISA.Dst)
    (hcanon : JoltRegisterEncoding.instructionIsCanonical instr = true)
    (hdst : instr.destination? = some dst) :
    JoltRegisterEncoding.destinationIsCanonical dst = true := by
  cases instr <;>
    simp_all [JoltISA.Instr.destination?,
      JoltRegisterEncoding.instructionIsCanonical]

theorem register42_capturedDestinationValue
    (dst : JoltISA.Dst) (s : SailJoltState) :
    TraceWitness.capturedDestinationValue dst s =
      JoltISA.sourceValue (register42_dstAsSrc dst) s := by
  cases dst <;> rfl

theorem register42_rdValue_eq_destination
    {F : Type} [Field F] (instr : JoltISA.Instr) (s : SailJoltState) :
    TraceWitness.rdValue (F := F) instr s =
      match instr.destination? with
      | some dst => ((JoltISA.sourceValue (register42_dstAsSrc dst) s).toNat : F)
      | none => 0 := by
  cases instr <;>
    simp [TraceWitness.rdValue, register42_capturedDestinationValue,
      JoltISA.Instr.destination?]

theorem register42_RdWa_real
    {F : Type} [Field F] (p : WitnessParams)
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (t : Fin p.traceLength) (hb : t.val < trace.rows.size)
    (register : Fin 128) :
    TraceWitness.RdWa (F := F) p trace register t =
      match trace.bytecode[(trace.rows[t.val]'hb).rowIndex].instruction.destination? with
      | some dst =>
          if register = TraceWitness.destinationRegisterAddress dst then 1 else 0
      | none => 0 := by
  unfold TraceWitness.RdWa
  simp only [dif_pos hb]
  cases instr :
      trace.bytecode[(trace.rows[t.val]'hb).rowIndex].instruction <;>
    simp [JoltISA.Instr.destination?, TraceWitness.capturedDestination] <;>
    rfl

theorem register42_destination_withRuntimeAdvice
    (instr : JoltISA.Instr) (advice : instr.RuntimeAdvice) :
    (instr.withRuntimeAdvice advice).destination? = instr.destination? := by
  cases instr <;> rfl

theorem register42_row_step
    {F : Type} [Field F] (p : WitnessParams)
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (register : Fin 128) (t : Fin p.traceLength)
    (hb : t.val < trace.rows.size) :
    ((JoltISA.sourceValue (register42_srcOfAddress register)
      (trace.rows[t.val]'hb).postState).toNat : F) =
      ((JoltISA.sourceValue (register42_srcOfAddress register)
        (trace.rows[t.val]'hb).preState).toNat : F) +
      TraceWitness.RdWa p trace register t * TraceWitness.RdInc p trace t := by
  let i : Fin trace.rows.size := ⟨t.val, hb⟩
  let row := trace.row i (by omega)
  let instr := trace.bytecode[row.rowIndex].instruction
  let src := register42_srcOfAddress register
  have ha := trace.rowAssumptions i
  have hready : ∀ rd, Assumptions.XRegReadable rd row.preState.sail := ha.xRegReadable
  have hwa := register42_RdWa_real (F := F) p trace t hb register
  change TraceWitness.RdWa (F := F) p trace register t =
    match instr.destination? with
    | some dst => if register = TraceWitness.destinationRegisterAddress dst then 1 else 0
    | none => 0 at hwa
  have hinc : TraceWitness.RdInc (F := F) p trace t =
      TraceWitness.rdValue instr row.postState -
        TraceWitness.rdValue instr row.preState := by
    unfold TraceWitness.RdInc
    simp only [dif_pos hb]
    rfl
  have hcanon : JoltRegisterEncoding.instructionIsCanonical instr = true :=
    trace.registerOperandsCanonical row.rowIndex
  have hframe (hneq : ∀ dst, instr.destination? = some dst →
      src ≠ register42_dstAsSrc dst) :
      JoltISA.sourceValue src row.postState =
        JoltISA.sourceValue src row.preState := by
    apply register42_instruction_preserves_other
      (instr.withRuntimeAdvice row.runtimeAdvice) src row.preState row.postState
    · intro dst hdst
      rw [register42_destination_withRuntimeAdvice] at hdst
      exact hneq dst hdst
    · exact hready
    · exact row.executes
  change ((JoltISA.sourceValue src row.postState).toNat : F) =
    ((JoltISA.sourceValue src row.preState).toNat : F) +
      TraceWitness.RdWa p trace register t * TraceWitness.RdInc p trace t
  cases hd : instr.destination? with
  | none =>
      have hs := hframe (by intro dst h; rw [hd] at h; cases h)
      rw [hinc, register42_rdValue_eq_destination,
        register42_rdValue_eq_destination, hd, hwa, hd]
      simp [hs]
  | some dst =>
      have hcanondst := register42_instruction_destination_canonical instr dst hcanon hd
      have hsrcdst := register42_srcOfDestinationAddress dst hcanondst
      by_cases hselected : register = TraceWitness.destinationRegisterAddress dst
      · have hsrc : src = register42_dstAsSrc dst := by
          dsimp [src]
          rw [hselected]
          exact hsrcdst
        rw [hinc, register42_rdValue_eq_destination,
          register42_rdValue_eq_destination, hwa]
        simp only [hd, hselected, ↓reduceIte, hsrc, one_mul]
        ring
      · have hneq : src ≠ register42_dstAsSrc dst := by
          intro heq
          rw [← hsrcdst] at heq
          have hadd := congrArg TraceWitness.sourceRegisterAddress heq
          change TraceWitness.sourceRegisterAddress
            (register42_srcOfAddress register) = _ at hadd
          rw [register42_srcOfAddress_address] at hadd
          rw [register42_srcOfAddress_address] at hadd
          exact hselected hadd
        have hs := hframe (by intro d h; rw [hd] at h; cases h; exact hneq)
        rw [hwa]
        simp [hd, hselected, hs]
