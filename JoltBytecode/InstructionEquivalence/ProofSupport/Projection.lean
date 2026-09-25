import JoltBytecode.InstructionEquivalence.ProofSupport.Basic
import JoltBytecode.InstructionEquivalence.Instructions.System.Common
import JoltBytecode.Bundles

/-!
# Projection proof facts

These are proof-facing facts about `System.systemProject`.
-/

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace Projection

/-- The persistent CSR virtual registers materialized by `systemProject` are
unchanged between two Jolt states. -/
def ProjectedVRegsPreserved (before after : SailJoltState) : Prop :=
  after.vregs JoltISA.trapHandlerVReg = before.vregs JoltISA.trapHandlerVReg ∧
  after.vregs JoltISA.mscratchVReg = before.vregs JoltISA.mscratchVReg ∧
  after.vregs JoltISA.mepcVReg = before.vregs JoltISA.mepcVReg ∧
  after.vregs JoltISA.mcauseVReg = before.vregs JoltISA.mcauseVReg ∧
  after.vregs JoltISA.mtvalVReg = before.vregs JoltISA.mtvalVReg ∧
  after.vregs JoltISA.mstatusVReg = before.vregs JoltISA.mstatusVReg

/-- Under the linked-CSR invariant, `systemProject` agrees with the old plain
projection on the initial state. -/
theorem systemProject_eq_project_of_compatible
    (js : SailJoltState)
    (h : LinkedCSRs js) :
    System.systemProject js = project js :=
  System.systemProject_eq_project_of_compatible js h

/-- Under the linked-CSR invariant, `systemProject` agrees with the embedded
generated Sail state. This is the instruction-facing form; callers should not
need to mention the legacy plain projection. -/
theorem systemProject_eq_sail_of_compatible
    (js : SailJoltState)
    (h : LinkedCSRs js) :
    System.systemProject js = js.sail :=
  System.systemProject_eq_project_of_compatible js h

/-!
## System-Project Frame Lemmas

These lemmas state that a Sail computation preserves the six generated-Sail
registers overwritten by `System.systemProject`: `mstatus`, `mtvec`,
`mscratch`, `mepc`, `mcause`, and `mtval`.

Instruction proofs can use this as a frame rule: prove the Sail monad does not
touch those registers, then the projection bridge says `systemProject` is a
no-op on the final embedded Sail state.
-/

/-- A pure `RETIRE_SUCCESS` projects to the same pure Sail retirement when the
initial linked-CSR invariant holds. -/
theorem systemProjectResult_pure_retire
    (js : SailJoltState)
    (hlinked : LinkedCSRs js) :
    System.systemProjectResult
      (((pure RETIRE_SUCCESS : JoltMonad ExecutionResult) js))
    =
    ((pure RETIRE_SUCCESS : SailM ExecutionResult) js.sail) := by
  simp only [pure, EStateM.pure, System.systemProjectResult]
  rw [systemProject_eq_sail_of_compatible js hlinked]

/-- `liftSail` distributes over bind. This lets instruction proofs rewrite a
lifted Sail `do` block into one lifted monadic line at a time. -/
theorem liftSail_bind
    (m : SailM α)
    (f : α → SailM β) :
    liftSail (m >>= f) =
      (liftSail m >>= fun x => liftSail (f x)) := by
  unfold liftSail
  funext js
  simp only [bind, EStateM.bind]
  cases hm : m js.sail <;> rfl

/-- The six Sail registers that `System.systemProject` overwrites are unchanged
between `s0` and `s1`. -/
structure PreservesSystemProjectRegs (s0 s1 : SailState) : Prop where
  mstatus :
    s1.regs.get? Register.mstatus = s0.regs.get? Register.mstatus
  mtvec :
    s1.regs.get? Register.mtvec = s0.regs.get? Register.mtvec
  mscratch :
    s1.regs.get? Register.mscratch = s0.regs.get? Register.mscratch
  mepc :
    s1.regs.get? Register.mepc = s0.regs.get? Register.mepc
  mcause :
    s1.regs.get? Register.mcause = s0.regs.get? Register.mcause
  mtval :
    s1.regs.get? Register.mtval = s0.regs.get? Register.mtval

/-- A monadic result preserves the six system-project registers if its final
state, whether success or error, preserves them. -/
def ResultPreservesSystemProjectRegs
    (s0 : SailState)
    (r : EStateM.Result (Error exception) SailState α) : Prop :=
  match r with
  | .ok _ s1 => PreservesSystemProjectRegs s0 s1
  | .error _ s1 => PreservesSystemProjectRegs s0 s1

/- Basic algebra for composing register-preservation facts. -/

theorem preservesSystemProjectRegs_refl
    (s : SailState) :
    PreservesSystemProjectRegs s s := by
  refine
    { mstatus := ?_
      mtvec := ?_
      mscratch := ?_
      mepc := ?_
      mcause := ?_
      mtval := ?_ }
  all_goals
    rfl

theorem preservesSystemProjectRegs_trans
    {s0 s1 s2 : SailState}
    (h01 : PreservesSystemProjectRegs s0 s1)
    (h12 : PreservesSystemProjectRegs s1 s2) :
    PreservesSystemProjectRegs s0 s2 := by
  refine
    { mstatus := ?_
      mtvec := ?_
      mscratch := ?_
      mepc := ?_
      mcause := ?_
      mtval := ?_ }
  · exact h12.mstatus.trans h01.mstatus
  · exact h12.mtvec.trans h01.mtvec
  · exact h12.mscratch.trans h01.mscratch
  · exact h12.mepc.trans h01.mepc
  · exact h12.mcause.trans h01.mcause
  · exact h12.mtval.trans h01.mtval

/- Generic monad-frame lemmas. These are the pieces that let us prove a compound
Sail monad preserves the six registers by proving each monadic line preserves
them. -/

theorem pure_preservesSystemProjectRegs
    (s : SailState)
    (value : α) :
    ResultPreservesSystemProjectRegs s
      (((pure value : SailM α) s)) := by
  simp only [pure, EStateM.pure, ResultPreservesSystemProjectRegs]
  exact preservesSystemProjectRegs_refl s

theorem bind_preservesSystemProjectRegs
    {m : SailM α}
    {f : α → SailM β}
    {s0 : SailState}
    (hm : ResultPreservesSystemProjectRegs s0 (m s0))
    (hf : ∀ value s1,
      m s0 = .ok value s1 →
      ResultPreservesSystemProjectRegs s1 ((f value) s1)) :
    ResultPreservesSystemProjectRegs s0 (((m >>= f) : SailM β) s0) := by
  cases hm_run : m s0 with
  | ok value s1 =>
      have hm_pres : PreservesSystemProjectRegs s0 s1 := by
        unfold ResultPreservesSystemProjectRegs at hm
        rw [hm_run] at hm
        exact hm
      have hf_pres := hf value s1 hm_run
      simp only [bind, EStateM.bind, hm_run]
      unfold ResultPreservesSystemProjectRegs at hf_pres ⊢
      cases hf_run : (f value) s1 with
      | ok result s2 =>
          rw [hf_run] at hf_pres
          exact preservesSystemProjectRegs_trans hm_pres hf_pres
      | error err s2 =>
          rw [hf_run] at hf_pres
          exact preservesSystemProjectRegs_trans hm_pres hf_pres
  | error err s1 =>
      unfold ResultPreservesSystemProjectRegs at hm
      rw [hm_run] at hm
      simp only [bind, EStateM.bind, hm_run, ResultPreservesSystemProjectRegs]
      exact hm

/- Primitive Sail computations used by branch instructions. -/

theorem readReg_preservesSystemProjectRegs
    (reg : Register)
    (s : SailState) :
    ResultPreservesSystemProjectRegs s
      (((Sail.readReg reg : SailM (RegisterType reg)) s)) := by
  unfold Sail.readReg PreSail.readReg
  simp only [bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get]
  cases hread : s.regs.get? reg with
  | some value =>
      simp only [pure, EStateM.pure, ResultPreservesSystemProjectRegs]
      exact preservesSystemProjectRegs_refl s
  | none =>
      simp only [throw, throwThe, MonadExceptOf.throw, EStateM.throw,
        ResultPreservesSystemProjectRegs]
      exact preservesSystemProjectRegs_refl s

theorem setNextPCState_preservesSystemProjectRegs
    (s : SailState)
    (target : BitVec 64) :
    PreservesSystemProjectRegs s (System.setNextPCState s target) := by
  refine
    { mstatus := ?_
      mtvec := ?_
      mscratch := ?_
      mepc := ?_
      mcause := ?_
      mtval := ?_ }
  all_goals
    unfold System.setNextPCState
    rw [System.extDHashMap_get?_insert_of_ne (h := by decide)]

theorem set_next_pc_preservesSystemProjectRegs
    (target : BitVec 64)
    (s : SailState) :
    ResultPreservesSystemProjectRegs s ((set_next_pc target) s) := by
  unfold set_next_pc redirect_callback
  unfold Sail.writeReg PreSail.writeReg
  simp only [bind, EStateM.bind, pure, EStateM.pure, modify, modifyGet,
    MonadStateOf.modifyGet, EStateM.modifyGet, ResultPreservesSystemProjectRegs]
  change PreservesSystemProjectRegs s (System.setNextPCState s target)
  exact setNextPCState_preservesSystemProjectRegs s target


private theorem currentlyEnabled_Ext_Zca_preservesSystemProjectRegs
    (s : SailState) :
    ResultPreservesSystemProjectRegs s ((currentlyEnabled extension.Ext_Zca) s) := by
  simpa [currentlyEnabled, Functor.map, bind] using
    bind_preservesSystemProjectRegs
    (bind_preservesSystemProjectRegs
      (readReg_preservesSystemProjectRegs Register.misa s)
      (fun _ s1 _ =>
        pure_preservesSystemProjectRegs s1 _))
    (fun _ s1 _ =>
      pure_preservesSystemProjectRegs s1 _)

theorem jump_to_preservesSystemProjectRegs
    (target : BitVec 64)
    (s : SailState) :
    ResultPreservesSystemProjectRegs s ((jump_to target) s) := by
  unfold jump_to ext_control_check_pc
  unfold SailME.run PreSail.PreSailME.run
  simp only [ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont,
    ExceptT.pure, bind, EStateM.bind, pure, EStateM.pure,
    Sail.assert, PreSail.assert]
  by_cases hbit0 : (BitVec.access target 0 == 0#1) = true
  · cases hzca : (currentlyEnabled extension.Ext_Zca) s with
    | error e s1 =>
        have hpres := currentlyEnabled_Ext_Zca_preservesSystemProjectRegs s
        unfold ResultPreservesSystemProjectRegs at hpres
        rw [hzca] at hpres
        simpa [hbit0, pure, EStateM.pure, bind, EStateM.bind,
          ExceptT.bindCont, liftM, monadLift, MonadLift.monadLift,
          ExceptT.lift, ExceptT.mk, EStateM.map, Functor.map, hzca,
          ResultPreservesSystemProjectRegs] using hpres
    | ok zca s1 =>
        have hpres_zca := currentlyEnabled_Ext_Zca_preservesSystemProjectRegs s
        have hzcapres : PreservesSystemProjectRegs s s1 := by
          unfold ResultPreservesSystemProjectRegs at hpres_zca
          rw [hzca] at hpres_zca
          exact hpres_zca
        by_cases halign :
            bit_to_bool (BitVec.access target 1) = true ∧
              LeanRV64D.Functions.not zca = true
        · simpa [hbit0, pure, EStateM.pure, bind, EStateM.bind,
            ExceptT.bindCont, hzca, halign, liftM, monadLift,
            MonadLift.monadLift, ExceptT.lift, ExceptT.mk, EStateM.map,
            Functor.map, ResultPreservesSystemProjectRegs] using hzcapres
        ·
          have hset := set_next_pc_preservesSystemProjectRegs target s1
          unfold ResultPreservesSystemProjectRegs at hset
          cases hsetpc : set_next_pc target s1 with
          | error e s2 =>
              rw [hsetpc] at hset
              simpa [hbit0, pure, EStateM.pure, bind, EStateM.bind,
                ExceptT.bindCont, hzca, halign, liftM, monadLift,
                MonadLift.monadLift, ExceptT.lift, ExceptT.mk, EStateM.map,
                Functor.map, hsetpc, ResultPreservesSystemProjectRegs] using
                preservesSystemProjectRegs_trans hzcapres hset
          | ok _ s2 =>
              rw [hsetpc] at hset
              simpa [hbit0, pure, EStateM.pure, bind, EStateM.bind,
                ExceptT.bindCont, hzca, halign, liftM, monadLift,
                MonadLift.monadLift, ExceptT.lift, ExceptT.mk, EStateM.map,
                Functor.map, hsetpc, ResultPreservesSystemProjectRegs] using
                preservesSystemProjectRegs_trans hzcapres hset
  · simpa [hbit0, pure, EStateM.pure, bind, EStateM.bind, throw, throwThe,
      MonadExceptOf.throw, EStateM.throw, ResultPreservesSystemProjectRegs] using
      preservesSystemProjectRegs_refl s

/- Projection bridge: preserving these six Sail registers is exactly what is
needed to keep Jolt's linked CSR virtual registers linked after changing only
the embedded Sail state. -/

theorem linkedCSRs_of_preservesSystemProjectRegs
    (js : SailJoltState)
    (s1 : SailState)
    (hlinked : LinkedCSRs js)
    (hpres : PreservesSystemProjectRegs js.sail s1) :
    LinkedCSRs ({ js with sail := s1 } : SailJoltState) := by
  rcases hlinked with
    ⟨hmstatus, hmtvec, hmscratch, hmepc, hmcause, hmtval⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨by rw [hpres.mstatus, hmstatus.value_eq]⟩
  · exact ⟨by rw [hpres.mtvec, hmtvec.value_eq]⟩
  · exact ⟨by rw [hpres.mscratch, hmscratch.value_eq]⟩
  · exact ⟨by rw [hpres.mepc, hmepc.value_eq]⟩
  · exact ⟨by rw [hpres.mcause, hmcause.value_eq]⟩
  · exact ⟨by rw [hpres.mtval, hmtval.value_eq]⟩

theorem systemProject_eq_sail_of_preservesSystemProjectRegs
    (js : SailJoltState)
    (s1 : SailState)
    (hlinked : LinkedCSRs js)
    (hpres : PreservesSystemProjectRegs js.sail s1) :
    System.systemProject ({ js with sail := s1 } : SailJoltState) = s1 := by
  exact systemProject_eq_sail_of_compatible
    ({ js with sail := s1 } : SailJoltState)
    (linkedCSRs_of_preservesSystemProjectRegs js s1 hlinked hpres)

theorem systemProjectResult_liftSail_eq_of_preservesSystemProjectRegs
    {m : SailM α}
    {js : SailJoltState}
    (hlinked : LinkedCSRs js)
    (hpres : ResultPreservesSystemProjectRegs js.sail (m js.sail)) :
    System.systemProjectResult ((liftSail m) js) = m js.sail := by
  unfold ResultPreservesSystemProjectRegs at hpres
  unfold liftSail System.systemProjectResult
  cases hm : m js.sail with
  | ok a s1 =>
      simp only [hm] at hpres ⊢
      rw [systemProject_eq_sail_of_preservesSystemProjectRegs
        js s1 hlinked hpres]
  | error e s1 =>
      simp only [hm] at hpres ⊢
      rw [systemProject_eq_sail_of_preservesSystemProjectRegs
        js s1 hlinked hpres]

/-- Projecting after an architectural x-register write is the same as writing
that x-register after projecting. -/
theorem systemProject_stateAfterWrite
    (js : SailJoltState) (rd : regidx) (value : BitVec 64) :
    System.systemProject { js with sail := stateAfterWrite js.sail rd value } =
      stateAfterWrite (System.systemProject js) rd value :=
  System.systemProject_stateAfterWrite js rd value

/-- If an instruction updates only the embedded Sail state and preserves the
CSR virtual registers projected by `systemProject`, then projection commutes with
that architectural x-register write. -/
theorem systemProject_stateAfterWrite_of_projected_vregs_preserved
    (before after : SailJoltState) (rd : regidx) (value : BitVec 64)
    (hsail : after.sail = stateAfterWrite before.sail rd value)
    (hprojected : ProjectedVRegsPreserved before after) :
    System.systemProject after = stateAfterWrite (System.systemProject before) rd value := by
  have hsame :
      System.systemProject after =
        System.systemProject { before with sail := stateAfterWrite before.sail rd value } := by
    rcases hprojected with
      ⟨hmtvec, hmscratch, hmepc, hmcause, hmtval, hmstatus⟩
    unfold System.systemProject
    simp only [hsail, hmtvec, hmscratch, hmepc, hmcause, hmtval, hmstatus]
  rw [hsame]
  exact systemProject_stateAfterWrite before rd value

/-- If a transition preserves the projected CSR virtual registers and leaves
the generated Sail register map unchanged, then linked CSRs remain linked after
the transition. This is the store-family projection bridge: stores update
memory, not registers. -/
theorem systemProject_eq_project_of_projected_vregs_preserved_of_sail_regs_eq
    (before after : SailJoltState)
    (hregs : after.sail.regs = before.sail.regs)
    (hprojected : ProjectedVRegsPreserved before after)
    (hlinked : LinkedCSRs before) :
    System.systemProject after = project after := by
  rcases hprojected with
    ⟨hmtvec, hmscratch, hmepc, hmcause, hmtval, hmstatus⟩
  rcases hlinked with
    ⟨hmstatusLinked, hmtvecLinked, hmscratchLinked, hmepcLinked,
      hmcauseLinked, hmtvalLinked⟩
  have hlinked_after : LinkedCSRs after := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact ⟨by rw [hregs, hmstatus, hmstatusLinked.value_eq]⟩
    · exact ⟨by rw [hregs, hmtvec, hmtvecLinked.value_eq]⟩
    · exact ⟨by rw [hregs, hmscratch, hmscratchLinked.value_eq]⟩
    · exact ⟨by rw [hregs, hmepc, hmepcLinked.value_eq]⟩
    · exact ⟨by rw [hregs, hmcause, hmcauseLinked.value_eq]⟩
    · exact ⟨by rw [hregs, hmtval, hmtvalLinked.value_eq]⟩
  exact systemProject_eq_project_of_compatible after hlinked_after

/-- Instruction-facing store-family projection bridge: if the transition
preserves projected CSR virtual registers and leaves the Sail register map
unchanged, `systemProject` agrees with the final embedded Sail state. -/
theorem systemProject_eq_sail_of_projected_vregs_preserved_of_sail_regs_eq
    (before after : SailJoltState)
    (hregs : after.sail.regs = before.sail.regs)
    (hprojected : ProjectedVRegsPreserved before after)
    (hlinked : LinkedCSRs before) :
    System.systemProject after = after.sail :=
  systemProject_eq_project_of_projected_vregs_preserved_of_sail_regs_eq
    before after hregs hprojected hlinked

/-- TODO: Docs -/
theorem systemProject_eq_sail_of_memory_update_then_write
    (before after : SailJoltState)
    (stored : SailState)
    (rd : regidx) (value : BitVec 64)
    (hsail : after.sail = stateAfterWrite stored rd value)
    (hregs : stored.regs = before.sail.regs)
    (hprojected : ProjectedVRegsPreserved before after)
    (hlinked : LinkedCSRs before) :
    System.systemProject after = after.sail := by
  let afterStore : SailJoltState := { before with sail := stored }
  have hstoreProjected : ProjectedVRegsPreserved before afterStore := by
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hwriteProjected : ProjectedVRegsPreserved afterStore after := by
    exact hprojected
  have hstoreProject : System.systemProject afterStore = stored := by
    exact
      systemProject_eq_sail_of_projected_vregs_preserved_of_sail_regs_eq
        before afterStore hregs hstoreProjected hlinked
  rw [systemProject_stateAfterWrite_of_projected_vregs_preserved
    afterStore after rd value hsail hwriteProjected]
  rw [hstoreProject, ← hsail]

/-- A pure `RETIRE_SUCCESS` after a successful architectural x-register write
projects to the same pure Sail retirement at the written Sail state. -/
theorem systemProjectResult_pure_retire_after_xreg_write
    (rd : regidx)
    (js : SailJoltState)
    (s' : SailState)
    (value : BitVec 64)
    (hlinked : LinkedCSRs js)
    (hwrite : wX_bits rd value js.sail = .ok () s') :
    System.systemProjectResult (
     (pure RETIRE_SUCCESS : JoltMonad ExecutionResult) ({ js with sail := s' } : SailJoltState)
     ) 
    =
    ((pure RETIRE_SUCCESS : SailM ExecutionResult) s') := by
  have h_project_initial : System.systemProject js = js.sail :=
    systemProject_eq_sail_of_compatible js hlinked
  have h_final_sail :
      ({ js with sail := s' } : SailJoltState).sail =
        stateAfterWrite js.sail rd value :=
    wX_bits_eq_stateAfterWrite rd value js.sail s' hwrite
  have h_projected_vregs :
      ProjectedVRegsPreserved js
        ({ js with sail := s' } : SailJoltState) := by
    unfold ProjectedVRegsPreserved
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  simp only [pure, EStateM.pure, System.systemProjectResult]
  rw [systemProject_stateAfterWrite_of_projected_vregs_preserved
    js ({ js with sail := s' } : SailJoltState) rd value
      h_final_sail h_projected_vregs]
  rw [h_project_initial]
  rw [← h_final_sail]

/-- Generic projected-vreg preservation theorem for any successful program run
whose instructions avoid protected Jolt registers.  The old classifier is
stronger than needed for `systemProject`, but it gives a reusable bridge. -/
theorem execProgram_preserves_projected_vregs_of_no_protected_writes
    {program : JoltISA.Program}
    {js js' : SailJoltState}
    {result : ExecutionResult}
    (hsafe : JoltISA.ProgramWritesNoProtectedVReg program)
    (hrun : (JoltISA.execProgram program).run js = .ok result js') :
    ProjectedVRegsPreserved js js' := by
  have hprotected :=
    JoltISA.execProgram_preserves_protected
      (js := js) (js' := js') (result := result) hsafe hrun
  exact ⟨
    hprotected JoltISA.trapHandlerVReg rfl,
    hprotected JoltISA.mscratchVReg rfl,
    hprotected JoltISA.mepcVReg rfl,
    hprotected JoltISA.mcauseVReg rfl,
    hprotected JoltISA.mtvalVReg rfl,
    hprotected JoltISA.mstatusVReg rfl⟩

end Projection

end
