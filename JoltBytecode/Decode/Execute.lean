import JoltBytecode.Step.Instructions

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail
  LeanRV64D LeanRV64D.Functions

open Lean Meta Elab Tactic

namespace Decode

private def Outputs {α : Type} (p : α → Prop) (m : SailM α) : Prop :=
  ∀ s a t, m s = .ok a t → p a

private theorem outputs_pure {α : Type} {p : α → Prop} (a : α) (h : p a) :
    Outputs p (pure a) := by
  intro s b t hr
  cases hr
  exact h

private theorem outputs_bind {α β : Type} {p : β → Prop} (m : SailM α)
    (k : α → SailM β) (h : ∀ a, Outputs p (k a)) : Outputs p (m >>= k) := by
  intro s b t hr
  cases hm : m s with
  | error e u => simp [bind, EStateM.bind, hm] at hr
  | ok a u => exact h a u b t (by simpa [bind, EStateM.bind, hm] using hr)

private def ExceptOutput {ε α : Type} (p : ε → Prop) (q : α → Prop) :
    Except (Sail.Error exception ⊕ ε) α → Prop
  | .ok a => q a
  | .error (.inl _) => True
  | .error (.inr e) => p e

private def OutputsE {ε α : Type} (p : ε → Prop) (q : α → Prop)
    (m : SailME ε α) : Prop := Outputs (ExceptOutput p q) (ExceptT.run m)

private theorem outputsE_bind {ε α β : Type} {p : ε → Prop} {q : β → Prop}
    (m : SailME ε α) (k : α → SailME ε β)
    (hm : OutputsE p (fun _ => True) m) (hk : ∀ a, OutputsE p q (k a)) :
    OutputsE p q (m >>= k) := by
  intro s r t hr
  cases hmrun : m s with
  | error e u => simp [ExceptT.run, ExceptT.mk, bind, ExceptT.bind, EStateM.bind, hmrun] at hr
  | ok a u =>
    have ha := hm s a u (by simpa only [ExceptT.run] using hmrun)
    cases a with
    | ok a => exact hk a u r t (by simpa [ExceptT.run, ExceptT.mk, bind, ExceptT.bind, ExceptT.bindCont, EStateM.bind, hmrun] using hr)
    | error e =>
      simp only [ExceptT.run, ExceptT.mk, bind, ExceptT.bind, ExceptT.bindCont, EStateM.bind, hmrun,
        pure, EStateM.pure] at hr
      cases hr
      cases e <;> exact ha

private theorem outputsE_pure {ε α : Type} {p : ε → Prop} {q : α → Prop}
    (a : α) (h : q a) : OutputsE p q (pure a) := by
  exact outputs_pure (p := ExceptOutput p q) (Except.ok a) h

private theorem outputsE_throw {ε α : Type} {p : ε → Prop} {q : α → Prop}
    (e : ε) (h : p e) : OutputsE p q (SailME.throw e) := by
  exact outputs_pure (p := ExceptOutput p q) (Except.error (.inr e)) h

private theorem outputsE_lift {ε α : Type} {p : ε → Prop} {q : α → Prop}
    (m : SailM α) (h : Outputs q m) : OutputsE p q (monadLift m) := by
  intro s r t hr
  cases hm : m s with
  | error e u => simp [ExceptT.run, ExceptT.mk, monadLift, MonadLift.monadLift,
      ExceptT.lift, Functor.map, EStateM.map, hm] at hr
  | ok a u =>
    simp only [ExceptT.run, ExceptT.mk, monadLift, MonadLift.monadLift,
      ExceptT.lift, Functor.map, EStateM.map, hm] at hr
    cases hr
    exact h _ _ _ hm

private theorem outputsE_any {ε α : Type} (p : ε → Prop) (m : SailM α) :
    OutputsE p (fun _ => True) (monadLift m) :=
  outputsE_lift m (fun _ _ _ _ => trivial)

private theorem outputsE_run {ε : Type} {p : ε → Prop} (m : SailME ε ε)
    (h : OutputsE p p m) : Outputs p (SailME.run m) := by
  intro s a t hr
  unfold SailME.run PreSailME.run at hr
  cases hm : ExceptT.run m s with
  | error e u => simp [bind, EStateM.bind, hm] at hr
  | ok r u =>
    have hh := h s r u hm
    cases r with
    | ok b =>
      simp only [bind, EStateM.bind, hm, pure, EStateM.pure] at hr
      cases hr
      exact hh
    | error e =>
      cases e with
      | inl e => simp [bind, EStateM.bind, hm, throw, throwThe, MonadExceptOf.throw, EStateM.throw] at hr
      | inr b =>
        simp only [bind, EStateM.bind, hm, pure, EStateM.pure] at hr
        cases hr
        exact hh

private theorem outputsE_until {ε α : Type} (p : ε → Prop) (fuel : Nat)
    (cond : α → SailME ε Bool) (body : α → SailME ε α)
    (hc : ∀ a, OutputsE p (fun _ => True) (cond a))
    (hb : ∀ a, OutputsE p (fun _ => True) (body a)) (a : α) :
    OutputsE p (fun _ => True) (untilFuelM fuel cond a body) := by
  unfold untilFuelM
  induction fuel generalizing a with
  | zero => exact outputsE_pure a trivial
  | succ n ih =>
    simp only [untilFuelM.go]
    refine outputsE_bind _ _ (hb a) (fun b => ?_)
    refine outputsE_bind _ _ (hc b) (fun c => ?_)
    cases c
    · exact ih b
    · exact outputsE_pure b trivial

private def NoExpand : ExecutionResult → Prop
  | .ExecuteAs _ => False
  | _ => True

private def MemorySafe {α : Type} : Result α ExecutionResult → Prop
  | .Ok _ => True
  | .Err e => NoExpand e

private partial def computationHead (x : Expr) : MetaM Expr := do
  let x ← instantiateMVars x
  match x.consumeMData with
  | .letE _ _ v b _ => computationHead (b.instantiate1 v)
  | e =>
    let e' := e.getAppFn.betaRev e.getAppRevArgs true
    if e' != e then computationHead e'
    else if let some e' ← reduceRecMatcher? e then computationHead e'
    else pure e

elab "decode_safe_memory" : tactic => do
  let mut rest := []
  while !(← getGoals).isEmpty do
    let g ← getMainGoal
    let progressed ← g.withContext do
      let ty := (← instantiateMVars (← g.getType)).consumeMData
      unless ty.isAppOf ``OutputsE do return false
      let m ← computationHead ty.getAppArgs.back!
      let gn ← g.change (mkAppN ty.getAppFn (ty.getAppArgs.set! (ty.getAppNumArgs - 1) m))
      setGoals (gn :: (← getGoals).tail!)
      let fn := m.getAppFn
      if fn.isConstOf ``Bind.bind then
        evalTactic (← `(tactic| refine outputsE_bind _ _ ?_ (fun _ => ?_)))
      else if fn.isConstOf ``Pure.pure then
        evalTactic (← `(tactic| exact outputsE_pure _ (by trivial)))
      else if fn.isConstOf ``SailME.throw then
        evalTactic (← `(tactic| exact outputsE_throw _ (by trivial)))
      else if fn.isConstOf ``andM then
        evalTactic (← `(tactic| unfold andM))
      else if fn.isConstOf ``untilFuelM then
        evalTactic (← `(tactic| refine outputsE_until _ _ _ _ (fun _ => ?_) (fun _ => ?_) _))
      else if fn.isConstOf ``MonadLift.monadLift || fn.isConstOf ``monadLift || fn.isConstOf ``liftM then
        let saved ← saveState
        try evalTactic (← `(tactic| exact outputsE_any _ _)) catch _ =>
          saved.restore
          return false
      else if fn.isConstOf ``ite || (← getMatcherInfo? fn.constName!).isSome then
        evalTactic (← `(tactic| split))
      else
        throwError "unhandled memory computation {m}; raw head {repr fn}"
      return true
    unless progressed do
      rest := rest ++ [← getMainGoal]
      setGoals ((← getGoals).tail!)
  setGoals rest

private theorem read_addr_safe (vaddr : virtaddr) (offset : BitVec 64) (width : Nat)
    (access : MemoryAccessType mem_payload) (aq rl res : Bool) :
    Outputs MemorySafe (vmem_read_addr vaddr offset width access aq rl res) := by
  unfold vmem_read_addr
  apply outputsE_run
  decode_safe_memory

private theorem write_addr_safe (vaddr : virtaddr) (width : Nat)
    (data : BitVec (8 * width)) (access : MemoryAccessType mem_payload) (aq rl res : Bool) :
    Outputs MemorySafe (vmem_write_addr vaddr width data access aq rl res) := by
  unfold vmem_write_addr
  apply outputsE_run
  decode_safe_memory

private theorem read_safe (r : regidx) (offset : BitVec 64) (width : Nat)
    (access : MemoryAccessType mem_payload) (aq rl res : Bool) :
    Outputs MemorySafe (vmem_read r offset width access aq rl res) := by
  unfold vmem_read
  apply outputsE_run
  decode_safe_memory
  all_goals exact outputsE_lift _ (read_addr_safe _ _ _ _ _ _ _)

private theorem write_safe (r : regidx) (offset : BitVec 64) (width : Nat)
    (data : BitVec (8 * width)) (access : MemoryAccessType mem_payload) (aq rl res : Bool) :
    Outputs MemorySafe (vmem_write r offset width data access aq rl res) := by
  unfold vmem_write
  apply outputsE_run
  decode_safe_memory
  all_goals exact outputsE_lift _ (write_addr_safe _ _ _ _ _ _ _)

private theorem jump_safe (target : BitVec 64) : Outputs NoExpand (jump_to target) := by
  unfold jump_to
  apply outputsE_run
  decode_safe_memory

private theorem outputs_bind_of {α β : Type} {p : α → Prop} {q : β → Prop}
    (m : SailM α) (k : α → SailM β) (hm : Outputs p m)
    (hk : ∀ a, p a → Outputs q (k a)) : Outputs q (m >>= k) := by
  intro s a t hr
  cases he : m s with
  | error e u => simp [bind, EStateM.bind, he] at hr
  | ok b u => exact hk b (hm s b u he) u a t (by simpa [bind, EStateM.bind, he] using hr)

private theorem full_of_outputs (ast : instruction) (h : Outputs NoExpand (execute ast)) :
    _root_.Step.executeFull ast = execute ast := by
  funext s
  unfold _root_.Step.executeFull
  cases hr : execute ast s with
  | error e t => simp [bind, EStateM.bind, hr]
  | ok r t =>
    have hh := h s r t hr
    simp only [bind, EStateM.bind, hr]
    cases r <;> first | rfl | exact False.elim hh

private theorem outputs_after_success (m : SailM ExecutionResult) (next : SailM Unit)
    (hm : Outputs NoExpand m) :
    Outputs NoExpand (do
      match (← m) with
      | .Retire_Success () => next; pure (.Retire_Success ())
      | other => pure other) := by
  refine outputs_bind_of _ _ hm (fun r hr => ?_)
  cases r <;> first
    | exact outputs_pure _ hr
    | exact outputs_bind next _ (fun _ => outputs_pure _ trivial)

/-- Base AST families produced by RV64 compressed instructions.
For example, C.LW expands to LOAD, and C.ADDI expands to ITYPE. -/
inductive CompressedBase : instruction → Prop
  | utype (imm rd op) : CompressedBase (.UTYPE (imm, rd, op))
  | itype (imm rs rd op) : CompressedBase (.ITYPE (imm, rs, rd, op))
  | shift (sh rs rd op) : CompressedBase (.SHIFTIOP (sh, rs, rd, op))
  | shiftw (sh rs rd op) : CompressedBase (.SHIFTIWOP (sh, rs, rd, op))
  | rtype (rs2 rs1 rd op) : CompressedBase (.RTYPE (rs2, rs1, rd, op))
  | rtypew (rs2 rs1 rd op) : CompressedBase (.RTYPEW (rs2, rs1, rd, op))
  | addiw (imm rs rd) : CompressedBase (.ADDIW (imm, rs, rd))
  | load (imm rs rd u width) : CompressedBase (.LOAD (imm, rs, rd, u, width))
  | store (imm rs2 rs1 width) : CompressedBase (.STORE (imm, rs2, rs1, width))
  | jal (imm rd) : CompressedBase (.JAL (imm, rd))
  | jalr (imm rs rd) : CompressedBase (.JALR (imm, rs, rd))
  | branch (imm rs2 rs1 op) : CompressedBase (.BTYPE (imm, rs2, rs1, op))
  | ebreak : CompressedBase (.EBREAK ())

elab "decode_final_result" : tactic => do
  while !(← getGoals).isEmpty do
    let g ← getMainGoal
    g.withContext do
      let ty := (← instantiateMVars (← g.getType)).consumeMData
      let m ← computationHead ty.getAppArgs.back!
      let gn ← g.change (mkAppN ty.getAppFn (ty.getAppArgs.set! (ty.getAppNumArgs - 1) m))
      setGoals (gn :: (← getGoals).tail!)
      if m.getAppFn.isConstOf ``Bind.bind then
        evalTactic (← `(tactic| refine outputs_bind _ _ (fun _ => ?_)))
      else if m.getAppFn.isConstOf ``Pure.pure then
        evalTactic (← `(tactic| exact outputs_pure _ (by trivial)))
      else if (← getMatcherInfo? m.getAppFn.constName!).isSome || m.getAppFn.isConstOf ``ite then
        evalTactic (← `(tactic| split))
      else throwError "non-final computation {m}"

/-- Executing one of the base families cannot request a further expansion.
For example, executeFull LOAD equals execute LOAD even when the load faults. -/
theorem compressedBase_executeFull {ast : instruction} (h : CompressedBase ast) :
    _root_.Step.executeFull ast = execute ast := by
  apply full_of_outputs
  cases h with
  | utype imm rd op =>
    simp only [execute, execute_UTYPE]
    decode_final_result
  | itype imm rs rd op =>
    simp only [execute, execute_ITYPE]
    decode_final_result
  | shift sh rs rd op =>
    simp only [execute, execute_SHIFTIOP]
    decode_final_result
  | shiftw sh rs rd op =>
    simp only [execute, execute_SHIFTIWOP]
    decode_final_result
  | rtype rs2 rs1 rd op =>
    simp only [execute, execute_RTYPE]
    decode_final_result
  | rtypew rs2 rs1 rd op =>
    simp only [execute, execute_RTYPEW]
    decode_final_result
  | addiw imm rs rd =>
    simp only [execute, execute_ADDIW]
    decode_final_result
  | ebreak =>
    simp only [execute, execute_EBREAK]
    decode_final_result
  | load imm rs rd u width =>
    simp only [execute, execute_LOAD]
    refine outputs_bind _ _ (fun _ => ?_)
    refine outputs_bind_of _ _ (read_safe _ _ _ _ _ _ _) (fun r hr => ?_)
    cases r with
    | Ok data => decode_final_result
    | Err e => exact outputs_pure _ hr
  | store imm rs2 rs1 width =>
    simp only [execute, execute_STORE]
    refine outputs_bind _ _ (fun _ => ?_)
    refine outputs_bind _ _ (fun _ => ?_)
    refine outputs_bind _ _ (fun _ => ?_)
    refine outputs_bind_of _ _ (write_safe _ _ _ _ _ _ _ _) (fun r hr => ?_)
    cases r with
    | Ok b => exact outputs_pure _ trivial
    | Err e => exact outputs_pure _ hr
  | jal imm rd =>
    simp only [execute, execute_JAL]
    refine outputs_bind _ _ (fun _ => ?_)
    refine outputs_bind _ _ (fun _ => ?_)
    exact outputs_after_success _ _ (jump_safe _)
  | jalr imm rs rd =>
    simp only [execute, execute_JALR]
    refine outputs_bind _ _ (fun _ => ?_)
    refine outputs_bind _ _ (fun _ => ?_)
    refine outputs_bind _ _ (fun _ => ?_)
    exact outputs_after_success _ _ (jump_safe _)
  | branch imm rs2 rs1 op =>
    simp only [execute, execute_BTYPE]
    refine outputs_bind _ _ (fun taken => ?_)
    cases taken
    · exact outputs_pure _ trivial
    · exact outputs_bind _ _ (fun _ => jump_safe _)

elab "complete_register_read" : tactic => withMainContext do
  let g ← getMainGoal
  let ty ← g.getType
  let some read := ty.find? (fun e => e.isAppOf ``LeanRV64D.readReg) | throwError "register read expected"
  let r := read.getAppArgs[0]!
  let some sd := (← getLCtx).findFromUserName? `s | throwError "state expected"
  let some hd := (← getLCtx).findFromUserName? `hinv | throwError "invariant expected"
  let hp ← mkAppM ``_root_.Step.StepInvariant.present #[hd.toExpr, r]
  let pr ← mkAppM ``_root_.Step.readReg_present #[r, sd.toExpr, hp]
  let name ← mkFreshUserName `available_read
  let gn ← g.assert name (← inferType pr) pr
  let (_, gn) ← gn.intro1P
  setGoals (gn :: (← getGoals).tail!)
  evalTactic (← `(tactic| (rcases ($(mkIdent name)) with ⟨v, hv⟩; exact ⟨v, by simp [hv, regval_from_reg, bind, EStateM.bind, pure, EStateM.pure]⟩)))

private theorem compressed_reg_read (r : regidx) (s : SailState)
    (hinv : _root_.Step.StepInvariant s) : ∃ v, rX_bits r s = .ok v s := by
  cases r with
  | Regidx r =>
    unfold rX_bits rX
    simp only [Sail.BitVec.toNatInt]
    split
    all_goals first
      | exact ⟨_, rfl⟩
      | complete_register_read

private theorem register_write_same (r : Register) (v : RegisterType r) (s : SailState)
    (hr : LeanRV64D.readReg r s = .ok v s) : LeanRV64D.writeReg r v s = .ok () s := by
  have hg : s.regs.get? r = some v := by
    unfold LeanRV64D.readReg Sail.ConcurrencyInterfaceV1.PreSail.readReg at hr
    cases he : s.regs.get? r with
    | none => simp [bind, EStateM.bind, get, MonadStateOf.get, getThe, EStateM.get, pure,
        he, throw, throwThe, MonadExceptOf.throw, EStateM.throw] at hr
    | some w =>
      simp [bind, EStateM.bind, get, MonadStateOf.get, getThe, EStateM.get, pure,
        EStateM.pure, he] at hr
      simpa [hr] using he
  have hm : s.regs.insert r v = s.regs := by
    apply Std.ExtDHashMap.ext_get?
    intro r'
    by_cases h : r = r'
    · subst r'; simp [hg]
    · simp [Std.ExtDHashMap.get?_insert, h]
  simp [LeanRV64D.writeReg, Sail.ConcurrencyInterfaceV1.PreSail.writeReg,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, hm]

private theorem register_callback_pure (r : regidx) (v : BitVec 64) :
    xreg_write_callback r v = pure () := by
  cases r
  simp only [xreg_write_callback, reg_name_forwards, encdec_reg_forwards_matches,
    get_config_use_abi_names, Bool.false_eq_true, Bool.not_false, ↓reduceIte,
    Functions.not, pure_bind, xreg_full_write_callback]

elab "complete_register_restore" : tactic => withMainContext do
  let g ← getMainGoal
  let some read := (← g.getType).find? (fun e => e.isAppOf ``LeanRV64D.readReg) | throwError "read expected"
  let r := read.getAppArgs[0]!
  let some sd := (← getLCtx).findFromUserName? `s | throwError "state expected"
  let some hd := (← getLCtx).findFromUserName? `hinv | throwError "invariant expected"
  let hp ← mkAppM ``_root_.Step.StepInvariant.present #[hd.toExpr, r]
  let pr ← mkAppM ``_root_.Step.readReg_present #[r, sd.toExpr, hp]
  let name ← mkFreshUserName `available_read
  let gn ← g.assert name (← inferType pr) pr
  let (_, gn) ← gn.intro1P
  setGoals (gn :: (← getGoals).tail!)
  evalTactic (← `(tactic| (rcases ($(mkIdent name)) with ⟨v, hv⟩; have hw := register_write_same _ _ _ hv; simp_all [regval_from_reg, regval_into_reg, bind, EStateM.bind, pure, EStateM.pure, register_callback_pure, Sail.BitVec.toNatInt])))

private theorem compressed_reg_restore (r : regidx) (s : SailState)
    (hinv : _root_.Step.StepInvariant s) :
    (do let v ← rX_bits r; wX_bits r v) s = .ok () s := by
  cases r with
  | Regidx r =>
    unfold rX_bits rX wX_bits wX
    simp only [Sail.BitVec.toNatInt]
    split
    all_goals try (solve | simp_all [bind, EStateM.bind, pure, EStateM.pure, regval_from_reg,
          regval_into_reg, register_callback_pure])
    all_goals complete_register_restore

/-- Adding zero to a register is a no-op in a state with all registers present;
for example, Sail's expansion of C.ADDI x1,0 restores x1's old value. -/
theorem compressed_add_zero (r : regidx) (s : SailState)
    (hinv : _root_.Step.StepInvariant s) :
    execute (.ITYPE (0, r, r, .ADDI)) s = .ok RETIRE_SUCCESS s := by
  obtain ⟨v, hv⟩ := compressed_reg_read r s hinv
  have h := compressed_reg_restore r s hinv
  simp only [bind, EStateM.bind, hv] at h
  simp [execute, execute_ITYPE, sign_extend, Sail.BitVec.signExtend,
    bind, EStateM.bind, pure, EStateM.pure, hv, h]

/-- Writing a U-type immediate to x0 has no effect, as with C.LUI x0,1. -/
theorem compressed_lui_zero (imm : BitVec 20) (s : SailState) :
    execute (.UTYPE (imm, zreg, .LUI)) s = .ok RETIRE_SUCCESS s := by rfl

/-- An ADDI targeting x0 is a no-op when its source can be read;
for example C.LI x0,1 reads x0 and discards its result. -/
theorem compressed_addi_zero (imm : BitVec 12) (r : regidx) (s : SailState)
    (hinv : _root_.Step.StepInvariant s) :
    execute (.ITYPE (imm, r, zreg, .ADDI)) s = .ok RETIRE_SUCCESS s := by
  obtain ⟨v, hv⟩ := compressed_reg_read r s hinv
  simp [execute, execute_ITYPE, hv, wX_bits, wX, zreg, zero_extend, Sail.BitVec.zeroExtend, Sail.BitVec.toNatInt, bind, EStateM.bind, pure, EStateM.pure]

/-- An ADD targeting x0 discards its result; C.MV x0,x1 is one example. -/
theorem compressed_add_zero_dest (a b : regidx) (s : SailState)
    (hinv : _root_.Step.StepInvariant s) :
    execute (.RTYPE (a, b, zreg, .ADD)) s = .ok RETIRE_SUCCESS s := by
  obtain ⟨va, ha⟩ := compressed_reg_read a s hinv
  obtain ⟨vb, hb⟩ := compressed_reg_read b s hinv
  simp [execute, execute_RTYPE, ha, hb, wX_bits, wX, zreg, zero_extend, Sail.BitVec.zeroExtend, Sail.BitVec.toNatInt, bind, EStateM.bind, pure, EStateM.pure]

/-- Equality and inequality branches may swap their source registers;
for example BEQ x0,x8 has the same behavior as BEQ x8,x0. -/
theorem compressed_branch_swap (imm : BitVec 13) (a b : regidx) (op : bop)
    (hop : op = .BEQ ∨ op = .BNE) (s : SailState)
    (hinv : _root_.Step.StepInvariant s) :
    execute (.BTYPE (imm, a, b, op)) s = execute (.BTYPE (imm, b, a, op)) s := by
  obtain ⟨va, ha⟩ := compressed_reg_read a s hinv
  obtain ⟨vb, hb⟩ := compressed_reg_read b s hinv
  have he : (va == vb) = (vb == va) := Bool.beq_comm
  rcases hop with rfl | rfl <;>
    simp only [execute, execute_BTYPE, ha, hb, bind, EStateM.bind, pure, EStateM.pure,
      bne, he]

end Decode
