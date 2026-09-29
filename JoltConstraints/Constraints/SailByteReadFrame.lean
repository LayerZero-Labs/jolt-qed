import JoltConstraints.Constraints.NextPCFrame

/-!
Reusable read-only frames for Sail's byte-load pipeline. They cover successful
monadic executions that return either a byte or a memory fault; neither case
changes Sail state. The HostIO frame carries the trace's existing machine-mode
assumptions across every byte of a live host call.
-/

set_option autoImplicit false

open Sail PreSail LeanRV64D.Functions mem_payload

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

theorem read_rule (r : Register) : Preserves (Sail.readReg r) := by
  intro s t v h
  cases readReg_pure r s v t h
  rfl

end SailReadOnly

namespace SailMEFrame
def Preserves {α β : Type} (m : SailME α β) : Prop :=
  SailReadOnly.Preserves (ExceptT.run m)

theorem pure_rule {α β : Type} (v : β) : Preserves (pure v : SailME α β) := by
  exact SailReadOnly.pure_rule _

theorem lift_rule {α β : Type} (m : SailM β)
    (hm : SailReadOnly.Preserves m) :
    Preserves (liftM m : SailME α β) := by
  intro s t v h
  change (m.map Except.ok) s = .ok v t at h
  cases hr : m s with
  | error e s' => simp [EStateM.map, hr] at h
  | ok x s' =>
    simp [EStateM.map, hr] at h
    rcases h with ⟨rfl, rfl⟩
    exact hm s s' x hr

theorem bind_rule {α β γ : Type} {m : SailME α β} {f : β → SailME α γ}
    (hm : Preserves m) (hf : ∀ x, Preserves (f x)) :
    Preserves (m >>= f) := by
  intro s t v h
  simp only [bind, ExceptT.bind, ExceptT.run, ExceptT.mk] at h
  cases hr : ExceptT.run m s with
  | error e s' =>
    change m s = .error e s' at hr
    simp only [EStateM.bind, hr] at h
    cases h
  | ok x s' =>
    change m s = .ok x s' at hr
    simp only [EStateM.bind, hr, ExceptT.bindCont] at h
    cases x with
    | error e =>
      simp [pure, EStateM.pure] at h
      rcases h with ⟨rfl, rfl⟩
      exact hm s s' (.error e) hr
    | ok a => exact (hf a s' t v h).trans (hm s s' (.ok a) hr)

theorem throw_rule {α β : Type} (e : α) : Preserves (SailME.throw e : SailME α β) := by
  intro s t v h
  cases h
  rfl

theorem forIn_loop {α β : Type} (range : IntRange)
    (f : (i : Int) → i ∈ range → β → SailME α (ForInStep β))
    (hf : ∀ i (hi : i ∈ range) b, Preserves (f i hi b))
    (b : β) (i : Int) (hs : (i - range.start) % range.step = 0) :
    Preserves (IntRange.forIn'.loop range f b i hs) := by
  induction b, i, hs using IntRange.forIn'.loop.induct range with
  | case1 b i hs hi ih =>
    rw [IntRange.forIn'.loop.eq_1]
    simp only [dif_pos hi]
    apply bind_rule (hf i hi b)
    intro step
    cases step with
    | done b' => exact pure_rule _
    | yield b' => exact ih b'
  | case2 b i hs hi =>
    rw [IntRange.forIn'.loop.eq_1]
    simp only [dif_neg hi]
    exact pure_rule _

theorem forIn_range {α β : Type} (range : IntRange) (b : β)
    (f : (i : Int) → i ∈ range → β → SailME α (ForInStep β))
    (hf : ∀ i (hi : i ∈ range) b, Preserves (f i hi b)) :
    Preserves (IntRange.forIn' range b f) := by
  exact forIn_loop range f hf b range.start (by simp)

theorem run_rule {α : Type} {m : SailME α α}
    (hm : Preserves m) : SailReadOnly.Preserves (SailME.run m) := by
  intro s t v h
  unfold SailME.run PreSail.PreSailME.run at h
  cases hr : ExceptT.run m s with
  | error e s' =>
    simp only [bind, EStateM.bind, hr] at h
    cases h
  | ok x s' =>
    simp only [bind, EStateM.bind, hr] at h
    cases x with
    | ok a =>
      simp only [pure, EStateM.pure] at h
      cases h
      exact hm s _ _ hr
    | error e =>
      cases e with
      | inl err =>
        simp only [throw] at h
        cases h
      | inr a =>
        simp only [pure, EStateM.pure] at h
        cases h
        exact hm s _ _ hr

end SailMEFrame

macro "sail_nextpc_auto" : tactic => `(tactic|
  repeat' first
  | exact SailReadOnly.read_rule _
  | exact SailReadOnly.pure_rule _
  | split
  | refine SailReadOnly.bind_rule ?_ (fun x => ?_))

theorem pmp_read_frame (n : Nat) :
    SailReadOnly.Preserves (pmpReadAddrReg n) := by
  unfold pmpReadAddrReg
  sail_nextpc_auto

theorem pmp_match_frame (addr : physaddr) (width : BitVec 64)
    (ent : BitVec 8) (pmpaddr prev : BitVec 64) :
    SailReadOnly.Preserves (pmpMatchAddr addr width ent pmpaddr prev) := by
  unfold pmpMatchAddr
  sail_nextpc_auto

theorem access_fault_frame :
    SailReadOnly.Preserves (accessFaultFromAccessType (MemoryAccessType.Load Data)) := by
  simpa only [accessFaultFromAccessType] using
    (SailReadOnly.pure_rule (ExceptionType.E_Load_Access_Fault ()))

theorem pmp_rwx_frame (cfg : BitVec 8) :
    SailReadOnly.Preserves (pmpCheckRWX cfg (MemoryAccessType.Load Data)) := by
  simpa only [pmpCheckRWX] using
    (SailReadOnly.pure_rule (_get_Pmpcfg_ent_R cfg == 1#1))

macro "sailme_nextpc_auto" : tactic => `(tactic|
  repeat' first
  | exact SailMEFrame.pure_rule _
  | exact SailMEFrame.throw_rule _
  | exact SailMEFrame.lift_rule _ (pmp_read_frame _)
  | exact SailMEFrame.lift_rule _ (pmp_match_frame _ _ _ _ _)
  | exact SailMEFrame.lift_rule _ access_fault_frame
  | exact SailMEFrame.lift_rule _ (pmp_rwx_frame _)
  | exact SailMEFrame.lift_rule _ (SailReadOnly.read_rule _)
  | refine SailMEFrame.forIn_range _ _ _ (fun i hi b => ?_)
  | fail_if_no_progress dsimp only [SailMEFrame.Preserves]
  | split
  | refine SailMEFrame.bind_rule ?_ (fun x => ?_))

theorem pmpCheck_readOnly (addr : physaddr) (width : Nat) (priv : Privilege) :
    SailReadOnly.Preserves (pmpCheck addr width (MemoryAccessType.Load Data) priv) := by
  unfold pmpCheck
  refine SailMEFrame.run_rule ?_
  simp only [sys_pmp_count]
  sailme_nextpc_auto

theorem sailAssert_readOnly (p : Bool) (message : String) :
    SailReadOnly.Preserves (Sail.assert p message) := by
  cases p with
  | false =>
    intro s t v h
    simp only [Sail.assert] at h
    cases h
  | true =>
    simpa only [Sail.assert, if_true] using (SailReadOnly.pure_rule ())

theorem alignmentFault_readOnly :
    SailReadOnly.Preserves
      (alignmentFaultFromAccessType (MemoryAccessType.Load Data)) := by
  simpa only [alignmentFaultFromAccessType] using
    (SailReadOnly.pure_rule (ExceptionType.E_Load_Addr_Align ()))

macro "sail_byte_auto" : tactic => `(tactic|
  repeat' first
  | simp_all only [reduceCtorEq]
  | exact SailReadOnly.read_rule _
  | exact SailReadOnly.pure_rule _
  | exact access_fault_frame
  | exact alignmentFault_readOnly
  | exact sailAssert_readOnly _ _
  | fail_if_no_progress dsimp only
  | split
  | refine SailReadOnly.bind_rule ?_ (fun x => ?_))

theorem pmaCheck_readOnly (addr : physaddr) (width : Nat) :
    SailReadOnly.Preserves
      (pmaCheck addr width (MemoryAccessType.Load Data) false) := by
  unfold pmaCheck
  sail_byte_auto

theorem internalError_readOnly {α : Type} (file : String) (line : Int)
    (message : String) :
    SailReadOnly.Preserves (internal_error file line message : SailM α) := by
  intro s t v h
  unfold internal_error Sail.sailThrow at h
  cases h

theorem alignmentPriority_readOnly (e : ExceptionType) :
    SailReadOnly.Preserves (alignmentOrAccessFaultPriority e) := by
  cases e <;>
    first
    | exact SailReadOnly.pure_rule _
    | exact internalError_readOnly _ _ _

theorem highestPriority_readOnly (l r : ExceptionType) :
    SailReadOnly.Preserves (highestPriorityAlignmentOrAccessFault l r) := by
  unfold highestPriorityAlignmentOrAccessFault
  refine SailReadOnly.bind_rule (alignmentPriority_readOnly l) (fun _ => ?_)
  refine SailReadOnly.bind_rule (alignmentPriority_readOnly r) (fun _ => ?_)
  split <;> exact SailReadOnly.pure_rule _

theorem physAccessCheck_readOnly (addr : physaddr) (width : Nat) (priv : Privilege) :
    SailReadOnly.Preserves
      (phys_access_check (MemoryAccessType.Load Data) priv addr width false) := by
  unfold phys_access_check
  repeat' first
    | exact SailReadOnly.pure_rule _
    | exact pmpCheck_readOnly _ _ _
    | exact pmaCheck_readOnly _ _
    | exact highestPriority_readOnly _ _
    | fail_if_no_progress dsimp only
    | split
    | refine SailReadOnly.bind_rule ?_ (fun x => ?_)

theorem withinClint_readOnly (addr : physaddr) (width : Nat) :
    SailReadOnly.Preserves (within_clint addr width) := by
  unfold within_clint
  exact SailReadOnly.pure_rule _

theorem withinHtif_readOnly (addr : physaddr) (width : Nat) :
    SailReadOnly.Preserves (within_htif_readable addr width) := by
  unfold within_htif_readable within_htif_writable
  sail_byte_auto

theorem withinMmio_readOnly (addr : physaddr) (width : Nat) :
    SailReadOnly.Preserves (within_mmio_readable addr width) := by
  unfold within_mmio_readable
  repeat' first
    | exact SailReadOnly.pure_rule _
    | exact withinClint_readOnly _ _
    | exact withinHtif_readOnly _ _
    | fail_if_no_progress dsimp only
    | split
    | refine SailReadOnly.bind_rule ?_ (fun x => ?_)

theorem htifLoad_readOnly (addr : physaddr) :
    SailReadOnly.Preserves (htif_load (MemoryAccessType.Load Data) addr 1) := by
  unfold htif_load
  repeat' first
    | simp_all only
    | exact SailReadOnly.pure_rule _
    | exact SailReadOnly.read_rule _
    | exact access_fault_frame
    | exact internalError_readOnly _ _ _
    | fail_if_no_progress dsimp only
    | split
    | refine SailReadOnly.bind_rule ?_ (fun x => ?_)

theorem clintLoad_readOnly (addr : physaddr) :
    SailReadOnly.Preserves (clint_load (MemoryAccessType.Load Data) addr 1) := by
  unfold clint_load
  repeat' first
    | simp_all only
    | exact SailReadOnly.pure_rule _
    | exact SailReadOnly.read_rule _
    | exact access_fault_frame
    | exact internalError_readOnly _ _ _
    | fail_if_no_progress dsimp only
    | split
    | refine SailReadOnly.bind_rule ?_ (fun x => ?_)

theorem mmioRead_readOnly (addr : physaddr) :
    SailReadOnly.Preserves (mmio_read (MemoryAccessType.Load Data) addr 1) := by
  unfold mmio_read
  repeat' first
    | exact SailReadOnly.pure_rule _
    | exact withinClint_readOnly _ _
    | exact withinHtif_readOnly _ _
    | exact clintLoad_readOnly _
    | exact htifLoad_readOnly _
    | exact access_fault_frame
    | fail_if_no_progress dsimp only
    | split
    | refine SailReadOnly.bind_rule ?_ (fun x => ?_)

theorem sailGet_readOnly : SailReadOnly.Preserves (get : SailM SailState) := by
  intro s t v h
  cases h
  rfl

theorem readByte_readOnly (addr : Nat) :
    SailReadOnly.Preserves (PreSail.readByte addr) := by
  unfold PreSail.readByte
  refine SailReadOnly.bind_rule sailGet_readOnly (fun s => ?_)
  split <;> first
    | exact SailReadOnly.pure_rule _
    | (intro s t v h; cases h)

theorem sailMemRead_readOnly
    (request : Sail.ConcurrencyInterfaceV1.Mem_read_request
      1 64 physaddrbits Unit RISCV_strong_access) :
    SailReadOnly.Preserves (PreSail.ConcurrencyInterfaceV1.sail_mem_read request) := by
  unfold PreSail.ConcurrencyInterfaceV1.sail_mem_read PreSail.readBytes
  repeat' first
    | exact SailReadOnly.pure_rule _
    | exact readByte_readOnly _
    | refine SailReadOnly.bind_rule ?_ (fun x => ?_)

theorem sailThrow_readOnly {α : Type} (e : Error exception) :
    SailReadOnly.Preserves (throw e : SailM α) := by
  intro s t v h
  cases h

theorem readRam_readOnly (addr : physaddr) :
    SailReadOnly.Preserves
      (LeanRV64D.Functions.read_ram read_kind.Read_plain addr 1 false) := by
  unfold LeanRV64D.Functions.read_ram
  repeat' first
    | simp_all only [reduceCtorEq]
    | exact SailReadOnly.pure_rule _
    | exact sailMemRead_readOnly _
    | exact sailThrow_readOnly _
    | exact internalError_readOnly _ _ _
    | fail_if_no_progress dsimp only
    | split
    | refine SailReadOnly.bind_rule ?_ (fun x => ?_)

theorem checkedMemRead_readOnly (addr : physaddr) (priv : Privilege) :
    SailReadOnly.Preserves
      (checked_mem_read (MemoryAccessType.Load Data) priv addr 1 false false false false) := by
  unfold checked_mem_read
  refine SailReadOnly.bind_rule (physAccessCheck_readOnly addr 1 priv) (fun result => ?_)
  cases result with
  | some _ => exact SailReadOnly.pure_rule _
  | none =>
    refine SailReadOnly.bind_rule (withinMmio_readOnly addr 1) (fun mmio => ?_)
    cases mmio with
    | true =>
      exact SailReadOnly.bind_rule (mmioRead_readOnly addr)
        (fun _ => SailReadOnly.pure_rule _)
    | false =>
      simp only [read_kind_of_flags, pure_bind]
      exact SailReadOnly.bind_rule (readRam_readOnly addr)
        (fun _ => SailReadOnly.pure_rule _)

theorem memReadPrivMeta_readOnly (addr : physaddr) (priv : Privilege) :
    SailReadOnly.Preserves
      (mem_read_priv_meta (MemoryAccessType.Load Data) priv addr 1 false false false false) := by
  unfold mem_read_priv_meta
  simp only [Bool.false_or, Bool.false_and, Bool.false_eq_true, if_false]
  exact SailReadOnly.bind_rule (checkedMemRead_readOnly addr priv)
    (fun _ => SailReadOnly.pure_rule _)

theorem memReadPriv_readOnly (addr : physaddr) (priv : Privilege) :
    SailReadOnly.Preserves
      (mem_read_priv (MemoryAccessType.Load Data) priv addr 1 false false false) := by
  unfold mem_read_priv
  exact SailReadOnly.bind_rule (memReadPrivMeta_readOnly addr priv)
    (fun _ => SailReadOnly.pure_rule _)

theorem privLevelBits_readOnly (value : BitVec 2 × BitVec 1) :
    SailReadOnly.Preserves (privLevel_bits_forwards value) := by
  unfold privLevel_bits_forwards
  repeat' first
    | exact SailReadOnly.pure_rule _
    | exact internalError_readOnly _ _ _
    | split

theorem effectivePrivilege_readOnly (mstatus : RegisterType Register.mstatus)
    (priv : Privilege) :
    SailReadOnly.Preserves
      (effectivePrivilege (MemoryAccessType.Load Data) mstatus priv) := by
  unfold effectivePrivilege
  repeat' first
    | exact SailReadOnly.pure_rule _
    | exact privLevelBits_readOnly _
    | split

theorem memRead_readOnly (addr : physaddr) :
    SailReadOnly.Preserves
      (mem_read (MemoryAccessType.Load Data) addr 1 false false false) := by
  unfold mem_read
  repeat' first
    | exact SailReadOnly.pure_rule _
    | exact SailReadOnly.read_rule _
    | exact effectivePrivilege_readOnly _ _
    | exact memReadPriv_readOnly _ _
    | fail_if_no_progress dsimp only
    | split
    | refine SailReadOnly.bind_rule ?_ (fun x => ?_)

theorem vmemReadAddr_readOnly (addr : BitVec 64) (s t : SailState)
    (v : Result (BitVec 8) ExecutionResult)
    (hpriv : Assumptions.CurPrivilegeMachine s)
    (hmprv : Assumptions.MstatusMprvZero s)
    (hrun : vmem_read_addr (virtaddr.Virtaddr addr) 0 1
      (MemoryAccessType.Load Data) false false false s = .ok v t) :
    t = s := by
  cases hmem : mem_read (MemoryAccessType.Load Data)
      (physaddr.Physaddr addr) 1 false false false s with
  | error e u =>
    unfold vmem_read_addr at hrun
    simp only [access_misaligned_1_false, Bool.false_eq_true, if_false] at hrun
    unfold SailME.run PreSail.PreSailME.run at hrun
    have htranslate := translateAddr_load_data_of_machine_mprv_zero addr s hpriv hmprv
    simp [bind, EStateM.bind, pure, EStateM.pure, EStateM.map,
      ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont,
      ExceptT.pure, ExceptT.lift,
      MonadLift.monadLift, SailME.throw, PreSail.PreSailME.throw, MonadExceptOf.throw,
      misaligned_order, sys_misaligned_order_decreasing,
      bits_of_virtaddr, Sail.assert, PreSail.assert,
      untilFuelM, untilFuelM.go, zeros, BitVec.zero, BitVec.addInt,
      Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange',
      liftM, monadLift, Functor.map, split_misaligned_1 addr, htranslate, hmem] at hrun
  | ok result u =>
    have hframe := memRead_readOnly (physaddr.Physaddr addr) s u result hmem
    unfold vmem_read_addr at hrun
    simp only [access_misaligned_1_false, Bool.false_eq_true, if_false] at hrun
    unfold SailME.run PreSail.PreSailME.run at hrun
    have htranslate := translateAddr_load_data_of_machine_mprv_zero addr s hpriv hmprv
    simp [bind, EStateM.bind, pure, EStateM.pure, EStateM.map,
      ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont,
      ExceptT.pure, ExceptT.lift,
      MonadLift.monadLift, SailME.throw, PreSail.PreSailME.throw, MonadExceptOf.throw,
      misaligned_order, sys_misaligned_order_decreasing,
      bits_of_virtaddr, Sail.assert, PreSail.assert,
      untilFuelM, untilFuelM.go, zeros, BitVec.zero, BitVec.addInt,
      Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange',
      liftM, monadLift, Functor.map, split_misaligned_1 addr, htranslate, hmem] at hrun
    cases result <;> simp_all [EStateM.pure, EStateM.bind, ExceptT.bindCont]

theorem readMemoryByte_readOnly (addr : BitVec 64) (s t : SailJoltState)
    (v : Result (BitVec 8) ExecutionResult)
    (hpriv : Assumptions.CurPrivilegeMachine s.sail)
    (hmprv : Assumptions.MstatusMprvZero s.sail)
    (hrun : JoltISA.readMemoryByte addr s = .ok v t) : t = s := by
  unfold JoltISA.readMemoryByte at hrun
  dsimp only at hrun
  split_ifs at hrun with hperipheral hdevice
  · cases hb : JoltISA.deviceByte? s.io addr.toNat with
    | none => simp only [hb] at hrun; cases hrun
    | some byte => simp only [hb] at hrun; cases hrun; rfl
  · cases hr : vmem_read_addr (virtaddr.Virtaddr addr) 0 1
        (MemoryAccessType.Load Data) false false false s.sail with
    | error e u =>
      simp only [liftSail, hr] at hrun
      cases hrun
    | ok value u =>
      have hsame := vmemReadAddr_readOnly addr s.sail u value hpriv hmprv hr
      simp only [liftSail, hr] at hrun
      cases hrun
      simp [hsame]

namespace JoltHostFrame

def Ready (s : SailJoltState) : Prop :=
  Assumptions.CurPrivilegeMachine s.sail ∧
  Assumptions.MstatusMprvZero s.sail

def Preserves {α : Type} (m : JoltMonad α) : Prop :=
  ∀ (s t : SailJoltState) (v : α), Ready s → m s = .ok v t → t.sail = s.sail

theorem pure_rule {α : Type} (v : α) : Preserves (pure v) := by
  intro s t x _ h
  cases h
  rfl

theorem bind_rule {α β : Type} {m : JoltMonad α} {f : α → JoltMonad β}
    (hm : Preserves m) (hf : ∀ x, Preserves (f x)) : Preserves (m >>= f) := by
  intro s t v hready h
  cases hr : m s with
  | error e s' => simp only [bind, EStateM.bind, hr] at h; cases h
  | ok x s' =>
    simp only [bind, EStateM.bind, hr] at h
    have hsail := hm s s' x hready hr
    have hready' : Ready s' := by simpa only [Ready, hsail] using hready
    exact (hf x s' t v hready' h).trans hsail

theorem read_rule (src : JoltISA.Src) : Preserves (JoltISA.readSrc src) := by
  intro s t v _ h
  obtain ⟨rfl, _⟩ := lookup_readSrc_value src s t v h
  rfl

theorem get_rule : Preserves (get : JoltMonad SailJoltState) := by
  intro s t v _ h
  cases h
  rfl

theorem throw_rule {α : Type} (e : Error exception) :
    Preserves (throw e : JoltMonad α) := by
  intro s t v _ h
  cases h

theorem modifyAdvice_rule
    (f : SailJoltState → SailJoltState)
    (hf : ∀ s, (f s).sail = s.sail) :
    Preserves (modify f : JoltMonad Unit) := by
  intro s t v _ h
  cases h
  exact hf s

theorem loadByte_rule (addr : BitVec 64) :
    Preserves (JoltISA.readMemoryByte addr) := by
  intro s t v hready h
  exact congrArg SailJoltState.sail
    (readMemoryByte_readOnly addr s t v hready.1 hready.2 h)

theorem readHostBytes_frame
    (overflowChecks incrementAfterLast : Bool) {width : Nat}
    (pointer : BitVec width) (n : Nat) (bytes : Array (BitVec 8)) :
    Preserves (JoltISA.readHostBytes JoltISA.readMemoryByte
      overflowChecks incrementAfterLast pointer n bytes) := by
  induction n generalizing pointer bytes with
  | zero => exact pure_rule _
  | succ n ih =>
    dsimp only [JoltISA.readHostBytes]
    refine bind_rule (loadByte_rule _) (fun result => ?_)
    cases result with
    | Err e => exact pure_rule _
    | Ok byte =>
      split_ifs with h
      · exact bind_rule (throw_rule _) (fun _ => ih _ _)
      · exact bind_rule (pure_rule _) (fun _ => ih _ _)

theorem execHostIO_frame : Preserves (JoltISA.execHostIO) := by
  unfold JoltISA.execHostIO JoltISA.execHostIOWith
  refine bind_rule get_rule (fun config => ?_)
  dsimp only
  split
  · exact pure_rule _
  · refine bind_rule (pure_rule _) (fun _ => ?_)
    refine bind_rule (read_rule _) (fun callId => ?_)
    repeat' first
      | exact readHostBytes_frame _ _ _ _ _
      | exact read_rule _
      | exact pure_rule _
      | exact throw_rule _
      | exact modifyAdvice_rule _ (by intro s; rfl)
      | split
      | refine bind_rule ?_ (fun x => ?_)

end JoltHostFrame

namespace JoltNextPCFrame

theorem hostIOFrame_of_exec (instr : JoltISA.Instr) (s t : SailJoltState)
    (ops : AssumptionOperands) (ha : TraceAssumptions s ops)
    (hexec : JoltISA.execInstr instr s = .ok (.Retire_Success ()) t) :
    HostIOFrame instr s t := by
  cases instr with
  | VirtualHostIO dst src imm =>
    have hready : JoltHostFrame.Ready s :=
      ⟨ha.curPrivilege, ha.mstatusMprv⟩
    have hsail := JoltHostFrame.execHostIO_frame s t (.Retire_Success ()) hready hexec
    exact congrArg (fun sail : SailState => sail.regs.get? Register.nextPC) hsail
  | _ => trivial

theorem row {program : JoltProgram} (trace : JoltTrace program)
    (i : Fin trace.rows.size)
    (hjump : JoltMetadata.opcodeFlag
      (program.expandedBytecode[trace.rows[i].rowIndex].expandedInstruction.withRuntimeAdvice
        trace.rows[i].runtimeAdvice) .Jump = false)
    (hnot : BranchTaken
      (program.expandedBytecode[trace.rows[i].rowIndex].expandedInstruction.withRuntimeAdvice
        trace.rows[i].runtimeAdvice) trace.rows[i].preState = false) :
    trace.rows[i].postState.sail.regs.get? Register.nextPC =
      trace.rows[i].preState.sail.regs.get? Register.nextPC := by
  apply instruction _ _ _ (trace.assumptionOperands i) (trace.rowAssumptions i)
    _ hjump hnot _ trace.rows[i].executes
  · rw [JoltPCFrame.memoryWindows_withRuntimeAdvice]
    exact trace.ramAccessAssumed i
  · exact hostIOFrame_of_exec _ _ _ _ (trace.rowAssumptions i) trace.rows[i].executes

end JoltNextPCFrame
