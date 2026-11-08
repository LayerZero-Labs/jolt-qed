import JoltBytecode.HartConfig
import JoltBytecode.InstructionEquivalence.ProofSupport.BundleLemmas
import JoltBytecode.InstructionEquivalence.Instructions.System.Common

/-!
# One Sail step on Jolt's hart

`try_step` is the Sail model's step function: it checks for interrupts,
fetches and decodes one instruction, executes it, handles the result and
advances the PC. This file splits it into three parts on the states Jolt can
reach: the prelude (count the instruction, set `nextPC` to the fall-through
address), `execute`, and the result handling (`stepFinish`).

The split holds under `StepInvariant`: the hart is active, in M-mode, with
`mie = 0` (so no interrupt is ever pending) and no landing pad expected.
-/

open Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace Step

/-- State facts that make `try_step` a plain fetch-decode-execute step. -/
structure StepInvariant (s : SailState) : Prop where
  /-- Every register is present. Sail's initial state has all of them, and
  register writes only overwrite. -/
  present : ∀ r, Assumptions.SailRegReadable r s
  active : s.regs.get? Register.hart_state =
    some (HartState.HART_ACTIVE () : RegisterType Register.hart_state)
  machine : s.regs.get? Register.cur_privilege =
    some (Privilege.Machine : RegisterType Register.cur_privilege)
  /-- No interrupt is enabled. `mie` resets to zero and Jolt never writes it. -/
  mie_zero : s.regs.get? Register.mie = some (0 : RegisterType Register.mie)
  /-- No interrupt is delegated. Without S-mode Sail asserts this. -/
  mideleg_zero : s.regs.get? Register.mideleg = some (0 : RegisterType Register.mideleg)
  /-- `misa.C` is set, so compressed instructions are enabled. `misa` is not
  writable in this configuration. -/
  misa_c : ∃ m : RegisterType Register.misa,
    s.regs.get? Register.misa = some m ∧ _get_Misa_C m = 1#1
  /-- No landing pad is expected. Zicfilp is off, so nothing sets `elp`. -/
  elp_none : s.regs.get? Register.elp =
    some (landing_pad_bits_backwards landing_pad_expectation.NO_LP_EXPECTED :
      RegisterType Register.elp)

theorem readReg_present (r : Register) (s : SailState)
    (h : Assumptions.SailRegReadable r s) :
    ∃ v, (LeanRV64D.readReg r : SailM (RegisterType r)) s = .ok v s := by
  obtain ⟨v, hv⟩ := h.exists_value
  exact ⟨v, readReg_eq_of_get? r s v hv⟩

/-- With `mie = 0` nothing is pending, whatever `mip` and `mstatus` hold. -/
theorem dispatchInterrupt_run (s : SailState) (hinv : StepInvariant s) :
    dispatchInterrupt Privilege.Machine s = .ok none s := by
  obtain ⟨mip, hmip⟩ := readReg_present Register.mip s (hinv.present _)
  obtain ⟨ms, hms⟩ := readReg_present Register.mstatus s (hinv.present _)
  have hmie := readReg_eq_of_get? Register.mie s _ hinv.mie_zero
  have hdeleg := readReg_eq_of_get? Register.mideleg s _ hinv.mideleg_zero
  have hMM : (Privilege.Machine == Privilege.Machine) = true := rfl
  have hMS : (Privilege.Machine == Privilege.Supervisor) = false := rfl
  unfold dispatchInterrupt getPendingSet
  simp [hMM, hMS, HartConfig.currentlyEnabled_S_run, orM, andM, toBool, bind, EStateM.bind, pure,
    EStateM.pure, hmip, hms, hmie, hdeleg, LeanRV64D.sail_assert,
    Sail.ConcurrencyInterfaceV1.PreSail.sail_assert, zeros, BitVec.zero]

/-- No landing pad is expected. -/
theorem is_landing_pad_expected_run (s : SailState) (hinv : StepInvariant s) :
    is_landing_pad_expected () s = .ok false s := by
  have help := readReg_eq_of_get? Register.elp s _ hinv.elp_none
  unfold is_landing_pad_expected
  simp only [bind, EStateM.bind, help, pure, EStateM.pure]
  rfl

/-- Write one register directly. -/
def setReg (s : SailState) (r : Register) (v : RegisterType r) : SailState :=
  { s with regs := s.regs.insert r v }

theorem writeReg_run (s : SailState) (r : Register) (v : RegisterType r) :
    (LeanRV64D.writeReg r v : SailM Unit) s = .ok () (setReg s r v) := rfl

theorem setReg_get?_ne (s : SailState) {r r' : Register} (v : RegisterType r) (h : r ≠ r') :
    (setReg s r v).regs.get? r' = s.regs.get? r' :=
  System.extDHashMap_get?_insert_of_ne s.regs v h

theorem setReg_present (s : SailState) (r : Register) (v : RegisterType r)
    (h : ∀ r', Assumptions.SailRegReadable r' s) :
    ∀ r', Assumptions.SailRegReadable r' (setReg s r v) := by
  intro r'
  by_cases hr : r = r'
  · subst hr
    exact ⟨⟨v, by simp [setReg, Std.ExtDHashMap.get?_insert_self]⟩⟩
  · rw [show Assumptions.SailRegReadable r' (setReg s r v) ↔ Assumptions.SailRegReadable r' s from
      ⟨fun ⟨h'⟩ => ⟨by rwa [setReg_get?_ne s v hr] at h'⟩,
       fun ⟨h'⟩ => ⟨by rwa [setReg_get?_ne s v hr]⟩⟩]
    exact h r'

/-- Registers the invariant mentions. Writing any other register keeps it. -/
def invariantReg (r : Register) : Prop :=
  r = Register.hart_state ∨ r = Register.cur_privilege ∨ r = Register.mie ∨
    r = Register.mideleg ∨ r = Register.misa ∨ r = Register.elp

theorem StepInvariant.setReg {s : SailState} (hinv : StepInvariant s)
    (r : Register) (v : RegisterType r) (hr : ¬ invariantReg r) :
    StepInvariant (Step.setReg s r v) := by
  simp only [invariantReg, not_or] at hr
  obtain ⟨h1, h2, h3, h4, h6, h5⟩ := hr
  exact
    { present := setReg_present s r v hinv.present
      active := by rw [setReg_get?_ne s v h1]; exact hinv.active
      machine := by rw [setReg_get?_ne s v h2]; exact hinv.machine
      mie_zero := by rw [setReg_get?_ne s v h3]; exact hinv.mie_zero
      mideleg_zero := by rw [setReg_get?_ne s v h4]; exact hinv.mideleg_zero
      misa_c := by rw [setReg_get?_ne s v h6]; exact hinv.misa_c
      elp_none := by rw [setReg_get?_ne s v h5]; exact hinv.elp_none }

theorem hartSupports_C : hartSupports extension.Ext_C = true := by
  simp [hartSupports, LeanRV64D.Functions.not]

/-- Compressed instructions are enabled. -/
theorem currentlyEnabled_Zca_run (s : SailState) (hinv : StepInvariant s) :
    currentlyEnabled extension.Ext_Zca s = .ok true s := by
  obtain ⟨m, hm, hc⟩ := hinv.misa_c
  have hread := readReg_eq_of_get? Register.misa s m hm
  have hZca : hartSupports extension.Ext_Zca = true := by simp [hartSupports]
  unfold currentlyEnabled
  unfold currentlyEnabled
  simp [hZca, hartSupports_C, andM, toBool, bind, EStateM.bind, pure, EStateM.pure, hread, hc]

section GeneratedNames

open zvk_vsm4r_funct6
open zvk_vsha2_funct6
open zvk_vaesem_funct6
open zvk_vaesef_funct6
open zvk_vaesdm_funct6
open zvk_vaesdf_funct6
open zvabd_vwabda_func6
open zvabd_vabd_func6
open zicondop
open xRET_type
open wxfunct6
open wvxfunct6
open wvvfunct6
open wvfunct6
open wrsop
open write_kind
open wmvxfunct6
open wmvvfunct6
open vxsgfunct6
open vxmsfunct6
open vxmfunct6
open vxmcfunct6
open vxfunct6
open vxcmpfunct6
open vvmsfunct6
open vvmfunct6
open vvmcfunct6
open vvfunct6
open vvcmpfunct6
open vregno
open vregidx
open vmlsop
open vlewidth
open visgfunct6
open virtaddr
open vimsfunct6
open vimfunct6
open vimcfunct6
open vifunct6
open vicmpfunct6
open vfwunary0
open vfunary1
open vfunary0
open vfnunary0
open vextfunct6
open vector_support
open uop
open stateen_bit
open sopw
open sop
open seed_opst
open rounding_mode
open ropw
open rop
open rmvvfunct6
open rivvfunct6
open rfwvvfunct6
open rfvvfunct6
open regno
open regidx
open read_kind
open pte_check_failure
open pmpAddrMatch
open physaddr
open option
open nxsfunct6
open nxfunct6
open nvsfunct6
open nvfunct6
open ntl_type
open nisfunct6
open nifunct6
open mvxmafunct6
open mvxfunct6
open mvvmafunct6
open mvvfunct6
open mmfunct6
open misaligned_fault
open mem_payload
open maskfunct3
open landing_pad_expectation
open iop
open instruction
open indexed_mop
open fwvvmafunct6
open fwvvfunct6
open fwvfunct6
open fwvfmafunct6
open fwvffunct6
open fwffunct6
open fvvmfunct6
open fvvmafunct6
open fvvfunct6
open fvfmfunct6
open fvfmafunct6
open fvffunct6
open fregno
open fregidx
open float_class
open f_un_x_op_H
open f_un_x_op_D
open f_un_rm_xf_op_S
open f_un_rm_xf_op_H
open f_un_rm_xf_op_D
open f_un_rm_fx_op_S
open f_un_rm_fx_op_H
open f_un_rm_fx_op_D
open f_un_rm_ff_op_S
open f_un_rm_ff_op_H
open f_un_rm_ff_op_D
open f_un_op_x_S
open f_un_op_f_S
open f_un_f_op_H
open f_un_f_op_D
open f_madd_op_S
open f_madd_op_H
open f_madd_op_D
open f_bin_x_op_H
open f_bin_x_op_D
open f_bin_rm_op_S
open f_bin_rm_op_H
open f_bin_rm_op_D
open f_bin_op_x_S
open f_bin_op_f_S
open f_bin_f_op_H
open f_bin_f_op_D
open extop_zbb
open extension
open exception
open ctl_result
open csrop
open cregidx
open checked_cbop
open cfregidx
open cbop_zicbop
open cbop_zicbom
open cbie
open cacheop
open bropw_zbb
open brop_zbs
open brop_zbkb
open brop_zbb
open breakpoint_cause
open bop
open biop_zbs
open biop
open barrier_kind
open amoop
open agtype
open XtvecModeReservedBehavior
open XenvcfgCbieReservedBehavior
open WaitReason
open VectorHalf
open TrapVectorMode
open TrapCause
open Step
open Software_Check_Code
open Signedness
open SWCheckCodes
open SATPMode
open Reservability
open Register
open RV32ZdinxOddRegisterReservedBehavior
open Privilege
open PmpWriteOnlyReservedBehavior
open PmpAddrMatchType
open PTW_Error
open PTE_Check
open MemoryAccessType
open InterruptType
open ISA_Format
open HartState
open FetchResult
open FeatureEnabledResult
open FcsrRmReservedBehavior
open Ext_DataAddr_Check
open ExtStatus
open ExtContextPolicy
open ExecutionResult
open ExceptionType
open CSRAccessType
open AtomicSupport
open Architecture
open AmocasOddRegisterReservedBehavior

/-- `execute`, followed by the expansion of a compressed instruction into the
base instruction it stands for, as `run_hart_active` does it. -/
def executeFull (ast : instruction) : SailM ExecutionResult := do
  match (← execute ast) with
  | .ExecuteAs other_inst => execute other_inst
  | result => pure result

/-- Everything `try_step` does after executing the instruction: handle the
result, then advance the PC and count the instruction. Copied from
`try_step`. -/
def stepFinish (step_val : Step) : SailM Bool := do
  match step_val with
  | .Step_Pending_Interrupt (intr, priv) =>
    (do
      let _ : Unit :=
        if ((get_config_print_instr ()) : Bool)
        then (print_bits "Handling interrupt: " (interruptType_bits_forwards intr))
        else ()
      (handle_interrupt intr priv))
  | .Step_Ext_Fetch_Failure e => (pure (ext_handle_fetch_check_error e))
  | .Step_Fetch_Failure (vaddr, e) => (handle_exception (bits_of_virtaddr vaddr) e)
  | .Step_Waiting _ =>
    LeanRV64D.sail_assert (hart_is_waiting (← readReg hart_state)) "cannot be Waiting in a non-Wait state"
  | .Step_Execute (.Retire_Success (), _) =>
    LeanRV64D.sail_assert (hart_is_active (← readReg hart_state)) "postlude/step.sail:211.74-211.75"
  | .Step_Execute (.ExecuteAs _, _) => LeanRV64D.sail_assert false "postlude/step.sail:213.49-213.50"
  | .Step_Execute (.Trap (priv, ctl, pc), _) => (set_next_pc (← (exception_handler priv ctl pc)))
  | .Step_Execute (.Memory_Exception (vaddr, e), _) => (handle_exception (bits_of_virtaddr vaddr) e)
  | .Step_Execute (.Illegal_Instruction (), instbits) =>
    (handle_exception (zero_extend (m := 64) instbits) (E_Illegal_Instr ()))
  | .Step_Execute (.Virtual_Instruction (), instbits) =>
    (handle_exception (zero_extend (m := 64) instbits) (E_Virtual_Instr ()))
  | .Step_Execute (.Enter_Wait wr, instbits) =>
    (do
      if ((wait_is_nop wr) : Bool)
      then LeanRV64D.sail_assert (hart_is_active (← readReg hart_state)) "postlude/step.sail:223.41-223.42"
      else
        (do
          if ((get_config_print_instr ()) : Bool)
          then
            (pure (print_endline
                (HAppend.hAppend "entering "
                  (HAppend.hAppend (wait_name_forwards wr)
                    (HAppend.hAppend " state at PC " (BitVec.toFormatted (← readReg PC)))))))
          else (pure ())
          writeReg hart_state (HART_WAITING (wr, instbits))))
  | .Step_Execute (.Ext_CSR_Check_Failure (), _) => (pure (ext_check_CSR_fail ()))
  | .Step_Execute (.Ext_ControlAddr_Check_Failure e, _) => (pure (ext_handle_control_check_error e))
  | .Step_Execute (.Ext_DataAddr_Check_Failure e, _) => (pure (ext_handle_data_check_error e))
  | .Step_Execute (.Ext_XRET_Priv_Failure (), _) => (pure (ext_fail_xret_priv ()))
  match (← readReg hart_state) with
  | .HART_WAITING _ => (pure true)
  | .HART_ACTIVE () =>
    (do
      (tick_pc ())
      let retired : Bool :=
        match step_val with
        | .Step_Execute (.Retire_Success (), g__0) => true
        | .Step_Execute (.Enter_Wait wr, g__1) =>
          (if ((wait_is_nop wr) : Bool)
          then true
          else false)
        | _ => false
      if ((←((pure retired) <&&> (do
           readReg minstret_increment))) : Bool)
      then writeReg minstret (BitVec.addInt (← readReg minstret) 1)
      else (pure ())
      if ((get_config_rvfi ()) : Bool)
      then
        writeReg rvfi_pc_data (Sail.BitVec.updateSubrange (← readReg rvfi_pc_data) 127 64
          (zero_extend (m := 64) (← (get_arch_pc ()))))
      else (pure ())
      let _ : Unit := (ext_post_step_hook ())
      (pure false))

end GeneratedNames

/-- The state after `try_step`'s prelude: `minstret_increment` holds whether
this instruction counts, and `nextPC` the fall-through address. -/
def preludeState (s : SailState) (inc : Bool) (pc : BitVec 64) (len : Int) : SailState :=
  setReg (setReg s Register.minstret_increment inc) Register.nextPC (BitVec.addInt pc len)

/-- The execute-and-finish part of `try_step`, from the post-prelude state. -/
def executeAndFinish (ast : instruction) (bits : BitVec 32) : SailM Bool := do
  let r ← executeFull ast
  stepFinish (.Step_Execute (r, bits))

/-- One `try_step` of a 32-bit instruction on Jolt's hart: run the prelude,
execute the decoded instruction, then `stepFinish`. -/
theorem try_step_base (n : Nat) (s : SailState) (hinv : StepInvariant s)
    (inc : Bool) (hinc : should_inc_minstret Privilege.Machine s = .ok inc s)
    (pc : BitVec 64) (hpc : s.regs.get? Register.PC = some pc)
    (w : BitVec 32) (ast : instruction)
    (hfetch : fetch () (setReg s Register.minstret_increment inc) =
      .ok (.F_Base w) (setReg s Register.minstret_increment inc))
    (hdec : ext_decode w (setReg s Register.minstret_increment inc) =
      .ok ast (setReg s Register.minstret_increment inc)) :
    try_step n false s =
      executeAndFinish ast (zero_extend (m := 32) w) (preludeState s inc pc 4) := by
  have hinv1 := hinv.setReg Register.minstret_increment inc (by simp [invariantReg])
  have hpriv := readReg_eq_of_get? Register.cur_privilege s _ hinv.machine
  have hhart := readReg_eq_of_get? Register.hart_state _ _ hinv1.active
  have hpriv1 := readReg_eq_of_get? Register.cur_privilege _ _ hinv1.machine
  have hpc1 := readReg_eq_of_get? Register.PC (setReg s Register.minstret_increment inc) pc
    (by rw [setReg_get?_ne _ _ (by decide)]; exact hpc)
  unfold try_step run_hart_active
  unfold SailME.run Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.run
  simp only [bind, EStateM.bind, hpriv, hinc, writeReg_run, hhart,
    ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont, ExceptT.pure, ExceptT.lift,
    liftM, monadLift, MonadLift.monadLift, EStateM.map, Functor.map, pure,
    hpriv1, dispatchInterrupt_run _ hinv1, hfetch, ext_fetch_hook, hdec,
    is_landing_pad_expected_run _ hinv1, get_config_print_instr, hpc1, is_lpad_instruction,
    Bool.false_eq_true, ↓reduceIte, Bool.false_and]
  unfold executeAndFinish executeFull preludeState
  simp only [bind, EStateM.bind]
  cases he : execute ast (setReg (setReg s Register.minstret_increment inc) Register.nextPC
      (BitVec.addInt pc 4)) with
  | error e s1 => rfl
  | ok a s1 =>
    cases a with
    | ExecuteAs other =>
      simp only [EStateM.map]
      cases execute other s1 <;> rfl
    | _ => first | rfl | (simp only [EStateM.map]; rfl)

/-- One `try_step` of a compressed instruction: as `try_step_base`, with the
fall-through address two bytes on. -/
theorem try_step_compressed (n : Nat) (s : SailState) (hinv : StepInvariant s)
    (inc : Bool) (hinc : should_inc_minstret Privilege.Machine s = .ok inc s)
    (pc : BitVec 64) (hpc : s.regs.get? Register.PC = some pc)
    (h : BitVec 16) (ast : instruction)
    (hfetch : fetch () (setReg s Register.minstret_increment inc) =
      .ok (.F_RVC h) (setReg s Register.minstret_increment inc))
    (hdec : ext_decode_compressed h (setReg s Register.minstret_increment inc) =
      .ok ast (setReg s Register.minstret_increment inc)) :
    try_step n false s =
      executeAndFinish ast (zero_extend (m := 32) h) (preludeState s inc pc 2) := by
  have hinv1 := hinv.setReg Register.minstret_increment inc (by simp [invariantReg])
  have hpriv := readReg_eq_of_get? Register.cur_privilege s _ hinv.machine
  have hhart := readReg_eq_of_get? Register.hart_state _ _ hinv1.active
  have hpriv1 := readReg_eq_of_get? Register.cur_privilege _ _ hinv1.machine
  have hpc1 := readReg_eq_of_get? Register.PC (setReg s Register.minstret_increment inc) pc
    (by rw [setReg_get?_ne _ _ (by decide)]; exact hpc)
  unfold try_step run_hart_active
  unfold SailME.run Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.run
  simp only [bind, EStateM.bind, hpriv, hinc, writeReg_run, hhart,
    ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont, ExceptT.pure, ExceptT.lift,
    liftM, monadLift, MonadLift.monadLift, EStateM.map, Functor.map, pure,
    hpriv1, dispatchInterrupt_run _ hinv1, hfetch, ext_fetch_hook, hdec,
    is_landing_pad_expected_run _ hinv1, get_config_print_instr, hpc1,
    currentlyEnabled_Zca_run _ hinv1, Bool.false_eq_true, ↓reduceIte]
  unfold executeAndFinish executeFull preludeState
  simp only [bind, EStateM.bind]
  cases he : execute ast (setReg (setReg s Register.minstret_increment inc) Register.nextPC
      (BitVec.addInt pc 2)) with
  | error e s1 => rfl
  | ok a s1 =>
    cases a with
    | ExecuteAs other =>
      simp only [EStateM.map]
      cases execute other s1 <;> rfl
    | _ => first | rfl | (simp only [EStateM.map]; rfl)

end Step

end
