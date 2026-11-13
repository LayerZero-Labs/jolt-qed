import JoltConstraints.WholeRun.Basic
import JoltConstraints.WholeRun.Bridge
import JoltConstraints.WholeRun.Init
import JoltConstraints.nextpc_frame
import JoltConstraints.inline_rows_ok
import JoltBytecode.Step.Ecall

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail
  LeanRV64D LeanRV64D.Functions

set_option autoImplicit false

noncomputable section

namespace WholeRun

/-- The legal persistent system values: mstatus contains only MIE/MPIE, mtvec
has mode 0 or 1, mepc is even, and a doubleword reservation equals the word one.
For example, zero in every virtual register satisfies all four conditions. -/
structure SystemInv (js : SailJoltState) : Prop where
  mstatus_bits : js.vregs JoltISA.mstatusVReg &&& ~~~(0x88#64) = 0#64
  mtvec_mode : (js.vregs JoltISA.trapHandlerVReg).getLsbD 1 = false
  mepc_align : (js.vregs JoltISA.mepcVReg).getLsbD 0 = false
  reservation_pair : js.vregs 33#7 = 0#64 ∨ js.vregs 33#7 = js.vregs 32#7

/-- Preserving the eight projected virtual registers preserves the system
invariant; for example, writing scratch v40 preserves it. -/
theorem SystemInv.of_preserved {s t : SailJoltState} (h : SystemInv s)
    (hf : Projection.ProjectedVRegsPreserved s t) : SystemInv t := by
  rcases hf with ⟨ht, _, he, _, _, hm, hw, hd⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hm]; exact h.mstatus_bits
  · rw [ht]; exact h.mtvec_mode
  · rw [he]; exact h.mepc_align
  · change t.vregs 32#7 = s.vregs 32#7 at hw
    change t.vregs 33#7 = s.vregs 33#7 at hd
    simpa only [hw, hd] using h.reservation_pair

/-- Equal virtual-register files have the same system invariant; for example,
advancing the PC changes no virtual register. -/
theorem SystemInv.of_vregs {s t : SailJoltState} (h : SystemInv s)
    (hv : t.vregs = s.vregs) : SystemInv t := by
  apply h.of_preserved
  simp [Projection.ProjectedVRegsPreserved, hv]

/-- Jolt initializes every virtual register to zero, so its initial state has
legal system values, even before executing its first instruction. -/
theorem SystemInv.init_state (entry : BitVec 64) (ram : Array (BitVec 8))
    (device : JoltDevice) (tape : JoltAdviceTape) (hostIO : JoltHostIOConfig := {}) :
    SystemInv (init_state entry ram device tape hostIO) := by
  constructor <;> simp [_root_.init_state]

/-- An honest trace begins with legal system values; for example, both
reservation virtual registers initially contain zero. -/
theorem SystemInv.initialState {inst : JoltInstance SourceInstruction}
    {inputs : JoltPrivateInputs} (trace : HonestTrace inst inputs) :
    SystemInv trace.initialState := by
  obtain ⟨ram, device, tape, he⟩ := initial_state_spec inst inputs _ trace.initialized
  rw [he]
  exact SystemInv.init_state _ _ _ _

private def VFrame (r : JoltISA.VReg) (s t : SailJoltState) : Prop :=
  t.vregs r = s.vregs r

private theorem vframe_refl (r : JoltISA.VReg) (s : SailJoltState) : VFrame r s s := rfl

private theorem vframe_trans (r : JoltISA.VReg) (s t u : SailJoltState)
    (h : VFrame r s t) (k : VFrame r t u) : VFrame r s u := k.trans h

private theorem lift_vframe {α : Type} (r : JoltISA.VReg) (m : SailM α) :
    StatePreservation.Preserves (VFrame r) (liftSail m) := by
  intro s t value h
  unfold liftSail at h
  cases hm : m s.sail <;> simp only [hm] at h
  · cases h; rfl
  · cases h

private theorem read_vframe (r : JoltISA.VReg) (src : JoltISA.Src) :
    StatePreservation.Preserves (VFrame r) (JoltISA.readSrc src) := by
  intro s t value h
  obtain ⟨rfl, _⟩ := lookup_readSrc_value src s t value h
  rfl

private theorem write_vframe (r : JoltISA.VReg) (dst : JoltISA.Dst)
    (value : BitVec 64) (hne : dst ≠ .vreg r) :
    StatePreservation.Preserves (VFrame r) (JoltISA.writeDst dst value) := by
  cases dst with
  | xreg rd => exact lift_vframe r (wX_bits rd value)
  | vreg vr =>
    intro s t result h
    simp only [JoltISA.writeDst, writeVReg] at h
    split at h
    · cases h
    · cases h
      exact if_neg (fun he => hne (congrArg JoltISA.Dst.vreg he.symm))

private theorem load_vframe (r : JoltISA.VReg) (addr : BitVec 64) :
    StatePreservation.Preserves (VFrame r) (JoltISA.Mmu.load_doubleword addr) := by
  intro s t value h
  rw [JoltISA.Mmu.load_doubleword_state h]
  rfl

private theorem store_vframe (r : JoltISA.VReg) (addr value : BitVec 64) :
    StatePreservation.Preserves (VFrame r) (JoltISA.Mmu.store_doubleword addr value) := by
  intro s t result h
  exact congrFun (JoltISA.Mmu.store_doubleword_regs h).2 r

private theorem row_vframe (i : JoltISA.Instr) (r : JoltISA.VReg)
    (hne : i.destination? ≠ some (.vreg r)) :
    StatePreservation.Preserves (VFrame r) (JoltISA.execInstr i) := by
  cases i
  case VirtualAdviceLoad dst count =>
    intro s t result h
    simp only [JoltISA.Instr.destination?, ne_eq, Option.some.injEq] at hne
    simp only [JoltISA.execInstr] at h
    split at h
    · cases h
    · rename_i value tape htape
      have hf := (StatePreservation.bind_rule (vframe_trans r)
        (write_vframe r dst _ hne)
        (fun _ => StatePreservation.pure_rule (vframe_refl r) _)
        { s with adviceTape := tape } t result h)
      exact hf
  case VirtualHostIO =>
    intro s t result h
    exact congrFun (execHostIO_keeps_state s t result h).2 r
  all_goals simp only [JoltISA.Instr.destination?, ne_eq, Option.some.injEq] at hne
  all_goals simp only [JoltISA.execInstr]
  all_goals
    preservation_auto [read_vframe r _, write_vframe r _ _ (by assumption),
      lift_vframe r _, load_vframe r _, store_vframe r _ _,
      StatePreservation.pure_rule (vframe_refl r) _,
      StatePreservation.throw_rule (VFrame r) _,
      StatePreservation.get_rule (vframe_refl r)]
      using (StatePreservation.bind_rule (vframe_trans r))

private def ProgramAvoids (r : JoltISA.VReg) : JoltISA.Program → Prop
  | .done _ => True
  | .instr i rest => i.destination? ≠ some (.vreg r) ∧ ProgramAvoids r rest

private theorem program_vframe (r : JoltISA.VReg) (p : JoltISA.Program)
    (hsafe : ProgramAvoids r p) :
    StatePreservation.Preserves (VFrame r) (JoltISA.execProgram p) := by
  induction p with
  | done value => exact StatePreservation.pure_rule (vframe_refl r) value
  | instr i rest ih =>
    simp only [JoltISA.execProgram]
    apply StatePreservation.bind_rule (vframe_trans r) (row_vframe i r hsafe.1)
    intro result
    split
    · exact ih hsafe.2
    · exact StatePreservation.pure_rule (vframe_refl r) _

@[simp] private theorem source_vreg (r : JoltISA.VReg) (s : SailJoltState) :
    JoltISA.sourceValue (.vreg r) s = s.vregs r := rfl

@[simp] private theorem source_zreg (s : SailJoltState) :
    JoltISA.sourceValue (.xreg (.Regidx 0#5)) s = 0#64 := rfl

@[simp] private theorem source_zero (r : regidx) (s : SailJoltState)
    (hz : JoltISA.isX0 r = true) : JoltISA.sourceValue (.xreg r) s = 0#64 := by
  rw [JoltISA.eq_regidx_zero_of_isX0_eq_true hz]
  rfl

private theorem mtvec_mask_bit (src : BitVec 64) :
    (src[1] && (jolt_virtual_shift_right_bitmask_value (src &&& 2#64))[1]) = false := by
  have h : (src.getLsbD 1 &&
      (jolt_virtual_shift_right_bitmask_value (src &&& 2#64)).getLsbD 1) = false := by
    rw [SystemProofs.mtvec_mode_mask]
    cases hb : src.getLsbD 1 <;> simp [hb]
  simpa using h

private theorem masked_and (old extra : BitVec 64)
    (h : old &&& ~~~(0x88#64) = 0#64) :
    old &&& (extra &&& ~~~(0x88#64)) = 0#64 := by
  calc
    _ = (old &&& ~~~(0x88#64)) &&& extra := by ac_rfl
    _ = 0#64 := by rw [h, BitVec.zero_and]

open Lean Elab Tactic in
elab "system_guard_row " h:ident : tactic => withMainContext do
  let decl ← (← getFVarId h).getDecl
  let some (_, lhs, _) := decl.type.eq? | throwError "expected an execution equality"
  unless lhs.isAppOf ``JoltISA.execProgram do throwError "expected a program"
  let p ← Lean.Meta.whnf lhs.getAppArgs[0]!
  unless p.isAppOf ``JoltISA.Program.instr do throwError "no row remains"

open Lean Elab Tactic in
elab "system_register_reads " h:ident : tactic => withMainContext do
  let decl ← (← getFVarId h).getDecl
  let some (_, lhs, _) := decl.type.eq? | throwError "expected an execution equality"
  let computation := if lhs.isAppOf ``EStateM.run then
      lhs.getAppArgs[lhs.getAppArgs.size - 2]! else lhs
  unless computation.isAppOf ``JoltISA.execInstr do throwError "expected a row"
  let instr := computation.getAppArgs[0]!
  let count := if instr.isAppOf ``JoltISA.Instr.XOR || instr.isAppOf ``JoltISA.Instr.AND ||
      instr.isAppOf ``JoltISA.Instr.OR || instr.isAppOf ``JoltISA.Instr.ANDN then 2 else 1
  evalTactic (← `(tactic| simp only [JoltISA.execInstr, EStateM.run] at $h:ident))
  for _ in [:count] do
    evalTactic (← `(tactic| replace $h := lookup_read_bind _ _ _ _ _ $h))

local macro "csr_rows" h:ident source:ident : tactic =>
  `(tactic|
    repeat' (
     simp (config := { failIfUnchanged := false }) only [EStateM.run] at $h:ident
     first
     | rw [SystemProofs.csrReadInto_run] at $h:ident
     | (
       system_guard_row $h
       replace $h := JoltISA.execProgram_instr_run_retire_inv _ _ _ _ $h
       rcases ($h:ident) with ⟨u, hstep, $h⟩
       system_register_reads hstep
       simp [($source:ident), JoltISA.writeDst, writeVReg, liftSail, wX_bits_stateAfterWrite,
         bind, EStateM.bind, pure, EStateM.pure, get, getThe, MonadStateOf.get,
         EStateM.get, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet,
         JoltISA.inlineTmp0, JoltISA.inlineTmp1, JoltISA.inlineTmp,
         JoltISA.inlineRegisterBase, JoltISA.numReservedVirtualRegisters,
         JoltISA.riscvRegisterBase, JoltISA.riscvRegisterCount,
         JoltISA.mstatusVReg, JoltISA.trapHandlerVReg, JoltISA.mepcVReg,
         JoltISA.mscratchVReg, JoltISA.mcauseVReg, JoltISA.mtvalVReg,
         JoltISA.SystemCSR.vreg, BitVec.reduceToNat, Nat.reduceLT,
         Bool.false_eq_true, ↓reduceIte] at hstep
       cases hstep)))

local macro "csr_clean_values" source:ident hm:ident ht:ident he:ident hp:ident : tactic =>
  `(tactic| (
    all_goals constructor
    all_goals
      simp [Riscv.andi, JoltISA.addWide_low, ($source:ident),
        SystemProofs.setCsr, SystemProofs.immediateSwapValue, SystemProofs.swapValue,
        SystemProofs.bitUpdate, JoltISA.csrImmediateMask,
        JoltISA.mstatusVReg, JoltISA.trapHandlerVReg, JoltISA.mepcVReg,
        JoltISA.mscratchVReg, JoltISA.mcauseVReg, JoltISA.mtvalVReg,
        JoltISA.SystemCSR.vreg, JoltISA.riscvRegisterBase, JoltISA.riscvRegisterCount,
        JoltISA.inlineTmp0, JoltISA.inlineTmp1, JoltISA.inlineTmp,
        JoltISA.inlineRegisterBase, JoltISA.numReservedVirtualRegisters,
        BitVec.and_assoc] at *
    all_goals
      simp (config := { failIfUnchanged := false })
        [Riscv.ori, ($hm:ident), ($ht:ident), ($he:ident), ($hp:ident),
          BitVec.and_or_distrib_right, BitVec.and_assoc, masked_and, mtvec_mask_bit]
    all_goals first | assumption | skip))

private theorem csr_swap_preserves (csr : JoltISA.SystemCSR) (rs1 rd : regidx)
    (s t : SailJoltState) (hs : SystemInv s)
    (hrun : JoltISA.execProgram (JoltISA.csrrwProgram csr rs1 rd) s =
      .ok RETIRE_SUCCESS t) : SystemInv t := by
  have hm := hs.mstatus_bits
  have ht := hs.mtvec_mode
  have he := hs.mepc_align
  have hp := hs.reservation_pair
  have hsource (regs : JoltISA.VReg → BitVec 64) :
      JoltISA.sourceValue (.xreg rs1) { s with vregs := regs } =
        JoltISA.sourceValue (.xreg rs1) s := rfl
  cases csr
  all_goals unfold JoltISA.csrrwProgram at hrun
  all_goals simp only [JoltISA.SystemCSR.vreg, reduceCtorEq, false_and, true_and,
    ite_false] at hrun
  all_goals split_ifs at hrun
  all_goals csr_rows hrun hsource
  all_goals simp (config := { failIfUnchanged := false }) only
    [JoltISA.execProgram, pure, EStateM.pure] at hrun
  all_goals cases hrun
  csr_clean_values hsource hm ht he hp
  all_goals
    have hz : JoltISA.isX0 rs1 = true := by assumption
    simp [hz]

private theorem csr_bit_preserves (clear : Bool) (csr : JoltISA.SystemCSR)
    (rs1 rd : regidx) (s t : SailJoltState) (hs : SystemInv s)
    (hrun : JoltISA.execProgram (JoltISA.csrBitUpdateProgram clear csr rs1 rd) s =
      .ok RETIRE_SUCCESS t) : SystemInv t := by
  have hm := hs.mstatus_bits
  have ht := hs.mtvec_mode
  have he := hs.mepc_align
  have hp := hs.reservation_pair
  have hsource (regs : JoltISA.VReg → BitVec 64) :
      JoltISA.sourceValue (.xreg rs1) { s with vregs := regs } =
        JoltISA.sourceValue (.xreg rs1) s := rfl
  cases csr <;> cases clear
  all_goals simp only [JoltISA.csrBitUpdateProgram, JoltISA.SystemCSR.vreg,
    Bool.not_false, Bool.not_true, Bool.false_and, Bool.true_and, decide_true,
    decide_false, reduceCtorEq, ite_false, ite_true] at hrun
  all_goals split_ifs at hrun
  all_goals csr_rows hrun hsource
  all_goals simp (config := { failIfUnchanged := false }) only
    [JoltISA.execProgram, pure, EStateM.pure] at hrun
  all_goals cases hrun
  csr_clean_values hsource hm ht he hp
  all_goals exact masked_and _ _ hm

private theorem bit_one_of_mask_zero (v : BitVec 64) (h : v &&& 2#64 = 0#64) :
    v.getLsbD 1 = false := by
  simpa using congrArg (fun x : BitVec 64 => x.getLsbD 1) h

private theorem csr_immediate_swap_preserves (csr : JoltISA.SystemCSR)
    (imm : BitVec 5) (rd : regidx) (s t : SailJoltState) (hs : SystemInv s)
    (hrun : JoltISA.execProgram (JoltISA.csrrwiProgram csr imm rd) s =
      .ok RETIRE_SUCCESS t) : SystemInv t := by
  rw [SystemProofs.csrrwiProgram_run] at hrun
  cases hrun
  have hm := hs.mstatus_bits
  have ht := hs.mtvec_mode
  have he := hs.mepc_align
  have hp := hs.reservation_pair
  cases csr
  csr_clean_values source_vreg hm ht he hp
  split_ifs with hmode
  · simpa using bit_one_of_mask_zero (imm.zeroExtend 64) hmode
  · simp

private theorem csr_immediate_bit_preserves (clear : Bool) (csr : JoltISA.SystemCSR)
    (imm : BitVec 5) (rd : regidx) (s t : SailJoltState) (hs : SystemInv s)
    (hrun : JoltISA.execProgram (JoltISA.csrImmediateBitUpdateProgram clear csr imm rd) s =
      .ok RETIRE_SUCCESS t) : SystemInv t := by
  rw [SystemProofs.csrImmediateBitUpdateProgram_run] at hrun
  cases hrun
  have hm := hs.mstatus_bits
  have ht := hs.mtvec_mode
  have he := hs.mepc_align
  have hp := hs.reservation_pair
  cases csr <;> cases clear
  csr_clean_values source_vreg hm ht he hp
  all_goals first
    | exact masked_and _ _ hm
    | (split_ifs <;> simp)

private def AvoidsWindow (lo hi : Nat) (p : JoltISA.Program) : Prop :=
  ∀ r : JoltISA.VReg, lo ≤ r.toNat → r.toNat < hi → ProgramAvoids r p

private theorem outside_window (lo hi : Nat) (r : JoltISA.VReg)
    (hlo : lo ≤ r.toNat) (hhi : r.toNat < hi) (n : Nat)
    (hn : n < lo ∨ hi ≤ n) (hbound : n < 128) : BitVec.ofNat 7 n ≠ r := by
  intro h
  have he := congrArg BitVec.toNat h
  change n % 128 = r.toNat at he
  rw [Nat.mod_eq_of_lt hbound] at he
  omega

private theorem window_preserves (p : JoltISA.Program) (s t : SailJoltState)
    (hsafe : AvoidsWindow 32 40 p) (hs : SystemInv s)
    (hrun : JoltISA.execProgram p s = .ok RETIRE_SUCCESS t) : SystemInv t := by
  have keep (r : JoltISA.VReg) (hlo : 32 ≤ r.toNat) (hhi : r.toNat < 40) :
      t.vregs r = s.vregs r := program_vframe r p (hsafe r hlo hhi) s t _ hrun
  apply hs.of_preserved
  exact ⟨keep _ (by decide) (by decide), keep _ (by decide) (by decide),
    keep _ (by decide) (by decide), keep _ (by decide) (by decide),
    keep _ (by decide) (by decide), keep _ (by decide) (by decide),
    keep _ (by decide) (by decide), keep _ (by decide) (by decide)⟩

private theorem ecall_status_bits (raw : BitVec 64) :
    ((raw &&& 8#64) * 16#64) &&& ~~~(0x88#64) = 0#64 := by
  rw [show 8#64 = (1#64 <<< 3) from rfl, SystemProofs.and_singleBit]
  cases hb : raw.getLsbD 3 <;> simp [hb]

private theorem mret_status_bits (raw : BitVec 64)
    (hm : raw &&& ~~~(0x88#64) = 0#64) :
    ((raw >>> 4) ||| 0x80#64) &&& ~~~(0x88#64) = 0#64 := by
  have he : raw &&& 0x88#64 = raw := by
    simpa using BitVec.and_not_eq_self_of_and_eq_zero raw (~~~(0x88#64)) hm
  rw [← he]
  simp [BitVec.ushiftRight_and_distrib, BitVec.and_or_distrib_right, BitVec.and_assoc]

private theorem ecall_preserves (s : SailJoltState) (pc next : BitVec 64)
    (hs : SystemInv s) (hpc : pc.getLsbD 0 = false) :
    SystemInv (SystemProofs.ecallPost s pc next) := by
  have hm := ecall_status_bits (s.vregs JoltISA.mstatusVReg)
  have ht := hs.mtvec_mode
  have he := hpc
  have hp := hs.reservation_pair
  csr_clean_values source_vreg hm ht he hp

private theorem reserve_pair (double : Bool) (rs1 : regidx) (s t : SailJoltState)
    (hrun : JoltISA.execProgram (SystemProofs.lrReserveRows double rs1) s =
      .ok RETIRE_SUCCESS t) : t.vregs 33#7 = 0#64 ∨ t.vregs 33#7 = t.vregs 32#7 := by
  have hsource (regs : JoltISA.VReg → BitVec 64) :
      JoltISA.sourceValue (.xreg rs1) { s with vregs := regs } =
        JoltISA.sourceValue (.xreg rs1) s := rfl
  cases double
  all_goals simp only [SystemProofs.lrReserveRows, Bool.false_eq_true, ite_true, ite_false] at hrun
  all_goals csr_rows hrun hsource
  all_goals simp only [JoltISA.execProgram, pure, EStateM.pure] at hrun
  all_goals cases hrun
  all_goals simp [JoltISA.addWide_low, hsource,
    show sign_extend (m := 64) (0#12) = 0#64 from rfl]

private inductive PairPlan : JoltISA.Program → Prop where
  | reserve (double : Bool) (rs1 : regidx) (rest : JoltISA.Program)
      (hsafe : ProgramAvoids 32#7 rest ∧ ProgramAvoids 33#7 rest) :
      PairPlan ((SystemProofs.lrReserveRows double rs1).append rest)
  | row (i : JoltISA.Instr) (rest : JoltISA.Program) (htail : PairPlan rest) :
      PairPlan (.instr i rest)

private theorem pairPlan_pair (p : JoltISA.Program) (hp : PairPlan p)
    (s t : SailJoltState) (hrun : JoltISA.execProgram p s = .ok RETIRE_SUCCESS t) :
    t.vregs 33#7 = 0#64 ∨ t.vregs 33#7 = t.vregs 32#7 := by
  induction hp generalizing s t with
  | reserve double rs1 rest hsafe =>
    obtain ⟨u, hreserve, hrest⟩ := JoltISA.execProgram_append_succeeds_inv _ _ s t hrun
    have hpair := reserve_pair double rs1 s u hreserve
    have hw := program_vframe 32#7 rest hsafe.1 u t _ hrest
    have hd := program_vframe 33#7 rest hsafe.2 u t _ hrest
    change t.vregs 32#7 = u.vregs 32#7 at hw
    change t.vregs 33#7 = u.vregs 33#7 at hd
    simpa only [hw, hd] using hpair
  | row i rest htail ih =>
    obtain ⟨u, _, hrest⟩ := JoltISA.execProgram_instr_run_retire_inv i rest s t hrun
    exact ih u t hrest

private theorem reservation_pair_plan (store double : Bool) (rd rs1 rs2 : regidx) :
    PairPlan (if store then SystemProofs.scRows double rd rs1 rs2
      else SystemProofs.lrRows double rd rs1 rs2) := by
  cases store <;> cases double
  all_goals simp only [SystemProofs.scRows, SystemProofs.lrRows,
    Bool.false_eq_true, ite_true, ite_false]
  all_goals simp only [JoltISA.lrwProgramAuto, JoltISA.lrdProgramAuto,
    JoltISA.scwProgramAuto, JoltISA.scdProgramAuto]
  all_goals split
  all_goals repeat' first
    | exact PairPlan.reserve false _ _
        (by simp [ProgramAvoids, JoltISA.Instr.destination?])
    | exact PairPlan.reserve true _ _
        (by simp [ProgramAvoids, JoltISA.Instr.destination?])
    | apply PairPlan.row

private theorem reservation_csr_avoids (store double : Bool) (rd rs1 rs2 : regidx) :
    AvoidsWindow 34 40 (if store then SystemProofs.scRows double rd rs1 rs2
      else SystemProofs.lrRows double rd rs1 rs2) := by
  intro r hlo hhi
  cases store <;> cases double
  all_goals simp only [SystemProofs.scRows, SystemProofs.lrRows,
    Bool.false_eq_true, ite_true, ite_false]
  all_goals simp only [JoltISA.lrwProgramAuto, JoltISA.lrdProgramAuto,
    JoltISA.scwProgramAuto, JoltISA.scdProgramAuto]
  all_goals split <;> simp [ProgramAvoids, JoltISA.Instr.destination?,
    outside_window 34 40 r hlo hhi]

private theorem reservation_preserves (store double : Bool) (rd rs1 rs2 : regidx)
    (s t : SailJoltState) (hs : SystemInv s)
    (hrun : JoltISA.execProgram (if store then SystemProofs.scRows double rd rs1 rs2
      else SystemProofs.lrRows double rd rs1 rs2) s = .ok RETIRE_SUCCESS t) : SystemInv t := by
  have keep (r : JoltISA.VReg) (hlo : 34 ≤ r.toNat) (hhi : r.toNat < 40) :
      t.vregs r = s.vregs r := program_vframe r _
        (reservation_csr_avoids store double rd rs1 rs2 r hlo hhi) s t _ hrun
  refine ⟨?_, ?_, ?_, pairPlan_pair _ (reservation_pair_plan store double rd rs1 rs2) s t hrun⟩
  · rw [keep _ (by decide) (by decide)]; exact hs.mstatus_bits
  · rw [keep _ (by decide) (by decide)]; exact hs.mtvec_mode
  · rw [keep _ (by decide) (by decide)]; exact hs.mepc_align

private def expandedCode : ExpandedSource → List JoltISA.Instr
  | .native i => [i]
  | .sequence rows => rows

private def ExpandedSafe (expanded : ExpandedSource) : Prop :=
  AvoidsWindow 32 40 (JoltISA.Program.seq (expandedCode expanded))

private def TouchesSystem : SourceInstruction → Prop
  | .riscv i => match i with
    | .ECALL | .MRET | .LR_W .. | .LR_D .. | .SC_W .. | .SC_D .. |
        .CSRRW .. | .CSRRS .. | .CSRRC .. | .CSRRWI .. | .CSRRSI .. | .CSRRCI .. => True
    | _ => False
  | .jolt _ => False
  | .inline .. => False

local macro "plain_rows_safe" : tactic =>
  `(tactic| (
    unfold ExpandedSafe AvoidsWindow
    intro r hlo hhi
    simp only [ExpandedSource.ofNative, ExpandedSource.ofProgram, ExpandedSource.ofPureProgram,
      expandedCode, JoltISA.Program.instrs, JoltISA.Instr.rewriteNative,
      JoltISA.Instr.destination?, JoltISA.sideEffectingDst, JoltISA.sideEffectingRdZeroDst,
      JoltISA.advicelbProgramAuto, JoltISA.adviceldProgramAuto, JoltISA.advicelhProgramAuto,
      JoltISA.advicelwProgramAuto, JoltISA.amoadddProgramAuto, JoltISA.amoaddwProgramAuto,
      JoltISA.amoanddProgramAuto, JoltISA.amoandwProgramAuto, JoltISA.amomaxdProgramAuto,
      JoltISA.amomaxudProgramAuto, JoltISA.amomaxuwProgramAuto, JoltISA.amomaxwProgramAuto,
      JoltISA.amomindProgramAuto, JoltISA.amominudProgramAuto, JoltISA.amominuwProgramAuto,
      JoltISA.amominwProgramAuto, JoltISA.amoordProgramAuto, JoltISA.amoorwProgramAuto,
      JoltISA.amoswapdProgramAuto, JoltISA.amoswapwProgramAuto, JoltISA.amoxordProgramAuto,
      JoltISA.amoxorwProgramAuto, JoltISA.divProgramAuto, JoltISA.divuProgramAuto,
      JoltISA.divuwProgramAuto, JoltISA.divwProgramAuto, JoltISA.ebreakProgram,
      JoltISA.lbProgramAuto, JoltISA.lbuProgramAuto, JoltISA.lhProgramAuto,
      JoltISA.lhuProgramAuto, JoltISA.lwProgramAuto, JoltISA.lwuProgramAuto,
      JoltISA.mulhProgramAuto, JoltISA.mulhsuProgramAuto, JoltISA.remProgramAuto,
      JoltISA.remuProgramAuto, JoltISA.remuwProgramAuto, JoltISA.remwProgramAuto,
      JoltISA.sbProgramAuto, JoltISA.shProgramAuto, JoltISA.sllProgramAuto,
      JoltISA.slliProgramAuto, JoltISA.slliwProgramAuto, JoltISA.sllwProgramAuto,
      JoltISA.sraProgramAuto, JoltISA.sraiProgramAuto, JoltISA.sraiwProgramAuto,
      JoltISA.srawProgramAuto, JoltISA.srlProgramAuto, JoltISA.srliProgramAuto,
      JoltISA.srliwProgramAuto, JoltISA.srlwProgramAuto, JoltISA.swProgramAuto]
    first | split_ifs | skip
    all_goals simp [expandedCode, ProgramAvoids, JoltISA.Program.seq,
      JoltISA.Program.instrs, JoltISA.Instr.destination?, JoltISA.Instr.canonicalNoOp,
      JoltISA.sideEffectingDst, JoltISA.sideEffectingRdZeroDst, JoltISA.inlineTmp,
      JoltISA.systemScratchVReg, JoltISA.inlineTmp0,
      JoltISA.inlineRegisterBase, JoltISA.riscvRegisterBase, JoltISA.riscvRegisterCount,
      JoltISA.numReservedVirtualRegisters, outside_window 32 40 r hlo hhi]))

/-- Rows that pass `inlineRowOk` write no reserved virtual register. For example, the
rows of any registered hash inline leave `vr32` to `vr39`, the reservation registers and
the CSR mirrors, alone. -/
private theorem inline_rows_avoid (rows : List JoltISA.Instr)
    (ok : rows.all ExpansionFacts.inlineRowOk = true) :
    AvoidsWindow 32 40 (JoltISA.Program.seq rows) := by
  intro r hlo hhi
  induction rows with
  | nil => trivial
  | cons row rest ih =>
    simp only [List.all_cons, Bool.and_eq_true] at ok
    refine ⟨?_, ih ok.2⟩
    have free : ExpansionFacts.reservedFree row = true := by
      have parts := ok.1
      simp only [ExpansionFacts.inlineRowOk, Bool.and_eq_true] at parts
      exact parts.1.2
    intro same
    simp only [ExpansionFacts.reservedFree, same, Bool.or_eq_true, decide_eq_true_eq] at free
    omega

private theorem plain_source_safe (source : SourceInstruction) (expanded : ExpandedSource)
    (hplain : ¬ TouchesSystem source) (he : source.expand = some expanded) :
    ExpandedSafe expanded := by
  cases source with
  | riscv i =>
    cases i
    all_goals simp only [TouchesSystem, not_true_eq_false, not_false_eq_true] at hplain
    all_goals first
      | exact False.elim hplain
      | (simp only [SourceInstruction.expand, Option.some.injEq] at he
         subst expanded
         plain_rows_safe)
  | jolt i =>
    cases i
    all_goals simp only [SourceInstruction.expand, Option.some.injEq] at he
    all_goals subst expanded
    all_goals plain_rows_safe
  | inline key rs1 rs2 rd =>
    simp only [SourceInstruction.expand] at he
    split at he
    · cases he
    · next registered =>
      simp only [Option.some.injEq] at he
      subst expanded
      exact inline_rows_avoid _
        (JoltISA.Inlines.InlineKey.expandRows_rowsOk key rs1 rs2 rd (by simpa using registered))

private theorem patch_avoids (r : JoltISA.VReg) (values : List (BitVec 64))
    (rows : List JoltISA.Instr) (hsafe : ProgramAvoids r (JoltISA.Program.seq rows)) :
    ProgramAvoids r (JoltISA.Program.seq (patchAdvice values rows)) := by
  induction rows generalizing values with
  | nil => trivial
  | cons i rest ih =>
    change (i.destination? ≠ some (.vreg r) ∧ ProgramAvoids r (JoltISA.Program.seq rest)) at hsafe
    unfold patchAdvice
    split <;> simp_all [JoltISA.Program.seq, ProgramAvoids, JoltISA.Instr.destination?]

private theorem stamp_code (address : BitVec 64) (compressed : Bool)
    (instrs : List JoltISA.Instr) :
    (stamp_sequence address compressed instrs).map (·.instruction) = instrs := by
  simp only [stamp_sequence, List.map_map, Function.comp_def]
  exact List.zipIdx_map_fst 0 instrs

private theorem expand_plain_safe (row : SourceInstructionRow SourceInstruction)
    (hplain : ¬ TouchesSystem row.instruction) (rows : List JoltInstructionRow)
    (hexpand : expand_instruction row = some rows) :
    AvoidsWindow 32 40 (JoltISA.Program.seq (rows.map (·.instruction))) := by
  cases he : row.instruction.expand with
  | none => simp only [expand_instruction, he] at hexpand; cases hexpand
  | some expanded =>
    have hs := plain_source_safe row.instruction expanded hplain he
    cases expanded with
    | native i =>
      simp only [expand_instruction, he, Option.some.injEq] at hexpand
      subst rows
      exact hs
    | sequence instrs =>
      simp only [expand_instruction, he] at hexpand
      split at hexpand
      · cases hexpand
      · cases hexpand
        rwa [stamp_code]

private theorem plain_block_preserves (program : Rv64ProgramImage SourceInstruction)
    (b : Block) (hruns : b.Runs program) (hplain : ¬ TouchesSystem b.row.instruction)
    (hs : SystemInv b.pre) : SystemInv b.post := by
  obtain ⟨_values, instrs, -, hblock, hrun⟩ := hruns.executes
  obtain ⟨rows, hexpand, hpatch⟩ := Option.map_eq_some_iff.mp hblock
  subst instrs
  have hsafe := expand_plain_safe b.row hplain rows hexpand
  apply window_preserves _ b.start b.post ?_ (hs.of_vregs rfl) hrun
  intro r hlo hhi
  exact patch_avoids r _ _ (hsafe r hlo hhi)

private theorem patch_empty (rows : List JoltISA.Instr) : patchAdvice [] rows = rows := by
  induction rows with
  | nil => rfl
  | cons i rest ih =>
    unfold patchAdvice
    split <;> simp_all only [List.headD_nil, List.tail_nil, List.cons.injEq, and_self]

/-- A block whose source expands to `p`, with no internal advice, runs that
program when `p` is the sequence of its rows; for example, ECALL runs `ecallProgram`. -/
theorem block_program_run (row : SourceInstructionRow SourceInstruction)
    (s t : SailJoltState) (p : JoltISA.Program)
    (hexpand : row.instruction.expand = some (ExpandedSource.ofProgram p))
    (hadvice : row.instruction.honestTracerAdvice s = [])
    (hseq : JoltISA.Program.seq p.instrs = p)
    (hrun : ∃ instrs, blockInstrs row s = some instrs ∧
      JoltISA.execProgram (JoltISA.Program.seq instrs) s = .ok RETIRE_SUCCESS t) :
    JoltISA.execProgram p s = .ok RETIRE_SUCCESS t := by
  obtain ⟨instrs, hblock, hrun⟩ := hrun
  simp only [blockInstrs, expand_instruction, hexpand, ExpandedSource.ofProgram, hadvice] at hblock
  split at hblock
  · cases hblock
  · simp only [Option.map_some, stamp_code, patch_empty, Option.some.injEq] at hblock
    subst instrs
    rwa [hseq] at hrun

private theorem foldr_csr_read (csr : JoltISA.SystemCSR) (rd : regidx)
    (p : JoltISA.Program) :
    List.foldr JoltISA.Program.instr (.done RETIRE_SUCCESS)
        (JoltISA.csrReadInto csr rd p).instrs =
      JoltISA.csrReadInto csr rd (List.foldr JoltISA.Program.instr (.done RETIRE_SUCCESS) p.instrs) := by
  unfold JoltISA.csrReadInto
  split_ifs <;> rfl

private theorem foldr_csr_swap (csr : JoltISA.SystemCSR) (src : JoltISA.Src) :
    List.foldr JoltISA.Program.instr (.done RETIRE_SUCCESS)
        (JoltISA.csrSwapWrite csr src).instrs = JoltISA.csrSwapWrite csr src := by
  cases csr <;> rfl

private theorem seq_csr_swap (csr : JoltISA.SystemCSR) (rs1 rd : regidx) :
    JoltISA.Program.seq (JoltISA.csrrwProgram csr rs1 rd).instrs =
      JoltISA.csrrwProgram csr rs1 rd := by
  unfold JoltISA.Program.seq JoltISA.csrrwProgram
  split_ifs
  all_goals simp only [JoltISA.Program.instrs, List.foldr, foldr_csr_read, foldr_csr_swap]

private theorem seq_csr_bit (clear : Bool) (csr : JoltISA.SystemCSR) (rs1 rd : regidx) :
    JoltISA.Program.seq (JoltISA.csrBitUpdateProgram clear csr rs1 rd).instrs =
      JoltISA.csrBitUpdateProgram clear csr rs1 rd := by
  unfold JoltISA.Program.seq JoltISA.csrBitUpdateProgram
  split_ifs
  all_goals simp only [JoltISA.Program.instrs, List.foldr, foldr_csr_read,
    JoltISA.pureWritebackRdZeroProgram]

private theorem seq_csr_immediate_swap (csr : JoltISA.SystemCSR) (imm : BitVec 5) (rd : regidx) :
    JoltISA.Program.seq (JoltISA.csrrwiProgram csr imm rd).instrs =
      JoltISA.csrrwiProgram csr imm rd := by
  cases csr
  all_goals unfold JoltISA.Program.seq JoltISA.csrrwiProgram
  all_goals first | split_ifs | skip
  all_goals simp only [JoltISA.Program.instrs, List.foldr, foldr_csr_read]
  all_goals split_ifs <;> simp only [JoltISA.Program.instrs, List.foldr]

private theorem seq_csr_immediate_bit (clear : Bool) (csr : JoltISA.SystemCSR)
    (imm : BitVec 5) (rd : regidx) :
    JoltISA.Program.seq (JoltISA.csrImmediateBitUpdateProgram clear csr imm rd).instrs =
      JoltISA.csrImmediateBitUpdateProgram clear csr imm rd := by
  unfold JoltISA.Program.seq JoltISA.csrImmediateBitUpdateProgram
  split_ifs
  all_goals simp only [JoltISA.Program.instrs, List.foldr, foldr_csr_read,
    JoltISA.pureWritebackRdZeroProgram]
  all_goals split_ifs <;> simp only [JoltISA.Program.instrs, List.foldr]

private theorem seq_reservation (store double : Bool) (rd rs1 rs2 : regidx) :
    JoltISA.Program.seq (if store then SystemProofs.scRows double rd rs1 rs2
        else SystemProofs.lrRows double rd rs1 rs2).instrs =
      (if store then SystemProofs.scRows double rd rs1 rs2
        else SystemProofs.lrRows double rd rs1 rs2) := by
  cases store <;> cases double
  all_goals simp only [SystemProofs.scRows, SystemProofs.lrRows,
    Bool.false_eq_true, ite_true, ite_false]
  all_goals simp only [JoltISA.lrwProgramAuto, JoltISA.lrdProgramAuto,
    JoltISA.scwProgramAuto, JoltISA.scdProgramAuto]
  all_goals split <;> rfl

private theorem ecall_run_preserves (s t : SailJoltState) (pc next : BitVec 64)
    (hs : SystemInv s) (hpc : pc.getLsbD 0 = false)
    (hPC : s.sail.regs.get? Register.PC = some pc)
    (hn : s.sail.regs.get? Register.nextPC = some next)
    (hrun : JoltISA.execProgram JoltISA.ecallProgram s = .ok RETIRE_SUCCESS t) : SystemInv t := by
  rw [SystemProofs.ecallProgram_run s pc next hPC hn] at hrun
  cases hrun
  exact ecall_preserves s pc next hs hpc

private theorem mret_run_preserves (s t : SailJoltState) (next : BitVec 64)
    (hs : SystemInv s) (hn : s.sail.regs.get? Register.nextPC = some next)
    (hrun : JoltISA.execProgram JoltISA.mretProgram s = .ok RETIRE_SUCCESS t) : SystemInv t := by
  rw [SystemProofs.mretProgram_run s next hn] at hrun
  cases hrun
  have hm := mret_status_bits (s.vregs JoltISA.mstatusVReg) hs.mstatus_bits
  have ht := hs.mtvec_mode
  have he := hs.mepc_align
  have hp := hs.reservation_pair
  csr_clean_values source_vreg hm ht he hp

private def SystemPreserves (p : JoltISA.Program) : Prop :=
  ∀ (s t : SailJoltState) (pc next : BitVec 64), SystemInv s → pc.getLsbD 0 = false →
    s.sail.regs.get? Register.PC = some pc →
    s.sail.regs.get? Register.nextPC = some next →
    JoltISA.execProgram p s = .ok RETIRE_SUCCESS t → SystemInv t

private theorem SystemPreserves.no_pc {p : JoltISA.Program}
    (h : ∀ s t, SystemInv s → JoltISA.execProgram p s = .ok RETIRE_SUCCESS t → SystemInv t) :
    SystemPreserves p := fun s t _ _ hs _ _ _ => h s t hs

private theorem system_program_data (source : SourceInstruction) (ht : TouchesSystem source) :
    ∃ p : JoltISA.Program, source.expand = some (ExpandedSource.ofProgram p) ∧
      JoltISA.Program.seq p.instrs = p ∧
      (∀ s, source.honestTracerAdvice s = []) ∧ SystemPreserves p := by
  cases source with
  | jolt i => exact False.elim ht
  | inline _ _ _ _ => exact False.elim ht
  | riscv i =>
    cases i
    all_goals simp only [TouchesSystem] at ht
    case ECALL =>
      exact ⟨JoltISA.ecallProgram, rfl, rfl, fun _ => rfl, ecall_run_preserves⟩
    case MRET =>
      exact ⟨JoltISA.mretProgram, rfl, rfl, fun _ => rfl,
        fun s t _ next hs _ _ hn => mret_run_preserves s t next hs hn⟩
    case CSRRW rd csr rs1 =>
      exact ⟨JoltISA.csrrwProgram csr rs1 rd, rfl, seq_csr_swap csr rs1 rd, fun _ => rfl,
        SystemPreserves.no_pc (csr_swap_preserves csr rs1 rd)⟩
    case CSRRS rd csr rs1 =>
      exact ⟨JoltISA.csrBitUpdateProgram false csr rs1 rd, rfl, seq_csr_bit false csr rs1 rd,
        fun _ => rfl, SystemPreserves.no_pc (csr_bit_preserves false csr rs1 rd)⟩
    case CSRRC rd csr rs1 =>
      exact ⟨JoltISA.csrBitUpdateProgram true csr rs1 rd, rfl, seq_csr_bit true csr rs1 rd,
        fun _ => rfl, SystemPreserves.no_pc (csr_bit_preserves true csr rs1 rd)⟩
    case CSRRWI rd csr imm =>
      exact ⟨JoltISA.csrrwiProgram csr imm rd, rfl, seq_csr_immediate_swap csr imm rd,
        fun _ => rfl, SystemPreserves.no_pc (csr_immediate_swap_preserves csr imm rd)⟩
    case CSRRSI rd csr imm =>
      exact ⟨JoltISA.csrImmediateBitUpdateProgram false csr imm rd, rfl,
        seq_csr_immediate_bit false csr imm rd, fun _ => rfl,
        SystemPreserves.no_pc (csr_immediate_bit_preserves false csr imm rd)⟩
    case CSRRCI rd csr imm =>
      exact ⟨JoltISA.csrImmediateBitUpdateProgram true csr imm rd, rfl,
        seq_csr_immediate_bit true csr imm rd, fun _ => rfl,
        SystemPreserves.no_pc (csr_immediate_bit_preserves true csr imm rd)⟩
    case LR_W rd rs1 aq rl =>
      exact ⟨SystemProofs.lrRows false rd rs1 zreg, rfl,
        seq_reservation false false rd rs1 zreg, fun _ => rfl,
        SystemPreserves.no_pc (reservation_preserves false false rd rs1 zreg)⟩
    case LR_D rd rs1 aq rl =>
      exact ⟨SystemProofs.lrRows true rd rs1 zreg, rfl,
        seq_reservation false true rd rs1 zreg, fun _ => rfl,
        SystemPreserves.no_pc (reservation_preserves false true rd rs1 zreg)⟩
    case SC_W rd rs1 rs2 aq rl =>
      exact ⟨SystemProofs.scRows false rd rs1 rs2, rfl,
        seq_reservation true false rd rs1 rs2, fun _ => rfl,
        SystemPreserves.no_pc (reservation_preserves true false rd rs1 rs2)⟩
    case SC_D rd rs1 rs2 aq rl =>
      exact ⟨SystemProofs.scRows true rd rs1 rs2, rfl,
        seq_reservation true true rd rs1 rs2, fun _ => rfl,
        SystemPreserves.no_pc (reservation_preserves true true rd rs1 rs2)⟩
    all_goals exact False.elim ht

/-- Every source block preserves the legal system values when its
source PC is even, a run invariant supplied separately.
For example, ECALL at address 16 saves the even value 16 in mepc. -/
theorem SystemInv.of_block {program : Rv64ProgramImage SourceInstruction} {b : Block}
    (hruns : b.Runs program) (hpc : b.row.address.getLsbD 0 = false)
    (hs : SystemInv b.pre) : SystemInv b.post := by
  by_cases ht : TouchesSystem b.row.instruction
  · obtain ⟨p, hexpand, hseq, hadvice, hpres⟩ := system_program_data b.row.instruction ht
    have hrun := block_program_run b.row b.start b.post p hexpand (hadvice b.start) hseq
      (hruns.executes_plain fun key rs1 rs2 rs3 inline => by rw [inline] at ht; exact ht)
    exact hpres b.start b.post b.row.address
      (b.row.address + if b.row.is_compressed then 2 else 4) (hs.of_vregs rfl) hpc
      (by simp [Block.start, advance_pc, Std.ExtDHashMap.get?_insert])
      (by simp [Block.start, advance_pc, Std.ExtDHashMap.get?_insert]) hrun
  · exact plain_block_preserves program b hruns ht hs

end WholeRun
