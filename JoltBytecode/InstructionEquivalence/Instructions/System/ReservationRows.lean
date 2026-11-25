import JoltBytecode.JoltISA.ExpansionsAutomated
import JoltBytecode.InstructionEquivalence.ProofSupport.NativeDispatch
import JoltBytecode.InstructionEquivalence.Instructions.System.CsrReg
import JoltBytecode.InstructionEquivalence.Instructions.AtomicFamily.WordProgram
import JoltBytecode.InstructionEquivalence.Instructions.AtomicFamily.Dword

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail
open LeanRV64D LeanRV64D.Functions

noncomputable section
namespace SystemProofs

/-- Replace Jolt's word and doubleword reservation registers.
For example, a word reservation at address a is represented by `(a, 0)`. -/
def withReservation (js : SailJoltState) (w d : BitVec 64) : SailJoltState :=
  { js with vregs := fun r => if r = 32#7 then w else if r = 33#7 then d else js.vregs r }

/-- Replacing v32/v33 projects to replacing Sail's three reservation registers.
For example, `(0, 0)` projects to an invalid reservation of width zero. -/
theorem systemProject_withReservation (js : SailJoltState) (w d : BitVec 64) :
    System.systemProject (withReservation js w d) =
      Step.setReg (Step.setReg (Step.setReg (System.systemProject js)
        Register.reservation_valid (w != 0#64)) Register.reservation_addr w)
          Register.reservation_width (System.reservationWidth w d) := by
  simp [withReservation, System.systemProject, Step.setReg,
    JoltISA.reservationWReg, JoltISA.reservationDReg, JoltISA.trapHandlerVReg,
    JoltISA.mscratchVReg, JoltISA.mepcVReg, JoltISA.mcauseVReg,
    JoltISA.mtvalVReg, JoltISA.mstatusVReg, JoltISA.riscvRegisterBase,
    JoltISA.riscvRegisterCount, System.extDHashMap_insert_insert_same,
    System.extDHashMap_insert_comm_of_ne]

/-- Select the Jolt LR program by access width.
For example, `double = true` selects LR.D. -/
def lrRows (double : Bool) (rd rs1 rs2 : regidx) : JoltISA.Program :=
  if double then JoltISA.lrdProgramAuto rd rs1 rs2 else JoltISA.lrwProgramAuto rd rs1 rs2

/-- The doubleword read by Jolt's LR rows.
For example, LR.W at address 12 reads its containing doubleword at address 8. -/
def reservationBase (double : Bool) (addr : BitVec 64) : BitVec 64 :=
  if double then addr else amoWordBase addr

/-- The shared lower-RAM assertion emitted before LR and SC accesses.
For example, it rejects addresses below `0x80000000`. -/
def reservationRamCheck (scratch : JoltISA.VReg) (rs1 : regidx) : JoltISA.Program :=
  .instr (.LUI (.vreg scratch) 0x80000000#64)
    (.instr (.VirtualAssertLTE (.vreg scratch) (.xreg rs1) 0#128) (.done RETIRE_SUCCESS))

/-- The lower-RAM assertion writes only its scratch register when it succeeds.
For example, address `0x80000008` passes this assertion. -/
theorem reservationRamCheck_run (scratch : JoltISA.VReg) (rs1 : regidx)
    (js : SailJoltState) (addr : BitVec 64)
    (hw : WritableVReg scratch) (hr : rX_bits rs1 js.sail = .ok addr js.sail)
    (hram : JoltISA.RAM_START_ADDRESS ≤ addr.toNat) :
    JoltISA.Program.Run (reservationRamCheck scratch rs1) js
      (stateAfterVRegWrite js scratch 0x80000000#64) := by
  unfold WritableVReg at hw
  simp only [JoltISA.RAM_START_ADDRESS] at hram
  simp [reservationRamCheck, RETIRE_SUCCESS, JoltISA.Program.Run,
    JoltISA.execProgram, JoltISA.execInstr, JoltISA.readSrc, readVReg,
    JoltISA.writeDst, writeVReg, stateAfterVRegWrite, liftSail, hr, hram, hw,
    bind, EStateM.bind, EStateM.run, pure, EStateM.pure, get, getThe, MonadStateOf.get,
    EStateM.get, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]

/-- LR's two persistent-register copies, before its memory rows.
For example, LR.W copies rs1 into v32 and zero into v33. -/
def lrReserveRows (double : Bool) (rs1 : regidx) : JoltISA.Program :=
  if double then
    .instr (JoltISA.Encoded.ADDI (.vreg 33#7) (.xreg rs1) 0#12)
      (.instr (JoltISA.Encoded.ADDI (.vreg 32#7) (.xreg rs1) 0#12) (.done RETIRE_SUCCESS))
  else
    .instr (JoltISA.Encoded.ADDI (.vreg 32#7) (.xreg rs1) 0#12)
      (.instr (JoltISA.Encoded.ADDI (.vreg 33#7) (.xreg (regidx.Regidx 0#5)) 0#12) (.done RETIRE_SUCCESS))

/-- The exact effect of LR's persistent-register copies.
For example, LR.D copies the same address into both reservation registers. -/
def lrReserved (double : Bool) (js : SailJoltState) (addr : BitVec 64) : SailJoltState :=
  if double then stateAfterVRegWrite (stateAfterVRegWrite js 33#7 addr) 32#7 addr
  else stateAfterVRegWrite (stateAfterVRegWrite js 32#7 addr) 33#7 0#64

/-- LR's persistent-register copies preserve all embedded Sail state.
For example, an LR.W reservation leaves the source register readable. -/
theorem lrReserveRows_run (double : Bool) (rs1 : regidx) (js : SailJoltState)
    (addr : BitVec 64) (hr : rX_bits rs1 js.sail = .ok addr js.sail) :
    JoltISA.Program.Run (lrReserveRows double rs1) js (lrReserved double js addr) := by
  have hz (s : SailState) : rX_bits (regidx.Regidx (0#5)) s = .ok 0#64 s := rX_bits_regidx_zero s
  have hsext : sign_extend (m := 64) (0#12) = 0#64 := rfl
  cases double <;>
    simp [lrReserveRows, lrReserved, RETIRE_SUCCESS, JoltISA.Program.Run,
      JoltISA.execProgram, JoltISA.execInstr, JoltISA.readSrc, readVReg,
      JoltISA.writeDst, writeVReg, stateAfterVRegWrite, liftSail, hr, hz, hsext,
      bind, EStateM.bind, EStateM.run, pure, EStateM.pure, get, getThe, MonadStateOf.get,
      EStateM.get, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]

/-- LR's read and destination-write rows after recording its reservation.
For example, LR.W extracts a signed word from its containing doubleword. -/
def lrReadRows (double : Bool) (rd rs1 : regidx) : JoltISA.Program :=
  let scratch : JoltISA.VReg := if JoltISA.isX0 rd then 41#7 else 40#7
  let dst := JoltISA.sideEffectingRdZeroDst rd
  if double then .instr (JoltISA.Encoded.LD .amo dst (.xreg rs1) 0#12) (.done RETIRE_SUCCESS)
  else .instr (JoltISA.Encoded.VirtualLoadW .amo (.vreg scratch) (.xreg rs1) 0#12
      (ExceptionType.E_SAMO_Addr_Align ()))
    (.instr (JoltISA.Encoded.VirtualWindowMaskW (.vreg (scratch + 1#7)) (.xreg rs1) 0#12)
      (.instr (.VirtualPextSigned dst (.vreg scratch) (.vreg (scratch + 1#7))) (.done RETIRE_SUCCESS)))

/-- The register effect of LR's read suffix.
For example, a discarded LR.W writes its signed result to scratch v40. -/
def lrReadPost (double : Bool) (rd : regidx) (js : SailJoltState)
    (addr value : BitVec 64) : SailJoltState :=
  let scratch : JoltISA.VReg := if JoltISA.isX0 rd then 41#7 else 40#7
  if double then NativeDispatch.afterDst js rd value
  else
    let loaded := stateAfterVRegWrite js scratch value
    let masked := stateAfterVRegWrite loaded (scratch + 1#7) (AtomicFamily.amoWordLaneMask addr)
    NativeDispatch.afterDst masked rd (AtomicFamily.amoWordLaneOld addr value)

/-- Signed extraction writes the destination selected by Jolt's x0 rewrite.
For example, a discarded LR.W writes its value to v40. -/
theorem reservationPext_run (rd : regidx) (value mask : JoltISA.VReg) (js : SailJoltState) :
    (JoltISA.execInstr (.VirtualPextSigned (JoltISA.sideEffectingRdZeroDst rd)
      (.vreg value) (.vreg mask))).run js = .ok RETIRE_SUCCESS
      (NativeDispatch.afterDst js rd (jolt_virtual_pext_signed_value (js.vregs value) (js.vregs mask))) := by
  simp only [JoltISA.execInstr, JoltISA.readSrc, readVReg,
    bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    get, getThe, MonadStateOf.get, EStateM.get, NativeDispatch.writeDst_run]

/-- A doubleword load writes the destination selected by Jolt's x0 rewrite.
For example, LR.D with rd = x0 writes its result to v40. -/
theorem reservationLd_run (rd rs1 : regidx) (js : SailJoltState) (addr value : BitVec 64)
    (hr : rX_bits rs1 js.sail = .ok addr js.sail) (ha : addr &&& 7#64 = 0#64)
    (hl : JoltISA.Mmu.load_doubleword addr js = .ok (.Ok value) js) :
    (JoltISA.execInstr (JoltISA.Encoded.LD .amo (JoltISA.sideEffectingRdZeroDst rd)
      (.xreg rs1) 0#12)).run js = .ok RETIRE_SUCCESS (NativeDispatch.afterDst js rd value) := by
  have hzero : sign_extend (m := 64) 0#12 = 0#64 := rfl
  have ha' : addr &&& (7 : BitVec 64) = 0 := ha
  simp [JoltISA.execInstr, JoltISA.readSrc, liftSail,
    bind, EStateM.bind, EStateM.run, hr, hzero, ha', hl,
    NativeDispatch.writeDst_run, pure, EStateM.pure]
  rw [if_pos ha]
  change (JoltISA.Mmu.load_doubleword addr >>= fun r =>
    match r with
    | .Ok v => JoltISA.writeDst (JoltISA.sideEffectingRdZeroDst rd) v *> pure RETIRE_SUCCESS
    | .Err e => pure e) js = _
  simp only [bind, EStateM.bind, hl, NativeDispatch.writeDst_run, pure, EStateM.pure]
  change (EStateM.bind (JoltISA.writeDst (JoltISA.sideEffectingRdZeroDst rd) value)
    (fun _ => EStateM.pure RETIRE_SUCCESS)) js = _
  simp only [EStateM.bind, NativeDispatch.writeDst_run, EStateM.pure]

/-- Execute the LR read suffix from an unchanged RAM read.
For example, LR.D writes exactly the 64 bits returned by Jolt's MMU. -/
theorem lrReadRows_run (double : Bool) (rd rs1 : regidx)
    (js : SailJoltState) (addr value : BitVec 64)
    (hr : rX_bits rs1 js.sail = .ok addr js.sail)
    (ha : addr &&& (if double then 7#64 else 3#64) = 0#64)
    (hload : JoltISA.Mmu.load_doubleword (reservationBase double addr) js = .ok (.Ok value) js) :
    JoltISA.Program.Run (lrReadRows double rd rs1) js (lrReadPost double rd js addr value) := by
  cases double with
  | true =>
      have hld := reservationLd_run rd rs1 js addr value hr ha hload
      change (JoltISA.execProgram (.instr _ (.done RETIRE_SUCCESS))).run js = _
      exact (JoltISA.execProgram_instr_run_retire _ _ js _ hld).trans rfl
  | false =>
      let scratch : JoltISA.VReg := if JoltISA.isX0 rd then 41#7 else 40#7
      let loaded := stateAfterVRegWrite js scratch value
      let masked := stateAfterVRegWrite loaded (scratch + 1#7) (AtomicFamily.amoWordLaneMask addr)
      have hw : WritableVReg scratch := by
        cases hd : JoltISA.isX0 rd <;> simp [scratch, hd, WritableVReg]
      have hm : WritableVReg (scratch + 1#7) := by
        cases hd : JoltISA.isX0 rd <;> simp [scratch, hd, WritableVReg]
      have hne : scratch ≠ scratch + 1#7 := by
        cases hd : JoltISA.isX0 rd <;> simp [scratch, hd]
      have hld := AtomicFamily.amo_word_floor_load_aligned_run rs1 scratch js addr value hr ha hload hw
      have hmask := JoltISA.virtual_window_mask_w_run_vreg_xreg (scratch + 1#7) rs1 0#12 loaded addr hr hm
      have hpext : (JoltISA.execInstr (.VirtualPextSigned (JoltISA.sideEffectingRdZeroDst rd)
          (.vreg scratch) (.vreg (scratch + 1#7)))).run masked =
          .ok RETIRE_SUCCESS (NativeDispatch.afterDst masked rd (AtomicFamily.amoWordLaneOld addr value)) := by
        simpa only [masked, loaded, stateAfterVRegWrite, if_neg hne, ite_true] using
          reservationPext_run rd scratch (scratch + 1#7) masked
      change (JoltISA.execProgram (.instr _ (.instr _ (.instr _ (.done RETIRE_SUCCESS))))).run js = _
      have h1 := JoltISA.execProgram_instr_run_retire _
        (.instr (JoltISA.Encoded.VirtualWindowMaskW (.vreg (scratch + 1#7)) (.xreg rs1) 0#12)
          (.instr (.VirtualPextSigned (JoltISA.sideEffectingRdZeroDst rd)
            (.vreg scratch) (.vreg (scratch + 1#7))) (.done RETIRE_SUCCESS))) js loaded hld
      have h2 := JoltISA.execProgram_instr_run_retire _
        (.instr (.VirtualPextSigned (JoltISA.sideEffectingRdZeroDst rd)
          (.vreg scratch) (.vreg (scratch + 1#7))) (.done RETIRE_SUCCESS)) loaded masked hmask
      have h3 := JoltISA.execProgram_instr_run_retire _ (.done RETIRE_SUCCESS) masked _ hpext
      exact h1.trans (h2.trans (h3.trans rfl))

/-- The complete register effect of LR's three fragments.
For example, discarded LR.D also updates scratch v40. -/
def lrPost (double : Bool) (rd : regidx) (js : SailJoltState)
    (addr value : BitVec 64) : SailJoltState :=
  let scratch : JoltISA.VReg := if JoltISA.isX0 rd then 41#7 else 40#7
  lrReadPost double rd (lrReserved double
    (stateAfterVRegWrite js scratch 0x80000000#64) addr) addr value

/-- Execute LR's three fragments to their complete register specification.
For example, LR.W records a reservation before its floor read. -/
theorem lrRows_run (double : Bool) (rd rs1 rs2 : regidx)
    (js : SailJoltState) (addr : BitVec 64)
    (hr : rX_bits rs1 js.sail = .ok addr js.sail)
    (ha : addr &&& (if double then 7#64 else 3#64) = 0#64)
    (hram : JoltISA.RAM_START_ADDRESS ≤ addr.toNat)
    (hbase : JoltISA.RAM_START_ADDRESS ≤ (reservationBase double addr).toNat)
    (hlegal : JoltISA.Mmu.effective_address_ok js.jolt_device
      (reservationBase double addr).toNat false = true) :
    JoltISA.execProgram (lrRows double rd rs1 rs2) js =
      .ok RETIRE_SUCCESS (lrPost double rd js addr
        (JoltISA.Mmu.ram_doubleword js.sail.mem (reservationBase double addr).toNat)) := by
  let scratch : JoltISA.VReg := if JoltISA.isX0 rd then 41#7 else 40#7
  let checked := stateAfterVRegWrite js scratch 0x80000000#64
  let reserved := lrReserved double checked addr
  have hscratch : WritableVReg scratch := by
    dsimp only [scratch]
    cases h : JoltISA.isX0 rd <;> simp [h, WritableVReg]
  have hcheck := reservationRamCheck_run scratch rs1 js addr hscratch hr hram
  have hreserve := lrReserveRows_run double rs1 checked addr hr
  have hrs : rX_bits rs1 reserved.sail = .ok addr reserved.sail := by
    cases double <;> exact hr
  have hload : JoltISA.Mmu.load_doubleword (reservationBase double addr) reserved =
        .ok (.Ok (JoltISA.Mmu.ram_doubleword js.sail.mem
          (reservationBase double addr).toNat)) reserved := by
    have hdev : reserved.jolt_device = js.jolt_device := by cases double <;> rfl
    have hsail : reserved.sail = js.sail := by cases double <;> rfl
    have hlegal' : JoltISA.Mmu.effective_address_ok reserved.jolt_device
        (reservationBase double addr).toNat false = true := by rw [hdev]; exact hlegal
    rw [← hsail]
    apply JoltISA.Mmu.load_doubleword_ram reserved _ _ hbase hlegal'
    cases double
    · exact AtomicFamily.amo_word_base_aligned addr
    · exact ha
  have hread := lrReadRows_run double rd rs1 reserved addr _ hrs ha hload
  have hshape : lrRows double rd rs1 rs2 =
      (reservationRamCheck scratch rs1).append
        ((lrReserveRows double rs1).append (lrReadRows double rd rs1)) := by
    cases hd : JoltISA.isX0 rd <;> cases double <;>
      simp [lrRows, reservationRamCheck, lrReserveRows, lrReadRows, scratch, hd,
        JoltISA.lrwProgramAuto, JoltISA.lrdProgramAuto, JoltISA.Program.append,
        RETIRE_SUCCESS, JoltISA.sideEffectingRdZeroDst, JoltISA.rdZeroRewriteVReg, JoltISA.inlineTmp, JoltISA.inlineRegisterBase,
        JoltISA.riscvRegisterBase, JoltISA.riscvRegisterCount, JoltISA.numReservedVirtualRegisters]
  rw [hshape]
  have hrun := hcheck.append (hreserve.append hread)
  have hpost : lrReadPost double rd reserved addr
      (JoltISA.Mmu.ram_doubleword js.sail.mem (reservationBase double addr).toNat) =
      lrPost double rd js addr
      (JoltISA.Mmu.ram_doubleword js.sail.mem (reservationBase double addr).toNat) := by
    rfl
  exact hrun.trans (congrArg (EStateM.Result.ok RETIRE_SUCCESS) hpost)

/-- LR writes its loaded value and replaces the reservation, preserving the
other architectural registers.
For example, LR.W records `(addr, 0)` and sign-extends its loaded word. -/
theorem lrRows_spec (double : Bool) (rd rs1 rs2 : regidx)
    (js : SailJoltState) (addr : BitVec 64)
    (hr : rX_bits rs1 js.sail = .ok addr js.sail)
    (ha : addr &&& (if double then 7#64 else 3#64) = 0#64)
    (hram : JoltISA.RAM_START_ADDRESS ≤ addr.toNat)
    (hbase : JoltISA.RAM_START_ADDRESS ≤ (reservationBase double addr).toNat)
    (hlegal : JoltISA.Mmu.effective_address_ok js.jolt_device
      (reservationBase double addr).toNat false = true) :
    System.systemProjectResult (JoltISA.execProgram (lrRows double rd rs1 rs2) js) =
      .ok RETIRE_SUCCESS (stateAfterWrite
        (System.systemProject (withReservation js addr (if double then addr else 0#64))) rd
        (if double then JoltISA.Mmu.ram_doubleword js.sail.mem addr.toNat else
          AtomicFamily.amoWordLaneOld addr
            (JoltISA.Mmu.ram_doubleword js.sail.mem (amoWordBase addr).toNat))) := by
  rw [lrRows_run double rd rs1 rs2 js addr hr ha hram hbase hlegal]
  have hzero (s : SailState) (v : BitVec 64) (h : JoltISA.isX0 rd = true) :
      stateAfterWrite s rd v = s := JoltISA.stateAfterWrite_of_isX0_eq_true h s v
  cases hd : JoltISA.isX0 rd <;> cases double <;>
    simp [System.systemProjectResult, lrPost, lrReserved, lrReadPost, NativeDispatch.afterDst,
      JoltISA.rdZeroRewriteVReg, hd, stateAfterVRegWrite,
      systemProject_withVRegs_writeRd, reservationBase]
  all_goals simp [withReservation, System.systemProject,
    AtomicFamily.amoWordLaneOld, AtomicFamily.amoWordLaneMask,
    JoltISA.riscvRegisterBase, JoltISA.riscvRegisterCount, JoltISA.reservationWReg,
    JoltISA.reservationDReg, JoltISA.trapHandlerVReg, JoltISA.mscratchVReg,
    JoltISA.mepcVReg, JoltISA.mcauseVReg, JoltISA.mtvalVReg, JoltISA.mstatusVReg, hzero, hd,
    JoltISA.inlineTmp, JoltISA.inlineRegisterBase, JoltISA.numReservedVirtualRegisters]

end SystemProofs
