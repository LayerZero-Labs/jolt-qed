import JoltBytecode.InstructionEquivalence.Instructions.System.ReservationRows
import JoltBytecode.InstructionEquivalence.ProofSupport.InstructionLemmas.Sub
import JoltBytecode.InstructionEquivalence.ProofSupport.InstructionLemmas.Mul
import JoltBytecode.InstructionEquivalence.ProofSupport.InstructionLemmas.Add

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail
open LeanRV64D LeanRV64D.Functions

noncomputable section
namespace SystemProofs

/-- SC's XOR followed by SLTIU produces the equality flag.
For example, comparing a reservation with its own address produces one. -/
theorem scCompare_value (reservation addr : BitVec 64) :
    jolt_sltu_value (reservation ^^^ addr) 1#64 =
      if addr == reservation then 1#64 else 0#64 := by
  by_cases he : addr = reservation
  · subst addr
    rw [BitVec.xor_self, jolt_sltu_value_eq_one_of_lt _ _ (by decide)]
    simp
  · have hn : ¬ (reservation ^^^ addr).toNat < (1#64).toNat := by
      intro hlt
      have hz : reservation ^^^ addr = 0#64 := BitVec.eq_of_toNat_eq (by simpa using Nat.lt_one_iff.mp hlt)
      exact he (BitVec.xor_eq_zero_iff.mp hz).symm
    rw [jolt_sltu_value_eq_zero_of_not_lt _ _ hn]
    simp [he]

/-- The two rows that compare an SC address with a reservation register.
For example, SC.D compares rs1 with v33. -/
def scCompareRows (flag reservation : JoltISA.VReg) (rs1 : regidx) : JoltISA.Program :=
  .instr (.XOR (.vreg flag) (.vreg reservation) (.xreg rs1))
    (.instr (JoltISA.Encoded.SLTIU (.vreg flag) (.vreg flag) 1#12) (.done RETIRE_SUCCESS))

/-- The reservation comparison writes a Boolean flag and preserves Sail state.
For example, an unequal address writes zero to the flag register. -/
theorem scCompareRows_run (flag reservation : JoltISA.VReg) (rs1 : regidx)
    (js : SailJoltState) (addr : BitVec 64) (hw : WritableVReg flag)
    (hr : rX_bits rs1 js.sail = .ok addr js.sail) :
    JoltISA.Program.Run (scCompareRows flag reservation rs1) js
      (stateAfterVRegWrite js flag (if addr == js.vregs reservation then 1#64 else 0#64)) := by
  unfold WritableVReg at hw
  have hsext : sign_extend (m := 64) 1#12 = 1#64 := rfl
  simp (config := { contextual := true }) [scCompareRows, JoltISA.Program.Run, JoltISA.execProgram, JoltISA.execInstr,
    RETIRE_SUCCESS, JoltISA.readSrc, readVReg, JoltISA.writeDst, writeVReg,
    stateAfterVRegWrite, liftSail, hr, hw, hsext, scCompare_value,
    bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    get, getThe, MonadStateOf.get, EStateM.get, modify, modifyGet,
    MonadStateOf.modifyGet, EStateM.modifyGet]

/-- The shared arithmetic selection used by both SC widths.
For example, flag zero selects old and flag one selects rs2. -/
def scSelectRows (result old flag : JoltISA.VReg) (rs2 : regidx) : JoltISA.Program :=
  .instr (.SUB (.vreg result) (.xreg rs2) (.vreg old))
    (.instr (.MUL (.vreg result) (.vreg result) (.vreg flag))
      (.instr (.ADD (.vreg result) (.vreg old) (.vreg result)) (.done RETIRE_SUCCESS)))

/-- The SC arithmetic selector writes old + (source - old) * flag.
For example, multiplying by zero leaves the loaded value unchanged. -/
theorem scSelectRows_run (result old flag : JoltISA.VReg) (rs2 : regidx)
    (js : SailJoltState) (src : BitVec 64) (hw : WritableVReg result)
    (hro : result ≠ old) (hrf : result ≠ flag)
    (hr : rX_bits rs2 js.sail = .ok src js.sail) :
    JoltISA.Program.Run (scSelectRows result old flag rs2) js
      (stateAfterVRegWrite js result
        (js.vregs old + (src - js.vregs old) * js.vregs flag)) := by
  let sub := stateAfterVRegWrite js result (src - js.vregs old)
  let mul := stateAfterVRegWrite sub result ((src - js.vregs old) * js.vregs flag)
  have hsub := JoltISA.sub_run_vreg_xreg_vreg result rs2 old js src hr hw
  have hmul : (JoltISA.execInstr (.MUL (.vreg result) (.vreg result) (.vreg flag))).run sub =
      .ok RETIRE_SUCCESS mul := by
    simpa only [sub, mul, stateAfterVRegWrite, ite_true, if_neg (Ne.symm hrf)] using
      JoltISA.mul_run_vreg_vreg_vreg result result flag sub hw
  have hadd := JoltISA.add_run_vreg_vreg_vreg result old result mul hw
  have hadd' : (JoltISA.execInstr (.ADD (.vreg result) (.vreg old) (.vreg result))).run mul =
      .ok RETIRE_SUCCESS (stateAfterVRegWrite js result
        (js.vregs old + (src - js.vregs old) * js.vregs flag)) := by
    simpa (config := { contextual := true }) [mul, sub, stateAfterVRegWrite, Ne.symm hro] using hadd
  change (JoltISA.execProgram (.instr _ (.instr _ (.instr _ (.done RETIRE_SUCCESS))))).run js = _
  have h1 := JoltISA.execProgram_instr_run_retire _
    (.instr (.MUL (.vreg result) (.vreg result) (.vreg flag))
      (.instr (.ADD (.vreg result) (.vreg old) (.vreg result)) (.done RETIRE_SUCCESS))) js sub hsub
  have h2 := JoltISA.execProgram_instr_run_retire _
    (.instr (.ADD (.vreg result) (.vreg old) (.vreg result)) (.done RETIRE_SUCCESS)) sub mul hmul
  have h3 := JoltISA.execProgram_instr_run_retire _ (.done RETIRE_SUCCESS) mul _ hadd'
  exact h1.trans (h2.trans (h3.trans rfl))

/-- The SC selector with a Boolean flag chooses exactly old or source.
For example, a successful reservation selects source. -/
theorem scSelect_value (success : Bool) (old src : BitVec 64) :
    old + (src - old) * (if success then 1#64 else 0#64) = if success then src else old := by
  cases success
  · simp
  · simp only [ite_true, BitVec.mul_one]
    rw [BitVec.add_comm, BitVec.sub_add_cancel]

/-- SC writes the inverted Boolean reservation flag to its destination.
For example, a matching reservation writes zero. -/
theorem scStatus_value (success : Bool) :
    (if success then 1#64 else 0#64) ^^^ 1#64 = if success then 0#64 else 1#64 := by
  cases success <;> rfl

/-- The status row uses Jolt's x0 destination rewrite.
For example, discarded SC.D writes its status to v40. -/
theorem scStatus_run (rd : regidx) (flag : JoltISA.VReg) (js : SailJoltState) :
    (JoltISA.execInstr (JoltISA.Encoded.XORI (JoltISA.sideEffectingRdZeroDst rd)
      (.vreg flag) 1#12)).run js = .ok RETIRE_SUCCESS
        (NativeDispatch.afterDst js rd (js.vregs flag ^^^ 1#64)) := by
  simp only [JoltISA.execInstr, JoltISA.readSrc, readVReg,
    bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    get, getThe, MonadStateOf.get, EStateM.get, NativeDispatch.writeDst_run]
  rfl

/-- The two reservation clears in SC's generated order.
For example, SC.D clears v33 before v32. -/
def scClearRows (double : Bool) : JoltISA.Program :=
  let first : JoltISA.VReg := if double then 33#7 else 32#7
  let second : JoltISA.VReg := if double then 32#7 else 33#7
  .instr (JoltISA.Encoded.ADDI (.vreg first) (.xreg (regidx.Regidx 0#5)) 0#12)
    (.instr (JoltISA.Encoded.ADDI (.vreg second) (.xreg (regidx.Regidx 0#5)) 0#12) (.done RETIRE_SUCCESS))

/-- The complete register effect of SC's reservation clears.
For example, either order leaves both reservation values zero. -/
def scCleared (double : Bool) (js : SailJoltState) : SailJoltState :=
  if double then stateAfterVRegWrite (stateAfterVRegWrite js 33#7 0#64) 32#7 0#64
  else stateAfterVRegWrite (stateAfterVRegWrite js 32#7 0#64) 33#7 0#64

/-- SC clears the reservation without changing Sail's embedded state.
For example, the status written by SC.W remains in rd. -/
theorem scClearRows_run (double : Bool) (js : SailJoltState) :
    JoltISA.Program.Run (scClearRows double) js (scCleared double js) := by
  have hz (s : SailState) : rX_bits (regidx.Regidx 0#5) s = .ok 0#64 s := rX_bits_regidx_zero s
  have hsext : sign_extend (m := 64) 0#12 = 0#64 := rfl
  cases double <;> simp [scClearRows, scCleared, stateAfterVRegWrite, JoltISA.Program.Run,
    RETIRE_SUCCESS, JoltISA.execProgram, JoltISA.execInstr, JoltISA.readSrc,
    JoltISA.writeDst, writeVReg, liftSail, hz, hsext, bind, EStateM.bind, EStateM.run,
    pure, EStateM.pure, get, getThe, MonadStateOf.get, EStateM.get,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]

/-- An aligned SC doubleword store uses the supplied direct RAM write.
For example, its value source can be the arithmetic selector's scratch register. -/
theorem reservationSd_run (rs1 : regidx) (source : JoltISA.VReg)
    (js : SailJoltState) (addr value : BitVec 64) (post : SailJoltState)
    (hr : rX_bits rs1 js.sail = .ok addr js.sail)
    (hv : js.vregs source = value) (ha : addr &&& 7#64 = 0#64)
    (hs : JoltISA.Mmu.store_doubleword addr value js = .ok (.Ok true) post) :
    (JoltISA.execInstr (JoltISA.Encoded.SD (.xreg rs1) (.vreg source) 0#12)).run js =
      .ok RETIRE_SUCCESS post := by
  have hzero : sign_extend (m := 64) 0#12 = 0#64 := rfl
  unfold JoltISA.execInstr JoltISA.readSrc readVReg liftSail
  simp only [hr, bind, EStateM.bind, EStateM.run, hzero, BitVec.add_zero,
    get, getThe, MonadStateOf.get, EStateM.get, pure, EStateM.pure, hv]
  have ha' : addr &&& (7 : BitVec 64) = 0 := ha
  refine (congrArg (fun m : JoltMonad ExecutionResult => m js) (if_pos ha')).trans ?_
  change (JoltISA.Mmu.store_doubleword addr value >>= fun r =>
    match r with | .Ok _ => pure RETIRE_SUCCESS | .Err e => pure e) js = _
  simp only [bind, EStateM.bind, hs, pure, EStateM.pure]

end SystemProofs
