import JoltBytecode.JoltISA.Expansions.System
import JoltBytecode.InstructionEquivalence.ProofSupport.Projection
import JoltBytecode.Step.SailCsr
import JoltBytecode.InstructionEquivalence.Instructions.System.Trap

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail
open LeanRV64D LeanRV64D.Functions

noncomputable section

namespace SystemProofs

/-- The architectural value read from a persistent Jolt CSR register.
For example, a zero virtual mstatus reads as `0x1800`, with MPP fixed to M. -/
def csrValue (csr : JoltISA.SystemCSR) (js : SailJoltState) : BitVec 64 :=
  if csr = .mstatus then js.vregs csr.vreg ||| 0x1800#64 else js.vregs csr.vreg

/-- Write a raw value to one persistent Jolt CSR register.
For example, writing 8 to the mstatus register makes its architectural value
`0x1808` under `systemProject`. -/
def setCsr (js : SailJoltState) (csr : JoltISA.SystemCSR) (v : BitVec 64) : SailJoltState :=
  { js with vregs := fun r => if r = csr.vreg then v else js.vregs r }

/-- Rewriting a persistent CSR with its current raw value preserves the state.
For example, storing the current v35 back to mscratch changes nothing. -/
theorem setCsr_self (js : SailJoltState) (csr : JoltISA.SystemCSR) :
    setCsr js csr (js.vregs csr.vreg) = js := by
  unfold setCsr
  congr 1
  funext r
  split <;> simp_all

/-- A CSR's virtual register is writable and its write changes only that entry.
For example, writing `mscratch` changes v35 and preserves the embedded state. -/
theorem writeCsr_run (csr : JoltISA.SystemCSR) (v : BitVec 64) (js : SailJoltState) :
    writeVReg csr.vreg v js = .ok () (setCsr js csr v) :=
  writeVReg_run_of_writable csr.vreg v js (by cases csr <;> unfold WritableVReg <;> decide)

/-- Every CSR admitted by Jolt is in Sail's six-address whitelist.
For example, `mscratch` has address `0x340`. -/
theorem isJoltCsr (csr : JoltISA.SystemCSR) : Step.IsJoltCsr csr.address := by
  cases csr <;> simp [Step.IsJoltCsr, JoltISA.SystemCSR.address]

/-- The projected CSR read returns the architectural virtual-register value.
For example, projecting v35 = 7 makes a read of `mscratch` return 7. -/
theorem csrRead_project (csr : JoltISA.SystemCSR) (js : SailJoltState) :
    Step.csrRead csr.address (System.systemProject js) = some (csrValue csr js) := by
  cases csr <;>
    simp [Step.csrRead, JoltISA.SystemCSR.address, csrValue, JoltISA.SystemCSR.vreg,
      System.systemProject, Std.ExtDHashMap.get?_insert]

/-- Legal persistent Jolt registers project to Sail's legal machine CSR values.
For example, raw mstatus zero projects to `0x1800` and an even v36 to an even mepc. -/
theorem csrLegal_project (js : SailJoltState)
    (hm : js.vregs JoltISA.mstatusVReg &&& ~~~(0x88#64) = 0#64)
    (ht : (js.vregs JoltISA.trapHandlerVReg).getLsbD 1 = false)
    (he : (js.vregs JoltISA.mepcVReg).getLsbD 0 = false) :
    Step.CsrLegal (System.systemProject js) := by
  have hmasked : js.vregs JoltISA.mstatusVReg &&& 0x88#64 = js.vregs JoltISA.mstatusVReg := by
    simpa using BitVec.and_not_eq_self_of_and_eq_zero
      (js.vregs JoltISA.mstatusVReg) (~~~(0x88#64)) hm
  refine ⟨⟨js.vregs JoltISA.mstatusVReg ||| 0x1800#64, ?_, ?_, mstatus_mpp_machine _⟩,
    ⟨js.vregs JoltISA.trapHandlerVReg, ?_, ht⟩,
    ⟨js.vregs JoltISA.mepcVReg, ?_, he⟩⟩
  · simp [System.systemProject, Std.ExtDHashMap.get?_insert]
  · rw [← hmasked]
    simp [BitVec.and_or_distrib_right, BitVec.and_assoc]
  · simp [System.systemProject, Std.ExtDHashMap.get?_insert]
  · simp [System.systemProject, Std.ExtDHashMap.get?_insert]

/-- A raw virtual CSR write projects to a write of its architectural value.
For example, writing v36 projects to writing Sail's `mepc`. -/
theorem systemProject_setCsr (js : SailJoltState) (csr : JoltISA.SystemCSR) (v : BitVec 64) :
    System.systemProject (setCsr js csr v) =
      Step.csrSet csr.address (if csr = .mstatus then v ||| 0x1800#64 else v)
        (System.systemProject js) := by
  cases csr <;>
    simp [setCsr, System.systemProject, Step.csrSet, Step.setReg,
      JoltISA.SystemCSR.address, JoltISA.SystemCSR.vreg,
      JoltISA.mstatusVReg, JoltISA.trapHandlerVReg, JoltISA.mscratchVReg,
      JoltISA.mepcVReg, JoltISA.mcauseVReg, JoltISA.mtvalVReg,
      JoltISA.reservationWReg, JoltISA.reservationDReg,
      JoltISA.riscvRegisterBase, JoltISA.riscvRegisterCount,
      System.extDHashMap_insert_insert_same, System.extDHashMap_insert_comm_of_ne]

/-- Projection commutes with a persistent CSR write followed by an integer
destination write.
For example, CSRRWI writes mepc and returns its old value in `x1`. -/
theorem systemProject_setCsr_writeRd (js : SailJoltState) (csr : JoltISA.SystemCSR)
    (v old : BitVec 64) (rd : regidx) :
    System.systemProject { setCsr js csr v with sail := stateAfterWrite js.sail rd old } =
      stateAfterWrite
        (Step.csrSet csr.address (if csr = .mstatus then v ||| 0x1800#64 else v)
          (System.systemProject js)) rd old := by
  calc
    _ = stateAfterWrite (System.systemProject (setCsr js csr v)) rd old := by
      simpa only [setCsr] using Projection.systemProject_stateAfterWrite (setCsr js csr v) rd old
    _ = _ := by rw [systemProject_setCsr]

/-- A CSR read prefix writes the old architectural value into `rd` before its
continuation, and leaves all virtual registers unchanged.
For example, an mstatus read adds the fixed MPP bits before writing `x1`. -/
theorem csrReadInto_run (csr : JoltISA.SystemCSR) (rd : regidx)
    (next : JoltISA.Program) (js : SailJoltState) :
    JoltISA.execProgram (JoltISA.csrReadInto csr rd next) js =
      JoltISA.execProgram next { js with sail := stateAfterWrite js.sail rd (csrValue csr js) } := by
  cases hz : JoltISA.isX0 rd with
  | true =>
    simp [JoltISA.csrReadInto, hz, JoltISA.stateAfterWrite_of_isX0_eq_true hz]
  | false =>
    by_cases hm : csr = .mstatus
    · subst csr
      simp [JoltISA.csrReadInto, hz, JoltISA.execProgram, JoltISA.execInstr,
        JoltISA.readSrc, readVReg, JoltISA.writeDst, liftSail, csrValue,
        bind, EStateM.bind, pure, EStateM.pure, get, getThe, MonadStateOf.get,
        EStateM.get, Riscv.ori, wX_bits_stateAfterWrite, RETIRE_SUCCESS]
    · simp [JoltISA.csrReadInto, hz, hm, JoltISA.execProgram, JoltISA.execInstr,
        JoltISA.readSrc, readVReg, JoltISA.writeDst, liftSail, csrValue,
        bind, EStateM.bind, pure, EStateM.pure, get, getThe, MonadStateOf.get,
        EStateM.get, JoltISA.addWide_low, wX_bits_stateAfterWrite, RETIRE_SUCCESS]

/-- A CSR bit update either clears or sets the selected bits.
For example, setting mask 8 changes a raw mstatus of zero to 8. -/
def bitUpdate (clear : Bool) (old mask : BitVec 64) : BitVec 64 :=
  if clear then old &&& ~~~mask else old ||| mask

/-- An empty bit-update mask preserves its input, whether setting or clearing.
For example, CSRRSI with immediate zero preserves its CSR. -/
theorem bitUpdate_zero (clear : Bool) (old : BitVec 64) : bitUpdate clear old 0#64 = old := by
  cases clear
  · exact BitVec.or_zero
  · change old &&& BitVec.allOnes 64 = old
    exact BitVec.and_allOnes

/-- A zero CSR immediate compiles to an empty update mask.
For example, both CSRRSI and CSRRCI of mtvec with immediate zero leave it alone. -/
theorem csrImmediateMask_zero (clear : Bool) (csr : JoltISA.SystemCSR) :
    JoltISA.csrImmediateMask clear csr 0#5 = 0#64 := by
  cases csr <;> cases clear <;> rfl

/-- The immediate CSR bit-update sequence reads `rd` and applies its compiled
mask to the persistent virtual register.
For example, CSRRSI with immediate 8 sets MIE in v39. -/
theorem csrImmediateBitUpdateProgram_run (clear : Bool) (csr : JoltISA.SystemCSR)
    (imm : BitVec 5) (rd : regidx) (js : SailJoltState) :
    JoltISA.execProgram (JoltISA.csrImmediateBitUpdateProgram clear csr imm rd) js =
      .ok RETIRE_SUCCESS
        { setCsr js csr (bitUpdate clear (js.vregs csr.vreg)
            (JoltISA.csrImmediateMask clear csr imm)) with
          sail := stateAfterWrite js.sail rd (csrValue csr js) } := by
  have hzero (s : SailState) : rX_bits (.Regidx 0#5) s = .ok 0#64 s :=
    rX_bits_regidx_zero s
  have hwzero (s : SailState) (v : BitVec 64) : stateAfterWrite s (.Regidx 0#5) v = s :=
    stateAfterWrite_regidx_zero s v
  unfold JoltISA.csrImmediateBitUpdateProgram
  rw [csrReadInto_run]
  by_cases hm : JoltISA.csrImmediateMask clear csr imm = 0#64
  · have hsame : setCsr js csr (bitUpdate clear (js.vregs csr.vreg) 0#64) = js := by
      rw [bitUpdate_zero, setCsr_self]
    simp only [hm, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, hsame]
    cases hz : JoltISA.isX0 rd <;>
      simp [hz, JoltISA.execProgram, JoltISA.pureWritebackRdZeroProgram,
        JoltISA.execInstr, JoltISA.readSrc, JoltISA.writeDst, liftSail,
        hzero, hwzero, wX_bits_stateAfterWrite,
        JoltISA.addWide_low, RETIRE_SUCCESS, pure, EStateM.pure, bind, EStateM.bind]
  · cases clear <;> simp only [Bool.false_eq_true, ↓reduceIte] at hm ⊢ <;>
      simp [hm, JoltISA.execProgram, JoltISA.execInstr, JoltISA.readSrc, readVReg,
        JoltISA.writeDst, writeCsr_run, setCsr, bitUpdate, Riscv.andi, Riscv.ori,
        RETIRE_SUCCESS, pure, EStateM.pure, bind, EStateM.bind,
        get, getThe, MonadStateOf.get, EStateM.get]

/-- The raw mask used by an ordinary CSR swap write.
For example, a mepc write clears bit zero, and a mstatus write keeps bits 3 and 7. -/
def swapValue (csr : JoltISA.SystemCSR) (v : BitVec 64) : BitVec 64 :=
  match csr with
  | .mstatus => v &&& 0x88#64
  | .mepc => v &&& ~~~(1#64)
  | _ => v

/-- The raw value stored by an immediate CSR swap.
A reserved mtvec mode keeps old bit zero and replaces the base.
For example, immediate 6 stores base 4 with the old direct or vectored mode. -/
def immediateSwapValue (csr : JoltISA.SystemCSR) (old : BitVec 64) (imm : BitVec 5) : BitVec 64 :=
  let bits := imm.zeroExtend 64
  if csr = .mtvec ∧ bits &&& 2#64 != 0#64 then
    (old &&& 1#64) ||| (bits &&& ~~~(3#64))
  else swapValue csr bits

/-- The immediate swap program returns the old CSR in `rd` and writes its
compiled immediate to the persistent virtual register.
For example, CSRRWI of mepc with immediate 17 stores 16. -/
theorem csrrwiProgram_run (csr : JoltISA.SystemCSR) (imm : BitVec 5)
    (rd : regidx) (js : SailJoltState) :
    JoltISA.execProgram (JoltISA.csrrwiProgram csr imm rd) js =
      .ok RETIRE_SUCCESS
        { setCsr js csr (immediateSwapValue csr (js.vregs csr.vreg) imm) with
          sail := stateAfterWrite js.sail rd (csrValue csr js) } := by
  have hzero (s : SailState) : rX_bits (.Regidx 0#5) s = .ok 0#64 s := rX_bits_regidx_zero s
  have hzreg (s : SailState) : rX_bits zreg s = .ok 0#64 s := by
    exact rX_bits_regidx_zero s
  have hw := writeCsr_run csr
  unfold JoltISA.csrrwiProgram
  rw [csrReadInto_run]
  cases csr <;>
    simp only [JoltISA.SystemCSR.vreg] at hw ⊢ <;>
    simp [immediateSwapValue, swapValue, JoltISA.SystemCSR.vreg, JoltISA.execProgram, JoltISA.execInstr,
      JoltISA.readSrc, JoltISA.writeDst, hw, hzero, hzreg, setCsr, readVReg, liftSail,
      Riscv.andi, Riscv.ori, JoltISA.addWide_low,
      RETIRE_SUCCESS, pure, EStateM.pure, bind, EStateM.bind,
      get, getThe, MonadStateOf.get, EStateM.get]

  all_goals first
  | rfl
  | (split <;>
    simp_all (config := { contextual := true }) [JoltISA.execProgram, JoltISA.execInstr, JoltISA.readSrc,
      JoltISA.writeDst, setCsr, readVReg, liftSail, Riscv.andi, Riscv.ori,
      JoltISA.addWide_low, RETIRE_SUCCESS, pure, EStateM.pure, bind, EStateM.bind,
      get, getThe, MonadStateOf.get, EStateM.get])
  all_goals first
  | rfl
  | (split <;> simp_all (config := { contextual := true })
      [JoltISA.execProgram, JoltISA.execInstr, JoltISA.readSrc, JoltISA.writeDst,
        JoltISA.SystemCSR.vreg, setCsr, readVReg, liftSail, Riscv.ori,
        RETIRE_SUCCESS, pure, EStateM.pure, bind, EStateM.bind,
        get, getThe, MonadStateOf.get, EStateM.get] <;>
      first | rfl | (funext r; split <;> simp_all))

/-- Masking one bit returns either the single-bit mask or zero.
For example, masking bit 1 of 6 returns 2. -/
theorem and_singleBit (v : BitVec 64) (bit : Nat) :
    v &&& (1#64 <<< bit) = if v.getLsbD bit then (1#64 <<< bit) else 0#64 := by
  have hmask (i : Nat) : (1#64 <<< bit).getLsbD i = decide (i = bit ∧ i < 64) := by
    rw [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_one]
    by_cases h : i = bit
    · subst i; simp
    · rcases (show i < bit ∨ i - bit ≠ 0 by omega) with hlt | hsub
      · simp [hlt, h]
      · simp [hsub, h]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  cases hv : v.getLsbD bit <;>
    simp only [hv, Bool.false_eq_true, ↓reduceIte, BitVec.getLsbD_and, hmask,
      BitVec.getLsbD_zero]
  all_goals by_cases hb : i = bit <;> simp_all

/-- The immediate swap's raw value becomes exactly Sail's legalized CSR value.
The old mtvec mode must be direct or vectored; for example, writing immediate
6 to old mtvec 1 yields architectural mtvec 5. -/
theorem immediateSwapValue_legal (csr : JoltISA.SystemCSR) (raw : BitVec 64)
    (imm : BitVec 5) (ht : csr = .mtvec → raw.getLsbD 1 = false) :
    (if csr = .mstatus then immediateSwapValue csr raw imm ||| 0x1800#64
      else immediateSwapValue csr raw imm) =
      Step.csrLegal csr.address (if csr = .mstatus then raw ||| 0x1800#64 else raw)
        (imm.zeroExtend 64) := by
  have hs (v : BitVec 64) : v &&& 2#64 = if v.getLsbD 1 then 2#64 else 0#64 :=
    and_singleBit v 1
  cases csr <;>
    simp [immediateSwapValue, swapValue, Step.csrLegal, JoltISA.SystemCSR.address]
  have hraw : raw &&& 3#64 = raw &&& 1#64 := by
    rw [show 3#64 = 1#64 ||| 2#64 from rfl, BitVec.and_or_distrib_left, hs]
    have hmode := ht rfl
    simp_all
  rw [hs]
  cases hb : (imm.zeroExtend 64).getLsbD 1 <;> simp_all [BitVec.or_comm]

/-- CSRRWI's Jolt rows agree with Sail's immediate CSR swap on the projected
Machine-mode hart with legal persistent system registers.
For example, swapping mepc with immediate 17 saves its old value in `rd`
and stores the aligned value 16. -/
theorem csrrwiProgram_eq_execute (csr : JoltISA.SystemCSR) (imm : BitVec 5)
    (rd : regidx) (js : SailJoltState)
    (hinv : Step.StepInvariant (System.systemProject js))
    (hm : js.vregs JoltISA.mstatusVReg &&& ~~~(0x88#64) = 0#64)
    (ht : (js.vregs JoltISA.trapHandlerVReg).getLsbD 1 = false)
    (he : (js.vregs JoltISA.mepcVReg).getLsbD 0 = false) :
    System.systemProjectResult (JoltISA.execProgram (JoltISA.csrrwiProgram csr imm rd) js) =
      execute (.CSRImm (csr.address, imm, rd, .CSRRW)) (System.systemProject js) := by
  rw [Step.execute_CSRImm_jolt csr.address (isJoltCsr csr) imm rd .CSRRW
    (System.systemProject js) hinv (csrLegal_project js hm ht he) _ (csrRead_project csr js),
    csrrwiProgram_run]
  simp only [System.systemProjectResult, true_or, ↓reduceIte, Step.csrApply]
  rw [systemProject_setCsr_writeRd]
  have hv := immediateSwapValue_legal csr (js.vregs csr.vreg) imm
    (fun hc => by subst csr; exact ht)
  simpa only [csrValue, zero_extend, Sail.BitVec.zeroExtend] using
    congrArg (fun value => EStateM.Result.ok (ε := Error exception) RETIRE_SUCCESS
      (stateAfterWrite (Step.csrSet csr.address value (System.systemProject js))
        rd (csrValue csr js))) hv

/-- Clearing a bit already known to be zero preserves a word.
For example, clearing bit 0 of an even saved mepc preserves it. -/
theorem clearSingleBit_self (raw : BitVec 64) (bit : Nat)
    (hbit : raw.getLsbD bit = false) : raw &&& ~~~(1#64 <<< bit) = raw := by
  apply BitVec.and_not_eq_self_of_and_eq_zero
  rw [and_singleBit, hbit]
  rfl

/-- Masking a clear operand does not affect bits outside a word's allowed mask.
For example, a word containing only MIE and MPIE ignores other cleared bits. -/
theorem clear_mask_eq (old src mask : BitVec 64) (h : old &&& mask = old) :
    old &&& ~~~(src &&& mask) = old &&& ~~~src := by
  have hz : old &&& ~~~mask = 0#64 := by
    rw [← h, BitVec.and_assoc, BitVec.and_not_self]
    exact BitVec.and_zero
  rw [BitVec.not_and, BitVec.and_or_distrib_left, hz]
  exact BitVec.or_zero

/-- The last two bitwise masks can be applied in either order.
For example, clearing source bits then keeping MIE equals keeping MIE first. -/
theorem and_right_comm (a b c : BitVec 64) : a &&& b &&& c = a &&& c &&& b := by
  ac_rfl

/-- The compiled CSR bit-update mask for a full-width source.
For example, setting mepc excludes bit zero and setting mstatus keeps only bits 3 and 7. -/
def csrBitMask (clear : Bool) (csr : JoltISA.SystemCSR) (bits : BitVec 64) : BitVec 64 :=
  match csr with
  | .mstatus => bits &&& 0x88#64
  | .mepc => bits &&& ~~~(1#64)
  | .mtvec => if !clear && (bits &&& 2#64 != 0#64) then bits &&& ~~~(3#64)
      else bits &&& ~~~(2#64)
  | _ => bits

/-- The bit-update mask gives Sail's legalized set or clear value.
Only the mstatus, mtvec and mepc restrictions are needed.
For example, setting mstatus with source 8 changes only MIE. -/
theorem csrBitUpdateValue_legal (clear : Bool) (csr : JoltISA.SystemCSR)
    (raw : BitVec 64) (bits : BitVec 64)
    (hm : csr = .mstatus → raw &&& ~~~(0x88#64) = 0#64)
    (ht : csr = .mtvec → raw.getLsbD 1 = false)
    (he : csr = .mepc → raw.getLsbD 0 = false) :
    (if csr = .mstatus then
      bitUpdate clear raw (csrBitMask clear csr bits) ||| 0x1800#64
      else bitUpdate clear raw (csrBitMask clear csr bits)) =
      Step.csrLegal csr.address (if csr = .mstatus then raw ||| 0x1800#64 else raw)
        (Step.csrApply (if clear then .CSRRC else .CSRRS)
          (if csr = .mstatus then raw ||| 0x1800#64 else raw) bits) := by
  have hm' : csr = .mstatus → raw &&& 0x88#64 = raw := by
    intro hc
    simpa using BitVec.and_not_eq_self_of_and_eq_zero raw (~~~(0x88#64)) (hm hc)
  have ht' : csr = .mtvec → raw &&& ~~~(2#64) = raw := by
    intro hc
    exact clearSingleBit_self raw 1 (ht hc)
  have he' : csr = .mepc → raw &&& ~~~(1#64) = raw := by
    intro hc
    exact clearSingleBit_self raw 0 (he hc)
  cases csr <;> cases clear <;>
    simp_all [bitUpdate, csrBitMask, Step.csrLegal, Step.csrApply,
      JoltISA.SystemCSR.address, BitVec.and_or_distrib_right, clear_mask_eq]
  case mstatus.true =>
    rw [and_right_comm raw _ 0x88#64, hm',
      and_right_comm 0x1800#64 _ 0x88#64]
    simp
  case mepc.true =>
    rw [and_right_comm raw _ 0xffff_ffff_ffff_fffe#64, he']
  case mtvec.false =>
    have hs : bits &&& 2#64 = if bits.getLsbD 1 then 2#64 else 0#64 := by
      simpa using and_singleBit (bits) 1
    have hp : raw &&& ~~~(3#64) ||| raw &&& 3#64 = raw := by
      rw [← BitVec.and_or_distrib_left, BitVec.not_or_self, BitVec.and_allOnes]
    rw [hs]
    cases hb : bits.getLsbD 1
    · have hclear : bits &&& ~~~(2#64) = bits := by
        apply clearSingleBit_self (bits) 1
        simpa using hb
      simp_all
    · have hvalue : raw ||| bits &&& ~~~(3#64) =
          raw &&& ~~~(3#64) ||| bits &&& ~~~(3#64) ||| raw &&& 3#64 := by
        calc
          _ = (raw &&& ~~~(3#64) ||| raw &&& 3#64) |||
              bits &&& ~~~(3#64) := by rw [hp]
          _ = _ := by ac_rfl
      simp_all

/-- The immediate bit-update mask gives Sail's legalized set or clear value.
Only the mstatus, mtvec and mepc restrictions are needed.
For example, setting mstatus with immediate 8 changes only MIE. -/
theorem immediateBitUpdateValue_legal (clear : Bool) (csr : JoltISA.SystemCSR)
    (raw : BitVec 64) (imm : BitVec 5)
    (hm : csr = .mstatus → raw &&& ~~~(0x88#64) = 0#64)
    (ht : csr = .mtvec → raw.getLsbD 1 = false)
    (he : csr = .mepc → raw.getLsbD 0 = false) :
    (if csr = .mstatus then
      bitUpdate clear raw (JoltISA.csrImmediateMask clear csr imm) ||| 0x1800#64
      else bitUpdate clear raw (JoltISA.csrImmediateMask clear csr imm)) =
      Step.csrLegal csr.address (if csr = .mstatus then raw ||| 0x1800#64 else raw)
        (Step.csrApply (if clear then .CSRRC else .CSRRS)
          (if csr = .mstatus then raw ||| 0x1800#64 else raw) (imm.zeroExtend 64)) := by
  have hmask : JoltISA.csrImmediateMask clear csr imm =
      csrBitMask clear csr (imm.zeroExtend 64) := by
    cases csr <;> rfl
  rw [hmask]
  exact csrBitUpdateValue_legal clear csr raw (imm.zeroExtend 64) hm ht he

/-- The immediate CSR set/clear programs agree with Sail on Jolt's legal
Machine-mode hart, including the no-write zero-immediate case.
For example, CSRRCI with immediate 8 clears mstatus.MIE. -/
theorem csrImmediateBitUpdateProgram_eq_execute (clear : Bool) (csr : JoltISA.SystemCSR)
    (imm : BitVec 5) (rd : regidx) (js : SailJoltState)
    (hinv : Step.StepInvariant (System.systemProject js))
    (hm : js.vregs JoltISA.mstatusVReg &&& ~~~(0x88#64) = 0#64)
    (ht : (js.vregs JoltISA.trapHandlerVReg).getLsbD 1 = false)
    (he : (js.vregs JoltISA.mepcVReg).getLsbD 0 = false) :
    System.systemProjectResult
        (JoltISA.execProgram (JoltISA.csrImmediateBitUpdateProgram clear csr imm rd) js) =
      execute (.CSRImm (csr.address, imm, rd, if clear then .CSRRC else .CSRRS))
        (System.systemProject js) := by
  rw [Step.execute_CSRImm_jolt csr.address (isJoltCsr csr) imm rd
    (if clear then .CSRRC else .CSRRS) (System.systemProject js)
    hinv (csrLegal_project js hm ht he) _ (csrRead_project csr js),
    csrImmediateBitUpdateProgram_run]
  simp only [System.systemProjectResult]
  by_cases hz : imm = 0#5
  · subst imm
    rw [csrImmediateMask_zero, bitUpdate_zero, setCsr_self]
    cases clear <;>
      simp [Projection.systemProject_stateAfterWrite, zero_extend, Sail.BitVec.zeroExtend]
  · have hz' : imm ≠ (0 : BitVec 5) := hz
    rw [if_pos (Or.inr hz'), systemProject_setCsr_writeRd]
    have hv := immediateBitUpdateValue_legal clear csr (js.vregs csr.vreg) imm
      (fun hc => by subst csr; exact hm)
      (fun hc => by subst csr; exact ht)
      (fun hc => by subst csr; exact he)
    simpa only [csrValue, zero_extend, Sail.BitVec.zeroExtend] using
      congrArg (fun value => EStateM.Result.ok (ε := Error exception) RETIRE_SUCCESS
        (stateAfterWrite (Step.csrSet csr.address value (System.systemProject js))
          rd (csrValue csr js))) hv

end SystemProofs
