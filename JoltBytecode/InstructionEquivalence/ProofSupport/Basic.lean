import JoltBytecode.InstructionEquivalence.ProofSupport.Lemmas
import JoltBytecode.InstructionEquivalence.ProofSupport.RegisterAccess
import JoltBytecode.JoltISA.VirtualRegisters
import JoltBytecode.InstructionEquivalence.ProofSupport.ValueLemmas
import JoltBytecode.InstructionEquivalence.ProofSupport.VirtualRegisters
import JoltBytecode.InstructionEquivalence.ProofSupport.ExpansionLayouts
import JoltBytecode.InstructionEquivalence.ProofSupport.ProtectedVRegWrites

set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions
open virtaddr MemoryAccessType mem_payload

set_option autoImplicit true

noncomputable section

/-!
# Instruction equivalence proof support

Shared proof assumptions and small helpers used by instruction-equivalence
files. This module intentionally does not contain mvcgen specs or generic
program closers; concrete instruction proofs should expose the emitted Jolt
instruction sequence directly.
-/

/-- A state is well-formed if every architectural register read succeeds
without changing the Sail state. -/
def WellFormed (js : SailJoltState) : Prop :=
  ∀ r : regidx, ∃ v, rX_bits r js.sail = .ok v js.sail

/-- Public instruction-equivalence contract: the projected Jolt result matches
the Sail result, and every protected Jolt register is preserved by any
successful Jolt run. -/
def ProgramMatchesSailWithProtectedFrame
    (js : SailJoltState)
    (jres : EStateM.Result (Error exception) SailJoltState α)
    (sres : EStateM.Result (Error exception) SailState α) : Prop :=
  projectResult jres = sres ∧
  ∀ result js',
    jres = .ok result js' →
    ∀ vr, JoltISA.IsProtectedJoltRegister vr →
      js'.vregs vr = js.vregs vr


namespace JoltISA

def DstWritesNoProtectedVReg : Dst → Prop
  | .xreg _ => True
  | .vreg vr => ¬ IsProtectedJoltRegister vr

private theorem inlineTmp_le6_not_protected (n : Nat) (h : n ≤ 6) :
    ¬ IsProtectedJoltRegister (inlineTmp n) := by
  interval_cases n
  · simpa [inlineTmp0] using inlineTmp0_not_protected
  · simpa [inlineTmp1] using inlineTmp1_not_protected
  · simpa [inlineTmp2] using inlineTmp2_not_protected
  · simpa [inlineTmp3] using inlineTmp3_not_protected
  · simpa [inlineTmp4] using inlineTmp4_not_protected
  · simpa [inlineTmp5] using inlineTmp5_not_protected
  · simpa [inlineTmp6] using inlineTmp6_not_protected

@[simp] theorem amoDoubleBinopOldVRegFor_not_protected (rd : regidx) :
    ¬ IsProtectedJoltRegister (amoDoubleBinopOldVRegFor rd) := by
  unfold amoDoubleBinopOldVRegFor amoVRegFor
  split <;> exact inlineTmp_le6_not_protected _ (by norm_num)

@[simp] theorem amoDoubleBinopNewVRegFor_not_protected (rd : regidx) :
    ¬ IsProtectedJoltRegister (amoDoubleBinopNewVRegFor rd) := by
  unfold amoDoubleBinopNewVRegFor amoVRegFor
  split <;> exact inlineTmp_le6_not_protected _ (by norm_num)

@[simp] theorem amoOldVRegFor_not_protected (rd : regidx) :
    ¬ IsProtectedJoltRegister (amoOldVRegFor rd) := by
  unfold amoOldVRegFor amoVRegFor
  split <;> exact inlineTmp_le6_not_protected _ (by norm_num)

@[simp] theorem amoNewVRegFor_not_protected (rd : regidx) :
    ¬ IsProtectedJoltRegister (amoNewVRegFor rd) := by
  unfold amoNewVRegFor amoVRegFor
  split <;> exact inlineTmp_le6_not_protected _ (by norm_num)

@[simp] theorem amoTmpVRegFor_not_protected (rd : regidx) :
    ¬ IsProtectedJoltRegister (amoTmpVRegFor rd) := by
  unfold amoTmpVRegFor amoVRegFor
  split <;> exact inlineTmp_le6_not_protected _ (by norm_num)

@[simp] theorem amoMaskVRegFor_not_protected (rd : regidx) :
    ¬ IsProtectedJoltRegister (amoMaskVRegFor rd) := by
  unfold amoMaskVRegFor amoVRegFor
  split <;> exact inlineTmp_le6_not_protected _ (by norm_num)

@[simp] theorem amoDwordVRegFor_not_protected (rd : regidx) :
    ¬ IsProtectedJoltRegister (amoDwordVRegFor rd) := by
  unfold amoDwordVRegFor amoVRegFor
  split <;> exact inlineTmp_le6_not_protected _ (by norm_num)

@[simp] theorem amoShiftVRegFor_not_protected (rd : regidx) :
    ¬ IsProtectedJoltRegister (amoShiftVRegFor rd) := by
  unfold amoShiftVRegFor amoVRegFor
  split <;> exact inlineTmp_le6_not_protected _ (by norm_num)

@[simp] theorem amoInlineTmpVRegFor_not_protected (rd : regidx) :
    ¬ IsProtectedJoltRegister (amoInlineTmpVRegFor rd) := by
  unfold amoInlineTmpVRegFor amoVRegFor
  split <;> exact inlineTmp_le6_not_protected _ (by norm_num)

@[simp] theorem amoWordSelectOldVRegFor_not_protected (rd : regidx) :
    ¬ IsProtectedJoltRegister (amoWordSelectOldVRegFor rd) := by
  unfold amoWordSelectOldVRegFor amoVRegFor
  split <;> exact inlineTmp_le6_not_protected _ (by norm_num)

@[simp] theorem amoWordSelectDwordVRegFor_not_protected (rd : regidx) :
    ¬ IsProtectedJoltRegister (amoWordSelectDwordVRegFor rd) := by
  unfold amoWordSelectDwordVRegFor amoVRegFor
  split <;> exact inlineTmp_le6_not_protected _ (by norm_num)

@[simp] theorem amoWordSelectShiftVRegFor_not_protected (rd : regidx) :
    ¬ IsProtectedJoltRegister (amoWordSelectShiftVRegFor rd) := by
  unfold amoWordSelectShiftVRegFor amoVRegFor
  split <;> exact inlineTmp_le6_not_protected _ (by norm_num)

@[simp] theorem amoWordSelectNewVRegFor_not_protected (rd : regidx) :
    ¬ IsProtectedJoltRegister (amoWordSelectNewVRegFor rd) := by
  unfold amoWordSelectNewVRegFor amoVRegFor
  split <;> exact inlineTmp_le6_not_protected _ (by norm_num)

@[simp] theorem amoWordSelectMaskVRegFor_not_protected (rd : regidx) :
    ¬ IsProtectedJoltRegister (amoWordSelectMaskVRegFor rd) := by
  unfold amoWordSelectMaskVRegFor amoVRegFor
  split <;> exact inlineTmp_le6_not_protected _ (by norm_num)

@[simp] theorem amoWordSelectInlineTmpVRegFor_not_protected (rd : regidx) :
    ¬ IsProtectedJoltRegister (amoWordSelectInlineTmpVRegFor rd) := by
  unfold amoWordSelectInlineTmpVRegFor amoVRegFor
  split <;> exact inlineTmp_le6_not_protected _ (by norm_num)

@[simp] theorem amoOldVRegFor_writable (rd : regidx) :
    WritableVReg (amoOldVRegFor rd) := by
  unfold amoOldVRegFor amoVRegFor WritableVReg
  split <;> decide

@[simp] theorem amoNewVRegFor_writable (rd : regidx) :
    WritableVReg (amoNewVRegFor rd) := by
  unfold amoNewVRegFor amoVRegFor WritableVReg
  split <;> decide

@[simp] theorem amoTmpVRegFor_writable (rd : regidx) :
    WritableVReg (amoTmpVRegFor rd) := by
  unfold amoTmpVRegFor amoVRegFor WritableVReg
  split <;> decide

@[simp] theorem amoOldVRegFor_ne_amoTmpVRegFor (rd : regidx) :
    amoOldVRegFor rd ≠ amoTmpVRegFor rd := by
  unfold amoOldVRegFor amoTmpVRegFor amoVRegFor
  split <;> decide

@[simp] theorem amoOldVRegFor_ne_amoNewVRegFor (rd : regidx) :
    amoOldVRegFor rd ≠ amoNewVRegFor rd := by
  unfold amoOldVRegFor amoNewVRegFor amoVRegFor
  split <;> decide

@[simp] theorem amoTmpVRegFor_ne_amoNewVRegFor (rd : regidx) :
    amoTmpVRegFor rd ≠ amoNewVRegFor rd := by
  unfold amoTmpVRegFor amoNewVRegFor amoVRegFor
  split <;> decide

def VRegWritesNoProtectedVReg (vr : VReg) : Prop :=
  ¬ IsProtectedJoltRegister vr

def InstrWritesNoProtectedVReg : Instr → Prop
  | .ADDI dst _ _ => DstWritesNoProtectedVReg dst
  | .ADDIW dst _ _ => DstWritesNoProtectedVReg dst
  | .ANDI dst _ _ => DstWritesNoProtectedVReg dst
  | .ORI dst _ _ => DstWritesNoProtectedVReg dst
  | .XORI dst _ _ => DstWritesNoProtectedVReg dst
  | .SLTI _ _ _ => False
  | .SLTIU _ _ _ => False
  | .LUI dst _ => DstWritesNoProtectedVReg dst
  | .AUIPC _ _ => False
  | .JAL _ _ => False
  | .JALR _ _ _ => False
  | .BEQ _ _ _ => False
  | .BNE _ _ _ => False
  | .BLT _ _ _ => False
  | .BGE _ _ _ => False
  | .BLTU _ _ _ => False
  | .BGEU _ _ _ => False
  | .FENCE => False
  | .ADD dst _ _ => DstWritesNoProtectedVReg dst
  | .ADDW dst _ _ => DstWritesNoProtectedVReg dst
  | .SUB dst _ _ => DstWritesNoProtectedVReg dst
  | .SUBW dst _ _ => DstWritesNoProtectedVReg dst
  | .MUL dst _ _ => DstWritesNoProtectedVReg dst
  | .MULW dst _ _ => DstWritesNoProtectedVReg dst
  | .MULHU dst _ _ => DstWritesNoProtectedVReg dst
  | .ANDN dst _ _ => DstWritesNoProtectedVReg dst
  | .OR dst _ _ => DstWritesNoProtectedVReg dst
  | .XOR dst _ _ => DstWritesNoProtectedVReg dst
  | .AND dst _ _ => DstWritesNoProtectedVReg dst
  | .SLT dst _ _ => DstWritesNoProtectedVReg dst
  | .SLTU dst _ _ => DstWritesNoProtectedVReg dst
  | .VirtualMULI dst _ _ => DstWritesNoProtectedVReg dst
  | .VirtualMULIW dst _ _ => DstWritesNoProtectedVReg dst
  | .VirtualPow2 dst _ _ => DstWritesNoProtectedVReg dst
  | .VirtualPow2W dst _ _ => DstWritesNoProtectedVReg dst
  | .VirtualPow2I _ _ => False
  | .VirtualPow2IW _ _ => False
  | .VirtualShiftRightBitmask dst _ _ => DstWritesNoProtectedVReg dst
  | .VirtualShiftRightBitmaskI _ _ => False
  | .VirtualShiftRightBitmaskW dst _ _ => DstWritesNoProtectedVReg dst
  | .VirtualSRLI dst _ _ => DstWritesNoProtectedVReg dst
  | .VirtualSRAI dst _ _ => DstWritesNoProtectedVReg dst
  | .VirtualSRLIW dst _ _ => DstWritesNoProtectedVReg dst
  | .VirtualSRAIW dst _ _ => DstWritesNoProtectedVReg dst
  | .VirtualSRL dst _ _ => DstWritesNoProtectedVReg dst
  | .VirtualSRA dst _ _ => DstWritesNoProtectedVReg dst
  | .VirtualSRLW dst _ _ => DstWritesNoProtectedVReg dst
  | .VirtualSRAW dst _ _ => DstWritesNoProtectedVReg dst
  | .VirtualROTRI _ _ _ => False
  | .VirtualROTRIW _ _ _ => False
  | .VirtualRev8W _ _ _ => False
  | .VirtualXORROT32 _ _ _ => False
  | .VirtualXORROT24 _ _ _ => False
  | .VirtualXORROT16 _ _ _ => False
  | .VirtualXORROT63 _ _ _ => False
  | .VirtualXORROTW16 _ _ _ => False
  | .VirtualXORROTW12 _ _ _ => False
  | .VirtualXORROTW8 _ _ _ => False
  | .VirtualXORROTW7 _ _ _ => False
  | .VirtualXORROTW22 _ _ _ => False
  | .VirtualXORROTW19 _ _ _ => False
  | .VirtualXORROTW6 _ _ _ => False
  | .VirtualAlignAddr dst _ _ => DstWritesNoProtectedVReg dst
  | .VirtualWindowMaskB dst _ _ => DstWritesNoProtectedVReg dst
  | .VirtualWindowMaskH dst _ _ => DstWritesNoProtectedVReg dst
  | .VirtualWindowMaskW dst _ _ => DstWritesNoProtectedVReg dst
  | .VirtualShiftDataB dst _ _ => DstWritesNoProtectedVReg dst
  | .VirtualShiftDataH dst _ _ => DstWritesNoProtectedVReg dst
  | .VirtualShiftDataW dst _ _ => DstWritesNoProtectedVReg dst
  | .VirtualPext dst _ _ => DstWritesNoProtectedVReg dst
  | .VirtualPextSigned dst _ _ => DstWritesNoProtectedVReg dst
  | .VirtualSignExtendWord dst _ _ => DstWritesNoProtectedVReg dst
  | .VirtualZeroExtendWord dst _ _ => DstWritesNoProtectedVReg dst
  | .VirtualMovsign dst _ _ => DstWritesNoProtectedVReg dst
  | .VirtualAssertHalfwordAlignment _ _ _ => True
  | .VirtualAssertWordAlignment _ _ _ => True
  | .LD _ dst _ _ => DstWritesNoProtectedVReg (sideEffectingDst dst)
  | .SD _ _ _ => True
  | .VirtualAdvice dst _ _ => DstWritesNoProtectedVReg dst
  | .VirtualAdviceLoad dst _ => DstWritesNoProtectedVReg dst
  | .VirtualAdviceLen _ _ _ => False
  | .VirtualHostIO _ _ _ => False
  | .VirtualAssertEQ _ _ _ => True
  | .VirtualAssertValidDiv0 _ _ _ => True
  | .VirtualNegateIf dst _ _ => DstWritesNoProtectedVReg dst
  | .VirtualAssertValidUnsignedRemainder _ _ _ => True
  | .VirtualAssertMulUNoOverflow _ _ _ => True
  | .VirtualAssertLTE _ _ _ => True

def ProgramWritesNoProtectedVReg : Program → Prop
  | .done _ => True
  | .instr instr rest =>
      InstrWritesNoProtectedVReg instr ∧ ProgramWritesNoProtectedVReg rest

private theorem readSrc_preserves_vregs
    {src : Src} {js js' : SailJoltState} {value : BitVec 64}
    (hrun : (readSrc src).run js = .ok value js') :
    js'.vregs = js.vregs := by
  cases src with
  | vreg vr =>
      unfold readSrc readVReg at hrun
      simp only [EStateM.run, get, getThe, MonadStateOf.get, pure] at hrun
      cases hrun
      rfl
  | xreg rs =>
      unfold readSrc liftSail at hrun
      simp only [EStateM.run] at hrun
      cases hread : rX_bits rs js.sail with
      | ok value' sail' =>
          rw [hread] at hrun
          cases hrun
          rfl
      | error e sail' =>
          rw [hread] at hrun
          cases hrun

private theorem liftSail_preserves_vregs
    {m : SailM α} {js js' : SailJoltState} {value : α}
    (hrun : (liftSail m).run js = .ok value js') :
    js'.vregs = js.vregs := by
  unfold liftSail at hrun
  simp only [EStateM.run] at hrun
  cases hm : m js.sail with
  | ok value' sail' =>
      rw [hm] at hrun
      cases hrun
      rfl
  | error e sail' =>
      rw [hm] at hrun
      cases hrun

private theorem readMemoryWord_preserves_vregs
    {address : BitVec 64} {js js' : SailJoltState}
    {value : Result (BitVec 64) ExecutionResult}
    (hrun : (readMemoryWord address).run js = .ok value js') :
    js'.vregs = js.vregs := by
  simp only [EStateM.run, readMemoryWord] at hrun
  split at hrun
  · split at hrun <;> cases hrun <;> rfl
  · exact liftSail_preserves_vregs hrun

private theorem writeMemoryWord_preserves_vregs
    {address value : BitVec 64} {js js' : SailJoltState}
    {result : Result Bool ExecutionResult}
    (hrun : (writeMemoryWord address value).run js = .ok result js') :
    js'.vregs = js.vregs := by
  simp only [EStateM.run, writeMemoryWord] at hrun
  split at hrun
  · split at hrun <;> cases hrun <;> rfl
  · exact liftSail_preserves_vregs hrun

private theorem writeDst_preserves_protected
    {dst : Dst} {js js' : SailJoltState} {value : BitVec 64}
    (hsafe : DstWritesNoProtectedVReg dst)
    (hrun : (writeDst dst value).run js = .ok () js') :
    ∀ vr, IsProtectedJoltRegister vr → js'.vregs vr = js.vregs vr := by
  cases dst with
  | xreg rd =>
      unfold writeDst liftSail at hrun
      simp only [EStateM.run] at hrun
      cases hwrite : wX_bits rd value js.sail with
      | ok u sail' =>
          rw [hwrite] at hrun
          cases hrun
          intro vr hprotected
          rfl
      | error e sail' =>
          rw [hwrite] at hrun
          cases hrun
  | vreg scratch =>
      unfold DstWritesNoProtectedVReg at hsafe
      by_cases harch : scratch.toNat < 32
      · unfold writeDst writeVReg at hrun
        simp only [harch, ↓reduceIte, EStateM.run, throw, throwThe,
          MonadExceptOf.throw, EStateM.throw] at hrun
        cases hrun
      unfold writeDst writeVReg at hrun
      simp only [harch, ↓reduceIte, EStateM.run, modify, modifyGet,
        MonadStateOf.modifyGet, EStateM.modifyGet] at hrun
      cases hrun
      intro vr hprotected
      by_cases hEq : vr = scratch
      · subst vr
        exact False.elim (hsafe hprotected)
      · simp only [hEq, ↓reduceIte]

private theorem dstWrite_preserves_protected
    {dst : Dst} {js js' : SailJoltState}
    {result : ExecutionResult} {value : BitVec 64}
    (hsafe : DstWritesNoProtectedVReg dst)
    (hrun : (do
        writeDst dst value
        pure RETIRE_SUCCESS : JoltMonad ExecutionResult).run js =
      .ok result js') :
    ∀ vr, IsProtectedJoltRegister vr → js'.vregs vr = js.vregs vr := by
  simp only [EStateM.run, bind, EStateM.bind] at hrun
  cases hwrite : (writeDst dst value).run js with
  | ok u js_afterWrite =>
      change writeDst dst value js = .ok u js_afterWrite at hwrite
      rw [hwrite] at hrun
      simp only [pure, EStateM.pure] at hrun
      cases hrun
      exact writeDst_preserves_protected hsafe hwrite
  | error e js_error =>
      change writeDst dst value js = .error e js_error at hwrite
      rw [hwrite] at hrun
      simp only at hrun
      cases hrun

private theorem alignmentAssert_preserves_protected
    {base : regidx} {imm : BitVec 12} {fault : ExceptionType}
    {mask : BitVec 64}
    {js js' : SailJoltState} {result : ExecutionResult}
    (hrun : (do
        let baseValue ← liftSail (rX_bits base)
        let addr := baseValue + sign_extend (m := 64) imm
        if addr &&& mask = 0 then
          pure RETIRE_SUCCESS
        else
          pure (ExecutionResult.Memory_Exception (Virtaddr addr, fault)) :
        JoltMonad ExecutionResult).run js = .ok result js') :
    ∀ vr, IsProtectedJoltRegister vr → js'.vregs vr = js.vregs vr := by
  simp only [EStateM.run, bind, EStateM.bind] at hrun
  cases hread : (liftSail (rX_bits base)).run js with
  | ok baseValue js_afterRead =>
      change liftSail (rX_bits base) js = .ok baseValue js_afterRead at hread
      rw [hread] at hrun
      let addr := baseValue + sign_extend (m := 64) imm
      by_cases halign : addr &&& mask = 0
      · simp only [addr, halign, ↓reduceIte, pure, EStateM.pure] at hrun
        cases hrun
        have hread_frame := liftSail_preserves_vregs hread
        intro vr hprotected
        rw [hread_frame]
      · simp only [addr, halign, ↓reduceIte, pure, EStateM.pure] at hrun
        cases hrun
        have hread_frame := liftSail_preserves_vregs hread
        intro vr hprotected
        rw [hread_frame]
  | error e js_error =>
      change liftSail (rX_bits base) js = .error e js_error at hread
      rw [hread] at hrun
      simp only at hrun
      cases hrun

private theorem unaryWrite_preserves_protected
    {src : Src} {dst : Dst} {js js' : SailJoltState}
    {result : ExecutionResult} {f : BitVec 64 → BitVec 64}
    (hsafe : DstWritesNoProtectedVReg dst)
    (hrun : (do
        let x ← readSrc src
        writeDst dst (f x)
        pure RETIRE_SUCCESS : JoltMonad ExecutionResult).run js =
      .ok result js') :
    ∀ vr, IsProtectedJoltRegister vr → js'.vregs vr = js.vregs vr := by
  simp only [EStateM.run, bind, EStateM.bind] at hrun
  cases hread : (readSrc src).run js with
  | ok x js_afterRead =>
      change readSrc src js = .ok x js_afterRead at hread
      rw [hread] at hrun
      simp only at hrun
      cases hwrite : (writeDst dst (f x)).run js_afterRead with
      | ok u js_afterWrite =>
          change writeDst dst (f x) js_afterRead = .ok u js_afterWrite at hwrite
          rw [hwrite] at hrun
          simp only [pure, EStateM.pure] at hrun
          cases hrun
          have hread_frame := readSrc_preserves_vregs hread
          have hwrite_frame := writeDst_preserves_protected hsafe hwrite
          intro vr hprotected
          rw [hwrite_frame vr hprotected, hread_frame]
      | error e js_error =>
          change writeDst dst (f x) js_afterRead = .error e js_error at hwrite
          rw [hwrite] at hrun
          simp only at hrun
          cases hrun
  | error e js_error =>
      change readSrc src js = .error e js_error at hread
      rw [hread] at hrun
      simp only at hrun
      cases hrun

private theorem binaryWrite_preserves_protected
    {lhs rhs : Src} {dst : Dst} {js js' : SailJoltState}
    {result : ExecutionResult} {f : BitVec 64 → BitVec 64 → BitVec 64}
    (hsafe : DstWritesNoProtectedVReg dst)
    (hrun : (do
        let x ← readSrc lhs
        let y ← readSrc rhs
        writeDst dst (f x y)
        pure RETIRE_SUCCESS : JoltMonad ExecutionResult).run js =
      .ok result js') :
    ∀ vr, IsProtectedJoltRegister vr → js'.vregs vr = js.vregs vr := by
  simp only [EStateM.run, bind, EStateM.bind] at hrun
  cases hread_lhs : (readSrc lhs).run js with
  | ok x js_afterLhs =>
      change readSrc lhs js = .ok x js_afterLhs at hread_lhs
      rw [hread_lhs] at hrun
      simp only at hrun
      cases hread_rhs : (readSrc rhs).run js_afterLhs with
      | ok y js_afterRhs =>
          change readSrc rhs js_afterLhs = .ok y js_afterRhs at hread_rhs
          rw [hread_rhs] at hrun
          simp only at hrun
          cases hwrite : (writeDst dst (f x y)).run js_afterRhs with
          | ok u js_afterWrite =>
              change writeDst dst (f x y) js_afterRhs = .ok u js_afterWrite at hwrite
              rw [hwrite] at hrun
              simp only [pure, EStateM.pure] at hrun
              cases hrun
              have hlhs_frame := readSrc_preserves_vregs hread_lhs
              have hrhs_frame := readSrc_preserves_vregs hread_rhs
              have hwrite_frame := writeDst_preserves_protected hsafe hwrite
              intro vr hprotected
              rw [hwrite_frame vr hprotected, hrhs_frame, hlhs_frame]
          | error e js_error =>
              change writeDst dst (f x y) js_afterRhs = .error e js_error at hwrite
              rw [hwrite] at hrun
              simp only at hrun
              cases hrun
      | error e js_error =>
          change readSrc rhs js_afterLhs = .error e js_error at hread_rhs
          rw [hread_rhs] at hrun
          simp only at hrun
          cases hrun
  | error e js_error =>
      change readSrc lhs js = .error e js_error at hread_lhs
      rw [hread_lhs] at hrun
      simp only at hrun
      cases hrun

private theorem binaryReadIfPureElseThrow_preserves_protected
    {lhs rhs : Src} {js js' : SailJoltState}
    {result : ExecutionResult}
    {p : BitVec 64 → BitVec 64 → Prop} [DecidableRel p]
    {msg : String}
    (hrun : (do
        let x ← readSrc lhs
        let y ← readSrc rhs
        if p x y then
          pure RETIRE_SUCCESS
        else
          throw (Error.Assertion msg) : JoltMonad ExecutionResult).run js =
      .ok result js') :
    ∀ vr, IsProtectedJoltRegister vr → js'.vregs vr = js.vregs vr := by
  simp only [EStateM.run, bind, EStateM.bind] at hrun
  cases hread_lhs : (readSrc lhs).run js with
  | ok x js_afterLhs =>
      change readSrc lhs js = .ok x js_afterLhs at hread_lhs
      rw [hread_lhs] at hrun
      simp only at hrun
      cases hread_rhs : (readSrc rhs).run js_afterLhs with
      | ok y js_afterRhs =>
          change readSrc rhs js_afterLhs = .ok y js_afterRhs at hread_rhs
          rw [hread_rhs] at hrun
          by_cases hp : p x y
          · simp only [hp, ↓reduceIte, pure, EStateM.pure] at hrun
            cases hrun
            have hlhs_frame := readSrc_preserves_vregs hread_lhs
            have hrhs_frame := readSrc_preserves_vregs hread_rhs
            intro vr hprotected
            rw [hrhs_frame, hlhs_frame]
          · simp only [hp, ↓reduceIte, throw, throwThe, MonadExceptOf.throw,
              EStateM.throw] at hrun
            cases hrun
      | error e js_error =>
          change readSrc rhs js_afterLhs = .error e js_error at hread_rhs
          rw [hread_rhs] at hrun
          simp only at hrun
          cases hrun
  | error e js_error =>
      change readSrc lhs js = .error e js_error at hread_lhs
      rw [hread_lhs] at hrun
      simp only at hrun
      cases hrun

private theorem binaryReadIfThrowElsePure_preserves_protected
    {lhs rhs : Src} {js js' : SailJoltState}
    {result : ExecutionResult}
    {p : BitVec 64 → BitVec 64 → Prop} [DecidableRel p]
    {msg : String}
    (hrun : (do
        let x ← readSrc lhs
        let y ← readSrc rhs
        if p x y then
          throw (Error.Assertion msg)
        else
          pure RETIRE_SUCCESS : JoltMonad ExecutionResult).run js =
      .ok result js') :
    ∀ vr, IsProtectedJoltRegister vr → js'.vregs vr = js.vregs vr := by
  simp only [EStateM.run, bind, EStateM.bind] at hrun
  cases hread_lhs : (readSrc lhs).run js with
  | ok x js_afterLhs =>
      change readSrc lhs js = .ok x js_afterLhs at hread_lhs
      rw [hread_lhs] at hrun
      simp only at hrun
      cases hread_rhs : (readSrc rhs).run js_afterLhs with
      | ok y js_afterRhs =>
          change readSrc rhs js_afterLhs = .ok y js_afterRhs at hread_rhs
          rw [hread_rhs] at hrun
          by_cases hp : p x y
          · simp only [hp, ↓reduceIte, throw, throwThe, MonadExceptOf.throw,
              EStateM.throw] at hrun
            cases hrun
          · simp only [hp, ↓reduceIte, pure, EStateM.pure] at hrun
            cases hrun
            have hlhs_frame := readSrc_preserves_vregs hread_lhs
            have hrhs_frame := readSrc_preserves_vregs hread_rhs
            intro vr hprotected
            rw [hrhs_frame, hlhs_frame]
      | error e js_error =>
          change readSrc rhs js_afterLhs = .error e js_error at hread_rhs
          rw [hread_rhs] at hrun
          simp only at hrun
          cases hrun
  | error e js_error =>
      change readSrc lhs js = .error e js_error at hread_lhs
      rw [hread_lhs] at hrun
      simp only at hrun
      cases hrun

private theorem ld_preserves_protected
    {faultClass : LoadFaultClass} {dst : Dst} {base : Src} {imm : BitVec 12}
    {js js' : SailJoltState} {result : ExecutionResult}
    (hsafe : DstWritesNoProtectedVReg (sideEffectingDst dst))
    (hrun : (do
        let baseValue ← readSrc base
        let addr := baseValue + sign_extend (m := 64) imm
        if addr &&& (7 : BitVec 64) = 0 then
          match ← readMemoryWord addr with
          | .Ok dword =>
              writeDst (sideEffectingDst dst) dword
              pure RETIRE_SUCCESS
          | .Err e => pure e
        else
          pure (ExecutionResult.Memory_Exception
            (Virtaddr addr, LoadFaultClass.alignFault faultClass)) :
        JoltMonad ExecutionResult).run js = .ok result js') :
    ∀ vr, IsProtectedJoltRegister vr → js'.vregs vr = js.vregs vr := by
  simp only [EStateM.run, bind, EStateM.bind] at hrun
  cases hbase : (readSrc base).run js with
  | ok baseValue js_afterBase =>
      change readSrc base js = .ok baseValue js_afterBase at hbase
      rw [hbase] at hrun
      simp only at hrun
      let addr := baseValue + sign_extend (m := 64) imm
      by_cases halign : addr &&& (7 : BitVec 64) = 0
      · simp only [addr, halign, ↓reduceIte] at hrun
        cases hmem :
            (readMemoryWord addr).run
                js_afterBase with
        | ok memResult js_afterMem =>
            change readMemoryWord (baseValue + sign_extend (m := 64) imm)
                js_afterBase = .ok memResult js_afterMem at hmem
            simp only [EStateM.bind, hmem] at hrun
            cases memResult with
            | Ok dword =>
                simp only at hrun
                cases hwrite : (writeDst (sideEffectingDst dst) dword).run js_afterMem with
                | ok u js_afterWrite =>
                    change writeDst (sideEffectingDst dst) dword js_afterMem =
                      .ok u js_afterWrite at hwrite
                    simp only [EStateM.bind, hwrite] at hrun
                    simp only [pure, EStateM.pure] at hrun
                    cases hrun
                    have hbase_frame := readSrc_preserves_vregs hbase
                    have hmem_frame := readMemoryWord_preserves_vregs hmem
                    have hwrite_frame := writeDst_preserves_protected hsafe hwrite
                    intro vr hprotected
                    rw [hwrite_frame vr hprotected, hmem_frame, hbase_frame]
                | error e js_error =>
                    change writeDst (sideEffectingDst dst) dword js_afterMem =
                      .error e js_error at hwrite
                    simp only [EStateM.bind, hwrite] at hrun
                    cases hrun
            | Err e =>
                simp only [pure, EStateM.pure] at hrun
                cases hrun
                have hbase_frame := readSrc_preserves_vregs hbase
                have hmem_frame := readMemoryWord_preserves_vregs hmem
                intro vr hprotected
                rw [hmem_frame, hbase_frame]
        | error e js_error =>
            change readMemoryWord (baseValue + sign_extend (m := 64) imm)
                js_afterBase = .error e js_error at hmem
            simp only [EStateM.bind, hmem] at hrun
            cases hrun
      · simp only [addr, halign, ↓reduceIte, pure, EStateM.pure] at hrun
        cases hrun
        have hbase_frame := readSrc_preserves_vregs hbase
        intro vr hprotected
        rw [hbase_frame]
  | error e js_error =>
      change readSrc base js = .error e js_error at hbase
      rw [hbase] at hrun
      simp only at hrun
      cases hrun

private theorem sd_preserves_protected
    {base value : Src} {imm : BitVec 12}
    {js js' : SailJoltState} {result : ExecutionResult}
    (hrun : (do
        let baseValue ← readSrc base
        let addr := baseValue + sign_extend (m := 64) imm
        let stored ← readSrc value
        if addr &&& (7 : BitVec 64) = 0 then
          match ← writeMemoryWord addr stored with
          | .Ok _ => pure RETIRE_SUCCESS
          | .Err e => pure e
        else
          pure (ExecutionResult.Memory_Exception
            (Virtaddr addr, ExceptionType.E_SAMO_Addr_Align ())) :
        JoltMonad ExecutionResult).run js = .ok result js') :
    ∀ vr, IsProtectedJoltRegister vr → js'.vregs vr = js.vregs vr := by
  simp only [EStateM.run, bind, EStateM.bind] at hrun
  cases hbase : (readSrc base).run js with
  | ok baseValue js_afterBase =>
      change readSrc base js = .ok baseValue js_afterBase at hbase
      rw [hbase] at hrun
      simp only at hrun
      let addr := baseValue + sign_extend (m := 64) imm
      cases hvalue : (readSrc value).run js_afterBase with
      | ok stored js_afterValue =>
          change readSrc value js_afterBase = .ok stored js_afterValue at hvalue
          rw [hvalue] at hrun
          by_cases halign : addr &&& (7 : BitVec 64) = 0
          · simp only [addr, halign, ↓reduceIte] at hrun
            cases hmem :
                (writeMemoryWord addr stored).run
                    js_afterValue with
            | ok memResult js_afterMem =>
                change writeMemoryWord (baseValue + sign_extend (m := 64) imm) stored
                    js_afterValue = .ok memResult js_afterMem at hmem
                simp only [EStateM.bind, hmem] at hrun
                cases memResult <;> simp only [pure, EStateM.pure] at hrun <;>
                  cases hrun
                all_goals
                  have hbase_frame := readSrc_preserves_vregs hbase
                  have hvalue_frame := readSrc_preserves_vregs hvalue
                  have hmem_frame := writeMemoryWord_preserves_vregs hmem
                  intro vr hprotected
                  rw [hmem_frame, hvalue_frame, hbase_frame]
            | error e js_error =>
                change writeMemoryWord (baseValue + sign_extend (m := 64) imm) stored
                    js_afterValue = .error e js_error at hmem
                simp only [EStateM.bind, hmem] at hrun
                cases hrun
          · simp only [addr, halign, ↓reduceIte, pure, EStateM.pure] at hrun
            cases hrun
            have hbase_frame := readSrc_preserves_vregs hbase
            have hvalue_frame := readSrc_preserves_vregs hvalue
            intro vr hprotected
            rw [hvalue_frame, hbase_frame]
      | error e js_error =>
          change readSrc value js_afterBase = .error e js_error at hvalue
          rw [hvalue] at hrun
          simp only at hrun
          cases hrun
  | error e js_error =>
      change readSrc base js = .error e js_error at hbase
      rw [hbase] at hrun
      simp only at hrun
      cases hrun

theorem execInstr_preserves_protected
    {instr : Instr} {js js' : SailJoltState} {result : ExecutionResult}
    (hsafe : InstrWritesNoProtectedVReg instr)
    (hrun : (execInstr instr).run js = .ok result js') :
    ∀ vr, IsProtectedJoltRegister vr → js'.vregs vr = js.vregs vr := by
  cases instr with
  | ADDI dst src imm =>
      exact unaryWrite_preserves_protected hsafe (by simpa [execInstr] using hrun)
  | ADDIW dst src imm =>
      exact unaryWrite_preserves_protected hsafe (by simpa [execInstr] using hrun)
  | ANDI dst src imm =>
      exact unaryWrite_preserves_protected hsafe (by simpa [execInstr] using hrun)
  | ORI dst src imm =>
      exact unaryWrite_preserves_protected hsafe (by simpa [execInstr] using hrun)
  | XORI dst src imm =>
      exact unaryWrite_preserves_protected hsafe (by simpa [execInstr] using hrun)
  | SLTI dst src imm =>
      cases hsafe
  | SLTIU dst src imm =>
      cases hsafe
  | LUI dst imm =>
      exact dstWrite_preserves_protected hsafe (by simpa [execInstr] using hrun)
  | AUIPC dst imm =>
      cases hsafe
  | JAL dst imm =>
      cases hsafe
  | JALR dst base imm =>
      cases hsafe
  | BEQ lhs rhs imm =>
      cases hsafe
  | BNE lhs rhs imm =>
      cases hsafe
  | BLT lhs rhs imm =>
      cases hsafe
  | BGE lhs rhs imm =>
      cases hsafe
  | BLTU lhs rhs imm =>
      cases hsafe
  | BGEU lhs rhs imm =>
      cases hsafe
  | FENCE =>
      cases hsafe
  | ADD dst lhs rhs =>
      exact binaryWrite_preserves_protected hsafe (by simpa [execInstr] using hrun)
  | ADDW dst lhs rhs =>
      exact binaryWrite_preserves_protected hsafe (by simpa [execInstr] using hrun)
  | SUB dst lhs rhs =>
      exact binaryWrite_preserves_protected hsafe (by simpa [execInstr] using hrun)
  | SUBW dst lhs rhs =>
      exact binaryWrite_preserves_protected hsafe (by simpa [execInstr] using hrun)
  | MUL dst lhs rhs =>
      exact binaryWrite_preserves_protected hsafe (by simpa [execInstr] using hrun)
  | MULW dst lhs rhs =>
      exact binaryWrite_preserves_protected hsafe (by simpa [execInstr] using hrun)
  | MULHU dst lhs rhs =>
      exact binaryWrite_preserves_protected hsafe (by simpa [execInstr] using hrun)
  | ANDN dst lhs rhs =>
      exact binaryWrite_preserves_protected hsafe (by simpa [execInstr] using hrun)
  | VirtualPow2I dst imm =>
      cases hsafe
  | VirtualPow2IW dst imm =>
      cases hsafe
  | VirtualShiftRightBitmaskI dst imm =>
      cases hsafe
  | VirtualROTRI dst src bitmask =>
      cases hsafe
  | VirtualROTRIW dst src bitmask =>
      cases hsafe
  | VirtualRev8W dst src _ =>
      cases hsafe
  | VirtualXORROT32 dst lhs rhs =>
      cases hsafe
  | VirtualXORROT24 dst lhs rhs =>
      cases hsafe
  | VirtualXORROT16 dst lhs rhs =>
      cases hsafe
  | VirtualXORROT63 dst lhs rhs =>
      cases hsafe
  | VirtualXORROTW16 dst lhs rhs =>
      cases hsafe
  | VirtualXORROTW12 dst lhs rhs =>
      cases hsafe
  | VirtualXORROTW8 dst lhs rhs =>
      cases hsafe
  | VirtualXORROTW7 dst lhs rhs =>
      cases hsafe
  | VirtualXORROTW22 dst lhs rhs =>
      cases hsafe
  | VirtualXORROTW19 dst lhs rhs =>
      cases hsafe
  | VirtualXORROTW6 dst lhs rhs =>
      cases hsafe
  | OR dst lhs rhs =>
      exact binaryWrite_preserves_protected hsafe (by simpa [execInstr] using hrun)
  | XOR dst lhs rhs =>
      exact binaryWrite_preserves_protected hsafe (by simpa [execInstr] using hrun)
  | AND dst lhs rhs =>
      exact binaryWrite_preserves_protected hsafe (by simpa [execInstr] using hrun)
  | SLT dst lhs rhs =>
      exact binaryWrite_preserves_protected hsafe (by simpa [execInstr] using hrun)
  | SLTU dst lhs rhs =>
      exact binaryWrite_preserves_protected hsafe (by simpa [execInstr] using hrun)
  | VirtualMULI dst src imm =>
      exact unaryWrite_preserves_protected hsafe (by simpa [execInstr] using hrun)
  | VirtualMULIW dst src imm =>
      exact unaryWrite_preserves_protected hsafe (by simpa [execInstr] using hrun)
  | VirtualPow2 dst src _ =>
      exact unaryWrite_preserves_protected hsafe (by simpa [execInstr] using hrun)
  | VirtualPow2W dst src _ =>
      exact unaryWrite_preserves_protected hsafe (by simpa [execInstr] using hrun)
  | VirtualShiftRightBitmask dst src _ =>
      exact unaryWrite_preserves_protected hsafe (by simpa [execInstr] using hrun)
  | VirtualShiftRightBitmaskW dst src _ =>
      exact unaryWrite_preserves_protected hsafe (by simpa [execInstr] using hrun)
  | VirtualSRLI dst src bitmask =>
      exact unaryWrite_preserves_protected hsafe (by simpa [execInstr] using hrun)
  | VirtualSRAI dst src bitmask =>
      exact unaryWrite_preserves_protected hsafe (by simpa [execInstr] using hrun)
  | VirtualSRLIW dst src bitmask =>
      exact unaryWrite_preserves_protected hsafe (by simpa [execInstr] using hrun)
  | VirtualSRAIW dst src bitmask =>
      exact unaryWrite_preserves_protected hsafe (by simpa [execInstr] using hrun)
  | VirtualSRL dst value bitmask =>
      exact binaryWrite_preserves_protected hsafe (by simpa [execInstr] using hrun)
  | VirtualSRA dst value bitmask =>
      exact binaryWrite_preserves_protected hsafe (by simpa [execInstr] using hrun)
  | VirtualSRLW dst value bitmask =>
      exact binaryWrite_preserves_protected hsafe (by simpa [execInstr] using hrun)
  | VirtualSRAW dst value bitmask =>
      exact binaryWrite_preserves_protected hsafe (by simpa [execInstr] using hrun)
  | VirtualAlignAddr dst base imm =>
      exact unaryWrite_preserves_protected hsafe (by simpa [execInstr] using hrun)
  | VirtualWindowMaskB dst base imm =>
      exact unaryWrite_preserves_protected hsafe (by simpa [execInstr] using hrun)
  | VirtualWindowMaskH dst base imm =>
      exact unaryWrite_preserves_protected hsafe (by simpa [execInstr] using hrun)
  | VirtualWindowMaskW dst base imm =>
      exact unaryWrite_preserves_protected hsafe (by simpa [execInstr] using hrun)
  | VirtualShiftDataB dst value address =>
      exact binaryWrite_preserves_protected hsafe (by simpa [execInstr] using hrun)
  | VirtualShiftDataH dst value address =>
      exact binaryWrite_preserves_protected hsafe (by simpa [execInstr] using hrun)
  | VirtualShiftDataW dst value address =>
      exact binaryWrite_preserves_protected hsafe (by simpa [execInstr] using hrun)
  | VirtualPext dst value mask =>
      exact binaryWrite_preserves_protected hsafe (by simpa [execInstr] using hrun)
  | VirtualPextSigned dst value mask =>
      exact binaryWrite_preserves_protected hsafe (by simpa [execInstr] using hrun)
  | VirtualSignExtendWord dst src _ =>
      exact unaryWrite_preserves_protected hsafe (by simpa [execInstr] using hrun)
  | VirtualZeroExtendWord dst src _ =>
      exact unaryWrite_preserves_protected hsafe (by simpa [execInstr] using hrun)
  | VirtualMovsign dst src _ =>
      exact unaryWrite_preserves_protected hsafe (by simpa [execInstr] using hrun)
  | VirtualAssertHalfwordAlignment base imm fault =>
      exact alignmentAssert_preserves_protected
        (mask := (1 : BitVec 64)) (by simpa [execInstr] using hrun)
  | VirtualAssertWordAlignment base imm fault =>
      exact alignmentAssert_preserves_protected
        (mask := (3 : BitVec 64)) (by simpa [execInstr] using hrun)
  | LD faultClass dst base imm =>
      exact ld_preserves_protected hsafe (by simpa [execInstr] using hrun)
  | SD base value imm =>
      exact sd_preserves_protected (by simpa [execInstr] using hrun)
  | VirtualAdvice dst value _ =>
      exact dstWrite_preserves_protected hsafe (by simpa [execInstr] using hrun)
  | VirtualAdviceLoad dst byteCount =>
      cases hread : readAdviceTape js.adviceTape byteCount with
      | none => simp [execInstr, EStateM.run, hread] at hrun
      | some result =>
          rcases result with ⟨value, tape⟩
          exact dstWrite_preserves_protected (js := { js with adviceTape := tape }) hsafe
            (by simpa [execInstr, EStateM.run, hread] using hrun)
  | VirtualAdviceLen dst src _ =>
      cases hsafe
  | VirtualHostIO dst src _ =>
      cases hsafe
  | VirtualAssertEQ lhs rhs imm =>
      by_cases himm : imm = 0#13
      · exact binaryReadIfPureElseThrow_preserves_protected
          (p := fun x y => x = y)
          (msg := "VirtualAssertEQ")
          (by simpa [execInstr, himm] using hrun)
      · simp only [execInstr, himm, ↓reduceIte, pure, EStateM.pure, EStateM.run] at hrun
        cases hrun
        intro vr hprotected
        rfl
  | VirtualAssertValidDiv0 divisor quotient _ =>
      exact binaryReadIfThrowElsePure_preserves_protected
        (p := fun d q => d = 0#64 ∧ q ≠ (-1 : BitVec 64))
        (msg := "VirtualAssertValidDiv0: divisor = 0 but quotient ≠ -1")
        (by simpa [execInstr] using hrun)
  | VirtualNegateIf dst signSource value =>
      exact binaryWrite_preserves_protected hsafe (by simpa [execInstr] using hrun)
  | VirtualAssertValidUnsignedRemainder remainder divisor _ =>
      exact binaryReadIfPureElseThrow_preserves_protected
        (p := fun r d => d = 0#64 ∨ r.toNat < d.toNat)
        (msg := "VirtualAssertValidUnsignedRemainder: r ≥ d ∧ d ≠ 0")
        (by simpa [execInstr] using hrun)
  | VirtualAssertMulUNoOverflow lhs rhs _ =>
      exact binaryReadIfPureElseThrow_preserves_protected
        (p := fun x y => x.toNat * y.toNat < 2 ^ 64)
        (msg := "VirtualAssertMulUNoOverflow")
        (by simpa [execInstr] using hrun)
  | VirtualAssertLTE lhs rhs _ =>
      exact binaryReadIfPureElseThrow_preserves_protected
        (p := fun x y => x.toNat ≤ y.toNat)
        (msg := "VirtualAssertLTE")
        (by simpa [execInstr] using hrun)

theorem execProgram_preserves_protected
    {program : Program} {js js' : SailJoltState} {result : ExecutionResult}
    (hsafe : ProgramWritesNoProtectedVReg program)
    (hrun : (execProgram program).run js = .ok result js') :
    ∀ vr, IsProtectedJoltRegister vr → js'.vregs vr = js.vregs vr := by
  induction program generalizing js js' result with
  | done doneResult =>
      unfold execProgram at hrun
      simp only [pure] at hrun
      cases hrun
      intro vr hprotected
      rfl
  | instr instr rest ih =>
      change InstrWritesNoProtectedVReg instr ∧
        ProgramWritesNoProtectedVReg rest at hsafe
      simp only [execProgram_instr, EStateM.run, bind, EStateM.bind] at hrun
      cases hinstr : (execInstr instr).run js with
      | error e js_error =>
          change execInstr instr js = .error e js_error at hinstr
          rw [hinstr] at hrun
          simp only at hrun
          cases hrun
      | ok headResult js_afterInstr =>
          change execInstr instr js = .ok headResult js_afterInstr at hinstr
          rw [hinstr] at hrun
          simp only at hrun
          have hhead :=
            execInstr_preserves_protected hsafe.1
              (by simpa [EStateM.run] using hinstr)
          cases headResult with
          | Retire_Success u =>
              cases u
              have htail := ih hsafe.2 hrun
              intro vr hprotected
              rw [htail vr hprotected, hhead vr hprotected]
          | ExecuteAs x =>
              simp only [pure, EStateM.pure] at hrun
              cases hrun
              exact hhead
          | Enter_Wait x =>
              simp only [pure, EStateM.pure] at hrun
              cases hrun
              exact hhead
          | Illegal_Instruction x =>
              simp only [pure, EStateM.pure] at hrun
              cases hrun
              exact hhead
          | Virtual_Instruction x =>
              simp only [pure, EStateM.pure] at hrun
              cases hrun
              exact hhead
          | Trap x =>
              simp only [pure, EStateM.pure] at hrun
              cases hrun
              exact hhead
          | Memory_Exception x =>
              simp only [pure, EStateM.pure] at hrun
              cases hrun
              exact hhead
          | Ext_CSR_Check_Failure x =>
              simp only [pure, EStateM.pure] at hrun
              cases hrun
              exact hhead
          | Ext_ControlAddr_Check_Failure x =>
              simp only [pure, EStateM.pure] at hrun
              cases hrun
              exact hhead
          | Ext_DataAddr_Check_Failure x =>
              simp only [pure, EStateM.pure] at hrun
              cases hrun
              exact hhead
          | Ext_XRET_Priv_Failure x =>
              simp only [pure, EStateM.pure] at hrun
              cases hrun
              exact hhead

/-- The `isX0` predicate recognizes architectural register `x0`. -/
theorem isX0_regidx_zero :
    isX0 (regidx.Regidx 0) = true := by
  unfold isX0
  simp

/-- If `isX0` succeeds, the register index is architectural `x0`. -/
theorem eq_regidx_zero_of_isX0_eq_true
    {rd : regidx}
    (h : isX0 rd = true) :
    rd = regidx.Regidx 0 := by
  cases rd with
  | Regidx bits =>
      unfold isX0 at h
      simp only at h
      have hbits : bits.toNat = 0 := of_decide_eq_true h
      congr
      exact BitVec.eq_of_toNat_eq hbits

/-- A write to a register recognized by `isX0` is a no-op in the pure Sail
write model. -/
theorem stateAfterWrite_of_isX0_eq_true
    {rd : regidx}
    (h : isX0 rd = true)
    (s : SailState) (val : BitVec 64) :
    stateAfterWrite s rd val = s := by
  rw [eq_regidx_zero_of_isX0_eq_true h]
  exact stateAfterWrite_regidx_zero s val

/-- If a register is not architectural `x0`, `isX0` returns `false`. -/
theorem isX0_eq_false_of_ne_zero
    {rd : regidx}
    (hrd : rd ≠ regidx.Regidx 0) :
    isX0 rd = false := by
  cases rd with
  | Regidx bits =>
      unfold isX0
      simp only
      apply decide_eq_false
      intro hbits
      apply hrd
      congr
      apply BitVec.eq_of_toNat_eq
      simpa using hbits

/-- For `rd ≠ x0`, pure-writeback trace dispatch uses the ordinary inline
sequence unchanged. -/
theorem pureWritebackTraceProgram_of_ne_zero
    {rd : regidx}
    (hrd : rd ≠ regidx.Regidx 0)
    (normal : Program) :
    pureWritebackTraceProgram rd normal = normal := by
  unfold pureWritebackTraceProgram
  rw [isX0_eq_false_of_ne_zero hrd]
  simp only [Bool.false_eq_true, ↓reduceIte]

theorem pureWritebackRdZeroProgram_writesNoProtected :
    ProgramWritesNoProtectedVReg pureWritebackRdZeroProgram := by
  simp [pureWritebackRdZeroProgram, ProgramWritesNoProtectedVReg,
    InstrWritesNoProtectedVReg, DstWritesNoProtectedVReg]

end JoltISA

end
