import JoltBytecode.InstructionEquivalence.ProofSupport.Projection

open Sail PreSail LeanRV64D.Functions

noncomputable section

namespace NativeDispatch

/-- Rust's x0 replacement selects exactly the no-op instruction and operands. -/
theorem pureWriteback_x0 (normal : JoltISA.Instr) :
    JoltISA.pureWritebackNativeInstr (regidx.Regidx 0) normal =
      JoltISA.Encoded.ADDI (.xreg (regidx.Regidx 0)) (.xreg (regidx.Regidx 0))
        (0 : BitVec 12) := rfl

/-- Reuse an instruction-body proof once its x0 case is known to leave the
full state unchanged; Rust's no-op replacement has the same state effect. -/
theorem pureWriteback_run_eq (rd : regidx) (normal : JoltISA.Instr)
    (js : SailJoltState)
    (hzero : JoltISA.isX0 rd = true →
      (JoltISA.execInstr normal).run js = .ok RETIRE_SUCCESS js) :
    (JoltISA.execInstr (JoltISA.pureWritebackNativeInstr rd normal)).run js =
      (JoltISA.execInstr normal).run js := by
  unfold JoltISA.pureWritebackNativeInstr
  split
  · rename_i hx0
    rw [hzero hx0]
    simp only [JoltISA.execInstr, JoltISA.readSrc, JoltISA.writeDst, liftSail,
      EStateM.run, bind, EStateM.bind, pure, EStateM.pure,
      rX_bits_regidx_zero, wX_bits_regidx_zero]
  · rfl

/-- Full state after Rust's native destination write.
Source x0 is redirected to temporary register 40; other destinations write xregs. -/
def afterDst (js : SailJoltState) (rd : regidx) (value : BitVec 64) : SailJoltState :=
  if JoltISA.isX0 rd then
    { js with vregs := fun r =>
        if r = JoltISA.rdZeroRewriteVReg then value else js.vregs r }
  else
    { js with sail := stateAfterWrite js.sail rd value }

/-- Executing the rewritten destination produces the full state above. -/
theorem writeDst_run (js : SailJoltState) (rd : regidx) (value : BitVec 64) :
    JoltISA.writeDst (JoltISA.sideEffectingRdZeroDst rd) value js =
      .ok () (afterDst js rd value) := by
  unfold JoltISA.sideEffectingRdZeroDst afterDst
  split
  · exact writeVReg_run_of_writable JoltISA.rdZeroRewriteVReg value js
      (by unfold WritableVReg; decide)
  · simp only [JoltISA.writeDst, liftSail, wX_bits_stateAfterWrite]

/-- The native destination write commutes with updating nextPC. -/
theorem afterDst_setNextPC (js : SailJoltState) (rd : regidx)
    (value target : BitVec 64) :
    { afterDst js rd value with
      sail := System.setNextPCState (afterDst js rd value).sail target } =
    afterDst { js with sail := System.setNextPCState js.sail target } rd value := by
  unfold afterDst
  split
  · rfl
  · simp only [Projection.stateAfterWrite_setNextPCState]

/-- Projection discards the x0 temporary write and retains ordinary xreg writes. -/
theorem systemProject_afterDst (js : SailJoltState) (rd : regidx)
    (value : BitVec 64) :
    System.systemProject (afterDst js rd value) =
      stateAfterWrite (System.systemProject js) rd value := by
  unfold afterDst
  split
  · rename_i hx0
    rw [JoltISA.stateAfterWrite_of_isX0_eq_true hx0]
    simp [System.systemProject, JoltISA.rdZeroRewriteVReg, JoltISA.inlineTmp,
      JoltISA.inlineRegisterBase, JoltISA.riscvRegisterBase,
      JoltISA.riscvRegisterCount, JoltISA.numReservedVirtualRegisters,
      JoltISA.trapHandlerVReg, JoltISA.mscratchVReg, JoltISA.mepcVReg,
      JoltISA.mcauseVReg, JoltISA.mtvalVReg, JoltISA.mstatusVReg]
  · exact Projection.systemProject_stateAfterWrite js rd value

end NativeDispatch

end
