import JoltBytecode.InstructionEquivalence.Instructions.AtomicFamily.Dword
import JoltBytecode.JoltISA.ExpansionsAutomated

set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace AtomicFamily

theorem amoxordProgram_doesNotWriteProtectedVRegs
    (rs2 rs1 rd : regidx) :
    JoltISA.ProgramWritesNoProtectedVReg
      (JoltISA.amoxordProgramAuto rd rs1 rs2) := by
  unfold JoltISA.amoxordProgramAuto
  split
  · simp only [JoltISA.ProgramWritesNoProtectedVReg,
      JoltISA.InstrWritesNoProtectedVReg, JoltISA.DstWritesNoProtectedVReg,
      true_and, and_true]
    exact ⟨JoltISA.not_protected_of_instructionTmp rfl,
      JoltISA.not_protected_of_instructionTmp rfl,
      JoltISA.not_protected_of_instructionTmp rfl⟩
  · simp only [JoltISA.ProgramWritesNoProtectedVReg,
      JoltISA.InstrWritesNoProtectedVReg, JoltISA.DstWritesNoProtectedVReg,
      and_true]
    exact ⟨JoltISA.not_protected_of_instructionTmp rfl,
      JoltISA.not_protected_of_instructionTmp rfl⟩

private theorem amoxordProgramCore_doesNotWriteProtectedVRegs
    (rs2 rs1 rd : regidx) :
    JoltISA.ProgramWritesNoProtectedVReg
      (JoltISA.amoDoubleBinopProgram
        (fun dst lhs rhs => .XOR dst lhs rhs) rs2 rs1 rd) := by
  rcases eq_or_ne (JoltISA.isX0 rd) true with hrd | hrd
  · simp [JoltISA.amoDoubleBinopProgram,
      JoltISA.ProgramWritesNoProtectedVReg,
      JoltISA.InstrWritesNoProtectedVReg, JoltISA.DstWritesNoProtectedVReg,
      JoltISA.amoDstFor, JoltISA.sideEffectingRdZeroDst, hrd]
  · simp [JoltISA.amoDoubleBinopProgram,
      JoltISA.ProgramWritesNoProtectedVReg,
      JoltISA.InstrWritesNoProtectedVReg, JoltISA.DstWritesNoProtectedVReg,
      JoltISA.amoDstFor, JoltISA.sideEffectingRdZeroDst, hrd]


/-- Sail's generated `AMOXOR.D` result expression reduces to dword xor. -/
theorem amoxord_sail_result (rs2Val loaded : BitVec 64) :
    amoDwordSailResult amoop.AMOXOR
      (show BitVec (8 * 8) from
        trunc (m := (((8 : Nat) : Int) * (8 : Int)).toNat) rs2Val)
      (BitVec.setWidth (8 * 8) loaded) =
    rs2Val ^^^ loaded := by
  unfold amoDwordSailResult
  unfold trunc Sail.BitVec.truncate
  rfl

/-- Main public theorem for `AMOXOR.D`.

The theorem takes one primitive-only atomic bundle. Exact memory facts are
derived internally from that bundle. -/
private theorem amoxordProgram_core_eq_sail
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (h : AmoDwordProgramEqSailAssumptions amoop.AMOXOR rs2 rs1 rd js) :
    System.systemProjectResult ((JoltISA.execProgram
      (JoltISA.amoDoubleBinopProgram
        (fun dst lhs rhs => .XOR dst lhs rhs) rs2 rs1 rd)).run js) =
      (execute_AMO amoop.AMOXOR false false rs2 rs1 8 rd).run js.sail := by
  let addr := h.rs1_val
  let rs2Val := h.rs2_val
  have hbytes : MemBytesPresentAt js.sail addr 8 := by
    simpa [addr] using Assumptions.DwordPresent.memBytesPresentAt h.dword_present
  have hload_pmp : Assumptions.LoadPmpOk addr 8 js.sail := by
    simpa [addr] using h.load_pmp.subaccess (offset := 0) (accessWidth := 8) (by omega)
  have hstore_pmp : Assumptions.StorePmpOk addr 8 js.sail := by
    simpa [addr] using h.store_pmp.subaccess (offset := 0) (accessWidth := 8) (by omega)
  have hatomic_pmp : Assumptions.AtomicPmpOk amoop.AMOXOR addr 8 js.sail := by
    simpa [addr] using h.atomic_pmp.subaccess (offset := 0) (accessWidth := 8) (by omega)
  have hread_mmio : Assumptions.NotReadableMmio addr 8 js.sail := by
    simpa [addr] using h.not_readable_mmio.subaccess (offset := 0) (accessWidth := 8) (by omega)
  have hwrite_mmio : Assumptions.NotWritableMmio addr 8 js.sail := by
    simpa [addr] using h.not_writable_mmio.subaccess (offset := 0) (accessWidth := 8) (by omega)
  by_cases h_align : addr &&& (7 : BitVec 64) = 0
  · exact
      amo_dword_double_binop_program_eq_sail_aligned
        amoop.AMOXOR (fun dst lhs rhs => .XOR dst lhs rhs)
        rs2 rs1 rd js h.cur_privilege h.mstatus_mprv addr rs2Val
        (rs2Val ^^^ loaded_dword_at js.sail addr hbytes
          (amo_dword_aligned_no_ovf addr h_align))
        h.rs1_read h.rs2_read h.rdReadable.exists_value
        hbytes hload_pmp hstore_pmp hatomic_pmp hread_mmio hwrite_mmio
        h_align (by decide) h.linkedCSRs
        (amoxordProgramCore_doesNotWriteProtectedVRegs rs2 rs1 rd)
        (amo_dword_xor_middle_after_load_into rs2 js addr rs2Val
          (loaded_dword_at js.sail addr hbytes
            (amo_dword_aligned_no_ovf addr h_align))
          h.rs2_read)
        (amoxord_sail_result rs2Val
          (loaded_dword_at js.sail addr hbytes
            (amo_dword_aligned_no_ovf addr h_align)))
  · exact
      amo_dword_double_binop_program_eq_sail_misaligned
        amoop.AMOXOR (fun dst lhs rhs => .XOR dst lhs rhs)
        rs2 rs1 rd js addr rs2Val h.rs1_read h.rs2_read h.linkedCSRs h_align

/-- Main public theorem for `AMOXOR.D`. -/
def amoxordProgramEqSailStatement
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (_h : AmoDwordProgramEqSailAssumptions amoop.AMOXOR rs2 rs1 rd js) : Prop :=
  System.systemProjectResult
      ((JoltISA.execProgram
        (JoltISA.amoxordProgramAuto rd rs1 rs2)).run js) =
    (execute_AMO amoop.AMOXOR false false rs2 rs1 8 rd).run js.sail

theorem amoxordProgram_eq_sail
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (h : AmoDwordProgramEqSailAssumptions amoop.AMOXOR rs2 rs1 rd js) :
    amoxordProgramEqSailStatement rs2 rs1 rd js h := by
  unfold amoxordProgramEqSailStatement
  have hcore := amoxordProgram_core_eq_sail rs2 rs1 rd js h
  cases hrd : JoltISA.isX0 rd <;>
    simpa only [JoltISA.amoxordProgramAuto,
      JoltISA.amoDoubleBinopProgram,
      JoltISA.amoDoubleBinopOldVRegFor,
      JoltISA.amoDoubleBinopNewVRegFor,
      JoltISA.amoVRegFor, JoltISA.amoDstFor,
      JoltISA.sideEffectingRdZeroDst, JoltISA.rdZeroRewriteVReg,
      hrd, Bool.false_eq_true, if_false, if_true] using hcore

end AtomicFamily

end
