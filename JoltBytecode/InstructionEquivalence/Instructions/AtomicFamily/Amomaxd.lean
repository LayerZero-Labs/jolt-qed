import JoltBytecode.InstructionEquivalence.Instructions.AtomicFamily.Dword
import JoltBytecode.JoltISA.ExpansionsAutomated

set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace AtomicFamily

theorem amomaxdProgram_doesNotWriteProtectedVRegs
    (rs2 rs1 rd : regidx) :
    JoltISA.ProgramWritesNoProtectedVReg
      (JoltISA.amomaxdProgramAuto rd rs1 rs2) := by
  unfold JoltISA.amomaxdProgramAuto
  split <;>
    simp only [JoltISA.ProgramWritesNoProtectedVReg,
      JoltISA.InstrWritesNoProtectedVReg, JoltISA.DstWritesNoProtectedVReg,
      true_and, and_true] <;>
    repeat' apply And.intro
  all_goals exact JoltISA.not_protected_of_instructionTmp rfl

private theorem amomaxdProgramCore_doesNotWriteProtectedVRegs
    (rs2 rs1 rd : regidx) :
    JoltISA.ProgramWritesNoProtectedVReg
      (JoltISA.amoDoubleSelectProgram
        (fun dst lhs rhs => .SLT dst lhs rhs)
        (.vreg (JoltISA.amoOldVRegFor rd)) (.xreg rs2) rs2 rs1 rd) := by
  rcases eq_or_ne (JoltISA.isX0 rd) true with hrd | hrd
  · simp [JoltISA.amoDoubleSelectProgram,
      JoltISA.ProgramWritesNoProtectedVReg,
      JoltISA.InstrWritesNoProtectedVReg, JoltISA.DstWritesNoProtectedVReg,
      JoltISA.amoDstFor, JoltISA.sideEffectingRdZeroDst, hrd]
  · simp [JoltISA.amoDoubleSelectProgram,
      JoltISA.ProgramWritesNoProtectedVReg,
      JoltISA.InstrWritesNoProtectedVReg, JoltISA.DstWritesNoProtectedVReg,
      JoltISA.amoDstFor, JoltISA.sideEffectingRdZeroDst, hrd]


/-- Sail's generated `AMOMAX.D` result expression reduces to signed max. -/
theorem amomaxd_sail_result (rs2Val loaded : BitVec 64) :
    amoDwordSailResult amoop.AMOMAX
      (show BitVec (8 * 8) from
        trunc (m := (((8 : Nat) : Int) * (8 : Int)).toNat) rs2Val)
      (BitVec.setWidth (8 * 8) loaded) =
    if (zopz0zK_s rs2Val loaded : Bool) then rs2Val else loaded := by
  unfold amoDwordSailResult
  unfold trunc Sail.BitVec.truncate
  rfl

/-- Main public theorem for `AMOMAX.D`.

The theorem takes one primitive-only atomic bundle. Exact memory facts are
derived internally from that bundle. -/
private theorem amomaxdProgram_core_eq_sail
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (h : AmoDwordProgramEqSailAssumptions amoop.AMOMAX rs2 rs1 rd js) :
    System.systemProjectResult ((JoltISA.execProgram
      (JoltISA.amoDoubleSelectProgram
        (fun dst lhs rhs => .SLT dst lhs rhs)
        (.vreg (JoltISA.amoOldVRegFor rd)) (.xreg rs2) rs2 rs1 rd
        )).run js) =
      (execute_AMO amoop.AMOMAX false false rs2 rs1 8 rd).run js.sail := by
  let addr := h.rs1_val
  let rs2Val := h.rs2_val
  have hbytes : MemBytesPresentAt js.sail addr 8 := by
    simpa [addr] using Assumptions.DwordPresent.memBytesPresentAt h.dword_present
  have hload_pmp : Assumptions.LoadPmpOk addr 8 js.sail := by
    simpa [addr] using h.load_pmp.subaccess (offset := 0) (accessWidth := 8) (by omega)
  have hstore_pmp : Assumptions.StorePmpOk addr 8 js.sail := by
    simpa [addr] using h.store_pmp.subaccess (offset := 0) (accessWidth := 8) (by omega)
  have hatomic_pmp : Assumptions.AtomicPmpOk amoop.AMOMAX addr 8 js.sail := by
    simpa [addr] using h.atomic_pmp.subaccess (offset := 0) (accessWidth := 8) (by omega)
  have hread_mmio : Assumptions.NotReadableMmio addr 8 js.sail := by
    simpa [addr] using h.not_readable_mmio.subaccess (offset := 0) (accessWidth := 8) (by omega)
  have hwrite_mmio : Assumptions.NotWritableMmio addr 8 js.sail := by
    simpa [addr] using h.not_writable_mmio.subaccess (offset := 0) (accessWidth := 8) (by omega)
  by_cases h_align : addr &&& (7 : BitVec 64) = 0
  · exact
      amo_dword_double_select_program_eq_sail_aligned
        amoop.AMOMAX (fun dst lhs rhs => .SLT dst lhs rhs)
        (.vreg (JoltISA.amoOldVRegFor rd)) (.xreg rs2)
        rs2 rs1 rd js h.cur_privilege h.mstatus_mprv addr rs2Val
        (if (zopz0zK_s rs2Val
            (loaded_dword_at js.sail addr hbytes
              (amo_dword_aligned_no_ovf addr h_align)) : Bool) then
          rs2Val
        else
          loaded_dword_at js.sail addr hbytes
            (amo_dword_aligned_no_ovf addr h_align))
        h.rs1_read h.rs2_read h.rdReadable.exists_value
        hbytes hload_pmp hstore_pmp hatomic_pmp hread_mmio hwrite_mmio
        h_align (by decide) h.linkedCSRs
        (amomaxdProgramCore_doesNotWriteProtectedVRegs rs2 rs1 rd)
        (amo_dword_max_middle_after_load_for rd rs2 js addr rs2Val
          (loaded_dword_at js.sail addr hbytes
            (amo_dword_aligned_no_ovf addr h_align))
          h.rs2_read)
        (amomaxd_sail_result rs2Val
          (loaded_dword_at js.sail addr hbytes
            (amo_dword_aligned_no_ovf addr h_align)))
  · exact
      amo_dword_double_select_program_eq_sail_misaligned
        amoop.AMOMAX (fun dst lhs rhs => .SLT dst lhs rhs)
        (.vreg (JoltISA.amoOldVRegFor rd)) (.xreg rs2)
        rs2 rs1 rd js addr rs2Val h.rs1_read h.rs2_read h.linkedCSRs h_align

/-- Main public theorem for `AMOMAX.D`. -/
def amomaxdProgramEqSailStatement
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (_h : AmoDwordProgramEqSailAssumptions amoop.AMOMAX rs2 rs1 rd js) : Prop :=
  System.systemProjectResult
      ((JoltISA.execProgram
        (JoltISA.amomaxdProgramAuto rd rs1 rs2)).run js) =
    (execute_AMO amoop.AMOMAX false false rs2 rs1 8 rd).run js.sail

theorem amomaxdProgram_eq_sail
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (h : AmoDwordProgramEqSailAssumptions amoop.AMOMAX rs2 rs1 rd js) :
    amomaxdProgramEqSailStatement rs2 rs1 rd js h := by
  unfold amomaxdProgramEqSailStatement
  have hcore := amomaxdProgram_core_eq_sail rs2 rs1 rd js h
  cases hrd : JoltISA.isX0 rd <;>
    simpa only [JoltISA.amomaxdProgramAuto,
      JoltISA.amoDoubleSelectProgram,
      JoltISA.amoOldVRegFor, JoltISA.amoNewVRegFor,
      JoltISA.amoTmpVRegFor, JoltISA.amoVRegFor,
      JoltISA.amoDstFor, JoltISA.sideEffectingRdZeroDst,
      JoltISA.rdZeroRewriteVReg,
      hrd, Bool.false_eq_true, if_false, if_true] using hcore

end AtomicFamily

end
