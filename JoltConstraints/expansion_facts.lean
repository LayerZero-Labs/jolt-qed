/-
Syntactic facts about the rows each expansion emits. `trace_interface.lean` turns
them into `ExpansionRowsValid`.
-/
import JoltConstraints.expansion_checks
import JoltConstraints.inline_rows_ok

open LeanRV64D

set_option autoImplicit false

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail LeanRV64D LeanRV64D.Functions

namespace ExpansionFacts

-- Evaluate the unchanged sequence checks after a program's branches are exposed.
macro "finish_rows_ok" : tactic => `(tactic| (
  all_goals
    simp only [JoltISA.Program.instrs, sequenceOk, rowsOk, sequenceRowOk, x0Ok, ordinary,
      JoltISA.Instr.destination?, isCanonicalNoOp, Bool.not_false, shiftsOk, shiftPairsOk,
      immShiftOk, isRegisterShift, masksFed, maskOk_srliBitmask, maskOk_sraiBitmask,
      wordMaskOk_shamt, jumpEndNoStore, sequenceJalrsVirtual, virtualJalrBaseUnwritten,
      advicePairsOk, nativeJalrBaseOk, loadWindowsOk, loadSelfChecked,
      leftOperandIsRegister, List.getLast?_cons, List.getLast?_nil,
      List.all_cons, List.all_nil, ExpansionTempLiveness.writes, *]
    first
    | rfl
    | cases_type regidx
      try simp only [BEq.beq, instBEqRegidx.beq, decide_true]
      rfl))

-- Unfold one program and expose its branches before checking every row.
macro "rows_ok " program:ident : tactic => `(tactic| (
  unfold $program
  repeat' split
  finish_rows_ok))

-- Jolt's CSR programs share read, write and operand-preparation combinators.
-- Expose those combinators once, then use the same sequence checks as above.
macro "system_rows_ok " program:ident : tactic => `(tactic| (
  unfold $program
  try dsimp only [JoltISA.csrReadInto, JoltISA.csrSwapWrite,
    JoltISA.csrBitUpdateProgram, JoltISA.csrImmediateBitUpdateProgram]
  repeat' (split <;> try simp_all only [Bool.not_eq_true, Bool.not_eq_false,
    Bool.and_eq_true, Bool.not_eq_true', Bool.not_eq_false', Bool.not_false, Bool.not_true,
    true_and, false_and, and_true, and_false, Bool.false_eq_true, Bool.true_eq_false,
    ↓reduceIte])
  finish_rows_ok))

-- For a pure program only rd ≠ x0 matters: take that branch first.
macro "pure_rows_ok " program:ident notX0:ident : tactic => `(tactic| (
  unfold $program
  simp only [$notX0:ident, Bool.false_eq_true, ↓reduceIte]
  repeat' split
  all_goals
    simp only [JoltISA.Program.instrs, sequenceOk, rowsOk, sequenceRowOk, x0Ok, ordinary,
      JoltISA.Instr.destination?, isCanonicalNoOp, Bool.not_false, shiftsOk, shiftPairsOk,
      immShiftOk, isRegisterShift, masksFed, maskOk_srliBitmask, maskOk_sraiBitmask,
      wordMaskOk_shamt, jumpEndNoStore, sequenceJalrsVirtual, virtualJalrBaseUnwritten,
      advicePairsOk, nativeJalrBaseOk, loadWindowsOk, loadSelfChecked,
      leftOperandIsRegister, List.getLast?_cons, List.getLast?_nil,
      List.all_cons, List.all_nil, ExpansionTempLiveness.writes, *]
    rfl))

-- Pure source-only programs: with rd = x0 Rust emits the native no-op instead
-- (ExpandedSource.ofPureProgram), so only rd ≠ x0 matters.

theorem slli_ok (rd rs1 : regidx) (shamt : BitVec 6) (notX0 : JoltISA.isX0 rd = false) :
    sequenceOk (JoltISA.slliProgramAuto rd rs1 shamt).instrs = true := by
  pure_rows_ok JoltISA.slliProgramAuto notX0

theorem srli_ok (rd rs1 : regidx) (shamt : BitVec 6) (notX0 : JoltISA.isX0 rd = false) :
    sequenceOk (JoltISA.srliProgramAuto rd rs1 shamt).instrs = true := by
  pure_rows_ok JoltISA.srliProgramAuto notX0

theorem srai_ok (rd rs1 : regidx) (shamt : BitVec 6) (notX0 : JoltISA.isX0 rd = false) :
    sequenceOk (JoltISA.sraiProgramAuto rd rs1 shamt).instrs = true := by
  pure_rows_ok JoltISA.sraiProgramAuto notX0

theorem sll_ok (rd rs1 rs2 : regidx) (notX0 : JoltISA.isX0 rd = false) :
    sequenceOk (JoltISA.sllProgramAuto rd rs1 rs2).instrs = true := by
  pure_rows_ok JoltISA.sllProgramAuto notX0

theorem srl_ok (rd rs1 rs2 : regidx) (notX0 : JoltISA.isX0 rd = false) :
    sequenceOk (JoltISA.srlProgramAuto rd rs1 rs2).instrs = true := by
  pure_rows_ok JoltISA.srlProgramAuto notX0

theorem sra_ok (rd rs1 rs2 : regidx) (notX0 : JoltISA.isX0 rd = false) :
    sequenceOk (JoltISA.sraProgramAuto rd rs1 rs2).instrs = true := by
  pure_rows_ok JoltISA.sraProgramAuto notX0

theorem slliw_ok (rd rs1 : regidx) (shamt : BitVec 5) (notX0 : JoltISA.isX0 rd = false) :
    sequenceOk (JoltISA.slliwProgramAuto rd rs1 shamt).instrs = true := by
  pure_rows_ok JoltISA.slliwProgramAuto notX0

theorem srliw_ok (rd rs1 : regidx) (shamt : BitVec 5) (notX0 : JoltISA.isX0 rd = false) :
    sequenceOk (JoltISA.srliwProgramAuto rd rs1 shamt).instrs = true := by
  pure_rows_ok JoltISA.srliwProgramAuto notX0

theorem sraiw_ok (rd rs1 : regidx) (shamt : BitVec 5) (notX0 : JoltISA.isX0 rd = false) :
    sequenceOk (JoltISA.sraiwProgramAuto rd rs1 shamt).instrs = true := by
  pure_rows_ok JoltISA.sraiwProgramAuto notX0

theorem sllw_ok (rd rs1 rs2 : regidx) (notX0 : JoltISA.isX0 rd = false) :
    sequenceOk (JoltISA.sllwProgramAuto rd rs1 rs2).instrs = true := by
  pure_rows_ok JoltISA.sllwProgramAuto notX0

theorem srlw_ok (rd rs1 rs2 : regidx) (notX0 : JoltISA.isX0 rd = false) :
    sequenceOk (JoltISA.srlwProgramAuto rd rs1 rs2).instrs = true := by
  pure_rows_ok JoltISA.srlwProgramAuto notX0

theorem sraw_ok (rd rs1 rs2 : regidx) (notX0 : JoltISA.isX0 rd = false) :
    sequenceOk (JoltISA.srawProgramAuto rd rs1 rs2).instrs = true := by
  pure_rows_ok JoltISA.srawProgramAuto notX0

theorem mulh_ok (rd rs1 rs2 : regidx) (notX0 : JoltISA.isX0 rd = false) :
    sequenceOk (JoltISA.mulhProgramAuto rd rs1 rs2).instrs = true := by
  pure_rows_ok JoltISA.mulhProgramAuto notX0

theorem mulhsu_ok (rd rs1 rs2 : regidx) (notX0 : JoltISA.isX0 rd = false) :
    sequenceOk (JoltISA.mulhsuProgramAuto rd rs1 rs2).instrs = true := by
  pure_rows_ok JoltISA.mulhsuProgramAuto notX0

theorem div_ok (rd rs1 rs2 : regidx) (q : BitVec 64) (notX0 : JoltISA.isX0 rd = false) :
    sequenceOk (JoltISA.divProgramAuto rd rs1 rs2 q).instrs = true := by
  pure_rows_ok JoltISA.divProgramAuto notX0

theorem divu_ok (rd rs1 rs2 : regidx) (q : BitVec 64) (notX0 : JoltISA.isX0 rd = false) :
    sequenceOk (JoltISA.divuProgramAuto rd rs1 rs2 q).instrs = true := by
  pure_rows_ok JoltISA.divuProgramAuto notX0

theorem rem_ok (rd rs1 rs2 : regidx) (q : BitVec 64) (notX0 : JoltISA.isX0 rd = false) :
    sequenceOk (JoltISA.remProgramAuto rd rs1 rs2 q).instrs = true := by
  pure_rows_ok JoltISA.remProgramAuto notX0

theorem remu_ok (rd rs1 rs2 : regidx) (q : BitVec 64) (notX0 : JoltISA.isX0 rd = false) :
    sequenceOk (JoltISA.remuProgramAuto rd rs1 rs2 q).instrs = true := by
  pure_rows_ok JoltISA.remuProgramAuto notX0

theorem divw_ok (rd rs1 rs2 : regidx) (q : BitVec 64) (notX0 : JoltISA.isX0 rd = false) :
    sequenceOk (JoltISA.divwProgramAuto rd rs1 rs2 q).instrs = true := by
  pure_rows_ok JoltISA.divwProgramAuto notX0

theorem divuw_ok (rd rs1 rs2 : regidx) (q : BitVec 64) (notX0 : JoltISA.isX0 rd = false) :
    sequenceOk (JoltISA.divuwProgramAuto rd rs1 rs2 q).instrs = true := by
  pure_rows_ok JoltISA.divuwProgramAuto notX0

theorem remw_ok (rd rs1 rs2 : regidx) (q : BitVec 64) (notX0 : JoltISA.isX0 rd = false) :
    sequenceOk (JoltISA.remwProgramAuto rd rs1 rs2 q).instrs = true := by
  pure_rows_ok JoltISA.remwProgramAuto notX0

theorem remuw_ok (rd rs1 rs2 : regidx) (q : BitVec 64) (notX0 : JoltISA.isX0 rd = false) :
    sequenceOk (JoltISA.remuwProgramAuto rd rs1 rs2 q).instrs = true := by
  pure_rows_ok JoltISA.remuwProgramAuto notX0

-- Programs with side effects, or with no rd, in every case.

theorem lb_ok (rd rs1 : regidx) (imm : BitVec 12) :
    sequenceOk (JoltISA.lbProgramAuto rd rs1 imm).instrs = true := by
  rows_ok JoltISA.lbProgramAuto

theorem lh_ok (rd rs1 : regidx) (imm : BitVec 12) :
    sequenceOk (JoltISA.lhProgramAuto rd rs1 imm).instrs = true := by
  rows_ok JoltISA.lhProgramAuto

theorem lw_ok (rd rs1 : regidx) (imm : BitVec 12) :
    sequenceOk (JoltISA.lwProgramAuto rd rs1 imm).instrs = true := by
  rows_ok JoltISA.lwProgramAuto

theorem lbu_ok (rd rs1 : regidx) (imm : BitVec 12) :
    sequenceOk (JoltISA.lbuProgramAuto rd rs1 imm).instrs = true := by
  rows_ok JoltISA.lbuProgramAuto

theorem lhu_ok (rd rs1 : regidx) (imm : BitVec 12) :
    sequenceOk (JoltISA.lhuProgramAuto rd rs1 imm).instrs = true := by
  rows_ok JoltISA.lhuProgramAuto

theorem lwu_ok (rd rs1 : regidx) (imm : BitVec 12) :
    sequenceOk (JoltISA.lwuProgramAuto rd rs1 imm).instrs = true := by
  rows_ok JoltISA.lwuProgramAuto

theorem sb_ok (rs1 rs2 : regidx) (imm : BitVec 12) :
    sequenceOk (JoltISA.sbProgramAuto rs1 rs2 imm).instrs = true := by
  rows_ok JoltISA.sbProgramAuto

theorem sh_ok (rs1 rs2 : regidx) (imm : BitVec 12) :
    sequenceOk (JoltISA.shProgramAuto rs1 rs2 imm).instrs = true := by
  rows_ok JoltISA.shProgramAuto

theorem sw_ok (rs1 rs2 : regidx) (imm : BitVec 12) :
    sequenceOk (JoltISA.swProgramAuto rs1 rs2 imm).instrs = true := by
  rows_ok JoltISA.swProgramAuto

theorem amoswapw_ok (rd rs1 rs2 : regidx) :
    sequenceOk (JoltISA.amoswapwProgramAuto rd rs1 rs2).instrs = true := by
  rows_ok JoltISA.amoswapwProgramAuto

theorem amoaddw_ok (rd rs1 rs2 : regidx) :
    sequenceOk (JoltISA.amoaddwProgramAuto rd rs1 rs2).instrs = true := by
  rows_ok JoltISA.amoaddwProgramAuto

theorem amoxorw_ok (rd rs1 rs2 : regidx) :
    sequenceOk (JoltISA.amoxorwProgramAuto rd rs1 rs2).instrs = true := by
  rows_ok JoltISA.amoxorwProgramAuto

theorem amoandw_ok (rd rs1 rs2 : regidx) :
    sequenceOk (JoltISA.amoandwProgramAuto rd rs1 rs2).instrs = true := by
  rows_ok JoltISA.amoandwProgramAuto

theorem amoorw_ok (rd rs1 rs2 : regidx) :
    sequenceOk (JoltISA.amoorwProgramAuto rd rs1 rs2).instrs = true := by
  rows_ok JoltISA.amoorwProgramAuto

theorem amominw_ok (rd rs1 rs2 : regidx) :
    sequenceOk (JoltISA.amominwProgramAuto rd rs1 rs2).instrs = true := by
  rows_ok JoltISA.amominwProgramAuto

theorem amomaxw_ok (rd rs1 rs2 : regidx) :
    sequenceOk (JoltISA.amomaxwProgramAuto rd rs1 rs2).instrs = true := by
  rows_ok JoltISA.amomaxwProgramAuto

theorem amominuw_ok (rd rs1 rs2 : regidx) :
    sequenceOk (JoltISA.amominuwProgramAuto rd rs1 rs2).instrs = true := by
  rows_ok JoltISA.amominuwProgramAuto

theorem amomaxuw_ok (rd rs1 rs2 : regidx) :
    sequenceOk (JoltISA.amomaxuwProgramAuto rd rs1 rs2).instrs = true := by
  rows_ok JoltISA.amomaxuwProgramAuto

theorem amoswapd_ok (rd rs1 rs2 : regidx) :
    sequenceOk (JoltISA.amoswapdProgramAuto rd rs1 rs2).instrs = true := by
  rows_ok JoltISA.amoswapdProgramAuto

theorem amoaddd_ok (rd rs1 rs2 : regidx) :
    sequenceOk (JoltISA.amoadddProgramAuto rd rs1 rs2).instrs = true := by
  rows_ok JoltISA.amoadddProgramAuto

theorem amoxord_ok (rd rs1 rs2 : regidx) :
    sequenceOk (JoltISA.amoxordProgramAuto rd rs1 rs2).instrs = true := by
  rows_ok JoltISA.amoxordProgramAuto

theorem amoandd_ok (rd rs1 rs2 : regidx) :
    sequenceOk (JoltISA.amoanddProgramAuto rd rs1 rs2).instrs = true := by
  rows_ok JoltISA.amoanddProgramAuto

theorem amoord_ok (rd rs1 rs2 : regidx) :
    sequenceOk (JoltISA.amoordProgramAuto rd rs1 rs2).instrs = true := by
  rows_ok JoltISA.amoordProgramAuto

theorem amomind_ok (rd rs1 rs2 : regidx) :
    sequenceOk (JoltISA.amomindProgramAuto rd rs1 rs2).instrs = true := by
  rows_ok JoltISA.amomindProgramAuto

theorem amomaxd_ok (rd rs1 rs2 : regidx) :
    sequenceOk (JoltISA.amomaxdProgramAuto rd rs1 rs2).instrs = true := by
  rows_ok JoltISA.amomaxdProgramAuto

theorem amominud_ok (rd rs1 rs2 : regidx) :
    sequenceOk (JoltISA.amominudProgramAuto rd rs1 rs2).instrs = true := by
  rows_ok JoltISA.amominudProgramAuto

theorem amomaxud_ok (rd rs1 rs2 : regidx) :
    sequenceOk (JoltISA.amomaxudProgramAuto rd rs1 rs2).instrs = true := by
  rows_ok JoltISA.amomaxudProgramAuto

theorem lrw_ok (rd rs1 rs2 : regidx) :
    sequenceOk (JoltISA.lrwProgramAuto rd rs1 rs2).instrs = true := by
  rows_ok JoltISA.lrwProgramAuto

theorem lrd_ok (rd rs1 rs2 : regidx) :
    sequenceOk (JoltISA.lrdProgramAuto rd rs1 rs2).instrs = true := by
  rows_ok JoltISA.lrdProgramAuto

theorem scw_ok (rd rs1 rs2 : regidx) :
    sequenceOk (JoltISA.scwProgramAuto rd rs1 rs2).instrs = true := by
  rows_ok JoltISA.scwProgramAuto

theorem scd_ok (rd rs1 rs2 : regidx) :
    sequenceOk (JoltISA.scdProgramAuto rd rs1 rs2).instrs = true := by
  rows_ok JoltISA.scdProgramAuto

theorem advicelb_ok (rd : regidx) :
    sequenceOk (JoltISA.advicelbProgramAuto rd).instrs = true := by
  rows_ok JoltISA.advicelbProgramAuto

theorem advicelh_ok (rd : regidx) :
    sequenceOk (JoltISA.advicelhProgramAuto rd).instrs = true := by
  rows_ok JoltISA.advicelhProgramAuto

theorem advicelw_ok (rd : regidx) :
    sequenceOk (JoltISA.advicelwProgramAuto rd).instrs = true := by
  rows_ok JoltISA.advicelwProgramAuto

theorem adviceld_ok (rd : regidx) :
    sequenceOk (JoltISA.adviceldProgramAuto rd).instrs = true := by
  rows_ok JoltISA.adviceldProgramAuto

theorem ecall_ok :
    sequenceOk (JoltISA.ecallProgram).instrs = true := by
  rows_ok JoltISA.ecallProgram

theorem ebreak_ok :
    sequenceOk (JoltISA.ebreakProgram).instrs = true := by
  rows_ok JoltISA.ebreakProgram

theorem mret_ok :
    sequenceOk (JoltISA.mretProgram).instrs = true := by
  rows_ok JoltISA.mretProgram

/-- The mstatus case of the CSR sequence check, with operands left symbolic. -/
private theorem csrrw_mstatus (rs1 rd : regidx) :
    sequenceOk (JoltISA.csrrwProgram .mstatus rs1 rd).instrs = true := by
  system_rows_ok JoltISA.csrrwProgram

/-- The mtvec case of the CSR sequence check, with operands left symbolic. -/
private theorem csrrw_mtvec (rs1 rd : regidx) :
    sequenceOk (JoltISA.csrrwProgram .mtvec rs1 rd).instrs = true := by
  system_rows_ok JoltISA.csrrwProgram

/-- The mscratch case of the CSR sequence check, with operands left symbolic. -/
private theorem csrrw_mscratch (rs1 rd : regidx) :
    sequenceOk (JoltISA.csrrwProgram .mscratch rs1 rd).instrs = true := by
  system_rows_ok JoltISA.csrrwProgram

/-- The mepc case of the CSR sequence check, with operands left symbolic. -/
private theorem csrrw_mepc (rs1 rd : regidx) :
    sequenceOk (JoltISA.csrrwProgram .mepc rs1 rd).instrs = true := by
  system_rows_ok JoltISA.csrrwProgram

/-- The mcause case of the CSR sequence check, with operands left symbolic. -/
private theorem csrrw_mcause (rs1 rd : regidx) :
    sequenceOk (JoltISA.csrrwProgram .mcause rs1 rd).instrs = true := by
  system_rows_ok JoltISA.csrrwProgram

/-- The mtval case of the CSR sequence check, with operands left symbolic. -/
private theorem csrrw_mtval (rs1 rd : regidx) :
    sequenceOk (JoltISA.csrrwProgram .mtval rs1 rd).instrs = true := by
  system_rows_ok JoltISA.csrrwProgram

/-- Every CSRRW expansion passes the sequence checks.
For example, mtvec's two temporaries are written before their first reads. -/
theorem csrrw_ok (csr : JoltISA.SystemCSR) (rs1 rd : regidx) :
    sequenceOk (JoltISA.csrrwProgram csr rs1 rd).instrs = true := by
  cases csr with
  | mstatus => exact csrrw_mstatus rs1 rd
  | mtvec => exact csrrw_mtvec rs1 rd
  | mscratch => exact csrrw_mscratch rs1 rd
  | mepc => exact csrrw_mepc rs1 rd
  | mcause => exact csrrw_mcause rs1 rd
  | mtval => exact csrrw_mtval rs1 rd

/-- The mstatus case of the CSR sequence check, with operands left symbolic. -/
private theorem csrBitUpdate_set_mstatus (rs1 rd : regidx) :
    sequenceOk (JoltISA.csrBitUpdateProgram false .mstatus rs1 rd).instrs = true := by
  system_rows_ok JoltISA.csrBitUpdateProgram

/-- The mtvec case of the CSR sequence check, with operands left symbolic. -/
private theorem csrBitUpdate_set_mtvec (rs1 rd : regidx) :
    sequenceOk (JoltISA.csrBitUpdateProgram false .mtvec rs1 rd).instrs = true := by
  system_rows_ok JoltISA.csrBitUpdateProgram

/-- The mscratch case of the CSR sequence check, with operands left symbolic. -/
private theorem csrBitUpdate_set_mscratch (rs1 rd : regidx) :
    sequenceOk (JoltISA.csrBitUpdateProgram false .mscratch rs1 rd).instrs = true := by
  system_rows_ok JoltISA.csrBitUpdateProgram

/-- The mepc case of the CSR sequence check, with operands left symbolic. -/
private theorem csrBitUpdate_set_mepc (rs1 rd : regidx) :
    sequenceOk (JoltISA.csrBitUpdateProgram false .mepc rs1 rd).instrs = true := by
  system_rows_ok JoltISA.csrBitUpdateProgram

/-- The mcause case of the CSR sequence check, with operands left symbolic. -/
private theorem csrBitUpdate_set_mcause (rs1 rd : regidx) :
    sequenceOk (JoltISA.csrBitUpdateProgram false .mcause rs1 rd).instrs = true := by
  system_rows_ok JoltISA.csrBitUpdateProgram

/-- The mtval case of the CSR sequence check, with operands left symbolic. -/
private theorem csrBitUpdate_set_mtval (rs1 rd : regidx) :
    sequenceOk (JoltISA.csrBitUpdateProgram false .mtval rs1 rd).instrs = true := by
  system_rows_ok JoltISA.csrBitUpdateProgram

/-- The mstatus case of the CSR sequence check, with operands left symbolic. -/
private theorem csrBitUpdate_clear_mstatus (rs1 rd : regidx) :
    sequenceOk (JoltISA.csrBitUpdateProgram true .mstatus rs1 rd).instrs = true := by
  system_rows_ok JoltISA.csrBitUpdateProgram

/-- The mtvec case of the CSR sequence check, with operands left symbolic. -/
private theorem csrBitUpdate_clear_mtvec (rs1 rd : regidx) :
    sequenceOk (JoltISA.csrBitUpdateProgram true .mtvec rs1 rd).instrs = true := by
  system_rows_ok JoltISA.csrBitUpdateProgram

/-- The mscratch case of the CSR sequence check, with operands left symbolic. -/
private theorem csrBitUpdate_clear_mscratch (rs1 rd : regidx) :
    sequenceOk (JoltISA.csrBitUpdateProgram true .mscratch rs1 rd).instrs = true := by
  system_rows_ok JoltISA.csrBitUpdateProgram

/-- The mepc case of the CSR sequence check, with operands left symbolic. -/
private theorem csrBitUpdate_clear_mepc (rs1 rd : regidx) :
    sequenceOk (JoltISA.csrBitUpdateProgram true .mepc rs1 rd).instrs = true := by
  system_rows_ok JoltISA.csrBitUpdateProgram

/-- The mcause case of the CSR sequence check, with operands left symbolic. -/
private theorem csrBitUpdate_clear_mcause (rs1 rd : regidx) :
    sequenceOk (JoltISA.csrBitUpdateProgram true .mcause rs1 rd).instrs = true := by
  system_rows_ok JoltISA.csrBitUpdateProgram

/-- The mtval case of the CSR sequence check, with operands left symbolic. -/
private theorem csrBitUpdate_clear_mtval (rs1 rd : regidx) :
    sequenceOk (JoltISA.csrBitUpdateProgram true .mtval rs1 rd).instrs = true := by
  system_rows_ok JoltISA.csrBitUpdateProgram

/-- Jolt's shared register CSR bit-update routine passes the sequence checks.
For example, both setting and clearing mstatus preserve canonical operands. -/
theorem csrBitUpdate_ok (clear : Bool) (csr : JoltISA.SystemCSR) (rs1 rd : regidx) :
    sequenceOk (JoltISA.csrBitUpdateProgram clear csr rs1 rd).instrs = true := by
  cases clear <;> cases csr
  · exact csrBitUpdate_set_mstatus rs1 rd
  · exact csrBitUpdate_set_mtvec rs1 rd
  · exact csrBitUpdate_set_mscratch rs1 rd
  · exact csrBitUpdate_set_mepc rs1 rd
  · exact csrBitUpdate_set_mcause rs1 rd
  · exact csrBitUpdate_set_mtval rs1 rd
  · exact csrBitUpdate_clear_mstatus rs1 rd
  · exact csrBitUpdate_clear_mtvec rs1 rd
  · exact csrBitUpdate_clear_mscratch rs1 rd
  · exact csrBitUpdate_clear_mepc rs1 rd
  · exact csrBitUpdate_clear_mcause rs1 rd
  · exact csrBitUpdate_clear_mtval rs1 rd

/-- Every CSRRS expansion passes the sequence checks, including the x0 no-op. -/
theorem csrrs_ok (csr : JoltISA.SystemCSR) (rs1 rd : regidx) :
    sequenceOk (JoltISA.csrrsProgram csr rs1 rd).instrs = true :=
  csrBitUpdate_ok false csr rs1 rd

/-- Every CSRRC expansion passes the sequence checks, including an aliased rd/rs1. -/
theorem csrrc_ok (csr : JoltISA.SystemCSR) (rs1 rd : regidx) :
    sequenceOk (JoltISA.csrrcProgram csr rs1 rd).instrs = true :=
  csrBitUpdate_ok true csr rs1 rd

/-- Every CSRRWI expansion passes the sequence checks.
For example, a reserved mtvec MODE needs no instruction-local temporary. -/
theorem csrrwi_ok (csr : JoltISA.SystemCSR) (uimm : BitVec 5) (rd : regidx) :
    sequenceOk (JoltISA.csrrwiProgram csr uimm rd).instrs = true := by
  cases csr <;> system_rows_ok JoltISA.csrrwiProgram

/-- The mstatus case of the CSR sequence check, with operands left symbolic. -/
private theorem csrImmediateBitUpdate_set_mstatus (uimm : BitVec 5) (rd : regidx) :
    sequenceOk (JoltISA.csrImmediateBitUpdateProgram false .mstatus uimm rd).instrs = true := by
  system_rows_ok JoltISA.csrImmediateBitUpdateProgram

/-- The mtvec case of the CSR sequence check, with operands left symbolic. -/
private theorem csrImmediateBitUpdate_set_mtvec (uimm : BitVec 5) (rd : regidx) :
    sequenceOk (JoltISA.csrImmediateBitUpdateProgram false .mtvec uimm rd).instrs = true := by
  system_rows_ok JoltISA.csrImmediateBitUpdateProgram

/-- The mscratch case of the CSR sequence check, with operands left symbolic. -/
private theorem csrImmediateBitUpdate_set_mscratch (uimm : BitVec 5) (rd : regidx) :
    sequenceOk (JoltISA.csrImmediateBitUpdateProgram false .mscratch uimm rd).instrs = true := by
  system_rows_ok JoltISA.csrImmediateBitUpdateProgram

/-- The mepc case of the CSR sequence check, with operands left symbolic. -/
private theorem csrImmediateBitUpdate_set_mepc (uimm : BitVec 5) (rd : regidx) :
    sequenceOk (JoltISA.csrImmediateBitUpdateProgram false .mepc uimm rd).instrs = true := by
  system_rows_ok JoltISA.csrImmediateBitUpdateProgram

/-- The mcause case of the CSR sequence check, with operands left symbolic. -/
private theorem csrImmediateBitUpdate_set_mcause (uimm : BitVec 5) (rd : regidx) :
    sequenceOk (JoltISA.csrImmediateBitUpdateProgram false .mcause uimm rd).instrs = true := by
  system_rows_ok JoltISA.csrImmediateBitUpdateProgram

/-- The mtval case of the CSR sequence check, with operands left symbolic. -/
private theorem csrImmediateBitUpdate_set_mtval (uimm : BitVec 5) (rd : regidx) :
    sequenceOk (JoltISA.csrImmediateBitUpdateProgram false .mtval uimm rd).instrs = true := by
  system_rows_ok JoltISA.csrImmediateBitUpdateProgram

/-- The mstatus case of the CSR sequence check, with operands left symbolic. -/
private theorem csrImmediateBitUpdate_clear_mstatus (uimm : BitVec 5) (rd : regidx) :
    sequenceOk (JoltISA.csrImmediateBitUpdateProgram true .mstatus uimm rd).instrs = true := by
  system_rows_ok JoltISA.csrImmediateBitUpdateProgram

/-- The mtvec case of the CSR sequence check, with operands left symbolic. -/
private theorem csrImmediateBitUpdate_clear_mtvec (uimm : BitVec 5) (rd : regidx) :
    sequenceOk (JoltISA.csrImmediateBitUpdateProgram true .mtvec uimm rd).instrs = true := by
  system_rows_ok JoltISA.csrImmediateBitUpdateProgram

/-- The mscratch case of the CSR sequence check, with operands left symbolic. -/
private theorem csrImmediateBitUpdate_clear_mscratch (uimm : BitVec 5) (rd : regidx) :
    sequenceOk (JoltISA.csrImmediateBitUpdateProgram true .mscratch uimm rd).instrs = true := by
  system_rows_ok JoltISA.csrImmediateBitUpdateProgram

/-- The mepc case of the CSR sequence check, with operands left symbolic. -/
private theorem csrImmediateBitUpdate_clear_mepc (uimm : BitVec 5) (rd : regidx) :
    sequenceOk (JoltISA.csrImmediateBitUpdateProgram true .mepc uimm rd).instrs = true := by
  system_rows_ok JoltISA.csrImmediateBitUpdateProgram

/-- The mcause case of the CSR sequence check, with operands left symbolic. -/
private theorem csrImmediateBitUpdate_clear_mcause (uimm : BitVec 5) (rd : regidx) :
    sequenceOk (JoltISA.csrImmediateBitUpdateProgram true .mcause uimm rd).instrs = true := by
  system_rows_ok JoltISA.csrImmediateBitUpdateProgram

/-- The mtval case of the CSR sequence check, with operands left symbolic. -/
private theorem csrImmediateBitUpdate_clear_mtval (uimm : BitVec 5) (rd : regidx) :
    sequenceOk (JoltISA.csrImmediateBitUpdateProgram true .mtval uimm rd).instrs = true := by
  system_rows_ok JoltISA.csrImmediateBitUpdateProgram

/-- Jolt's shared immediate CSR bit-update routine passes the sequence checks.
For example, a zero effective mask with rd = x0 emits the canonical no-op. -/
theorem csrImmediateBitUpdate_ok
    (clear : Bool) (csr : JoltISA.SystemCSR) (uimm : BitVec 5) (rd : regidx) :
    sequenceOk (JoltISA.csrImmediateBitUpdateProgram clear csr uimm rd).instrs = true := by
  cases clear <;> cases csr
  · exact csrImmediateBitUpdate_set_mstatus uimm rd
  · exact csrImmediateBitUpdate_set_mtvec uimm rd
  · exact csrImmediateBitUpdate_set_mscratch uimm rd
  · exact csrImmediateBitUpdate_set_mepc uimm rd
  · exact csrImmediateBitUpdate_set_mcause uimm rd
  · exact csrImmediateBitUpdate_set_mtval uimm rd
  · exact csrImmediateBitUpdate_clear_mstatus uimm rd
  · exact csrImmediateBitUpdate_clear_mtvec uimm rd
  · exact csrImmediateBitUpdate_clear_mscratch uimm rd
  · exact csrImmediateBitUpdate_clear_mepc uimm rd
  · exact csrImmediateBitUpdate_clear_mcause uimm rd
  · exact csrImmediateBitUpdate_clear_mtval uimm rd

/-- Every CSRRSI expansion passes the sequence checks, including immediate zero. -/
theorem csrrsi_ok (csr : JoltISA.SystemCSR) (uimm : BitVec 5) (rd : regidx) :
    sequenceOk (JoltISA.csrrsiProgram csr uimm rd).instrs = true :=
  csrImmediateBitUpdate_ok false csr uimm rd

/-- Every CSRRCI expansion passes the sequence checks, including immediate zero. -/
theorem csrrci_ok (csr : JoltISA.SystemCSR) (uimm : BitVec 5) (rd : regidx) :
    sequenceOk (JoltISA.csrrciProgram csr uimm rd).instrs = true :=
  csrImmediateBitUpdate_ok true csr uimm rd

-- A branch's offset comes from a 13-bit immediate (FormatB, sign-extended).
def BranchOffsetOk : JoltISA.Instr → Prop
  | .BEQ _ _ imm | .BNE _ _ imm | .BLT _ _ imm | .BGE _ _ imm
  | .BLTU _ _ imm | .BGEU _ _ imm => ∃ offset : BitVec 13, imm = offset.signExtend 128
  | _ => True

-- Natives: one row, after Rust's rd = x0 rewrite. A native row writes x0 only as
-- the canonical no-op, its register operands are canonical, and it is not a shift
-- that reads a bitmask.
/-- Syntactic checks for a native row, including an architectural JALR base,
absence of a narrow advice load, and a load that range-checks its own value
(`loadWindowsOk`). For example, native JALR x0, 0(x2) passes after the
destination rewrite, while a lone one-byte advice load fails. -/
def nativeRowOk (instruction : JoltISA.Instr) : Bool :=
  (x0Ok instruction && JoltRegisterEncoding.instructionIsCanonical instruction &&
    immShiftOk instruction && !isRegisterShift instruction &&
    ExpansionTempLiveness.tempsReadAfterWrite [instruction] &&
    nativeJalrBaseOk instruction && advicePairsOk [instruction]) &&
    loadWindowsOk [instruction]

/-- A native row writes x0 only as the canonical no-op; for example, JAL x0 is rewritten. -/
theorem nativeRowOk_x0Ok (instruction : JoltISA.Instr)
    (ok : nativeRowOk instruction = true) : x0Ok instruction = true := by
  simp only [nativeRowOk, Bool.and_eq_true] at ok
  exact ok.1.1.1.1.1.1.1

/-- Native operands use canonical register storage; for example, x2 is architectural. -/
theorem nativeRowOk_canonical (instruction : JoltISA.Instr)
    (ok : nativeRowOk instruction = true) : JoltRegisterEncoding.instructionIsCanonical instruction = true := by
  simp only [nativeRowOk, Bool.and_eq_true] at ok
  exact ok.1.1.1.1.1.1.2

/-- A native immediate shift has a valid mask; for example, a native ADDI has no shift to check. -/
theorem nativeRowOk_immShiftOk (instruction : JoltISA.Instr)
    (ok : nativeRowOk instruction = true) : immShiftOk instruction = true := by
  simp only [nativeRowOk, Bool.and_eq_true] at ok
  exact ok.1.1.1.1.1.2

/-- A native row is not a register-mask shift; for example, JALR needs no mask producer. -/
theorem nativeRowOk_not_registerShift (instruction : JoltISA.Instr)
    (ok : nativeRowOk instruction = true) : isRegisterShift instruction = false := by
  simp only [nativeRowOk, Bool.and_eq_true] at ok
  simpa only [Bool.not_eq_eq_eq_not, Bool.not_true] using ok.1.1.1.1.2

/-- A native row does not read an uninitialized temporary; for example, JALR reads an architectural base. -/
theorem nativeRowOk_tempsReadAfterWrite (instruction : JoltISA.Instr)
    (ok : nativeRowOk instruction = true) : ExpansionTempLiveness.tempsReadAfterWrite [instruction] = true := by
  simp only [nativeRowOk, Bool.and_eq_true] at ok
  exact ok.1.1.1.2

/-- A native JALR reads an architectural base; for example, JALR x1, 0(x2) reads x2. -/
theorem nativeRowOk_nativeJalrBaseOk (instruction : JoltISA.Instr)
    (ok : nativeRowOk instruction = true) : nativeJalrBaseOk instruction = true := by
  simp only [nativeRowOk, Bool.and_eq_true] at ok
  exact ok.1.1.2

/-- A native row cannot be a narrow advice load; for example, AdviceLB needs a sequence. -/
theorem nativeRowOk_advicePairsOk (instruction : JoltISA.Instr)
    (ok : nativeRowOk instruction = true) : advicePairsOk [instruction] = true := by
  simp only [nativeRowOk, Bool.and_eq_true] at ok
  exact ok.1.2

/-- A native load checks itself; for example, native LD passes. -/
theorem nativeRowOk_loadWindowsOk (instruction : JoltISA.Instr)
    (ok : nativeRowOk instruction = true) : loadWindowsOk [instruction] = true := by
  simp only [nativeRowOk, Bool.and_eq_true] at ok
  exact ok.2

-- What `trace_interface.lean` needs from one source instruction's expansion.
def ExpandedOk : ExpandedSource → Prop
  | .native instruction => nativeRowOk instruction = true ∧ BranchOffsetOk instruction
  | .sequence instructions => sequenceOk instructions = true

-- Unfold Rust's rd = x0 rewrite on one native instruction, split on rd = x0, and
-- evaluate the checks.
macro "native_ok" : tactic => `(tactic| (
  simp only [ExpandedOk, ExpandedSource.ofNative, JoltISA.Instr.rewriteNative,
    JoltISA.Instr.destination?, JoltISA.sideEffectingDst, JoltISA.sideEffectingRdZeroDst]
  repeat' split
  all_goals
    refine ⟨?_, ?_⟩
    · simp only [nativeRowOk, x0Ok, isCanonicalNoOp, JoltISA.Instr.destination?,
        Bool.not_false, immShiftOk, isRegisterShift, nativeJalrBaseOk, advicePairsOk,
        loadWindowsOk, loadSelfChecked, leftOperandIsRegister, *]
      rfl
    · first
        | trivial
        | exact ⟨_, rfl⟩))

theorem lui_native_ok (rd : regidx) (imm : BitVec 20) :
    ExpandedOk (.ofNative (JoltISA.Instr.LUI (.xreg rd) (JoltISA.luiValue imm))) := by
  native_ok

theorem auipc_native_ok (rd : regidx) (imm : BitVec 20) :
    ExpandedOk (.ofNative (JoltISA.Encoded.AUIPC (.xreg rd) imm)) := by
  native_ok

theorem jal_native_ok (rd : regidx) (imm : BitVec 21) :
    ExpandedOk (.ofNative (JoltISA.Encoded.JAL (.xreg rd) imm)) := by
  native_ok

theorem jalr_native_ok (rd rs1 : regidx) (imm : BitVec 12) :
    ExpandedOk (.ofNative (JoltISA.Encoded.JALR (.xreg rd) (.xreg rs1) imm)) := by
  native_ok

theorem beq_native_ok (rs1 rs2 : regidx) (imm : BitVec 13) :
    ExpandedOk (.ofNative (JoltISA.Encoded.BEQ (.xreg rs1) (.xreg rs2) imm)) := by
  native_ok

theorem bne_native_ok (rs1 rs2 : regidx) (imm : BitVec 13) :
    ExpandedOk (.ofNative (JoltISA.Encoded.BNE (.xreg rs1) (.xreg rs2) imm)) := by
  native_ok

theorem blt_native_ok (rs1 rs2 : regidx) (imm : BitVec 13) :
    ExpandedOk (.ofNative (JoltISA.Encoded.BLT (.xreg rs1) (.xreg rs2) imm)) := by
  native_ok

theorem bge_native_ok (rs1 rs2 : regidx) (imm : BitVec 13) :
    ExpandedOk (.ofNative (JoltISA.Encoded.BGE (.xreg rs1) (.xreg rs2) imm)) := by
  native_ok

theorem bltu_native_ok (rs1 rs2 : regidx) (imm : BitVec 13) :
    ExpandedOk (.ofNative (JoltISA.Encoded.BLTU (.xreg rs1) (.xreg rs2) imm)) := by
  native_ok

theorem bgeu_native_ok (rs1 rs2 : regidx) (imm : BitVec 13) :
    ExpandedOk (.ofNative (JoltISA.Encoded.BGEU (.xreg rs1) (.xreg rs2) imm)) := by
  native_ok

theorem addi_native_ok (rd rs1 : regidx) (imm : BitVec 12) :
    ExpandedOk (.ofNative (JoltISA.Encoded.ADDI (.xreg rd) (.xreg rs1) imm)) := by
  native_ok

theorem slti_native_ok (rd rs1 : regidx) (imm : BitVec 12) :
    ExpandedOk (.ofNative (JoltISA.Encoded.SLTI (.xreg rd) (.xreg rs1) imm)) := by
  native_ok

theorem sltiu_native_ok (rd rs1 : regidx) (imm : BitVec 12) :
    ExpandedOk (.ofNative (JoltISA.Encoded.SLTIU (.xreg rd) (.xreg rs1) imm)) := by
  native_ok

theorem xori_native_ok (rd rs1 : regidx) (imm : BitVec 12) :
    ExpandedOk (.ofNative (JoltISA.Encoded.XORI (.xreg rd) (.xreg rs1) imm)) := by
  native_ok

theorem ori_native_ok (rd rs1 : regidx) (imm : BitVec 12) :
    ExpandedOk (.ofNative (JoltISA.Encoded.ORI (.xreg rd) (.xreg rs1) imm)) := by
  native_ok

theorem andi_native_ok (rd rs1 : regidx) (imm : BitVec 12) :
    ExpandedOk (.ofNative (JoltISA.Encoded.ANDI (.xreg rd) (.xreg rs1) imm)) := by
  native_ok

theorem addiw_native_ok (rd rs1 : regidx) (imm : BitVec 12) :
    ExpandedOk (.ofNative (JoltISA.Encoded.ADDIW (.xreg rd) (.xreg rs1) imm)) := by
  native_ok

theorem add_native_ok (rd rs1 rs2 : regidx) :
    ExpandedOk (.ofNative (JoltISA.Instr.ADD (.xreg rd) (.xreg rs1) (.xreg rs2))) := by
  native_ok

theorem sub_native_ok (rd rs1 rs2 : regidx) :
    ExpandedOk (.ofNative (JoltISA.Instr.SUB (.xreg rd) (.xreg rs1) (.xreg rs2))) := by
  native_ok

theorem slt_native_ok (rd rs1 rs2 : regidx) :
    ExpandedOk (.ofNative (JoltISA.Instr.SLT (.xreg rd) (.xreg rs1) (.xreg rs2))) := by
  native_ok

theorem sltu_native_ok (rd rs1 rs2 : regidx) :
    ExpandedOk (.ofNative (JoltISA.Instr.SLTU (.xreg rd) (.xreg rs1) (.xreg rs2))) := by
  native_ok

theorem xor_native_ok (rd rs1 rs2 : regidx) :
    ExpandedOk (.ofNative (JoltISA.Instr.XOR (.xreg rd) (.xreg rs1) (.xreg rs2))) := by
  native_ok

theorem or_native_ok (rd rs1 rs2 : regidx) :
    ExpandedOk (.ofNative (JoltISA.Instr.OR (.xreg rd) (.xreg rs1) (.xreg rs2))) := by
  native_ok

theorem and_native_ok (rd rs1 rs2 : regidx) :
    ExpandedOk (.ofNative (JoltISA.Instr.AND (.xreg rd) (.xreg rs1) (.xreg rs2))) := by
  native_ok

theorem andn_native_ok (rd rs1 rs2 : regidx) :
    ExpandedOk (.ofNative (JoltISA.Instr.ANDN (.xreg rd) (.xreg rs1) (.xreg rs2))) := by
  native_ok

theorem addw_native_ok (rd rs1 rs2 : regidx) :
    ExpandedOk (.ofNative (JoltISA.Instr.ADDW (.xreg rd) (.xreg rs1) (.xreg rs2))) := by
  native_ok

theorem subw_native_ok (rd rs1 rs2 : regidx) :
    ExpandedOk (.ofNative (JoltISA.Instr.SUBW (.xreg rd) (.xreg rs1) (.xreg rs2))) := by
  native_ok

theorem mul_native_ok (rd rs1 rs2 : regidx) :
    ExpandedOk (.ofNative (JoltISA.Instr.MUL (.xreg rd) (.xreg rs1) (.xreg rs2))) := by
  native_ok

theorem mulhu_native_ok (rd rs1 rs2 : regidx) :
    ExpandedOk (.ofNative (JoltISA.Instr.MULHU (.xreg rd) (.xreg rs1) (.xreg rs2))) := by
  native_ok

theorem mulw_native_ok (rd rs1 rs2 : regidx) :
    ExpandedOk (.ofNative (JoltISA.Instr.MULW (.xreg rd) (.xreg rs1) (.xreg rs2))) := by
  native_ok

theorem fence_native_ok :
    ExpandedOk (.ofNative (JoltISA.Instr.FENCE)) := by
  native_ok

theorem ld_native_ok (rd rs1 : regidx) (imm : BitVec 12) :
    ExpandedOk (.ofNative (JoltISA.Encoded.LD .normal (.xreg rd) (.xreg rs1) imm)) := by
  native_ok

theorem sd_native_ok (rs1 rs2 : regidx) (imm : BitVec 12) :
    ExpandedOk (.ofNative (JoltISA.Encoded.SD (.xreg rs1) (.xreg rs2) imm)) := by
  native_ok

theorem virtualRev8W_native_ok (rd rs1 : regidx) :
    ExpandedOk (.ofNative (JoltISA.Instr.VirtualRev8W (.xreg rd) (.xreg rs1))) := by
  native_ok

theorem virtualAssertEQ_native_ok (rs1 rs2 : regidx) (imm : BitVec 13) :
    ExpandedOk (.ofNative (JoltISA.Encoded.VirtualAssertEQ (.xreg rs1) (.xreg rs2) imm)) := by
  native_ok

/-- An operandless host call satisfies the native-row expansion checks.
For example, it reads no instruction temporary and has no destination to rewrite.
See jolt/crates/jolt-program/src/expand/materialize.rs:79-101 at 5def437f. -/
theorem virtualHostIO_native_ok :
    ExpandedOk (.ofNative JoltISA.Instr.VirtualHostIO) := by
  native_ok

-- A source-only program's expansion, in every case.
theorem ofProgram_ok (program : JoltISA.Program) (rows : sequenceOk program.instrs = true) :
    ExpandedOk (.ofProgram program) :=
  rows

-- A pure source-only program: the native no-op for rd = x0, else its rows.
theorem ofPureProgram_ok (rd : regidx) (program : JoltISA.Program)
    (rows : JoltISA.isX0 rd = false → sequenceOk program.instrs = true) :
    ExpandedOk (.ofPureProgram rd program) := by
  unfold ExpandedSource.ofPureProgram
  split
  · exact ⟨rfl, trivial⟩
  · next notX0 => exact rows (by simpa using notX0)

-- Every source instruction's expansion satisfies `ExpandedOk`. One arm per case of
-- `SourceInstruction.expand`, each citing the small lemma for its program or native.
theorem expand_ok : ∀ (source : SourceInstruction) (expanded : ExpandedSource),
    source.expand = some expanded → ExpandedOk expanded
  | .riscv (.LUI rd imm), _, h => by cases h; exact lui_native_ok ..
  | .riscv (.AUIPC rd imm), _, h => by cases h; exact auipc_native_ok ..
  | .riscv (.JAL rd imm), _, h => by cases h; exact jal_native_ok ..
  | .riscv (.JALR rd rs1 imm), _, h => by cases h; exact jalr_native_ok ..
  | .riscv (.BEQ rs1 rs2 imm), _, h => by cases h; exact beq_native_ok ..
  | .riscv (.BNE rs1 rs2 imm), _, h => by cases h; exact bne_native_ok ..
  | .riscv (.BLT rs1 rs2 imm), _, h => by cases h; exact blt_native_ok ..
  | .riscv (.BGE rs1 rs2 imm), _, h => by cases h; exact bge_native_ok ..
  | .riscv (.BLTU rs1 rs2 imm), _, h => by cases h; exact bltu_native_ok ..
  | .riscv (.BGEU rs1 rs2 imm), _, h => by cases h; exact bgeu_native_ok ..
  | .riscv (.LB rd rs1 imm), _, h => by cases h; exact ofProgram_ok _ (lb_ok ..)
  | .riscv (.LH rd rs1 imm), _, h => by cases h; exact ofProgram_ok _ (lh_ok ..)
  | .riscv (.LW rd rs1 imm), _, h => by cases h; exact ofProgram_ok _ (lw_ok ..)
  | .riscv (.LBU rd rs1 imm), _, h => by cases h; exact ofProgram_ok _ (lbu_ok ..)
  | .riscv (.LHU rd rs1 imm), _, h => by cases h; exact ofProgram_ok _ (lhu_ok ..)
  | .riscv (.SB rs2 rs1 imm), _, h => by cases h; exact ofProgram_ok _ (sb_ok ..)
  | .riscv (.SH rs2 rs1 imm), _, h => by cases h; exact ofProgram_ok _ (sh_ok ..)
  | .riscv (.SW rs2 rs1 imm), _, h => by cases h; exact ofProgram_ok _ (sw_ok ..)
  | .riscv (.ADDI rd rs1 imm), _, h => by cases h; exact addi_native_ok ..
  | .riscv (.SLTI rd rs1 imm), _, h => by cases h; exact slti_native_ok ..
  | .riscv (.SLTIU rd rs1 imm), _, h => by cases h; exact sltiu_native_ok ..
  | .riscv (.XORI rd rs1 imm), _, h => by cases h; exact xori_native_ok ..
  | .riscv (.ORI rd rs1 imm), _, h => by cases h; exact ori_native_ok ..
  | .riscv (.ANDI rd rs1 imm), _, h => by cases h; exact andi_native_ok ..
  | .riscv (.SLLI rd rs1 shamt), _, h => by cases h; exact ofPureProgram_ok _ _ (fun notX0 => slli_ok (notX0 := notX0) ..)
  | .riscv (.SRLI rd rs1 shamt), _, h => by cases h; exact ofPureProgram_ok _ _ (fun notX0 => srli_ok (notX0 := notX0) ..)
  | .riscv (.SRAI rd rs1 shamt), _, h => by cases h; exact ofPureProgram_ok _ _ (fun notX0 => srai_ok (notX0 := notX0) ..)
  | .riscv (.ADD rd rs1 rs2), _, h => by cases h; exact add_native_ok ..
  | .riscv (.SUB rd rs1 rs2), _, h => by cases h; exact sub_native_ok ..
  | .riscv (.SLL rd rs1 rs2), _, h => by cases h; exact ofPureProgram_ok _ _ (fun notX0 => sll_ok (notX0 := notX0) ..)
  | .riscv (.SLT rd rs1 rs2), _, h => by cases h; exact slt_native_ok ..
  | .riscv (.SLTU rd rs1 rs2), _, h => by cases h; exact sltu_native_ok ..
  | .riscv (.XOR rd rs1 rs2), _, h => by cases h; exact xor_native_ok ..
  | .riscv (.SRL rd rs1 rs2), _, h => by cases h; exact ofPureProgram_ok _ _ (fun notX0 => srl_ok (notX0 := notX0) ..)
  | .riscv (.SRA rd rs1 rs2), _, h => by cases h; exact ofPureProgram_ok _ _ (fun notX0 => sra_ok (notX0 := notX0) ..)
  | .riscv (.OR rd rs1 rs2), _, h => by cases h; exact or_native_ok ..
  | .riscv (.AND rd rs1 rs2), _, h => by cases h; exact and_native_ok ..
  | .riscv (.ANDN rd rs1 rs2), _, h => by cases h; exact andn_native_ok ..
  | .riscv (.FENCE), _, h => by cases h; exact fence_native_ok ..
  | .riscv (.ECALL), _, h => by cases h; exact ofProgram_ok _ (ecall_ok ..)
  | .riscv (.EBREAK), _, h => by cases h; exact ofProgram_ok _ (ebreak_ok ..)
  | .riscv (.LWU rd rs1 imm), _, h => by cases h; exact ofProgram_ok _ (lwu_ok ..)
  | .riscv (.LD rd rs1 imm), _, h => by cases h; exact ld_native_ok ..
  | .riscv (.SD rs2 rs1 imm), _, h => by cases h; exact sd_native_ok ..
  | .riscv (.ADDIW rd rs1 imm), _, h => by cases h; exact addiw_native_ok ..
  | .riscv (.SLLIW rd rs1 shamt), _, h => by cases h; exact ofPureProgram_ok _ _ (fun notX0 => slliw_ok (notX0 := notX0) ..)
  | .riscv (.SRLIW rd rs1 shamt), _, h => by cases h; exact ofPureProgram_ok _ _ (fun notX0 => srliw_ok (notX0 := notX0) ..)
  | .riscv (.SRAIW rd rs1 shamt), _, h => by cases h; exact ofPureProgram_ok _ _ (fun notX0 => sraiw_ok (notX0 := notX0) ..)
  | .riscv (.ADDW rd rs1 rs2), _, h => by cases h; exact addw_native_ok ..
  | .riscv (.SUBW rd rs1 rs2), _, h => by cases h; exact subw_native_ok ..
  | .riscv (.SLLW rd rs1 rs2), _, h => by cases h; exact ofPureProgram_ok _ _ (fun notX0 => sllw_ok (notX0 := notX0) ..)
  | .riscv (.SRLW rd rs1 rs2), _, h => by cases h; exact ofPureProgram_ok _ _ (fun notX0 => srlw_ok (notX0 := notX0) ..)
  | .riscv (.SRAW rd rs1 rs2), _, h => by cases h; exact ofPureProgram_ok _ _ (fun notX0 => sraw_ok (notX0 := notX0) ..)
  | .riscv (.MUL rd rs1 rs2), _, h => by cases h; exact mul_native_ok ..
  | .riscv (.MULH rd rs1 rs2), _, h => by cases h; exact ofPureProgram_ok _ _ (fun notX0 => mulh_ok (notX0 := notX0) ..)
  | .riscv (.MULHU rd rs1 rs2), _, h => by cases h; exact mulhu_native_ok ..
  | .riscv (.MULHSU rd rs1 rs2), _, h => by cases h; exact ofPureProgram_ok _ _ (fun notX0 => mulhsu_ok (notX0 := notX0) ..)
  | .riscv (.DIV rd rs1 rs2 q), _, h => by cases h; exact ofPureProgram_ok _ _ (fun notX0 => div_ok (notX0 := notX0) ..)
  | .riscv (.DIVU rd rs1 rs2 q), _, h => by cases h; exact ofPureProgram_ok _ _ (fun notX0 => divu_ok (notX0 := notX0) ..)
  | .riscv (.REM rd rs1 rs2 q), _, h => by cases h; exact ofPureProgram_ok _ _ (fun notX0 => rem_ok (notX0 := notX0) ..)
  | .riscv (.REMU rd rs1 rs2 q), _, h => by cases h; exact ofPureProgram_ok _ _ (fun notX0 => remu_ok (notX0 := notX0) ..)
  | .riscv (.MULW rd rs1 rs2), _, h => by cases h; exact mulw_native_ok ..
  | .riscv (.DIVW rd rs1 rs2 q), _, h => by cases h; exact ofPureProgram_ok _ _ (fun notX0 => divw_ok (notX0 := notX0) ..)
  | .riscv (.DIVUW rd rs1 rs2 q), _, h => by cases h; exact ofPureProgram_ok _ _ (fun notX0 => divuw_ok (notX0 := notX0) ..)
  | .riscv (.REMW rd rs1 rs2 q), _, h => by cases h; exact ofPureProgram_ok _ _ (fun notX0 => remw_ok (notX0 := notX0) ..)
  | .riscv (.REMUW rd rs1 rs2 q), _, h => by cases h; exact ofPureProgram_ok _ _ (fun notX0 => remuw_ok (notX0 := notX0) ..)
  | .riscv (.LR_W rd rs1 _ _), _, h => by cases h; exact ofProgram_ok _ (lrw_ok ..)
  | .riscv (.SC_W rd rs1 rs2 _ _), _, h => by cases h; exact ofProgram_ok _ (scw_ok ..)
  | .riscv (.AMOSWAP_W rd rs1 rs2 _ _), _, h => by cases h; exact ofProgram_ok _ (amoswapw_ok ..)
  | .riscv (.AMOADD_W rd rs1 rs2 _ _), _, h => by cases h; exact ofProgram_ok _ (amoaddw_ok ..)
  | .riscv (.AMOXOR_W rd rs1 rs2 _ _), _, h => by cases h; exact ofProgram_ok _ (amoxorw_ok ..)
  | .riscv (.AMOAND_W rd rs1 rs2 _ _), _, h => by cases h; exact ofProgram_ok _ (amoandw_ok ..)
  | .riscv (.AMOOR_W rd rs1 rs2 _ _), _, h => by cases h; exact ofProgram_ok _ (amoorw_ok ..)
  | .riscv (.AMOMIN_W rd rs1 rs2 _ _), _, h => by cases h; exact ofProgram_ok _ (amominw_ok ..)
  | .riscv (.AMOMAX_W rd rs1 rs2 _ _), _, h => by cases h; exact ofProgram_ok _ (amomaxw_ok ..)
  | .riscv (.AMOMINU_W rd rs1 rs2 _ _), _, h => by cases h; exact ofProgram_ok _ (amominuw_ok ..)
  | .riscv (.AMOMAXU_W rd rs1 rs2 _ _), _, h => by cases h; exact ofProgram_ok _ (amomaxuw_ok ..)
  | .riscv (.LR_D rd rs1 _ _), _, h => by cases h; exact ofProgram_ok _ (lrd_ok ..)
  | .riscv (.SC_D rd rs1 rs2 _ _), _, h => by cases h; exact ofProgram_ok _ (scd_ok ..)
  | .riscv (.AMOSWAP_D rd rs1 rs2 _ _), _, h => by cases h; exact ofProgram_ok _ (amoswapd_ok ..)
  | .riscv (.AMOADD_D rd rs1 rs2 _ _), _, h => by cases h; exact ofProgram_ok _ (amoaddd_ok ..)
  | .riscv (.AMOXOR_D rd rs1 rs2 _ _), _, h => by cases h; exact ofProgram_ok _ (amoxord_ok ..)
  | .riscv (.AMOAND_D rd rs1 rs2 _ _), _, h => by cases h; exact ofProgram_ok _ (amoandd_ok ..)
  | .riscv (.AMOOR_D rd rs1 rs2 _ _), _, h => by cases h; exact ofProgram_ok _ (amoord_ok ..)
  | .riscv (.AMOMIN_D rd rs1 rs2 _ _), _, h => by cases h; exact ofProgram_ok _ (amomind_ok ..)
  | .riscv (.AMOMAX_D rd rs1 rs2 _ _), _, h => by cases h; exact ofProgram_ok _ (amomaxd_ok ..)
  | .riscv (.AMOMINU_D rd rs1 rs2 _ _), _, h => by cases h; exact ofProgram_ok _ (amominud_ok ..)
  | .riscv (.AMOMAXU_D rd rs1 rs2 _ _), _, h => by cases h; exact ofProgram_ok _ (amomaxud_ok ..)
  | .riscv (.CSRRW rd csr rs1), _, h => by cases h; exact ofProgram_ok _ (csrrw_ok ..)
  | .riscv (.CSRRS rd csr rs1), _, h => by cases h; exact ofProgram_ok _ (csrrs_ok ..)
  | .riscv (.CSRRC rd csr rs1), _, h => by cases h; exact ofProgram_ok _ (csrrc_ok ..)
  | .riscv (.CSRRWI rd csr uimm), _, h => by cases h; exact ofProgram_ok _ (csrrwi_ok ..)
  | .riscv (.CSRRSI rd csr uimm), _, h => by cases h; exact ofProgram_ok _ (csrrsi_ok ..)
  | .riscv (.CSRRCI rd csr uimm), _, h => by cases h; exact ofProgram_ok _ (csrrci_ok ..)
  | .riscv (.MRET), _, h => by cases h; exact ofProgram_ok _ (mret_ok ..)
  | .jolt (.AdviceLB rd), _, h => by cases h; exact ofProgram_ok _ (advicelb_ok ..)
  | .jolt (.AdviceLH rd), _, h => by cases h; exact ofProgram_ok _ (advicelh_ok ..)
  | .jolt (.AdviceLW rd), _, h => by cases h; exact ofProgram_ok _ (advicelw_ok ..)
  | .jolt (.AdviceLD rd), _, h => by cases h; exact ofProgram_ok _ (adviceld_ok ..)
  | .jolt (.VirtualRev8W rd rs1), _, h => by cases h; exact virtualRev8W_native_ok ..
  | .jolt (.VirtualAssertEQ rs1 rs2 imm), _, h => by cases h; exact virtualAssertEQ_native_ok ..
  | .jolt .VirtualHostIO, _, h => by cases h; exact virtualHostIO_native_ok
  | .inline key rs1 rs2 rs3, _, h => by
    simp only [SourceInstruction.expand] at h
    split at h
    · cases h
    · next registered =>
      cases h
      exact JoltISA.Inlines.InlineKey.expandRows_sequenceOk key rs1 rs2 rs3
        (by simpa using registered)

/-- The first read of each instruction temporary in a source expansion follows
a write within that same expansion. Reserved virtual registers are excluded. -/
theorem expand_temps_ok (source : SourceInstruction) (expanded : ExpandedSource)
    (h : source.expand = some expanded) :
    ExpansionTempLiveness.ExpandedTempsOk expanded := by
  have ok := expand_ok source expanded h
  cases expanded with
  | native row =>
    exact nativeRowOk_tempsReadAfterWrite row ok.1
  | sequence rows =>
    exact sequenceOk_tempsReadAfterWrite rows ok

/-- The Store circuit flag is the instruction's Store opcode flag: stamping
metadata does not affect it. For example, a stamped SD retains Store = true.
See jolt/crates/jolt-riscv/src/lib.rs:399-421 at 8bbb2357. -/
theorem circuitFlag_store_eq_opcodeFlag (row : JoltInstructionRow) :
    JoltMetadata.circuitFlag row .Store =
      JoltMetadata.opcodeFlag row.instruction .Store := rfl

/-- Materializing one source preserves the ordered instruction list and its
checks. A native expansion has one instruction satisfying the native checks;
a sequence satisfies the sequence checker, including its jump and advice checks.
For example, stamping ECALL keeps its final JALR in the last position.
See jolt/crates/jolt-program/src/expand/metadata.rs:25-53 and
jolt/crates/jolt-program/src/expand/materialize.rs:71-101 at 8bbb2357. -/
theorem expand_instruction_checks (source : SourceInstructionRow SourceInstruction)
    (rows : List JoltInstructionRow) (expanded : expand_instruction source = some rows) :
    match source.instruction.expand with
    | none => False
    | some (.native instruction) =>
        rows.map (·.instruction) = [instruction] ∧
        nativeRowOk instruction = true ∧
        nativeJalrBaseOk instruction = true ∧ advicePairsOk [instruction] = true
    | some (.sequence instructions) =>
        rows.map (·.instruction) = instructions ∧
        sequenceOk instructions = true ∧
        jumpEndNoStore instructions = true ∧
        sequenceJalrsVirtual instructions = true ∧
        virtualJalrBaseUnwritten instructions = true ∧
        advicePairsOk instructions = true := by
  unfold expand_instruction at expanded
  cases sourceExpansion : source.instruction.expand with
  | none => simp only [sourceExpansion] at expanded; cases expanded
  | some result =>
      have ok := expand_ok source.instruction result sourceExpansion
      cases result with
      | native instruction =>
          simp only [sourceExpansion, Option.some.injEq] at expanded ⊢
          subst rows
          exact ⟨rfl, ok.1, nativeRowOk_nativeJalrBaseOk instruction ok.1,
            nativeRowOk_advicePairsOk instruction ok.1⟩
      | sequence instructions =>
          simp only [sourceExpansion] at expanded ⊢
          split at expanded
          · cases expanded
          · cases expanded
            have instructionList :
                (stamp_sequence source.address source.is_compressed instructions).map
                  (·.instruction) = instructions := by
              apply List.ext_getElem
              · simp only [stamp_sequence, List.length_map, List.length_zipIdx]
              · intro i leftBound rightBound
                simp only [stamp_sequence, List.getElem_map, List.getElem_zipIdx]
            exact ⟨instructionList, ok, sequenceOk_jumpEndNoStore instructions ok,
              sequenceOk_sequenceJalrsVirtual instructions ok,
              sequenceOk_virtualJalrBaseUnwritten instructions ok,
              sequenceOk_advicePairsOk instructions ok⟩

/-- Transfer a property of instruction lists from the native and sequence checks
into the instructions of materialized rows.
For example, an advice-pair property follows from the corresponding projection
of each checker, while stamping changes only the row metadata. -/
theorem expand_instruction_property (property : List JoltISA.Instr → Prop)
    (native : ∀ instruction, nativeRowOk instruction = true → property [instruction])
    (sequence : ∀ instructions, sequenceOk instructions = true → property instructions)
    (source : SourceInstructionRow SourceInstruction) (rows : List JoltInstructionRow)
    (expanded : expand_instruction source = some rows) :
    property (rows.map (·.instruction)) := by
  have checks := expand_instruction_checks source rows expanded
  cases shape : source.instruction.expand with
  | none => simp only [shape] at checks
  | some result =>
    cases result with
    | native instruction =>
      simp only [shape] at checks
      rw [checks.1]
      exact native instruction checks.2.1
    | sequence instructions =>
      simp only [shape] at checks
      rw [checks.1]
      exact sequence instructions checks.2.1

end ExpansionFacts
