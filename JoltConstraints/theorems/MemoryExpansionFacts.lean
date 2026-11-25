/-
Syntactic facts about the memory rows each expansion emits: every memory row
and every ShiftData row has a sign-extended 12-bit offset, and every ShiftData
row is followed, two rows later, by a store with the same base and offset.
The address-sum constraints (01), (08) and (11) use these facts to rule out a
64-bit wrap of `base + imm`.
-/
import JoltConstraints.theorems.expansion_facts
import JoltConstraints.theorems.program_facts

open LeanRV64D

set_option autoImplicit false

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail LeanRV64D LeanRV64D.Functions

namespace MemoryExpansionFacts

/-- Whether a 64-bit immediate is a sign-extended 12-bit offset, that is, its
signed value lies in `[-2048, 2048)`.
For example, the offset of `lb x1, -16(x2)` passes, while `2^63` fails. -/
def smallImm (imm : BitVec 64) : Bool :=
  decide (-2048 ≤ imm.toInt) && decide (imm.toInt < 2048)

/-- A sign-extended 12-bit offset is small.
For example, the encoded offset `0xff0` sign-extends to `-16`. -/
theorem smallImm_sign_extend (offset : BitVec 12) :
    smallImm (sign_extend (m := 64) offset) = true := by
  have lower := BitVec.le_toInt offset
  have upper := BitVec.toInt_lt (x := offset)
  have same : (sign_extend (m := 64) offset).toInt = offset.toInt :=
    BitVec.toInt_signExtend_of_le (by decide)
  simp only [smallImm, same, Bool.and_eq_true, decide_eq_true_eq]
  norm_num at lower upper
  omega

/-- The base and offset of a memory row: LD, SD, VirtualLoadB/H/W or
VirtualStoreB/H/W. For example, `SD x2 x3 8` returns `(x2, 8)`. -/
def accessOperands? : JoltISA.Instr → Option (JoltISA.Src × BitVec 64)
  | .LD _ _ base imm | .SD base _ imm
  | .VirtualLoadB _ _ base imm _ | .VirtualLoadH _ _ base imm _
  | .VirtualLoadW _ _ base imm _ | .VirtualStoreB base _ imm _
  | .VirtualStoreH base _ imm _ | .VirtualStoreW base _ imm _ => some (base, imm)
  | _ => none

/-- The address source and offset of a ShiftData row.
For example, `VirtualShiftDataW v41 x3 x2 0` returns `(x2, 0)`. -/
def shiftDataOperands? : JoltISA.Instr → Option (JoltISA.Src × BitVec 64)
  | .VirtualShiftDataB _ _ address imm | .VirtualShiftDataH _ _ address imm
  | .VirtualShiftDataW _ _ address imm => some (address, imm)
  | _ => none

/-- The base and offset of a floor store row.
For example, `VirtualStoreW x2 v40 0 fault` returns `(x2, 0)`. -/
def floorStoreOperands? : JoltISA.Instr → Option (JoltISA.Src × BitVec 64)
  | .VirtualStoreB base _ imm _ | .VirtualStoreH base _ imm _
  | .VirtualStoreW base _ imm _ => some (base, imm)
  | _ => none

/-- Whether a memory or ShiftData row has a small offset; other rows pass.
For example, `LD x1 x2 (sign_extend 8)` passes. -/
def rowImmOk (instruction : JoltISA.Instr) : Bool :=
  (match accessOperands? instruction with
   | some (_, imm) => smallImm imm
   | none => true) &&
  (match shiftDataOperands? instruction with
   | some (_, imm) => smallImm imm
   | none => true)

/-- Whether an instruction writes a virtual register and is not a halt.
For example, `ADD v40 v40 v41` does, and `ADD x1 x1 x2` does not. -/
def writesVRegOnly (instruction : JoltISA.Instr) : Bool :=
  (match instruction.destination? with
   | some (.vreg _) => true
   | _ => false) &&
  instruction.haltKind?.isNone

/-- Whether two sources name the same architectural register.
For example, `x2` and `x2` do, and `x2` and `v2` do not. -/
def sameXReg : JoltISA.Src → JoltISA.Src → Bool
  | .xreg (.Regidx first), .xreg (.Regidx second) => first == second
  | _, _ => false

/-- Every architectural source names itself. For example, `sameXReg x2 x2`. -/
@[simp] theorem sameXReg_xreg_self (register : regidx) :
    sameXReg (.xreg register) (.xreg register) = true := by
  cases register
  simp [sameXReg]

/-- Two sources that `sameXReg` accepts are the same architectural register.
For example, accepting `x2` and `x2` gives one source. -/
theorem sameXReg_eq {first second : JoltISA.Src} (same : sameXReg first second = true) :
    first = second ∧ ∃ register, first = .xreg register := by
  cases first with
  | vreg _ => simp [sameXReg] at same
  | xreg first =>
    cases second with
    | vreg _ => simp [sameXReg] at same
    | xreg second =>
      cases first
      cases second
      simp only [sameXReg, beq_iff_eq] at same
      subst same
      exact ⟨rfl, _, rfl⟩

/-- Whether a ShiftData row `first`, followed by `second` and `third`, is the
middle of Jolt's store pattern: `second` and `first` write only virtual registers,
and `third` is a floor store with the same architectural base and offset.
For example, `ShiftDataW v41 x3 x2 0`, `ADD v40 v40 v41`, `StoreW x2 v40 0`
passes. -/
def shiftDataTripleOk (first second third : JoltISA.Instr) : Bool :=
  match shiftDataOperands? first, floorStoreOperands? third with
  | some (address, imm), some (base, offset) =>
      sameXReg address base && imm == offset && writesVRegOnly first && writesVRegOnly second
  | _, _ => false

/-- Whether a ShiftData row `first` is followed by two rows forming the store
pattern; other rows pass. For example, a final ShiftData row fails. -/
def shiftDataNextOk (first : JoltISA.Instr) : List JoltISA.Instr → Bool
  | second :: third :: _ =>
      (shiftDataOperands? first).isNone || shiftDataTripleOk first second third
  | _ => (shiftDataOperands? first).isNone

/-- The memory checks on an instruction list: every row has a small memory
offset, and every ShiftData row starts a store pattern.
For example, the rows of `SB x3, 4(x2)` pass. -/
def memoryRowsOk : List JoltISA.Instr → Bool
  | [] => true
  | first :: rest => rowImmOk first && shiftDataNextOk first rest && memoryRowsOk rest

/-- The memory checks on one source instruction's expansion.
For example, a native `LD` passes, and a native ShiftData row would fail. -/
def ExpandedMemoryOk : ExpandedSource → Prop
  | .native instruction => memoryRowsOk [instruction] = true
  | .sequence instructions => memoryRowsOk instructions = true

-- Evaluate the memory checks after a program's branches are exposed.
-- Try `rfl` first; it handles rows whose offsets are literals.
macro "finish_memory_ok" : tactic => `(tactic| (
  all_goals first
  | rfl
  | simp only [JoltISA.Program.instrs, memoryRowsOk, rowImmOk, shiftDataNextOk,
      shiftDataTripleOk, accessOperands?, shiftDataOperands?, floorStoreOperands?,
      writesVRegOnly, JoltISA.Instr.destination?, JoltISA.Instr.haltKind?,
      smallImm_sign_extend, sameXReg_xreg_self, beq_self_eq_true, Option.isNone_none,
      Option.isNone_some, Bool.and_true, Bool.true_and, Bool.or_true, Bool.true_or,
      Bool.false_or, Bool.or_false]))

-- Unfold one program and expose its branches before checking every row.
macro "memory_rows_ok " program:ident : tactic => `(tactic| (
  unfold $program
  repeat' split
  finish_memory_ok))

-- The CSR programs share combinators; expose them first.
macro "system_memory_ok " program:ident : tactic => `(tactic| (
  unfold $program
  try dsimp only [JoltISA.csrReadInto, JoltISA.csrSwapWrite,
    JoltISA.csrBitUpdateProgram, JoltISA.csrImmediateBitUpdateProgram]
  repeat' split
  finish_memory_ok))

-- Unfold Rust's rd = x0 rewrite on one native instruction and evaluate the checks.
macro "native_memory_ok" : tactic => `(tactic| (
  simp only [ExpandedMemoryOk, ExpandedSource.ofNative, JoltISA.Instr.rewriteNative,
    JoltISA.Instr.destination?, JoltISA.sideEffectingDst, JoltISA.sideEffectingRdZeroDst]
  repeat' split
  finish_memory_ok))

/-- A source-only program whose rows pass passes as an expansion.
For example, the rows of `LB` pass as `ofProgram`. -/
theorem ofProgram_memoryOk (program : JoltISA.Program)
    (rows : memoryRowsOk program.instrs = true) :
    ExpandedMemoryOk (.ofProgram program) :=
  rows

/-- A pure program passes as an expansion: its rd = x0 form is the native no-op.
For example, `SLL x0, x1, x2` emits one ADDI row. -/
theorem ofPureProgram_memoryOk (rd : regidx) (program : JoltISA.Program)
    (rows : memoryRowsOk program.instrs = true) :
    ExpandedMemoryOk (.ofPureProgram rd program) := by
  unfold ExpandedSource.ofPureProgram
  split
  · rfl
  · exact rows

section Programs

variable (rd rs1 rs2 : regidx)

theorem slli_memoryOk (shamt : BitVec 6) :
    memoryRowsOk (JoltISA.slliProgramAuto rd rs1 shamt).instrs = true := by
  memory_rows_ok JoltISA.slliProgramAuto
theorem srli_memoryOk (shamt : BitVec 6) :
    memoryRowsOk (JoltISA.srliProgramAuto rd rs1 shamt).instrs = true := by
  memory_rows_ok JoltISA.srliProgramAuto
theorem srai_memoryOk (shamt : BitVec 6) :
    memoryRowsOk (JoltISA.sraiProgramAuto rd rs1 shamt).instrs = true := by
  memory_rows_ok JoltISA.sraiProgramAuto
theorem sll_memoryOk : memoryRowsOk (JoltISA.sllProgramAuto rd rs1 rs2).instrs = true := by
  memory_rows_ok JoltISA.sllProgramAuto
theorem srl_memoryOk : memoryRowsOk (JoltISA.srlProgramAuto rd rs1 rs2).instrs = true := by
  memory_rows_ok JoltISA.srlProgramAuto
theorem sra_memoryOk : memoryRowsOk (JoltISA.sraProgramAuto rd rs1 rs2).instrs = true := by
  memory_rows_ok JoltISA.sraProgramAuto
theorem slliw_memoryOk (shamt : BitVec 5) :
    memoryRowsOk (JoltISA.slliwProgramAuto rd rs1 shamt).instrs = true := by
  memory_rows_ok JoltISA.slliwProgramAuto
theorem srliw_memoryOk (shamt : BitVec 5) :
    memoryRowsOk (JoltISA.srliwProgramAuto rd rs1 shamt).instrs = true := by
  memory_rows_ok JoltISA.srliwProgramAuto
theorem sraiw_memoryOk (shamt : BitVec 5) :
    memoryRowsOk (JoltISA.sraiwProgramAuto rd rs1 shamt).instrs = true := by
  memory_rows_ok JoltISA.sraiwProgramAuto
theorem sllw_memoryOk : memoryRowsOk (JoltISA.sllwProgramAuto rd rs1 rs2).instrs = true := by
  memory_rows_ok JoltISA.sllwProgramAuto
theorem srlw_memoryOk : memoryRowsOk (JoltISA.srlwProgramAuto rd rs1 rs2).instrs = true := by
  memory_rows_ok JoltISA.srlwProgramAuto
theorem sraw_memoryOk : memoryRowsOk (JoltISA.srawProgramAuto rd rs1 rs2).instrs = true := by
  memory_rows_ok JoltISA.srawProgramAuto
theorem mulh_memoryOk : memoryRowsOk (JoltISA.mulhProgramAuto rd rs1 rs2).instrs = true := by
  memory_rows_ok JoltISA.mulhProgramAuto
theorem mulhsu_memoryOk :
    memoryRowsOk (JoltISA.mulhsuProgramAuto rd rs1 rs2).instrs = true := by
  memory_rows_ok JoltISA.mulhsuProgramAuto
theorem div_memoryOk (q : BitVec 64) :
    memoryRowsOk (JoltISA.divProgramAuto rd rs1 rs2 q).instrs = true := by
  memory_rows_ok JoltISA.divProgramAuto
theorem divu_memoryOk (q : BitVec 64) :
    memoryRowsOk (JoltISA.divuProgramAuto rd rs1 rs2 q).instrs = true := by
  memory_rows_ok JoltISA.divuProgramAuto
theorem rem_memoryOk (q : BitVec 64) :
    memoryRowsOk (JoltISA.remProgramAuto rd rs1 rs2 q).instrs = true := by
  memory_rows_ok JoltISA.remProgramAuto
theorem remu_memoryOk (q : BitVec 64) :
    memoryRowsOk (JoltISA.remuProgramAuto rd rs1 rs2 q).instrs = true := by
  memory_rows_ok JoltISA.remuProgramAuto
theorem divw_memoryOk (q : BitVec 64) :
    memoryRowsOk (JoltISA.divwProgramAuto rd rs1 rs2 q).instrs = true := by
  memory_rows_ok JoltISA.divwProgramAuto
theorem divuw_memoryOk (q : BitVec 64) :
    memoryRowsOk (JoltISA.divuwProgramAuto rd rs1 rs2 q).instrs = true := by
  memory_rows_ok JoltISA.divuwProgramAuto
theorem remw_memoryOk (q : BitVec 64) :
    memoryRowsOk (JoltISA.remwProgramAuto rd rs1 rs2 q).instrs = true := by
  memory_rows_ok JoltISA.remwProgramAuto
theorem remuw_memoryOk (q : BitVec 64) :
    memoryRowsOk (JoltISA.remuwProgramAuto rd rs1 rs2 q).instrs = true := by
  memory_rows_ok JoltISA.remuwProgramAuto
theorem lb_memoryOk (imm : BitVec 12) :
    memoryRowsOk (JoltISA.lbProgramAuto rd rs1 imm).instrs = true := by
  memory_rows_ok JoltISA.lbProgramAuto
theorem lh_memoryOk (imm : BitVec 12) :
    memoryRowsOk (JoltISA.lhProgramAuto rd rs1 imm).instrs = true := by
  memory_rows_ok JoltISA.lhProgramAuto
theorem lw_memoryOk (imm : BitVec 12) :
    memoryRowsOk (JoltISA.lwProgramAuto rd rs1 imm).instrs = true := by
  memory_rows_ok JoltISA.lwProgramAuto
theorem lbu_memoryOk (imm : BitVec 12) :
    memoryRowsOk (JoltISA.lbuProgramAuto rd rs1 imm).instrs = true := by
  memory_rows_ok JoltISA.lbuProgramAuto
theorem lhu_memoryOk (imm : BitVec 12) :
    memoryRowsOk (JoltISA.lhuProgramAuto rd rs1 imm).instrs = true := by
  memory_rows_ok JoltISA.lhuProgramAuto
theorem lwu_memoryOk (imm : BitVec 12) :
    memoryRowsOk (JoltISA.lwuProgramAuto rd rs1 imm).instrs = true := by
  memory_rows_ok JoltISA.lwuProgramAuto
theorem sb_memoryOk (imm : BitVec 12) :
    memoryRowsOk (JoltISA.sbProgramAuto rs1 rs2 imm).instrs = true := by
  memory_rows_ok JoltISA.sbProgramAuto
theorem sh_memoryOk (imm : BitVec 12) :
    memoryRowsOk (JoltISA.shProgramAuto rs1 rs2 imm).instrs = true := by
  memory_rows_ok JoltISA.shProgramAuto
theorem sw_memoryOk (imm : BitVec 12) :
    memoryRowsOk (JoltISA.swProgramAuto rs1 rs2 imm).instrs = true := by
  memory_rows_ok JoltISA.swProgramAuto
theorem amoswapw_memoryOk :
    memoryRowsOk (JoltISA.amoswapwProgramAuto rd rs1 rs2).instrs = true := by
  memory_rows_ok JoltISA.amoswapwProgramAuto
theorem amoaddw_memoryOk :
    memoryRowsOk (JoltISA.amoaddwProgramAuto rd rs1 rs2).instrs = true := by
  memory_rows_ok JoltISA.amoaddwProgramAuto
theorem amoxorw_memoryOk :
    memoryRowsOk (JoltISA.amoxorwProgramAuto rd rs1 rs2).instrs = true := by
  memory_rows_ok JoltISA.amoxorwProgramAuto
theorem amoandw_memoryOk :
    memoryRowsOk (JoltISA.amoandwProgramAuto rd rs1 rs2).instrs = true := by
  memory_rows_ok JoltISA.amoandwProgramAuto
theorem amoorw_memoryOk :
    memoryRowsOk (JoltISA.amoorwProgramAuto rd rs1 rs2).instrs = true := by
  memory_rows_ok JoltISA.amoorwProgramAuto
theorem amominw_memoryOk :
    memoryRowsOk (JoltISA.amominwProgramAuto rd rs1 rs2).instrs = true := by
  memory_rows_ok JoltISA.amominwProgramAuto
theorem amomaxw_memoryOk :
    memoryRowsOk (JoltISA.amomaxwProgramAuto rd rs1 rs2).instrs = true := by
  memory_rows_ok JoltISA.amomaxwProgramAuto
theorem amominuw_memoryOk :
    memoryRowsOk (JoltISA.amominuwProgramAuto rd rs1 rs2).instrs = true := by
  memory_rows_ok JoltISA.amominuwProgramAuto
theorem amomaxuw_memoryOk :
    memoryRowsOk (JoltISA.amomaxuwProgramAuto rd rs1 rs2).instrs = true := by
  memory_rows_ok JoltISA.amomaxuwProgramAuto
theorem amoswapd_memoryOk :
    memoryRowsOk (JoltISA.amoswapdProgramAuto rd rs1 rs2).instrs = true := by
  memory_rows_ok JoltISA.amoswapdProgramAuto
theorem amoaddd_memoryOk :
    memoryRowsOk (JoltISA.amoadddProgramAuto rd rs1 rs2).instrs = true := by
  memory_rows_ok JoltISA.amoadddProgramAuto
theorem amoxord_memoryOk :
    memoryRowsOk (JoltISA.amoxordProgramAuto rd rs1 rs2).instrs = true := by
  memory_rows_ok JoltISA.amoxordProgramAuto
theorem amoandd_memoryOk :
    memoryRowsOk (JoltISA.amoanddProgramAuto rd rs1 rs2).instrs = true := by
  memory_rows_ok JoltISA.amoanddProgramAuto
theorem amoord_memoryOk :
    memoryRowsOk (JoltISA.amoordProgramAuto rd rs1 rs2).instrs = true := by
  memory_rows_ok JoltISA.amoordProgramAuto
theorem amomind_memoryOk :
    memoryRowsOk (JoltISA.amomindProgramAuto rd rs1 rs2).instrs = true := by
  memory_rows_ok JoltISA.amomindProgramAuto
theorem amomaxd_memoryOk :
    memoryRowsOk (JoltISA.amomaxdProgramAuto rd rs1 rs2).instrs = true := by
  memory_rows_ok JoltISA.amomaxdProgramAuto
theorem amominud_memoryOk :
    memoryRowsOk (JoltISA.amominudProgramAuto rd rs1 rs2).instrs = true := by
  memory_rows_ok JoltISA.amominudProgramAuto
theorem amomaxud_memoryOk :
    memoryRowsOk (JoltISA.amomaxudProgramAuto rd rs1 rs2).instrs = true := by
  memory_rows_ok JoltISA.amomaxudProgramAuto
theorem lrw_memoryOk : memoryRowsOk (JoltISA.lrwProgramAuto rd rs1 rs2).instrs = true := by
  memory_rows_ok JoltISA.lrwProgramAuto
theorem lrd_memoryOk : memoryRowsOk (JoltISA.lrdProgramAuto rd rs1 rs2).instrs = true := by
  memory_rows_ok JoltISA.lrdProgramAuto
theorem scw_memoryOk : memoryRowsOk (JoltISA.scwProgramAuto rd rs1 rs2).instrs = true := by
  memory_rows_ok JoltISA.scwProgramAuto
theorem scd_memoryOk : memoryRowsOk (JoltISA.scdProgramAuto rd rs1 rs2).instrs = true := by
  memory_rows_ok JoltISA.scdProgramAuto
theorem advicelb_memoryOk : memoryRowsOk (JoltISA.advicelbProgramAuto rd).instrs = true := by
  memory_rows_ok JoltISA.advicelbProgramAuto
theorem advicelh_memoryOk : memoryRowsOk (JoltISA.advicelhProgramAuto rd).instrs = true := by
  memory_rows_ok JoltISA.advicelhProgramAuto
theorem advicelw_memoryOk : memoryRowsOk (JoltISA.advicelwProgramAuto rd).instrs = true := by
  memory_rows_ok JoltISA.advicelwProgramAuto
theorem adviceld_memoryOk : memoryRowsOk (JoltISA.adviceldProgramAuto rd).instrs = true := by
  memory_rows_ok JoltISA.adviceldProgramAuto

end Programs

theorem ecall_memoryOk : memoryRowsOk JoltISA.ecallProgram.instrs = true := by
  memory_rows_ok JoltISA.ecallProgram
theorem ebreak_memoryOk : memoryRowsOk JoltISA.ebreakProgram.instrs = true := by
  memory_rows_ok JoltISA.ebreakProgram
theorem mret_memoryOk : memoryRowsOk JoltISA.mretProgram.instrs = true := by
  memory_rows_ok JoltISA.mretProgram

theorem csrrw_memoryOk (csr : JoltISA.SystemCSR) (rs1 rd : regidx) :
    memoryRowsOk (JoltISA.csrrwProgram csr rs1 rd).instrs = true := by
  cases csr <;> system_memory_ok JoltISA.csrrwProgram

private theorem csrBitUpdate_set_mstatus_memoryOk (rs1 rd : regidx) :
    memoryRowsOk (JoltISA.csrBitUpdateProgram false .mstatus rs1 rd).instrs = true := by
  system_memory_ok JoltISA.csrBitUpdateProgram

private theorem csrBitUpdate_set_mtvec_memoryOk (rs1 rd : regidx) :
    memoryRowsOk (JoltISA.csrBitUpdateProgram false .mtvec rs1 rd).instrs = true := by
  system_memory_ok JoltISA.csrBitUpdateProgram

private theorem csrBitUpdate_set_mscratch_memoryOk (rs1 rd : regidx) :
    memoryRowsOk (JoltISA.csrBitUpdateProgram false .mscratch rs1 rd).instrs = true := by
  system_memory_ok JoltISA.csrBitUpdateProgram

private theorem csrBitUpdate_set_mepc_memoryOk (rs1 rd : regidx) :
    memoryRowsOk (JoltISA.csrBitUpdateProgram false .mepc rs1 rd).instrs = true := by
  system_memory_ok JoltISA.csrBitUpdateProgram

private theorem csrBitUpdate_set_mcause_memoryOk (rs1 rd : regidx) :
    memoryRowsOk (JoltISA.csrBitUpdateProgram false .mcause rs1 rd).instrs = true := by
  system_memory_ok JoltISA.csrBitUpdateProgram

private theorem csrBitUpdate_set_mtval_memoryOk (rs1 rd : regidx) :
    memoryRowsOk (JoltISA.csrBitUpdateProgram false .mtval rs1 rd).instrs = true := by
  system_memory_ok JoltISA.csrBitUpdateProgram

private theorem csrBitUpdate_clear_mstatus_memoryOk (rs1 rd : regidx) :
    memoryRowsOk (JoltISA.csrBitUpdateProgram true .mstatus rs1 rd).instrs = true := by
  system_memory_ok JoltISA.csrBitUpdateProgram

private theorem csrBitUpdate_clear_mtvec_memoryOk (rs1 rd : regidx) :
    memoryRowsOk (JoltISA.csrBitUpdateProgram true .mtvec rs1 rd).instrs = true := by
  system_memory_ok JoltISA.csrBitUpdateProgram

private theorem csrBitUpdate_clear_mscratch_memoryOk (rs1 rd : regidx) :
    memoryRowsOk (JoltISA.csrBitUpdateProgram true .mscratch rs1 rd).instrs = true := by
  system_memory_ok JoltISA.csrBitUpdateProgram

private theorem csrBitUpdate_clear_mepc_memoryOk (rs1 rd : regidx) :
    memoryRowsOk (JoltISA.csrBitUpdateProgram true .mepc rs1 rd).instrs = true := by
  system_memory_ok JoltISA.csrBitUpdateProgram

private theorem csrBitUpdate_clear_mcause_memoryOk (rs1 rd : regidx) :
    memoryRowsOk (JoltISA.csrBitUpdateProgram true .mcause rs1 rd).instrs = true := by
  system_memory_ok JoltISA.csrBitUpdateProgram

private theorem csrBitUpdate_clear_mtval_memoryOk (rs1 rd : regidx) :
    memoryRowsOk (JoltISA.csrBitUpdateProgram true .mtval rs1 rd).instrs = true := by
  system_memory_ok JoltISA.csrBitUpdateProgram

theorem csrBitUpdate_memoryOk (clear : Bool) (csr : JoltISA.SystemCSR) (rs1 rd : regidx) :
    memoryRowsOk (JoltISA.csrBitUpdateProgram clear csr rs1 rd).instrs = true := by
  cases clear <;> cases csr <;> first
  | exact csrBitUpdate_set_mstatus_memoryOk rs1 rd
  | exact csrBitUpdate_set_mtvec_memoryOk rs1 rd
  | exact csrBitUpdate_set_mscratch_memoryOk rs1 rd
  | exact csrBitUpdate_set_mepc_memoryOk rs1 rd
  | exact csrBitUpdate_set_mcause_memoryOk rs1 rd
  | exact csrBitUpdate_set_mtval_memoryOk rs1 rd
  | exact csrBitUpdate_clear_mstatus_memoryOk rs1 rd
  | exact csrBitUpdate_clear_mtvec_memoryOk rs1 rd
  | exact csrBitUpdate_clear_mscratch_memoryOk rs1 rd
  | exact csrBitUpdate_clear_mepc_memoryOk rs1 rd
  | exact csrBitUpdate_clear_mcause_memoryOk rs1 rd
  | exact csrBitUpdate_clear_mtval_memoryOk rs1 rd

theorem csrrwi_memoryOk (csr : JoltISA.SystemCSR) (uimm : BitVec 5) (rd : regidx) :
    memoryRowsOk (JoltISA.csrrwiProgram csr uimm rd).instrs = true := by
  cases csr <;> system_memory_ok JoltISA.csrrwiProgram

theorem csrImmediateBitUpdate_memoryOk
    (clear : Bool) (csr : JoltISA.SystemCSR) (uimm : BitVec 5) (rd : regidx) :
    memoryRowsOk (JoltISA.csrImmediateBitUpdateProgram clear csr uimm rd).instrs = true := by
  cases clear <;> cases csr <;> system_memory_ok JoltISA.csrImmediateBitUpdateProgram

/-- Every source instruction's expansion passes the memory checks.
For example, `SW x3, 4(x2)` emits `ShiftDataW v41 x3 x2 4`, `ADD v40 v40 v41`
and `StoreW x2 v40 4`, and its offset 4 is small.
Jolt at ff6fc6568: `crates/jolt-program/src/expand/memory/shared.rs`
(`expand_narrow_store`) and `crates/jolt-program/src/expand/memory/shared.rs`
(`LaneWindow`). -/
theorem expand_memoryOk : ∀ (source : SourceInstruction) (expanded : ExpandedSource),
    source.expand = some expanded → ExpandedMemoryOk expanded
  | .riscv (.LUI _ _), _, h
  | .riscv (.AUIPC _ _), _, h
  | .riscv (.JAL _ _), _, h
  | .riscv (.JALR _ _ _), _, h
  | .riscv (.BEQ _ _ _), _, h
  | .riscv (.BNE _ _ _), _, h
  | .riscv (.BLT _ _ _), _, h
  | .riscv (.BGE _ _ _), _, h
  | .riscv (.BLTU _ _ _), _, h
  | .riscv (.BGEU _ _ _), _, h
  | .riscv (.ADDI _ _ _), _, h
  | .riscv (.SLTI _ _ _), _, h
  | .riscv (.SLTIU _ _ _), _, h
  | .riscv (.XORI _ _ _), _, h
  | .riscv (.ORI _ _ _), _, h
  | .riscv (.ANDI _ _ _), _, h
  | .riscv (.ADD _ _ _), _, h
  | .riscv (.SUB _ _ _), _, h
  | .riscv (.SLT _ _ _), _, h
  | .riscv (.SLTU _ _ _), _, h
  | .riscv (.XOR _ _ _), _, h
  | .riscv (.OR _ _ _), _, h
  | .riscv (.AND _ _ _), _, h
  | .riscv (.ANDN _ _ _), _, h
  | .riscv .FENCE, _, h
  | .riscv (.LD _ _ _), _, h
  | .riscv (.SD _ _ _), _, h
  | .riscv (.ADDIW _ _ _), _, h
  | .riscv (.ADDW _ _ _), _, h
  | .riscv (.SUBW _ _ _), _, h
  | .riscv (.MUL _ _ _), _, h
  | .riscv (.MULHU _ _ _), _, h
  | .riscv (.MULW _ _ _), _, h
  | .jolt (.VirtualRev8W _ _), _, h
  | .jolt (.VirtualAssertEQ _ _ _), _, h
  | .jolt .VirtualHostIO, _, h
  | .jolt .JoltSuccess, _, h => by cases h; native_memory_ok
  | .riscv (.LB rd rs1 imm), _, h => by cases h; exact ofProgram_memoryOk _ (lb_memoryOk ..)
  | .riscv (.LH rd rs1 imm), _, h => by cases h; exact ofProgram_memoryOk _ (lh_memoryOk ..)
  | .riscv (.LW rd rs1 imm), _, h => by cases h; exact ofProgram_memoryOk _ (lw_memoryOk ..)
  | .riscv (.LBU rd rs1 imm), _, h => by cases h; exact ofProgram_memoryOk _ (lbu_memoryOk ..)
  | .riscv (.LHU rd rs1 imm), _, h => by cases h; exact ofProgram_memoryOk _ (lhu_memoryOk ..)
  | .riscv (.SB rs2 rs1 imm), _, h => by cases h; exact ofProgram_memoryOk _ (sb_memoryOk ..)
  | .riscv (.SH rs2 rs1 imm), _, h => by cases h; exact ofProgram_memoryOk _ (sh_memoryOk ..)
  | .riscv (.SW rs2 rs1 imm), _, h => by cases h; exact ofProgram_memoryOk _ (sw_memoryOk ..)
  | .riscv (.SLLI rd rs1 shamt), _, h => by
      cases h; exact ofPureProgram_memoryOk _ _ (slli_memoryOk ..)
  | .riscv (.SRLI rd rs1 shamt), _, h => by
      cases h; exact ofPureProgram_memoryOk _ _ (srli_memoryOk ..)
  | .riscv (.SRAI rd rs1 shamt), _, h => by
      cases h; exact ofPureProgram_memoryOk _ _ (srai_memoryOk ..)
  | .riscv (.SLL rd rs1 rs2), _, h => by
      cases h; exact ofPureProgram_memoryOk _ _ (sll_memoryOk ..)
  | .riscv (.SRL rd rs1 rs2), _, h => by
      cases h; exact ofPureProgram_memoryOk _ _ (srl_memoryOk ..)
  | .riscv (.SRA rd rs1 rs2), _, h => by
      cases h; exact ofPureProgram_memoryOk _ _ (sra_memoryOk ..)
  | .riscv (.ECALL), _, h => by cases h; exact ofProgram_memoryOk _ ecall_memoryOk
  | .riscv (.EBREAK), _, h => by cases h; exact ofProgram_memoryOk _ ebreak_memoryOk
  | .riscv (.LWU rd rs1 imm), _, h => by cases h; exact ofProgram_memoryOk _ (lwu_memoryOk ..)
  | .riscv (.SLLIW rd rs1 shamt), _, h => by
      cases h; exact ofPureProgram_memoryOk _ _ (slliw_memoryOk ..)
  | .riscv (.SRLIW rd rs1 shamt), _, h => by
      cases h; exact ofPureProgram_memoryOk _ _ (srliw_memoryOk ..)
  | .riscv (.SRAIW rd rs1 shamt), _, h => by
      cases h; exact ofPureProgram_memoryOk _ _ (sraiw_memoryOk ..)
  | .riscv (.SLLW rd rs1 rs2), _, h => by
      cases h; exact ofPureProgram_memoryOk _ _ (sllw_memoryOk ..)
  | .riscv (.SRLW rd rs1 rs2), _, h => by
      cases h; exact ofPureProgram_memoryOk _ _ (srlw_memoryOk ..)
  | .riscv (.SRAW rd rs1 rs2), _, h => by
      cases h; exact ofPureProgram_memoryOk _ _ (sraw_memoryOk ..)
  | .riscv (.MULH rd rs1 rs2), _, h => by
      cases h; exact ofPureProgram_memoryOk _ _ (mulh_memoryOk ..)
  | .riscv (.MULHSU rd rs1 rs2), _, h => by
      cases h; exact ofPureProgram_memoryOk _ _ (mulhsu_memoryOk ..)
  | .riscv (.DIV rd rs1 rs2 q), _, h => by
      cases h; exact ofPureProgram_memoryOk _ _ (div_memoryOk ..)
  | .riscv (.DIVU rd rs1 rs2 q), _, h => by
      cases h; exact ofPureProgram_memoryOk _ _ (divu_memoryOk ..)
  | .riscv (.REM rd rs1 rs2 q), _, h => by
      cases h; exact ofPureProgram_memoryOk _ _ (rem_memoryOk ..)
  | .riscv (.REMU rd rs1 rs2 q), _, h => by
      cases h; exact ofPureProgram_memoryOk _ _ (remu_memoryOk ..)
  | .riscv (.DIVW rd rs1 rs2 q), _, h => by
      cases h; exact ofPureProgram_memoryOk _ _ (divw_memoryOk ..)
  | .riscv (.DIVUW rd rs1 rs2 q), _, h => by
      cases h; exact ofPureProgram_memoryOk _ _ (divuw_memoryOk ..)
  | .riscv (.REMW rd rs1 rs2 q), _, h => by
      cases h; exact ofPureProgram_memoryOk _ _ (remw_memoryOk ..)
  | .riscv (.REMUW rd rs1 rs2 q), _, h => by
      cases h; exact ofPureProgram_memoryOk _ _ (remuw_memoryOk ..)
  | .riscv (.LR_W rd rs1 _ _), _, h => by cases h; exact ofProgram_memoryOk _ (lrw_memoryOk ..)
  | .riscv (.SC_W rd rs1 rs2 _ _), _, h => by
      cases h; exact ofProgram_memoryOk _ (scw_memoryOk ..)
  | .riscv (.AMOSWAP_W rd rs1 rs2 _ _), _, h => by
      cases h; exact ofProgram_memoryOk _ (amoswapw_memoryOk ..)
  | .riscv (.AMOADD_W rd rs1 rs2 _ _), _, h => by
      cases h; exact ofProgram_memoryOk _ (amoaddw_memoryOk ..)
  | .riscv (.AMOXOR_W rd rs1 rs2 _ _), _, h => by
      cases h; exact ofProgram_memoryOk _ (amoxorw_memoryOk ..)
  | .riscv (.AMOAND_W rd rs1 rs2 _ _), _, h => by
      cases h; exact ofProgram_memoryOk _ (amoandw_memoryOk ..)
  | .riscv (.AMOOR_W rd rs1 rs2 _ _), _, h => by
      cases h; exact ofProgram_memoryOk _ (amoorw_memoryOk ..)
  | .riscv (.AMOMIN_W rd rs1 rs2 _ _), _, h => by
      cases h; exact ofProgram_memoryOk _ (amominw_memoryOk ..)
  | .riscv (.AMOMAX_W rd rs1 rs2 _ _), _, h => by
      cases h; exact ofProgram_memoryOk _ (amomaxw_memoryOk ..)
  | .riscv (.AMOMINU_W rd rs1 rs2 _ _), _, h => by
      cases h; exact ofProgram_memoryOk _ (amominuw_memoryOk ..)
  | .riscv (.AMOMAXU_W rd rs1 rs2 _ _), _, h => by
      cases h; exact ofProgram_memoryOk _ (amomaxuw_memoryOk ..)
  | .riscv (.LR_D rd rs1 _ _), _, h => by cases h; exact ofProgram_memoryOk _ (lrd_memoryOk ..)
  | .riscv (.SC_D rd rs1 rs2 _ _), _, h => by
      cases h; exact ofProgram_memoryOk _ (scd_memoryOk ..)
  | .riscv (.AMOSWAP_D rd rs1 rs2 _ _), _, h => by
      cases h; exact ofProgram_memoryOk _ (amoswapd_memoryOk ..)
  | .riscv (.AMOADD_D rd rs1 rs2 _ _), _, h => by
      cases h; exact ofProgram_memoryOk _ (amoaddd_memoryOk ..)
  | .riscv (.AMOXOR_D rd rs1 rs2 _ _), _, h => by
      cases h; exact ofProgram_memoryOk _ (amoxord_memoryOk ..)
  | .riscv (.AMOAND_D rd rs1 rs2 _ _), _, h => by
      cases h; exact ofProgram_memoryOk _ (amoandd_memoryOk ..)
  | .riscv (.AMOOR_D rd rs1 rs2 _ _), _, h => by
      cases h; exact ofProgram_memoryOk _ (amoord_memoryOk ..)
  | .riscv (.AMOMIN_D rd rs1 rs2 _ _), _, h => by
      cases h; exact ofProgram_memoryOk _ (amomind_memoryOk ..)
  | .riscv (.AMOMAX_D rd rs1 rs2 _ _), _, h => by
      cases h; exact ofProgram_memoryOk _ (amomaxd_memoryOk ..)
  | .riscv (.AMOMINU_D rd rs1 rs2 _ _), _, h => by
      cases h; exact ofProgram_memoryOk _ (amominud_memoryOk ..)
  | .riscv (.AMOMAXU_D rd rs1 rs2 _ _), _, h => by
      cases h; exact ofProgram_memoryOk _ (amomaxud_memoryOk ..)
  | .riscv (.CSRRW rd csr rs1), _, h => by
      cases h; exact ofProgram_memoryOk _ (csrrw_memoryOk ..)
  | .riscv (.CSRRS rd csr rs1), _, h => by
      cases h; exact ofProgram_memoryOk _ (csrBitUpdate_memoryOk false ..)
  | .riscv (.CSRRC rd csr rs1), _, h => by
      cases h; exact ofProgram_memoryOk _ (csrBitUpdate_memoryOk true ..)
  | .riscv (.CSRRWI rd csr uimm), _, h => by
      cases h; exact ofProgram_memoryOk _ (csrrwi_memoryOk ..)
  | .riscv (.CSRRSI rd csr uimm), _, h => by
      cases h; exact ofProgram_memoryOk _ (csrImmediateBitUpdate_memoryOk false ..)
  | .riscv (.CSRRCI rd csr uimm), _, h => by
      cases h; exact ofProgram_memoryOk _ (csrImmediateBitUpdate_memoryOk true ..)
  | .riscv (.MRET), _, h => by cases h; exact ofProgram_memoryOk _ mret_memoryOk
  | .jolt (.AdviceLB rd), _, h => by cases h; exact ofProgram_memoryOk _ (advicelb_memoryOk ..)
  | .jolt (.AdviceLH rd), _, h => by cases h; exact ofProgram_memoryOk _ (advicelh_memoryOk ..)
  | .jolt (.AdviceLW rd), _, h => by cases h; exact ofProgram_memoryOk _ (advicelw_memoryOk ..)
  | .jolt (.AdviceLD rd), _, h => by cases h; exact ofProgram_memoryOk _ (adviceld_memoryOk ..)

/-- Each materialized expansion passes the memory checks on its instructions.
For example, the three rows of `SW x3, 4(x2)` pass. -/
theorem expand_instruction_memoryRowsOk (source : SourceInstructionRow SourceInstruction)
    (rows : List JoltInstructionRow) (expanded : expand_instruction source = some rows) :
    memoryRowsOk (rows.map (·.instruction)) = true := by
  have checks := ExpansionFacts.expand_instruction_checks source rows expanded
  cases shape : source.instruction.expand with
  | none => simp only [shape] at checks
  | some result =>
    have ok := expand_memoryOk source.instruction result shape
    cases result with
    | native instruction =>
      simp only [shape] at checks
      rw [checks.1]
      exact ok
    | sequence instructions =>
      simp only [shape] at checks
      rw [checks.1]
      exact ok

/-- Every instruction of a list that passes the memory checks has a small offset.
For example, the store row of `SW x3, 4(x2)` has offset 4. -/
theorem memoryRowsOk_rowImmOk : ∀ (instructions : List JoltISA.Instr),
    memoryRowsOk instructions = true → ∀ instruction ∈ instructions, rowImmOk instruction = true
  | [], _, _, member => by simp at member
  | first :: rest, ok, instruction, member => by
    simp only [memoryRowsOk, Bool.and_eq_true] at ok
    rcases List.mem_cons.mp member with same | inRest
    · subst same
      exact ok.1.1
    · exact memoryRowsOk_rowImmOk rest ok.2 instruction inRest

/-- Every selected item starts a consecutive triple satisfying `relation`.
For example, every ShiftData row starts a triple that ends in its store. -/
def Triples {α : Type} (selected : α → Prop) (relation : α → α → α → Prop)
    (items : List α) : Prop :=
  ∀ (k : Nat) (inRange : k < items.length), selected items[k] →
    ∃ next : k + 2 < items.length,
      relation items[k] (items[k + 1]'(by omega)) items[k + 2]

/-- A list that passes the memory checks has a store pattern after each ShiftData row.
For example, `ShiftDataW v41 x3 x2 4` is followed by `ADD v40 v40 v41` and
`StoreW x2 v40 4`. -/
theorem memoryRowsOk_triples : ∀ (instructions : List JoltISA.Instr),
    memoryRowsOk instructions = true →
    Triples (fun instruction => (shiftDataOperands? instruction).isSome = true)
      (fun first second third => shiftDataTripleOk first second third = true) instructions
  | [], _ => by
    intro k inRange
    simp at inRange
  | first :: rest, ok => by
    simp only [memoryRowsOk, Bool.and_eq_true] at ok
    obtain ⟨⟨_, next⟩, restOk⟩ := ok
    intro k inRange selected
    cases k with
    | zero =>
      simp only [List.getElem_cons_zero] at selected
      have notNone : (shiftDataOperands? first).isNone = false := by
        cases operands : shiftDataOperands? first
        · simp [operands] at selected
        · rfl
      rcases rest with _ | ⟨second, _ | ⟨third, tail⟩⟩
      · simp [shiftDataNextOk, notNone] at next
      · simp [shiftDataNextOk, notNone] at next
      · simp only [shiftDataNextOk, notNone, Bool.false_or] at next
        exact ⟨by simp, next⟩
    | succ k =>
      obtain ⟨bound, related⟩ := memoryRowsOk_triples rest restOk k
        (by simp only [List.length_cons] at inRange; omega)
        (by simpa only [List.getElem_cons_succ] using selected)
      exact ⟨by simp only [List.length_cons]; omega, by simpa only [List.getElem_cons_succ]
        using related⟩

private theorem triples_append {α : Type} (selected : α → Prop)
    (relation : α → α → α → Prop) (front back : List α)
    (frontTriples : Triples selected relation front)
    (backTriples : Triples selected relation back) :
    Triples selected relation (front ++ back) := by
  intro k inRange choose
  rw [List.length_append] at inRange
  by_cases inFront : k < front.length
  · rw [List.getElem_append_left inFront] at choose
    obtain ⟨next, related⟩ := frontTriples k inFront choose
    refine ⟨by simp only [List.length_append]; omega, ?_⟩
    rw [List.getElem_append_left inFront, List.getElem_append_left (by omega),
      List.getElem_append_left next]
    exact related
  · rw [List.getElem_append_right (by omega)] at choose
    obtain ⟨next, related⟩ := backTriples (k - front.length) (by omega) choose
    refine ⟨by simp only [List.length_append]; omega, ?_⟩
    rw [List.getElem_append_right (by omega), List.getElem_append_right (by omega),
      List.getElem_append_right (by omega)]
    have one : k + 1 - front.length = k - front.length + 1 := by omega
    have two : k + 2 - front.length = k - front.length + 2 := by omega
    simp only [one, two]
    exact related

private theorem triples_flatten {α : Type} (selected : α → Prop)
    (relation : α → α → α → Prop) (chunks : List (List α))
    (each : ∀ chunk ∈ chunks, Triples selected relation chunk) :
    Triples selected relation chunks.flatten := by
  induction chunks with
  | nil => intro k inRange; simp at inRange
  | cons front rest ih =>
    exact triples_append selected relation front rest.flatten
      (each front List.mem_cons_self)
      (ih (fun chunk member => each chunk (List.mem_cons_of_mem _ member)))

/-- The relation the store-pattern lift gives on bytecode rows: the instructions
form the store pattern, and the first two rows continue their expansion.
For example, the ShiftData and ADD rows of `SW x3, 4(x2)` continue. -/
def ShiftDataRowsOk (first second third : JoltInstructionRow) : Prop :=
  shiftDataTripleOk first.instruction second.instruction third.instruction = true ∧
    first.continues = true ∧ second.continues = true

/-- The store pattern holds on materialized rows, and the first two rows continue.
For example, the ShiftData row of `SW x3, 4(x2)` has countdown 2. -/
theorem materialized_triples (rows : List JoltInstructionRow) (address : BitVec 64)
    (compressed : Bool) (layout : ExpandedRows address compressed rows)
    (ok : memoryRowsOk (rows.map (·.instruction)) = true) :
    Triples (fun row => (shiftDataOperands? row.instruction).isSome = true)
      ShiftDataRowsOk rows := by
  intro k inRange choose
  obtain ⟨next, related⟩ := memoryRowsOk_triples _ ok k
    (by simpa only [List.length_map] using inRange)
    (by simpa only [List.getElem_map] using choose)
  simp only [List.length_map] at next
  simp only [List.getElem_map] at related
  have continues : ∀ j (bound : j + 1 < rows.length), rows[j].continues = true := by
    intro j bound
    have countdown := layout.countdown j (by omega)
    simp only [JoltInstructionRow.continues, bne_iff_ne]
    intro zero
    rw [zero] at countdown
    change 0 = rows.length - 1 - j at countdown
    omega
  exact ⟨next, related, continues k (by omega), continues (k + 1) (by omega)⟩

/-- Every ShiftData row of the program's bytecode starts the store pattern, inside
one expansion. For example, a bytecode ShiftData row at index 7 is followed by its
ADD row at 8 and its store row at 9. -/
theorem expand_program_triples (image : Rv64ProgramImage SourceInstruction)
    (bytecode : Array JoltInstructionRow) (expanded : expand_program image = some bytecode) :
    Triples (fun row => (shiftDataOperands? row.instruction).isSome = true)
      ShiftDataRowsOk bytecode.toList := by
  unfold expand_program at expanded
  cases mapped : image.instructions.toList.mapM expand_instruction with
  | none => rw [mapped] at expanded; cases expanded
  | some chunks =>
    rw [mapped, Option.map_some, Option.some.injEq] at expanded
    subst expanded
    rw [List.toList_toArray]
    apply triples_flatten
    intro rows member
    obtain ⟨k, inRange, rfl⟩ := List.mem_iff_getElem.mp member
    obtain ⟨lengths, steps⟩ := option_mapM_results expand_instruction _ chunks mapped
    have step := steps k (by omega) inRange
    exact materialized_triples _ _ _ (expand_instruction_expandedRows _ _ step)
      (expand_instruction_memoryRowsOk _ _ step)

/-- Every row of the program's bytecode has a small memory offset.
For example, the `LD x1, 8(x2)` row has offset 8. -/
theorem expand_program_rowImmOk (image : Rv64ProgramImage SourceInstruction)
    (bytecode : Array JoltInstructionRow) (expanded : expand_program image = some bytecode)
    (row : JoltInstructionRow) (member : row ∈ bytecode.toList) :
    rowImmOk row.instruction = true := by
  obtain ⟨source, _, rows, sourceExpanded, inRows⟩ :=
    expand_program_source_of_row image bytecode expanded row member
  exact memoryRowsOk_rowImmOk _ (expand_instruction_memoryRowsOk source rows sourceExpanded)
    row.instruction (List.mem_map_of_mem inRows)

end MemoryExpansionFacts
