/-
Syntactic facts about the rows each expansion emits. `trace_interface.lean` turns
them into `ExpansionRowsValid`.
-/
import JoltConstraints.expansions
import JoltConstraints.register_encoding
import JoltConstraints.metadata
import JoltConstraints.expansion_temp_liveness

set_option autoImplicit false

open Sail PreSail LeanRV64D.Functions

namespace ExpansionFacts

-- The canonical no-op, `ADDI x0, x0, 0`.
def isCanonicalNoOp : JoltISA.Instr → Bool
  | .ADDI (.xreg dst) (.xreg src) imm => JoltISA.isX0 dst && JoltISA.isX0 src && imm == 0
  | _ => false

-- A row of a sequence writes x0 only as the canonical no-op (so a jump writes a real
-- register), is not a branch, and has canonical register operands. Rust emits a
-- one-row no-op sequence for `csrrs x0, csr, x0` (expand/control_flow/csrrs.rs).
def x0Ok (instruction : JoltISA.Instr) : Bool :=
  match instruction.destination? with
  | some (.xreg rd) => !JoltISA.isX0 rd || isCanonicalNoOp instruction
  | _ => true

def sequenceRowOk (instruction : JoltISA.Instr) : Bool :=
  x0Ok instruction &&
  !JoltMetadata.instructionFlag instruction .Branch &&
  JoltRegisterEncoding.instructionIsCanonical instruction &&
  (match instruction with
   | .VirtualHostIO .. => false
   | _ => true)

-- A row that is not its instruction's last is not a jump, a branch or HostIO.
def ordinary (instruction : JoltISA.Instr) : Bool :=
  !JoltMetadata.opcodeFlag instruction .Jump &&
  !JoltMetadata.instructionFlag instruction .Branch &&
  (match instruction with
   | .VirtualHostIO .. => false
   | _ => true)

-- Every row is a sequence row, and every row but the last is ordinary.
def rowsOk : List JoltISA.Instr → Bool
  | [] => true
  | [last] => sequenceRowOk last
  | row :: rest => sequenceRowOk row && ordinary row && rowsOk rest

-- Right-shift bitmasks: set exactly at bits s and above (for the word shifts, bits s
-- to 31). Rust's shift tables read a shift's right operand this way.
def rightShiftMask (s : Nat) : Nat := ((1 <<< (64 - s)) - 1) <<< s

def wordShiftMask (s : Nat) : Nat := (1 <<< 32) - (1 <<< s)

def maskOk (mask : Nat) : Bool :=
  mask == rightShiftMask (ctz mask) && decide (ctz mask < 64)

def wordMaskOk (mask : Nat) : Bool :=
  mask == wordShiftMask (ctz mask) && decide (ctz mask < 32)

-- An immediate shift's mask is a right-shift bitmask; no expansion emits a rotate.
def immShiftOk : JoltISA.Instr → Bool
  | .VirtualSRLI _ _ mask | .VirtualSRAI _ _ mask => maskOk mask
  | .VirtualSRLIW _ _ mask | .VirtualSRAIW _ _ mask => wordMaskOk mask
  | .VirtualROTRI .. | .VirtualROTRIW .. => false
  | _ => true

-- A shift that reads its mask from a register.
def isRegisterShift : JoltISA.Instr → Bool
  | .VirtualSRL .. | .VirtualSRA .. | .VirtualSRLW .. | .VirtualSRAW .. => true
  | _ => false

-- `previous` writes the mask register that the shift `current` reads.
def masksFed : JoltISA.Instr → JoltISA.Instr → Bool
  | .VirtualShiftRightBitmask (.vreg written) _ _, .VirtualSRL _ _ (.vreg read)
  | .VirtualShiftRightBitmask (.vreg written) _ _, .VirtualSRA _ _ (.vreg read)
  | .VirtualShiftRightBitmaskW (.vreg written) _ _, .VirtualSRLW _ _ (.vreg read)
  | .VirtualShiftRightBitmaskW (.vreg written) _ _, .VirtualSRAW _ _ (.vreg read) =>
      written == read
  | _, _ => false

-- Every immediate shift has a bitmask, and every register shift comes right after
-- the row that writes its mask.
def shiftPairsOk (previous : JoltISA.Instr) : List JoltISA.Instr → Bool
  | [] => true
  | current :: rest =>
      immShiftOk current && (!isRegisterShift current || masksFed previous current) &&
        shiftPairsOk current rest

def shiftsOk : List JoltISA.Instr → Bool
  | [] => true
  | first :: rest => immShiftOk first && !isRegisterShift first && shiftPairsOk first rest

/-- If the final instruction is JAL or JALR, every instruction has its Store
opcode flag unset. For example, ECALL ends in JALR and contains no store.
See jolt/crates/jolt-program/src/expand/control_flow/ecall.rs:23-52 at 8bbb2357. -/
def jumpEndNoStore (instructions : List JoltISA.Instr) : Bool :=
  match instructions.getLast? with
  | some (.JAL ..) | some (.JALR ..) =>
      instructions.all fun instruction => !JoltMetadata.opcodeFlag instruction .Store
  | _ => true

/-- Every JALR in a sequence has a virtual destination and a virtual base.
For example, MRET reads virtual mepc and writes its link to a temporary.
See jolt/crates/jolt-program/src/expand/control_flow/mret.rs:11-18 at 8bbb2357. -/
def sequenceJalrsVirtual (instructions : List JoltISA.Instr) : Bool :=
  instructions.all fun instruction =>
    match instruction with
    | .JALR (.vreg _) (.vreg _) _ => true
    | .JALR .. => false
    | _ => true

/-- Each virtual-base, virtual-destination JALR reads a virtual register that
no instruction in its sequence names as a virtual destination.
For example, ECALL jumps through mtvec without writing mtvec.
See jolt/crates/jolt-program/src/expand/control_flow/ecall.rs:15-50 at 8bbb2357. -/
def virtualJalrBaseUnwritten (instructions : List JoltISA.Instr) : Bool :=
  instructions.all fun instruction =>
    match instruction with
    | .JALR (.vreg _) (.vreg base) _ =>
        instructions.all fun other => !ExpansionTempLiveness.writes base other
    | _ => true

/-- Every advice load of fewer than eight bytes is immediately followed by
a multiply that shifts those bytes to the high end of a 64-bit word.
Both rows write the same nonzero architectural register, or the x0 rewrite's
virtual register 40, and the multiply reads that register.
These are exactly the destination and source forms of `sideEffectingRdZeroDst`
and `adviceReadSource`: for example, AdviceLB x0 loads virtual register 40,
then multiplies that register by `slliMultiplier (BitVec.ofNat 6 56)`.
A narrow load at the end of the list fails this check.
See jolt/crates/jolt-program/src/expand/memory/shared.rs:137-169 at 8bbb2357. -/
def advicePairsOk : List JoltISA.Instr → Bool
  | [] => true
  | instruction :: rest =>
      (match instruction with
       | .VirtualAdviceLoad dst width =>
           if width.toNat < 8 then
             match rest with
             | .VirtualMULI nextDst src multiplier :: _ =>
                 (match dst, nextDst, src with
                  | .xreg rd, .xreg nextRd, .xreg rs =>
                      !JoltISA.isX0 rd && nextRd == rd && rs == rd
                  | .vreg rd, .vreg nextRd, .vreg rs =>
                      rd == JoltISA.rdZeroRewriteVReg && nextRd == rd && rs == rd
                  | _, _, _ => false) &&
                   multiplier == JoltISA.slliMultiplier
                     (BitVec.ofNat 6 (64 - 8 * width.toNat))
             | _ => false
           else true
       | _ => true) && advicePairsOk rest

/-- A native JALR has an architectural base; its destination may be
architectural or virtual after the x0 rewrite.
For example, native JALR x0, 0(x2) retains x2 as its base.
See jolt/crates/jolt-program/src/expand/mod.rs:126-170 at 8bbb2357. -/
def nativeJalrBaseOk : JoltISA.Instr → Bool
  | .JALR _ (.vreg _) _ => false
  | _ => true

/-- All syntactic checks for one source sequence: valid rows and shifts,
initialized temporaries, jump/store separation, virtual JALRs with unchanged
bases, and adjacent narrow advice multiplies. For example, ECALL passes all
checks while a sequence that stores before its final JAL does not. -/
def sequenceOk (instructions : List JoltISA.Instr) : Bool :=
  rowsOk instructions && shiftsOk instructions &&
    ExpansionTempLiveness.tempsReadAfterWrite instructions &&
    jumpEndNoStore instructions && sequenceJalrsVirtual instructions &&
    virtualJalrBaseUnwritten instructions && advicePairsOk instructions

/-- Every row passes the sequence row checks; for example, ECALL contains no branch. -/
theorem sequenceOk_rowsOk (instructions : List JoltISA.Instr)
    (ok : sequenceOk instructions = true) : rowsOk instructions = true := by
  simp only [sequenceOk, Bool.and_eq_true] at ok
  exact ok.1.1.1.1.1.1

/-- Shifts use the required masks; for example, a register shift follows its mask producer. -/
theorem sequenceOk_shiftsOk (instructions : List JoltISA.Instr)
    (ok : sequenceOk instructions = true) : shiftsOk instructions = true := by
  simp only [sequenceOk, Bool.and_eq_true] at ok
  exact ok.1.1.1.1.1.2

/-- Temporary reads follow writes; for example, ECALL initializes its scratch register. -/
theorem sequenceOk_tempsReadAfterWrite (instructions : List JoltISA.Instr)
    (ok : sequenceOk instructions = true) : ExpansionTempLiveness.tempsReadAfterWrite instructions = true := by
  simp only [sequenceOk, Bool.and_eq_true] at ok
  exact ok.1.1.1.1.2

/-- A sequence ending in a jump has no store; for example, ECALL ends in JALR. -/
theorem sequenceOk_jumpEndNoStore (instructions : List JoltISA.Instr)
    (ok : sequenceOk instructions = true) : jumpEndNoStore instructions = true := by
  simp only [sequenceOk, Bool.and_eq_true] at ok
  exact ok.1.1.1.2

/-- Sequence JALRs have virtual operands; for example, MRET reads virtual mepc. -/
theorem sequenceOk_sequenceJalrsVirtual (instructions : List JoltISA.Instr)
    (ok : sequenceOk instructions = true) : sequenceJalrsVirtual instructions = true := by
  simp only [sequenceOk, Bool.and_eq_true] at ok
  exact ok.1.1.2

/-- A virtual jump base is unwritten in its sequence; for example, ECALL preserves mtvec. -/
theorem sequenceOk_virtualJalrBaseUnwritten (instructions : List JoltISA.Instr)
    (ok : sequenceOk instructions = true) : virtualJalrBaseUnwritten instructions = true := by
  simp only [sequenceOk, Bool.and_eq_true] at ok
  exact ok.1.2

/-- Narrow advice loads have the required multiply; for example, AdviceLB shifts by 56 bits. -/
theorem sequenceOk_advicePairsOk (instructions : List JoltISA.Instr)
    (ok : sequenceOk instructions = true) : advicePairsOk instructions = true := by
  simp only [sequenceOk, Bool.and_eq_true] at ok
  exact ok.2

-- ctz reads off the lowest set bit.
theorem ctz_eq_of_bits : ∀ (s n : Nat), (∀ i < s, n.testBit i = false) → n.testBit s = true →
    ctz n = s
  | 0, n, _, bit => by
    rw [Nat.testBit_zero, decide_eq_true_eq] at bit
    unfold ctz
    rw [if_neg (by omega), if_pos bit]
  | s + 1, n, low, bit => by
    have even : n % 2 = 0 := by
      have := low 0 (by omega)
      rw [Nat.testBit_zero, decide_eq_false_iff_not] at this
      omega
    have nonzero : n ≠ 0 := by
      rintro rfl
      simp at bit
    unfold ctz
    rw [if_neg nonzero, if_neg (by omega), ctz_eq_of_bits s (n / 2)]
    · omega
    · intro i below
      rw [← Nat.testBit_succ]
      exact low (i + 1) (by omega)
    · rw [← Nat.testBit_succ]
      exact bit

theorem rightShiftMask_testBit (s i : Nat) (sLt : s < 64) :
    (rightShiftMask s).testBit i = (decide (s ≤ i) && decide (i < 64)) := by
  unfold rightShiftMask
  rw [Nat.one_shiftLeft, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
  by_cases above : s ≤ i
  · simp only [ge_iff_le, above, decide_true, Bool.true_and]
    by_cases inside : i < 64 <;> simp [inside] <;> omega
  · simp [above]

theorem wordShiftMask_testBit (s i : Nat) (sLt : s < 32) :
    (wordShiftMask s).testBit i = (decide (s ≤ i) && decide (i < 32)) := by
  have shifted : wordShiftMask s = (2 ^ (32 - s) - 1) <<< s := by
    unfold wordShiftMask
    rw [Nat.one_shiftLeft, Nat.one_shiftLeft, Nat.shiftLeft_eq, Nat.sub_mul, ← Nat.pow_add,
      Nat.sub_add_cancel (by omega), one_mul]
  rw [shifted, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
  by_cases above : s ≤ i
  · simp only [ge_iff_le, above, decide_true, Bool.true_and]
    by_cases inside : i < 32 <;> simp [inside] <;> omega
  · simp [above]

theorem ctz_rightShiftMask (s : Nat) (sLt : s < 64) : ctz (rightShiftMask s) = s :=
  ctz_eq_of_bits s _ (fun i below => by simp [rightShiftMask_testBit s i sLt]; omega)
    (by simp [rightShiftMask_testBit s s sLt, sLt])

theorem ctz_wordShiftMask (s : Nat) (sLt : s < 32) : ctz (wordShiftMask s) = s :=
  ctz_eq_of_bits s _ (fun i below => by simp [wordShiftMask_testBit s i sLt]; omega)
    (by simp [wordShiftMask_testBit s s sLt, sLt])

theorem maskOk_srliBitmask (shamt : BitVec 6) : maskOk (JoltISA.srliBitmask shamt) = true := by
  have same : JoltISA.srliBitmask shamt = rightShiftMask shamt.toNat := rfl
  simp [maskOk, same, ctz_rightShiftMask _ shamt.isLt, shamt.isLt]

theorem maskOk_sraiBitmask (shamt : BitVec 6) : maskOk (JoltISA.sraiBitmask shamt) = true :=
  maskOk_srliBitmask shamt

theorem wordMaskOk_shamt (shamt : BitVec 5) :
    wordMaskOk ((1 <<< 32) - (1 <<< shamt.toNat)) = true := by
  have same : (1 <<< 32) - (1 <<< shamt.toNat) = wordShiftMask shamt.toNat := rfl
  rw [same]
  unfold wordMaskOk
  rw [ctz_wordShiftMask _ shamt.isLt]
  simp [shamt.isLt]

-- Unfold one program, split on its `if`s, and evaluate the checks; the split
-- hypotheses rule out x0 where a branch writes rd.
macro "rows_ok " program:ident : tactic => `(tactic| (
  unfold $program
  repeat' split
  all_goals
    simp only [JoltISA.Program.instrs, sequenceOk, rowsOk, sequenceRowOk, x0Ok, ordinary,
      JoltISA.Instr.destination?, isCanonicalNoOp, Bool.not_false, shiftsOk, shiftPairsOk,
      immShiftOk, isRegisterShift, masksFed, maskOk_srliBitmask, maskOk_sraiBitmask,
      wordMaskOk_shamt, jumpEndNoStore, sequenceJalrsVirtual, virtualJalrBaseUnwritten,
      advicePairsOk, nativeJalrBaseOk, List.getLast?_cons, List.getLast?_nil,
      List.all_cons, List.all_nil, ExpansionTempLiveness.writes, *]
    first
    | rfl
    | cases_type regidx
      simp only [BEq.beq, instBEqRegidx.beq, decide_true]
      rfl))

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
      advicePairsOk, nativeJalrBaseOk, List.getLast?_cons, List.getLast?_nil,
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

theorem csrrw_ok (csr : JoltISA.SystemCSR) (rs1 rd : regidx) :
    sequenceOk (JoltISA.csrrwProgram csr rs1 rd).instrs = true := by
  -- The CSR's virtual register is fixed per CSR, so split on which CSR it is.
  cases csr <;> rows_ok JoltISA.csrrwProgram

theorem csrrs_ok (csr : JoltISA.SystemCSR) (rs1 rd : regidx) :
    sequenceOk (JoltISA.csrrsProgram csr rs1 rd).instrs = true := by
  -- The CSR's virtual register is fixed per CSR, so split on which CSR it is.
  cases csr <;> rows_ok JoltISA.csrrsProgram

-- A branch's offset comes from a 13-bit immediate (FormatB, sign-extended).
def BranchOffsetOk : JoltISA.Instr → Prop
  | .BEQ _ _ imm | .BNE _ _ imm | .BLT _ _ imm | .BGE _ _ imm
  | .BLTU _ _ imm | .BGEU _ _ imm => ∃ offset : BitVec 13, imm = offset.signExtend 128
  | _ => True

-- Natives: one row, after Rust's rd = x0 rewrite. A native row writes x0 only as
-- the canonical no-op, its register operands are canonical, and it is not a shift
-- that reads a bitmask.
/-- Syntactic checks for a native row, including an architectural JALR base
and absence of a narrow advice load. For example, native JALR x0, 0(x2)
passes after the destination rewrite, while a lone one-byte advice load fails. -/
def nativeRowOk (instruction : JoltISA.Instr) : Bool :=
  x0Ok instruction && JoltRegisterEncoding.instructionIsCanonical instruction &&
    immShiftOk instruction && !isRegisterShift instruction &&
    ExpansionTempLiveness.tempsReadAfterWrite [instruction] &&
    nativeJalrBaseOk instruction && advicePairsOk [instruction]

/-- A native row writes x0 only as the canonical no-op; for example, JAL x0 is rewritten. -/
theorem nativeRowOk_x0Ok (instruction : JoltISA.Instr)
    (ok : nativeRowOk instruction = true) : x0Ok instruction = true := by
  simp only [nativeRowOk, Bool.and_eq_true] at ok
  exact ok.1.1.1.1.1.1

/-- Native operands use canonical register storage; for example, x2 is architectural. -/
theorem nativeRowOk_canonical (instruction : JoltISA.Instr)
    (ok : nativeRowOk instruction = true) : JoltRegisterEncoding.instructionIsCanonical instruction = true := by
  simp only [nativeRowOk, Bool.and_eq_true] at ok
  exact ok.1.1.1.1.1.2

/-- A native immediate shift has a valid mask; for example, a native ADDI has no shift to check. -/
theorem nativeRowOk_immShiftOk (instruction : JoltISA.Instr)
    (ok : nativeRowOk instruction = true) : immShiftOk instruction = true := by
  simp only [nativeRowOk, Bool.and_eq_true] at ok
  exact ok.1.1.1.1.2

/-- A native row is not a register-mask shift; for example, JALR needs no mask producer. -/
theorem nativeRowOk_not_registerShift (instruction : JoltISA.Instr)
    (ok : nativeRowOk instruction = true) : isRegisterShift instruction = false := by
  simp only [nativeRowOk, Bool.and_eq_true] at ok
  simpa only [Bool.not_eq_eq_eq_not, Bool.not_true] using ok.1.1.1.2

/-- A native row does not read an uninitialized temporary; for example, JALR reads an architectural base. -/
theorem nativeRowOk_tempsReadAfterWrite (instruction : JoltISA.Instr)
    (ok : nativeRowOk instruction = true) : ExpansionTempLiveness.tempsReadAfterWrite [instruction] = true := by
  simp only [nativeRowOk, Bool.and_eq_true] at ok
  exact ok.1.1.2

/-- A native JALR reads an architectural base; for example, JALR x1, 0(x2) reads x2. -/
theorem nativeRowOk_nativeJalrBaseOk (instruction : JoltISA.Instr)
    (ok : nativeRowOk instruction = true) : nativeJalrBaseOk instruction = true := by
  simp only [nativeRowOk, Bool.and_eq_true] at ok
  exact ok.1.2

/-- A native row cannot be a narrow advice load; for example, AdviceLB needs a sequence. -/
theorem nativeRowOk_advicePairsOk (instruction : JoltISA.Instr)
    (ok : nativeRowOk instruction = true) : advicePairsOk [instruction] = true := by
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
        Bool.not_false, immShiftOk, isRegisterShift, nativeJalrBaseOk, advicePairsOk, *]
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
  | .riscv (.MRET), _, h => by cases h; exact ofProgram_ok _ (mret_ok ..)
  | .jolt (.AdviceLB rd), _, h => by cases h; exact ofProgram_ok _ (advicelb_ok ..)
  | .jolt (.AdviceLH rd), _, h => by cases h; exact ofProgram_ok _ (advicelh_ok ..)
  | .jolt (.AdviceLW rd), _, h => by cases h; exact ofProgram_ok _ (advicelw_ok ..)
  | .jolt (.AdviceLD rd), _, h => by cases h; exact ofProgram_ok _ (adviceld_ok ..)
  | .jolt (.VirtualRev8W rd rs1), _, h => by cases h; exact virtualRev8W_native_ok ..
  | .jolt (.VirtualAssertEQ rs1 rs2 imm), _, h => by cases h; exact virtualAssertEQ_native_ok ..
  | .jolt .VirtualHostIO, _, h => by cases h; exact virtualHostIO_native_ok

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
