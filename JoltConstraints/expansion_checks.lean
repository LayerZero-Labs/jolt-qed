/-
The syntactic checks on the rows of one source instruction's expansion, and their
basic facts. `expansion_facts.lean` proves that every expansion passes them.
-/
import JoltConstraints.expansions
import JoltConstraints.register_encoding
import JoltConstraints.metadata
import JoltConstraints.expansion_temp_liveness

open LeanRV64D

set_option autoImplicit false

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail LeanRV64D LeanRV64D.Functions

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

-- An immediate shift's or rotate's mask is a right-shift bitmask. Built-in expansions
-- emit no rotate; inline rows do (SHA-256 and Keccak), with the same mask shapes.
def immShiftOk : JoltISA.Instr → Bool
  | .VirtualSRLI _ _ mask | .VirtualSRAI _ _ mask | .VirtualROTRI _ _ mask => maskOk mask
  | .VirtualSRLIW _ _ mask | .VirtualSRAIW _ _ mask | .VirtualROTRIW _ _ mask =>
      wordMaskOk mask
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

/-- Every advice load reads 1, 2, 4 or 8 bytes; a nine-byte load fails.
Every advice load of fewer than eight bytes is immediately followed by
a multiply that shifts those bytes to the high end of a 64-bit word.
Both rows write the same nonzero architectural register, or the x0 rewrite's
virtual register 40, and the multiply reads that register.
These are exactly the destination and source forms of `sideEffectingRdZeroDst`
and `adviceReadSource`: for example, AdviceLB x0 loads virtual register 40,
then multiplies that register by `slliMultiplier (BitVec.ofNat 6 56)`.
A narrow load at the end of the list fails this check.
See jolt/crates/jolt-program/src/expand/memory/shared.rs:137-169 at 8bbb2357.
The width check follows jolt/tracer/src/instruction/virtual_advice_load.rs
(`VirtualAdviceLoad::exec`) at 5def437f. -/
def advicePairsOk : List JoltISA.Instr → Bool
  | [] => true
  | instruction :: rest =>
      (match instruction with
       | .VirtualAdviceLoad dst width =>
           decide (width.toNat = 1 ∨ width.toNat = 2 ∨
             width.toNat = 4 ∨ width.toNat = 8) &&
           (if width.toNat < 8 then
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
           else true)
       | _ => true) && advicePairsOk rest

/-- Every advice load in a checked list has a supported byte count.
For example, the first row of AdviceLH reads two bytes.
See jolt/tracer/src/instruction/virtual_advice_load.rs
(`VirtualAdviceLoad::exec`) at 5def437f. -/
theorem advicePairsOk_width (instructions : List JoltISA.Instr)
    (ok : advicePairsOk instructions = true) {destination : JoltISA.Dst} {width : BitVec 64}
    (member : JoltISA.Instr.VirtualAdviceLoad destination width ∈ instructions) :
    width.toNat = 1 ∨ width.toNat = 2 ∨ width.toNat = 4 ∨ width.toNat = 8 := by
  induction instructions with
  | nil => cases member
  | cons first rest ih =>
    rcases List.mem_cons.mp member with rfl | later
    · simp only [advicePairsOk, Bool.and_eq_true, decide_eq_true_eq] at ok
      exact ok.1.1
    · simp only [advicePairsOk, Bool.and_eq_true] at ok
      exact ih ok.2 later

/-- A native JALR has an architectural base; its destination may be
architectural or virtual after the x0 rewrite.
For example, native JALR x0, 0(x2) retains x2 as its base.
See jolt/crates/jolt-program/src/expand/mod.rs:126-170 at 8bbb2357. -/
def nativeJalrBaseOk : JoltISA.Instr → Bool
  | .JALR _ (.vreg _) _ => false
  | _ => true

/-- A sequence contains no equality assertion with a nonzero immediate.
For example, an assertion comparing temporary 40 with immediate 2 fails this
check, while a zero-immediate equality assertion passes. -/
def noSpoilAsserts (instructions : List JoltISA.Instr) : Bool :=
  instructions.all fun instruction =>
    match instruction with
    | .VirtualAssertEQ _ _ imm => imm == 0
    | _ => true

/-- All syntactic checks for one source sequence: valid rows and shifts,
initialized temporaries, jump/store separation, virtual JALRs with unchanged
bases, adjacent narrow advice multiplies, and no nonzero-immediate equality
assertion. For example, ECALL passes all checks while a sequence that stores
before its final JAL does not. -/
def sequenceOk (instructions : List JoltISA.Instr) : Bool :=
  rowsOk instructions && shiftsOk instructions &&
    ExpansionTempLiveness.tempsReadAfterWrite instructions &&
    jumpEndNoStore instructions && sequenceJalrsVirtual instructions &&
    virtualJalrBaseUnwritten instructions && advicePairsOk instructions &&
    noSpoilAsserts instructions

/-- Every row passes the sequence row checks; for example, ECALL contains no branch. -/
theorem sequenceOk_rowsOk (instructions : List JoltISA.Instr)
    (ok : sequenceOk instructions = true) : rowsOk instructions = true := by
  simp only [sequenceOk, Bool.and_eq_true] at ok
  exact ok.1.1.1.1.1.1.1

/-- Shifts use the required masks; for example, a register shift follows its mask producer. -/
theorem sequenceOk_shiftsOk (instructions : List JoltISA.Instr)
    (ok : sequenceOk instructions = true) : shiftsOk instructions = true := by
  simp only [sequenceOk, Bool.and_eq_true] at ok
  exact ok.1.1.1.1.1.1.2

/-- Temporary reads follow writes; for example, ECALL initializes its scratch register. -/
theorem sequenceOk_tempsReadAfterWrite (instructions : List JoltISA.Instr)
    (ok : sequenceOk instructions = true) : ExpansionTempLiveness.tempsReadAfterWrite instructions = true := by
  simp only [sequenceOk, Bool.and_eq_true] at ok
  exact ok.1.1.1.1.1.2

/-- A sequence ending in a jump has no store; for example, ECALL ends in JALR. -/
theorem sequenceOk_jumpEndNoStore (instructions : List JoltISA.Instr)
    (ok : sequenceOk instructions = true) : jumpEndNoStore instructions = true := by
  simp only [sequenceOk, Bool.and_eq_true] at ok
  exact ok.1.1.1.1.2

/-- Sequence JALRs have virtual operands; for example, MRET reads virtual mepc. -/
theorem sequenceOk_sequenceJalrsVirtual (instructions : List JoltISA.Instr)
    (ok : sequenceOk instructions = true) : sequenceJalrsVirtual instructions = true := by
  simp only [sequenceOk, Bool.and_eq_true] at ok
  exact ok.1.1.1.2

/-- A virtual jump base is unwritten in its sequence; for example, ECALL preserves mtvec. -/
theorem sequenceOk_virtualJalrBaseUnwritten (instructions : List JoltISA.Instr)
    (ok : sequenceOk instructions = true) : virtualJalrBaseUnwritten instructions = true := by
  simp only [sequenceOk, Bool.and_eq_true] at ok
  exact ok.1.1.2

/-- Narrow advice loads have the required multiply; for example, AdviceLB shifts by 56 bits. -/
theorem sequenceOk_advicePairsOk (instructions : List JoltISA.Instr)
    (ok : sequenceOk instructions = true) : advicePairsOk instructions = true := by
  simp only [sequenceOk, Bool.and_eq_true] at ok
  exact ok.1.2

/-- A checked sequence has no spoil assert; for example, no row can compare
temporary 40 with a nonzero immediate. -/
theorem sequenceOk_noSpoilAsserts (instructions : List JoltISA.Instr)
    (ok : sequenceOk instructions = true) : noSpoilAsserts instructions = true := by
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

/-! ### One check per row for long inline sequences

`sequenceOk` reads `ctz`, which is well-founded recursion, and pairs of adjacent rows.
For thousands of generated inline rows `inlineRowOk` checks each row on its own with
functions that reduce by `rfl`, and `sequenceOk_of_inlineRowsOk` recovers `sequenceOk`.
-/

/-- The mask is a 64-bit right-shift bitmask, found by trying every shift.
Example: `fastMaskOk (2 ^ 63) = true` (shift 63) and `fastMaskOk 3 = false`. -/
def fastMaskOk (mask : Nat) : Bool :=
  (List.range 64).any fun shift => mask == rightShiftMask shift

/-- The mask is a word right-shift bitmask, found by trying every shift.
Example: `fastWordMaskOk 0xFFFC0000 = true` (shift 18). -/
def fastWordMaskOk (mask : Nat) : Bool :=
  (List.range 32).any fun shift => mask == wordShiftMask shift

/-- `immShiftOk` with the masks checked by `fastMaskOk` and `fastWordMaskOk`.
Example: `VirtualROTRI vr49 vr48 (2 ^ 63)` passes. -/
def fastImmShiftOk : JoltISA.Instr → Bool
  | .VirtualSRLI _ _ mask | .VirtualSRAI _ _ mask | .VirtualROTRI _ _ mask => fastMaskOk mask
  | .VirtualSRLIW _ _ mask | .VirtualSRAIW _ _ mask | .VirtualROTRIW _ _ mask =>
      fastWordMaskOk mask
  | _ => true

/-- The row reads no instruction temporary `vr40..47`.
Example: `XOR vr48 vr48 vr84` passes; `ADD vr48 vr40 vr49` does not. -/
def noTempRead (row : JoltISA.Instr) : Bool :=
  (List.range 8).all fun index => !ExpansionTempLiveness.reads (BitVec.ofNat 7 (40 + index)) row

/-- The row is not a jump, an advice row, an advice load or an equality assertion with a
nonzero immediate. Example: `SD x10 vr48 0` passes; `JALR vr40 vr41 0` and
`VirtualAdvice vr52 v 0` do not. -/
def straightLineRow : JoltISA.Instr → Bool
  | .JAL .. | .JALR .. | .VirtualAdvice .. | .VirtualAdviceLoad .. => false
  | .VirtualAssertEQ _ _ imm => imm == 0
  | _ => true

/-- The row writes none of the eight reserved virtual registers `vr32` to `vr39`, which
hold Jolt's CSR mirrors. Example: `ADDI vr40 x10 0` passes; `ADDI vr39 x10 0` does not. -/
def reservedFree (row : JoltISA.Instr) : Bool :=
  match row.destination? with
  | some (.vreg v) => decide (v.toNat < 32) || decide (40 ≤ v.toNat)
  | _ => true

/-- The per-row check for inline rows: a valid ordinary sequence row with a well-formed
mask, no register shift, no read of an instruction temporary, no write to a reserved
virtual register, and no jump, advice row, advice load or nonzero-immediate equality
assertion.
Example: every row of the generated `KECCAK256_ABSORB_PERMUTE` rows passes. -/
def inlineRowOk (row : JoltISA.Instr) : Bool :=
  sequenceRowOk row && ordinary row && fastImmShiftOk row && !isRegisterShift row &&
    noTempRead row && straightLineRow row && reservedFree row

theorem maskOk_of_fast (mask : Nat) (fast : fastMaskOk mask = true) : maskOk mask = true := by
  obtain ⟨shift, below, same⟩ := List.any_eq_true.mp fast
  have below : shift < 64 := List.mem_range.mp below
  rw [beq_iff_eq] at same
  subst same
  simp [maskOk, ctz_rightShiftMask _ below, below]

theorem wordMaskOk_of_fast (mask : Nat) (fast : fastWordMaskOk mask = true) :
    wordMaskOk mask = true := by
  obtain ⟨shift, below, same⟩ := List.any_eq_true.mp fast
  have below : shift < 32 := List.mem_range.mp below
  rw [beq_iff_eq] at same
  subst same
  simp [wordMaskOk, ctz_wordShiftMask _ below, below]

theorem immShiftOk_of_fast (row : JoltISA.Instr) (fast : fastImmShiftOk row = true) :
    immShiftOk row = true := by
  cases row <;> simp only [fastImmShiftOk, immShiftOk] at fast ⊢ <;>
    first
    | exact maskOk_of_fast _ fast
    | exact wordMaskOk_of_fast _ fast
    | rfl

private theorem inlineRowOk_parts {row : JoltISA.Instr} (ok : inlineRowOk row = true) :
    sequenceRowOk row = true ∧ ordinary row = true ∧ immShiftOk row = true ∧
      isRegisterShift row = false ∧ noTempRead row = true ∧ straightLineRow row = true := by
  simp only [inlineRowOk, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at ok
  exact ⟨ok.1.1.1.1.1.1, ok.1.1.1.1.1.2, immShiftOk_of_fast _ ok.1.1.1.1.2, ok.1.1.1.2,
    ok.1.1.2, ok.1.2⟩

private theorem rowsOk_of_inline : ∀ rows : List JoltISA.Instr,
    rows.all inlineRowOk = true → rowsOk rows = true
  | [], _ => rfl
  | [last], ok => by
    simp only [List.all_cons, List.all_nil, Bool.and_true] at ok
    exact (inlineRowOk_parts ok).1
  | row :: next :: rest, ok => by
    simp only [List.all_cons, Bool.and_eq_true] at ok
    have head := inlineRowOk_parts ok.1
    have tail := rowsOk_of_inline (next :: rest) (by
      simp only [List.all_cons, Bool.and_eq_true]; exact ok.2)
    simp only [rowsOk, head.1, head.2.1, tail, Bool.and_self]

private theorem shiftPairsOk_of_inline (previous : JoltISA.Instr) : ∀ rows : List JoltISA.Instr,
    rows.all inlineRowOk = true → shiftPairsOk previous rows = true
  | [], _ => rfl
  | row :: rest, ok => by
    simp only [List.all_cons, Bool.and_eq_true] at ok
    have head := inlineRowOk_parts ok.1
    simp only [shiftPairsOk, head.2.2.1, head.2.2.2.1, Bool.not_false, Bool.true_or,
      shiftPairsOk_of_inline row rest ok.2, Bool.and_self]

private theorem firstAccessIsWrite_of_noRead (register : JoltISA.VReg) :
    ∀ rows : List JoltISA.Instr, (∀ row ∈ rows, ExpansionTempLiveness.reads register row = false) →
      ExpansionTempLiveness.firstAccessIsWrite register rows = true
  | [], _ => rfl
  | row :: rest, noRead => by
    simp only [ExpansionTempLiveness.firstAccessIsWrite, noRead row List.mem_cons_self,
      Bool.not_false, Bool.true_and,
      firstAccessIsWrite_of_noRead register rest
        (fun other mem => noRead other (List.mem_cons_of_mem _ mem)),
      Bool.or_true]

/-- Rows that pass `inlineRowOk` one by one pass all the sequence checks.
Example: the generated `SHA256_INLINE` rows pass `sequenceOk`. -/
theorem sequenceOk_of_inlineRowsOk (rows : List JoltISA.Instr)
    (ok : rows.all inlineRowOk = true) : sequenceOk rows = true := by
  have each : ∀ row ∈ rows, inlineRowOk row = true := List.all_eq_true.mp ok
  have straight : ∀ row ∈ rows, straightLineRow row = true :=
    fun row mem => (inlineRowOk_parts (each row mem)).2.2.2.2.2
  have shifts : shiftsOk rows = true := by
    cases rows with
    | nil => rfl
    | cons row rest =>
      simp only [List.all_cons, Bool.and_eq_true] at ok
      have head := inlineRowOk_parts ok.1
      simp only [shiftsOk, head.2.2.1, head.2.2.2.1, Bool.not_false,
        shiftPairsOk_of_inline row rest ok.2, Bool.and_self]
  have temps : ExpansionTempLiveness.tempsReadAfterWrite rows = true := by
    unfold ExpansionTempLiveness.tempsReadAfterWrite
    rw [List.all_eq_true]
    intro index inRange
    apply firstAccessIsWrite_of_noRead
    intro row mem
    have noRead := (inlineRowOk_parts (each row mem)).2.2.2.2.1
    unfold noTempRead at noRead
    have := List.all_eq_true.mp noRead index inRange
    simpa only [Bool.not_eq_eq_eq_not, Bool.not_true] using this
  have jumpEnd : jumpEndNoStore rows = true := by
    unfold jumpEndNoStore
    split
    · rename_i last
      have := straight _ (List.mem_of_getLast? last)
      simp [straightLineRow] at this
    · rename_i last
      have := straight _ (List.mem_of_getLast? last)
      simp [straightLineRow] at this
    · rfl
  have jalrs : sequenceJalrsVirtual rows = true := by
    unfold sequenceJalrsVirtual
    rw [List.all_eq_true]
    intro row mem
    have := straight row mem
    split <;> simp_all [straightLineRow]
  have bases : virtualJalrBaseUnwritten rows = true := by
    unfold virtualJalrBaseUnwritten
    rw [List.all_eq_true]
    intro row mem
    have := straight row mem
    split <;> simp_all [straightLineRow]
  have advice : advicePairsOk rows = true := by
    clear ok shifts temps jumpEnd jalrs bases each
    induction rows with
    | nil => rfl
    | cons row rest ih =>
      have head := straight row List.mem_cons_self
      simp only [advicePairsOk, ih (fun r mem => straight r (List.mem_cons_of_mem _ mem)),
        Bool.and_true]
      split <;> simp_all [straightLineRow]
  have spoil : noSpoilAsserts rows = true := by
    unfold noSpoilAsserts
    rw [List.all_eq_true]
    intro row mem
    have := straight row mem
    split <;> simp_all [straightLineRow]
  simp only [sequenceOk, rowsOk_of_inline rows ok, shifts, temps, jumpEnd, jalrs, bases, advice,
    spoil, Bool.and_self]

end ExpansionFacts
