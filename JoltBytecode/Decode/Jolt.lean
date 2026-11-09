import JoltBytecode.RiscvInstruction

/-!
Jolt's image decoder and RV64 compressed-instruction normalization at
`669cf17ea` (a16z/jolt branch `align/system-semantics`, the same files as
a16z/jolt#2384), before a16z/jolt#2381 rejects the parcel `0x6001`.
The opcode and operand helpers transcribe `crates/jolt-program/src/image/decode.rs`;
the parcel normalization transcribes `crates/jolt-riscv/src/uncompress.rs`.
-/

open LeanRV64D

namespace Decode

/-- Destination register, from Jolt's `rd` and `format_*_operands`; e.g. ADDI x1 uses 1. -/
def rd (w : BitVec 32) : regidx := .Regidx (w.extractLsb 11 7)

/-- First source register, from Jolt's `rs1` and `format_*_operands`; e.g. ADDI x1,x2 uses 2. -/
def rs1 (w : BitVec 32) : regidx := .Regidx (w.extractLsb 19 15)

/-- Second source register, from Jolt's `rs2` and `format_r_operands`; e.g. ADD x1,x2,x3 uses 3. -/
def rs2 (w : BitVec 32) : regidx := .Regidx (w.extractLsb 24 20)

/-- Raw I immediate from `format_i_operands` and `format_load_operands`; -1 is 0xfff. -/
def immI (w : BitVec 32) : BitVec 12 := w.extractLsb 31 20

/-- Raw S immediate from `format_s_operands`; its two pieces encode e.g. SD's offset. -/
def immS (w : BitVec 32) : BitVec 12 := w.extractLsb 31 25 ++ w.extractLsb 11 7

/-- Raw B immediate from `format_b_operands`, including the implicit low zero; e.g. offset 2. -/
def immB (w : BitVec 32) : BitVec 13 :=
  w.extractLsb 31 31 ++ w.extractLsb 7 7 ++ w.extractLsb 30 25 ++ w.extractLsb 11 8 ++ 0#1

/-- Raw U immediate from `format_u_operands`, before shifting by twelve; e.g. LUI's 0x12345. -/
def immU (w : BitVec 32) : BitVec 20 := w.extractLsb 31 12

/-- Raw J immediate from `format_j_operands`, including the implicit low zero; e.g. offset 2. -/
def immJ (w : BitVec 32) : BitVec 21 :=
  w.extractLsb 31 31 ++ w.extractLsb 19 12 ++ w.extractLsb 20 20 ++ w.extractLsb 30 21 ++ 0#1

/-- Jolt's `funct3` selector; ADDI has selector zero. -/
def funct3 (w : BitVec 32) : Nat := (w.extractLsb 14 12).toNat

/-- Jolt's `funct7` selector; SUB has selector 0x20. -/
def funct7 (w : BitVec 32) : Nat := (w.extractLsb 31 25).toNat

/-- Supported CSR addresses, as accepted by the expander; 0x300 denotes mstatus.
Jolt rejects other addresses in `crates/jolt-program/src/expand/control_flow/csrrs.rs`
(`expand_csrrs`, line 14), and the corresponding CSRRW expansion. -/
def csr (w : BitVec 32) : Option JoltISA.SystemCSR :=
  match (immI w).toNat with
  | 0x300 => some .mstatus
  | 0x305 => some .mtvec
  | 0x340 => some .mscratch
  | 0x341 => some .mepc
  | 0x342 => some .mcause
  | 0x343 => some .mtval
  | _ => none

/-- Jolt's `decode_instruction` followed by its operand formats, for standard encodings.
For example, 0x00100093 decodes to ADDI x1,x0,1.
`advice` supplies the division/remainder operand absent from the encoding. -/
def joltDecode (w : BitVec 32) (advice : BitVec 64) : Option RiscvInstruction :=
  let d := rd w
  let a := rs1 w
  let b := rs2 w
  match (w.extractLsb 6 0).toNat with
  | 0x37 => some (.LUI d (immU w))
  | 0x17 => some (.AUIPC d (immU w))
  | 0x6f => some (.JAL d (immJ w))
  | 0x67 => if funct3 w = 0 then some (.JALR d a (immI w)) else none
  | 0x63 => match funct3 w with
    | 0 => some (.BEQ a b (immB w))
    | 1 => some (.BNE a b (immB w))
    | 4 => some (.BLT a b (immB w))
    | 5 => some (.BGE a b (immB w))
    | 6 => some (.BLTU a b (immB w))
    | 7 => some (.BGEU a b (immB w))
    | _ => none
  | 0x03 => match funct3 w with
    | 0 => some (.LB d a (immI w))
    | 1 => some (.LH d a (immI w))
    | 2 => some (.LW d a (immI w))
    | 3 => some (.LD d a (immI w))
    | 4 => some (.LBU d a (immI w))
    | 5 => some (.LHU d a (immI w))
    | 6 => some (.LWU d a (immI w))
    | _ => none
  | 0x23 => match funct3 w with
    | 0 => some (.SB b a (immS w))
    | 1 => some (.SH b a (immS w))
    | 2 => some (.SW b a (immS w))
    | 3 => some (.SD b a (immS w))
    | _ => none
  | 0x13 => match funct3 w with
    | 0 => some (.ADDI d a (immI w))
    | 2 => some (.SLTI d a (immI w))
    | 3 => some (.SLTIU d a (immI w))
    | 4 => some (.XORI d a (immI w))
    | 6 => some (.ORI d a (immI w))
    | 7 => some (.ANDI d a (immI w))
    | 1 => if w.extractLsb 31 26 = 0 then some (.SLLI d a (w.extractLsb 25 20)) else none
    | 5 => match (w.extractLsb 31 26).toNat with
      | 0 => some (.SRLI d a (w.extractLsb 25 20))
      | 0x10 => some (.SRAI d a (w.extractLsb 25 20))
      | _ => none
    | _ => none
  | 0x1b => match funct3 w, funct7 w with
    | 0, _ => some (.ADDIW d a (immI w))
    | 1, 0 => some (.SLLIW d a (w.extractLsb 24 20))
    | 5, 0 => some (.SRLIW d a (w.extractLsb 24 20))
    | 5, 0x20 => some (.SRAIW d a (w.extractLsb 24 20))
    | _, _ => none
  | 0x33 => match funct3 w, funct7 w with
    | 0, 0 => some (.ADD d a b)
    | 0, 0x20 => some (.SUB d a b)
    | 1, 0 => some (.SLL d a b)
    | 2, 0 => some (.SLT d a b)
    | 3, 0 => some (.SLTU d a b)
    | 4, 0 => some (.XOR d a b)
    | 5, 0 => some (.SRL d a b)
    | 5, 0x20 => some (.SRA d a b)
    | 6, 0 => some (.OR d a b)
    | 7, 0 => some (.AND d a b)
    | 0, 1 => some (.MUL d a b)
    | 1, 1 => some (.MULH d a b)
    | 2, 1 => some (.MULHSU d a b)
    | 3, 1 => some (.MULHU d a b)
    | 4, 1 => some (.DIV d a b advice)
    | 5, 1 => some (.DIVU d a b advice)
    | 6, 1 => some (.REM d a b advice)
    | 7, 1 => some (.REMU d a b advice)
    | _, _ => none
  | 0x3b => match funct3 w, funct7 w with
    | 0, 0 => some (.ADDW d a b)
    | 0, 0x20 => some (.SUBW d a b)
    | 1, 0 => some (.SLLW d a b)
    | 5, 0 => some (.SRLW d a b)
    | 5, 0x20 => some (.SRAW d a b)
    | 0, 1 => some (.MULW d a b)
    | 4, 1 => some (.DIVW d a b advice)
    | 5, 1 => some (.DIVUW d a b advice)
    | 6, 1 => some (.REMW d a b advice)
    | 7, 1 => some (.REMUW d a b advice)
    | _, _ => none
  | 0x0f => if funct3 w = 0 then some .FENCE else none
  | 0x2f =>
    let aq := w.getLsbD 26
    let rl := w.getLsbD 25
    match funct3 w, (w.extractLsb 31 27).toNat with
    | 2, 2 => if w.extractLsb 24 20 = 0 then some (.LR_W d a aq rl) else none
    | 3, 2 => if w.extractLsb 24 20 = 0 then some (.LR_D d a aq rl) else none
    | 2, 3 => some (.SC_W d a b aq rl)
    | 3, 3 => some (.SC_D d a b aq rl)
    | 2, 1 => some (.AMOSWAP_W d a b aq rl)
    | 3, 1 => some (.AMOSWAP_D d a b aq rl)
    | 2, 0 => some (.AMOADD_W d a b aq rl)
    | 3, 0 => some (.AMOADD_D d a b aq rl)
    | 2, 12 => some (.AMOAND_W d a b aq rl)
    | 3, 12 => some (.AMOAND_D d a b aq rl)
    | 2, 8 => some (.AMOOR_W d a b aq rl)
    | 3, 8 => some (.AMOOR_D d a b aq rl)
    | 2, 4 => some (.AMOXOR_W d a b aq rl)
    | 3, 4 => some (.AMOXOR_D d a b aq rl)
    | 2, 16 => some (.AMOMIN_W d a b aq rl)
    | 3, 16 => some (.AMOMIN_D d a b aq rl)
    | 2, 20 => some (.AMOMAX_W d a b aq rl)
    | 3, 20 => some (.AMOMAX_D d a b aq rl)
    | 2, 24 => some (.AMOMINU_W d a b aq rl)
    | 3, 24 => some (.AMOMINU_D d a b aq rl)
    | 2, 28 => some (.AMOMAXU_W d a b aq rl)
    | 3, 28 => some (.AMOMAXU_D d a b aq rl)
    | _, _ => none
  | 0x73 => match funct3 w with
    | 0 => if w = 0x00000073 then some .ECALL
      else if w = 0x00100073 then some .EBREAK
      else if w = 0x30200073 then some .MRET else none
    | 1 => (csr w).map fun c => .CSRRW d c a
    | 2 => (csr w).map fun c => .CSRRS d c a
    | 3 => (csr w).map fun c => .CSRRC d c a
    | 5 => (csr w).map fun c => .CSRRWI d c (w.extractLsb 19 15)
    | 6 => (csr w).map fun c => .CSRRSI d c (w.extractLsb 19 15)
    | 7 => (csr w).map fun c => .CSRRCI d c (w.extractLsb 19 15)
    | _ => none
  -- Inline, decode_custom, and field-inline opcodes are outside standard RISC-V.
  | _ => none

/-- Jolt's `sign_bit_mask` in `uncompress.rs`; a set sign bit supplies the mask, e.g. -32. -/
def signBitMask (value bit mask : BitVec 32) : BitVec 32 :=
  if value &&& bit = bit then mask else 0

/-- Jolt's `j_offset`, the scattered signed C.J displacement; e.g. -2. -/
def jOffset (h : BitVec 32) : BitVec 32 :=
  signBitMask h 0x1000 0xfffff000 ||| ((h >>> 1) &&& 0x800) |||
    ((h >>> 7) &&& 0x10) ||| ((h >>> 1) &&& 0x300) ||| ((h <<< 2) &&& 0x400) |||
    ((h >>> 1) &&& 0x40) ||| ((h <<< 1) &&& 0x80) ||| ((h >>> 2) &&& 0xe) ||| ((h <<< 3) &&& 0x20)

/-- Jolt's `branch_immediates`, the high and low B-format pieces for C.BEQZ/C.BNEZ; e.g. offset 2. -/
def branchImmediates (h : BitVec 32) : BitVec 32 × BitVec 32 :=
  let o := signBitMask h 0x1000 0xfffffe00 ||| ((h >>> 4) &&& 0x100) |||
    ((h >>> 7) &&& 0x18) ||| ((h <<< 1) &&& 0xc0) ||| ((h >>> 2) &&& 6) ||| ((h <<< 3) &&& 0x20)
  (((o >>> 6) &&& 0x40) ||| ((o >>> 5) &&& 0x3f),
    ((o >>> 11) &&& 1) ||| (o &&& 0x1e))

/-- Jolt's `uncompress_rv64_instruction`, including invalid parcels; e.g. 0x6001 becomes 0x13. -/
def joltUncompress (parcel : BitVec 16) : BitVec 32 :=
  let h := parcel.setWidth 32
  let r := (h >>> 7) &&& 0x1f
  let rp := ((h >>> 7) &&& 7) + 8
  let bp := ((h >>> 2) &&& 7) + 8
  let ci := signBitMask h 0x1000 0xffffffc0 ||| ((h >>> 7) &&& 0x20) ||| ((h >>> 2) &&& 0x1f)
  let sh := ((h >>> 7) &&& 0x20) ||| ((h >>> 2) &&& 0x1f)
  match (h &&& 3).toNat, ((h >>> 13) &&& 7).toNat with
  | 0, 0 =>
    let u := ((h >>> 7) &&& 0x30) ||| ((h >>> 1) &&& 0x3c0) |||
      ((h >>> 4) &&& 4) ||| ((h >>> 2) &&& 8)
    if u ≠ 0 then (u <<< 20) ||| (2 <<< 15) ||| (bp <<< 7) ||| 0x13 else 0xffffffff
  | 0, 1 | 0, 3 =>
    let o := ((h >>> 7) &&& 0x38) ||| ((h <<< 1) &&& 0xc0)
    (o <<< 20) ||| (rp <<< 15) ||| (3 <<< 12) ||| (bp <<< 7) |||
      (if ((h >>> 13) &&& 7) = 1 then 0x07 else 0x03)
  | 0, 2 =>
    let o := ((h >>> 7) &&& 0x38) ||| ((h >>> 4) &&& 4) ||| ((h <<< 1) &&& 0x40)
    (o <<< 20) ||| (rp <<< 15) ||| (2 <<< 12) ||| (bp <<< 7) ||| 0x03
  | 0, 5 | 0, 6 | 0, 7 =>
    let f := ((h >>> 13) &&& 7).toNat
    let o := ((h >>> 7) &&& 0x38) ||| ((h <<< 1) &&& (if f = 6 then 0x40 else 0xc0)) |||
      (if f = 6 then ((h >>> 4) &&& 4) else 0)
    (((o >>> 5) &&& 0x7f) <<< 25) ||| (bp <<< 20) ||| (rp <<< 15) |||
      ((if f = 6 then 2 else 3) <<< 12) ||| ((o &&& 0x1f) <<< 7) |||
      (if f = 5 then 0x27 else 0x23)
  | 1, 0 => if r = 0 ∨ ci = 0 then 0x13 else (ci <<< 20) ||| (r <<< 15) ||| (r <<< 7) ||| 0x13
  | 1, 1 => if r ≠ 0 then (ci <<< 20) ||| (r <<< 15) ||| (r <<< 7) ||| 0x1b else 0xffffffff
  | 1, 2 => if r ≠ 0 then (ci <<< 20) ||| (r <<< 7) ||| 0x13 else 0x13
  | 1, 3 =>
    if r = 2 then
      let imm := signBitMask h 0x1000 0xfffffc00 ||| ((h >>> 3) &&& 0x200) |||
        ((h >>> 2) &&& 0x10) ||| ((h <<< 1) &&& 0x40) ||| ((h <<< 4) &&& 0x180) ||| ((h <<< 3) &&& 0x20)
      if imm ≠ 0 then (imm <<< 20) ||| (r <<< 15) ||| (r <<< 7) ||| 0x13 else 0xffffffff
    else if r ≠ 0 then
      let imm := signBitMask h 0x1000 0xfffc0000 ||| ((h <<< 5) &&& 0x20000) ||| ((h <<< 10) &&& 0x1f000)
      if imm ≠ 0 then imm ||| (r <<< 7) ||| 0x37 else 0xffffffff
    else 0x13
  | 1, 4 => match ((h >>> 10) &&& 3).toNat with
    | 0 => (sh <<< 20) ||| (rp <<< 15) ||| (5 <<< 12) ||| (rp <<< 7) ||| 0x13
    | 1 => (0x20 <<< 25) ||| (sh <<< 20) ||| (rp <<< 15) ||| (5 <<< 12) ||| (rp <<< 7) ||| 0x13
    | 2 => (ci <<< 20) ||| (rp <<< 15) ||| (7 <<< 12) ||| (rp <<< 7) ||| 0x13
    | 3 =>
      let a := ((h >>> 12) &&& 1).toNat
      let b := ((h >>> 5) &&& 3).toNat
      let op : BitVec 32 := if a = 0 then 0x33 else 0x3b
      let f3 : BitVec 32 := if a = 0 then (if b = 1 then 4 else if b = 2 then 6 else 7) else 0
      let f7 : BitVec 32 := if b = 0 then 0x20 else 0
      if a = 0 ∨ b < 2 then
        (f7 <<< 25) ||| (bp <<< 20) ||| (rp <<< 15) |||
          ((if b = 0 then 0 else f3) <<< 12) ||| (rp <<< 7) ||| op
      else 0xffffffff
    | _ => 0xffffffff
  | 1, 5 =>
    let o := jOffset h
    let imm := ((o >>> 1) &&& 0x80000) ||| ((o <<< 8) &&& 0x7fe00) |||
      ((o >>> 3) &&& 0x100) ||| ((o >>> 12) &&& 0xff)
    (imm <<< 12) ||| 0x6f
  | 1, 6 | 1, 7 =>
    let (a, b) := branchImmediates h
    (a <<< 25) ||| (rp <<< 20) ||| (if ((h >>> 13) &&& 7) = 7 then 1 <<< 12 else 0) ||| (b <<< 7) ||| 0x63
  | 2, 0 => (sh <<< 20) ||| (r <<< 15) ||| (1 <<< 12) ||| (r <<< 7) ||| 0x13
  | 2, 1 | 2, 2 | 2, 3 =>
    let f := ((h >>> 13) &&& 7).toNat
    let o := ((h >>> 7) &&& 0x20) ||| ((h >>> 2) &&& (if f = 2 then 0x1c else 0x18)) |||
      ((h <<< 4) &&& (if f = 2 then 0xc0 else 0x1c0))
    if r ≠ 0 then (o <<< 20) ||| (2 <<< 15) ||| ((if f = 2 then 2 else 3) <<< 12) |||
      (r <<< 7) ||| (if f = 1 then 0x07 else 0x03) else 0xffffffff
  | 2, 4 =>
    let b := (h >>> 2) &&& 0x1f
    match ((h >>> 12) &&& 1).toNat with
    | 0 => if b = 0 then (if r = 0 then 0xffffffff else (r <<< 15) ||| 0x67)
      else if r = 0 then 0x13 else (b <<< 20) ||| (r <<< 7) ||| 0x33
    | _ => if b = 0 then (if r = 0 then 0x00100073 else (r <<< 15) ||| (1 <<< 7) ||| 0x67)
      else if r = 0 then 0x13 else (b <<< 20) ||| (r <<< 15) ||| (r <<< 7) ||| 0x33
  | 2, 5 | 2, 6 | 2, 7 =>
    let f := ((h >>> 13) &&& 7).toNat
    let b := (h >>> 2) &&& 0x1f
    let o := ((h >>> 7) &&& (if f = 6 then 0x3c else 0x38)) |||
      ((h >>> 1) &&& (if f = 6 then 0xc0 else 0x1c0))
    (((o >>> 5) &&& 0x3f) <<< 25) ||| (b <<< 20) ||| (2 <<< 15) |||
      ((if f = 6 then 2 else 3) <<< 12) ||| ((o &&& 0x1f) <<< 7) |||
      (if f = 5 then 0x27 else 0x23)
  | _, _ => 0xffffffff

/-- Compressed parcels the RISC-V specification marks reserved but Jolt accepts.
Sail rejects them as C_ILLEGAL; see the deviation list in docs/riscv-alignment.md.
For example, 0x6001 is a reserved C.LUI, although Jolt expands it to ADDI x0,x0,0. -/
def ReservedAccepted (h : BitVec 16) : Prop :=
  -- C.LUI nzimm=0 is RESERVED. Only rd=x0 is accepted by Jolt (canonical ADDI no-op);
  -- Sail returns C_ILLEGAL. rd=x2 (C.ADDI16SP) and other rd return 0xffffffff in Jolt.
  h.extractLsb 1 0 = 1 ∧ h.extractLsb 15 13 = 3 ∧ h.extractLsb 11 7 = 0 ∧
    h.extractLsb 12 12 = 0 ∧ h.extractLsb 6 2 = 0

end Decode
