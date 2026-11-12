import JoltTests.ExpansionParity.Row

/-!
# Rust source records as Lean source instructions

The driver writes each source instruction as its `SourceInstructionKind` name
and its `NormalizedOperands` (`rd`, `rs1`, `rs2`, `imm`), the operands Jolt's
decoder produces (`crates/jolt-program/src/image/decode.rs` at the pin).
This module maps such a record to the Lean `SourceInstruction`
(`JoltConstraints/expansion_helpers.lean`, `JoltBytecode/RiscvInstruction.lean`).

Lean's constructors hold the encoded fields, so the map inverts Jolt's
normalization: a 12-bit immediate must be the sign extension of its low 12 bits,
`SRAI`'s immediate is `0x400 | shamt`, an upper immediate has zero low 12 bits,
and a CSR address must be one of the six `JoltISA.SystemCSR` constructors.
When the operands do not fit, or Lean has no constructor for the kind, the map
says why instead of guessing.
-/

open Lean LeanRV64D

namespace ExpansionParity

/-- A source record in the driver's schema. -/
structure SourceView where
  kind : String
  address : Nat
  rd : Option Nat
  rs1 : Option Nat
  rs2 : Option Nat
  imm : Int
  compressed : Bool
  inlineName : Option String
  deriving Inhabited

def SourceView.ofJson (j : Json) : Except String SourceView := do
  let inlineName ← match ← getField j "inline" with
    | .null => pure none
    | v => some <$> (← getField v "name").getStr?
  pure
    { kind := ← (← getField j "kind").getStr?
      address := ← (← getField j "address").getNat?
      rd := ← optNat j "rd"
      rs1 := ← optNat j "rs1"
      rs2 := ← optNat j "rs2"
      imm := ← intOfString "imm" (← (← getField j "imm").getStr?)
      compressed := ← (← getField j "is_compressed").getBool?
      inlineName }

/-- Why a Rust source record has no Lean source instruction. -/
inductive NoLeanSource where
  /-- Lean's `SourceInstruction` has no constructor for this Rust kind. -/
  | kind (kind : String)
  /-- The Lean constructor exists but cannot hold these operands. -/
  | operand (kind why : String)

def NoLeanSource.describe : NoLeanSource → String
  | .kind k => s!"Lean's SourceInstruction has no constructor for Rust kind {k}"
  | .operand k why => s!"Lean's {k} constructor cannot hold the operands: {why}"

abbrev MapM := Except NoLeanSource

def u64 (i : Int) : Nat := (i % ((2 : Int) ^ 64)).toNat

def reg (kind field : String) : Option Nat → MapM regidx
  | some n =>
      if n < 32 then pure (regidx.Regidx (BitVec.ofNat 5 n))
      else throw (.operand kind s!"{field} = {n} is not x0..x31")
  | none => throw (.operand kind s!"{field} is missing")

/-- A `w`-bit field whose sign extension to 64 bits is the Rust immediate
(taken modulo 2^64, since Jolt prints some immediates as u64 and some as i64). -/
def sext (kind : String) (w : Nat) (i : Int) : MapM (BitVec w) :=
  let b : BitVec w := BitVec.ofInt w i
  if (b.signExtend 64).toNat == u64 i then pure b
  else throw (.operand kind s!"immediate {i} is not a sign-extended {w}-bit value")

/-- LUI and AUIPC: Jolt's immediate is the sign-extended `imm20 << 12`. -/
def upper (kind : String) (i : Int) : MapM (BitVec 20) :=
  let b : BitVec 20 := BitVec.ofNat 20 (u64 i / 4096)
  if ((b ++ (0 : BitVec 12)).signExtend 64).toNat == u64 i then pure b
  else throw (.operand kind s!"immediate {i} is not a sign-extended imm20 << 12")

/-- Shift amount of width `w`.
`decode.rs` normalizes SRAI's and SRAIW's immediate to `0x400 | shamt`, while
Jolt's golden fixture passes the bare shift amount; `expand_srai` and
`expand_sraiw` read only `imm & 0x3f` and `imm & 0x1f` (`shifts/srai.rs:11`,
`shifts/sraiw.rs:6`), so an arithmetic shift accepts both forms. -/
def shamt (kind : String) (w : Nat) (arith : Bool) (i : Int) : MapM (BitVec w) :=
  let s := if arith && i ≥ 0x400 then i - 0x400 else i
  if 0 ≤ s && s < (2 : Int) ^ w then pure (BitVec.ofNat w s.toNat)
  else throw (.operand kind
    s!"immediate {i} is not {if arith then "[0x400 |] " else ""}a {w}-bit shift amount")

def systemCSRs : List JoltISA.SystemCSR :=
  [.mstatus, .mtvec, .mscratch, .mepc, .mcause, .mtval]

/-- The five-bit immediate of `CSRRWI`, `CSRRSI` and `CSRRCI`. Jolt's decoder
carries it in the `rs1` operand (`expand/control_flow/csr_immediate.rs` at
`c336a6da7`, `uimm = rs1(instruction)`). -/
def uimm5 (kind : String) : Option Nat → MapM (BitVec 5)
  | some n =>
      if n < 32 then pure (BitVec.ofNat 5 n)
      else throw (.operand kind s!"uimm (rs1 field) = {n} is not a 5-bit value")
  | none => throw (.operand kind "uimm (rs1 field) is missing")

def csr (kind : String) (i : Int) : MapM JoltISA.SystemCSR := do
  let address ← sext kind 12 i
  match systemCSRs.find? (·.address == address) with
  | some c => pure c
  | none => throw (.operand kind s!"CSR {address.toNat} is not a JoltISA.SystemCSR")

/-- The Lean source instruction for a Rust source record.
Operands Lean does not carry are fixed: the division quotient (advice; it does
not reach the rows' encoded fields) is 0 and the atomic `aq`/`rl` bits are false. -/
def SourceView.toLean (s : SourceView) : MapM SourceInstruction := do
  let k := s.kind
  let rd := reg k "rd" s.rd
  let rs1 := reg k "rs1" s.rs1
  let rs2 := reg k "rs2" s.rs2
  let i12 := sext k 12 s.imm
  let i13 := sext k 13 s.imm
  let rv (i : RiscvInstruction) : MapM SourceInstruction := pure (.riscv i)
  let jc (i : JoltCustomInstruction) : MapM SourceInstruction := pure (.jolt i)
  match k with
  | "LUI" => rv (.LUI (← rd) (← upper k s.imm))
  | "AUIPC" => rv (.AUIPC (← rd) (← upper k s.imm))
  | "JAL" => rv (.JAL (← rd) (← sext k 21 s.imm))
  | "JALR" => rv (.JALR (← rd) (← rs1) (← i12))
  | "BEQ" => rv (.BEQ (← rs1) (← rs2) (← i13))
  | "BNE" => rv (.BNE (← rs1) (← rs2) (← i13))
  | "BLT" => rv (.BLT (← rs1) (← rs2) (← i13))
  | "BGE" => rv (.BGE (← rs1) (← rs2) (← i13))
  | "BLTU" => rv (.BLTU (← rs1) (← rs2) (← i13))
  | "BGEU" => rv (.BGEU (← rs1) (← rs2) (← i13))
  | "LB" => rv (.LB (← rd) (← rs1) (← i12))
  | "LH" => rv (.LH (← rd) (← rs1) (← i12))
  | "LW" => rv (.LW (← rd) (← rs1) (← i12))
  | "LBU" => rv (.LBU (← rd) (← rs1) (← i12))
  | "LHU" => rv (.LHU (← rd) (← rs1) (← i12))
  | "LWU" => rv (.LWU (← rd) (← rs1) (← i12))
  | "LD" => rv (.LD (← rd) (← rs1) (← i12))
  | "SB" => rv (.SB (← rs2) (← rs1) (← i12))
  | "SH" => rv (.SH (← rs2) (← rs1) (← i12))
  | "SW" => rv (.SW (← rs2) (← rs1) (← i12))
  | "SD" => rv (.SD (← rs2) (← rs1) (← i12))
  | "ADDI" => rv (.ADDI (← rd) (← rs1) (← i12))
  | "SLTI" => rv (.SLTI (← rd) (← rs1) (← i12))
  | "SLTIU" => rv (.SLTIU (← rd) (← rs1) (← i12))
  | "XORI" => rv (.XORI (← rd) (← rs1) (← i12))
  | "ORI" => rv (.ORI (← rd) (← rs1) (← i12))
  | "ANDI" => rv (.ANDI (← rd) (← rs1) (← i12))
  | "ADDIW" => rv (.ADDIW (← rd) (← rs1) (← i12))
  | "SLLI" => rv (.SLLI (← rd) (← rs1) (← shamt k 6 false s.imm))
  | "SRLI" => rv (.SRLI (← rd) (← rs1) (← shamt k 6 false s.imm))
  | "SRAI" => rv (.SRAI (← rd) (← rs1) (← shamt k 6 true s.imm))
  | "SLLIW" => rv (.SLLIW (← rd) (← rs1) (← shamt k 5 false s.imm))
  | "SRLIW" => rv (.SRLIW (← rd) (← rs1) (← shamt k 5 false s.imm))
  | "SRAIW" => rv (.SRAIW (← rd) (← rs1) (← shamt k 5 true s.imm))
  | "ADD" => rv (.ADD (← rd) (← rs1) (← rs2))
  | "SUB" => rv (.SUB (← rd) (← rs1) (← rs2))
  | "SLL" => rv (.SLL (← rd) (← rs1) (← rs2))
  | "SLT" => rv (.SLT (← rd) (← rs1) (← rs2))
  | "SLTU" => rv (.SLTU (← rd) (← rs1) (← rs2))
  | "XOR" => rv (.XOR (← rd) (← rs1) (← rs2))
  | "SRL" => rv (.SRL (← rd) (← rs1) (← rs2))
  | "SRA" => rv (.SRA (← rd) (← rs1) (← rs2))
  | "OR" => rv (.OR (← rd) (← rs1) (← rs2))
  | "AND" => rv (.AND (← rd) (← rs1) (← rs2))
  | "ANDN" => rv (.ANDN (← rd) (← rs1) (← rs2))
  | "ADDW" => rv (.ADDW (← rd) (← rs1) (← rs2))
  | "SUBW" => rv (.SUBW (← rd) (← rs1) (← rs2))
  | "SLLW" => rv (.SLLW (← rd) (← rs1) (← rs2))
  | "SRLW" => rv (.SRLW (← rd) (← rs1) (← rs2))
  | "SRAW" => rv (.SRAW (← rd) (← rs1) (← rs2))
  | "MUL" => rv (.MUL (← rd) (← rs1) (← rs2))
  | "MULH" => rv (.MULH (← rd) (← rs1) (← rs2))
  | "MULHU" => rv (.MULHU (← rd) (← rs1) (← rs2))
  | "MULHSU" => rv (.MULHSU (← rd) (← rs1) (← rs2))
  | "MULW" => rv (.MULW (← rd) (← rs1) (← rs2))
  | "DIV" => rv (.DIV (← rd) (← rs1) (← rs2) 0)
  | "DIVU" => rv (.DIVU (← rd) (← rs1) (← rs2) 0)
  | "REM" => rv (.REM (← rd) (← rs1) (← rs2) 0)
  | "REMU" => rv (.REMU (← rd) (← rs1) (← rs2) 0)
  | "DIVW" => rv (.DIVW (← rd) (← rs1) (← rs2) 0)
  | "DIVUW" => rv (.DIVUW (← rd) (← rs1) (← rs2) 0)
  | "REMW" => rv (.REMW (← rd) (← rs1) (← rs2) 0)
  | "REMUW" => rv (.REMUW (← rd) (← rs1) (← rs2) 0)
  | "FENCE" => rv .FENCE
  | "ECALL" => rv .ECALL
  | "EBREAK" => rv .EBREAK
  | "MRET" => rv .MRET
  | "LRW" => rv (.LR_W (← rd) (← rs1) false false)
  | "LRD" => rv (.LR_D (← rd) (← rs1) false false)
  | "SCW" => rv (.SC_W (← rd) (← rs1) (← rs2) false false)
  | "SCD" => rv (.SC_D (← rd) (← rs1) (← rs2) false false)
  | "AMOSWAPW" => rv (.AMOSWAP_W (← rd) (← rs1) (← rs2) false false)
  | "AMOADDW" => rv (.AMOADD_W (← rd) (← rs1) (← rs2) false false)
  | "AMOXORW" => rv (.AMOXOR_W (← rd) (← rs1) (← rs2) false false)
  | "AMOANDW" => rv (.AMOAND_W (← rd) (← rs1) (← rs2) false false)
  | "AMOORW" => rv (.AMOOR_W (← rd) (← rs1) (← rs2) false false)
  | "AMOMINW" => rv (.AMOMIN_W (← rd) (← rs1) (← rs2) false false)
  | "AMOMAXW" => rv (.AMOMAX_W (← rd) (← rs1) (← rs2) false false)
  | "AMOMINUW" => rv (.AMOMINU_W (← rd) (← rs1) (← rs2) false false)
  | "AMOMAXUW" => rv (.AMOMAXU_W (← rd) (← rs1) (← rs2) false false)
  | "AMOSWAPD" => rv (.AMOSWAP_D (← rd) (← rs1) (← rs2) false false)
  | "AMOADDD" => rv (.AMOADD_D (← rd) (← rs1) (← rs2) false false)
  | "AMOXORD" => rv (.AMOXOR_D (← rd) (← rs1) (← rs2) false false)
  | "AMOANDD" => rv (.AMOAND_D (← rd) (← rs1) (← rs2) false false)
  | "AMOORD" => rv (.AMOOR_D (← rd) (← rs1) (← rs2) false false)
  | "AMOMIND" => rv (.AMOMIN_D (← rd) (← rs1) (← rs2) false false)
  | "AMOMAXD" => rv (.AMOMAX_D (← rd) (← rs1) (← rs2) false false)
  | "AMOMINUD" => rv (.AMOMINU_D (← rd) (← rs1) (← rs2) false false)
  | "AMOMAXUD" => rv (.AMOMAXU_D (← rd) (← rs1) (← rs2) false false)
  | "CSRRW" => rv (.CSRRW (← rd) (← csr k s.imm) (← rs1))
  | "CSRRS" => rv (.CSRRS (← rd) (← csr k s.imm) (← rs1))
  | "CSRRC" => rv (.CSRRC (← rd) (← csr k s.imm) (← rs1))
  | "CSRRWI" => rv (.CSRRWI (← rd) (← csr k s.imm) (← uimm5 k s.rs1))
  | "CSRRSI" => rv (.CSRRSI (← rd) (← csr k s.imm) (← uimm5 k s.rs1))
  | "CSRRCI" => rv (.CSRRCI (← rd) (← csr k s.imm) (← uimm5 k s.rs1))
  | "AdviceLB" => jc (.AdviceLB (← rd))
  | "AdviceLH" => jc (.AdviceLH (← rd))
  | "AdviceLW" => jc (.AdviceLW (← rd))
  | "AdviceLD" => jc (.AdviceLD (← rd))
  | "VirtualRev8W" => jc (.VirtualRev8W (← rd) (← rs1))
  | "VirtualAssertEQ" => jc (.VirtualAssertEQ (← rs1) (← rs2) (← i13))
  | "VirtualHostIO" => jc .VirtualHostIO
  | _ => throw (.kind k)

/-- Lean source kinds that Jolt's decoder produces only from a16z/jolt#2384
(`decode.rs:195-208` at `c336a6da7`), not at the pin. The driver emits them
only when built with the `zicsr-remaining` feature; `runT1` reports which of
them a `rows.jsonl` lacks. -/
def zicsrRemainingKinds : List String := ["CSRRC", "CSRRWI", "CSRRSI", "CSRRCI"]

end ExpansionParity
