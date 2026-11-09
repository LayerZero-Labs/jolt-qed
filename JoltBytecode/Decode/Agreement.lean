import JoltBytecode.Decode.ProofSupport

/-!
Agreement of Jolt's standard instruction decoder at `b65455e6d` with Sail's
RV64IMAC decoder. Cases follow Jolt's opcode and function-field tables in
`crates/jolt-program/src/image/decode.rs`.
-/

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail
  LeanRV64D LeanRV64D.Functions

namespace Decode

private theorem agree_LUI (w : BitVec 32)
    (hop : (Sail.BitVec.extractLsb w 6 0).toNat = 55)
    (s : SailState) :
    ∃ ast, ext_decode w s = .ok ast s ∧ _root_.Step.Matches (.LUI (rd w) (immU w)) ast := by
  decode32_case

private theorem agree_AUIPC (w : BitVec 32)
    (hop : (Sail.BitVec.extractLsb w 6 0).toNat = 23)
    (s : SailState) :
    ∃ ast, ext_decode w s = .ok ast s ∧ _root_.Step.Matches (.AUIPC (rd w) (immU w)) ast := by
  decode32_case

private theorem agree_JAL (w : BitVec 32)
    (hop : (Sail.BitVec.extractLsb w 6 0).toNat = 111)
    (s : SailState) :
    ∃ ast, ext_decode w s = .ok ast s ∧ _root_.Step.Matches (.JAL (rd w) (immJ w)) ast := by
  decode32_case

private theorem agree_JALR (w : BitVec 32)
    (hop : (Sail.BitVec.extractLsb w 6 0).toNat = 103)
    (h0 : (Sail.BitVec.extractLsb w 14 12).toNat = 0)
    (s : SailState) :
    ∃ ast, ext_decode w s = .ok ast s ∧ _root_.Step.Matches (.JALR (rd w) (rs1 w) (immI w)) ast := by
  decode32_case

private theorem agree_BEQ (w : BitVec 32)
    (hop : (Sail.BitVec.extractLsb w 6 0).toNat = 99)
    (h0 : (Sail.BitVec.extractLsb w 14 12).toNat = 0)
    (s : SailState) :
    ∃ ast, ext_decode w s = .ok ast s ∧ _root_.Step.Matches (.BEQ (rs1 w) (rs2 w) (immB w)) ast := by
  decode32_case

private theorem agree_BNE (w : BitVec 32)
    (hop : (Sail.BitVec.extractLsb w 6 0).toNat = 99)
    (h0 : (Sail.BitVec.extractLsb w 14 12).toNat = 1)
    (s : SailState) :
    ∃ ast, ext_decode w s = .ok ast s ∧ _root_.Step.Matches (.BNE (rs1 w) (rs2 w) (immB w)) ast := by
  decode32_case

private theorem agree_BLT (w : BitVec 32)
    (hop : (Sail.BitVec.extractLsb w 6 0).toNat = 99)
    (h0 : (Sail.BitVec.extractLsb w 14 12).toNat = 4)
    (s : SailState) :
    ∃ ast, ext_decode w s = .ok ast s ∧ _root_.Step.Matches (.BLT (rs1 w) (rs2 w) (immB w)) ast := by
  decode32_case

private theorem agree_BGE (w : BitVec 32)
    (hop : (Sail.BitVec.extractLsb w 6 0).toNat = 99)
    (h0 : (Sail.BitVec.extractLsb w 14 12).toNat = 5)
    (s : SailState) :
    ∃ ast, ext_decode w s = .ok ast s ∧ _root_.Step.Matches (.BGE (rs1 w) (rs2 w) (immB w)) ast := by
  decode32_case

private theorem agree_BLTU (w : BitVec 32)
    (hop : (Sail.BitVec.extractLsb w 6 0).toNat = 99)
    (h0 : (Sail.BitVec.extractLsb w 14 12).toNat = 6)
    (s : SailState) :
    ∃ ast, ext_decode w s = .ok ast s ∧ _root_.Step.Matches (.BLTU (rs1 w) (rs2 w) (immB w)) ast := by
  decode32_case

private theorem agree_BGEU (w : BitVec 32)
    (hop : (Sail.BitVec.extractLsb w 6 0).toNat = 99)
    (h0 : (Sail.BitVec.extractLsb w 14 12).toNat = 7)
    (s : SailState) :
    ∃ ast, ext_decode w s = .ok ast s ∧ _root_.Step.Matches (.BGEU (rs1 w) (rs2 w) (immB w)) ast := by
  decode32_case

private theorem agree_LB (w : BitVec 32)
    (hop : (Sail.BitVec.extractLsb w 6 0).toNat = 3)
    (h0 : (Sail.BitVec.extractLsb w 14 12).toNat = 0)
    (s : SailState) :
    ∃ ast, ext_decode w s = .ok ast s ∧ _root_.Step.Matches (.LB (rd w) (rs1 w) (immI w)) ast := by
  decode32_case

private theorem agree_LH (w : BitVec 32)
    (hop : (Sail.BitVec.extractLsb w 6 0).toNat = 3)
    (h0 : (Sail.BitVec.extractLsb w 14 12).toNat = 1)
    (s : SailState) :
    ∃ ast, ext_decode w s = .ok ast s ∧ _root_.Step.Matches (.LH (rd w) (rs1 w) (immI w)) ast := by
  decode32_case

private theorem agree_LW (w : BitVec 32)
    (hop : (Sail.BitVec.extractLsb w 6 0).toNat = 3)
    (h0 : (Sail.BitVec.extractLsb w 14 12).toNat = 2)
    (s : SailState) :
    ∃ ast, ext_decode w s = .ok ast s ∧ _root_.Step.Matches (.LW (rd w) (rs1 w) (immI w)) ast := by
  decode32_case

private theorem agree_LD (w : BitVec 32)
    (hop : (Sail.BitVec.extractLsb w 6 0).toNat = 3)
    (h0 : (Sail.BitVec.extractLsb w 14 12).toNat = 3)
    (s : SailState) :
    ∃ ast, ext_decode w s = .ok ast s ∧ _root_.Step.Matches (.LD (rd w) (rs1 w) (immI w)) ast := by
  decode32_case

private theorem agree_LBU (w : BitVec 32)
    (hop : (Sail.BitVec.extractLsb w 6 0).toNat = 3)
    (h0 : (Sail.BitVec.extractLsb w 14 12).toNat = 4)
    (s : SailState) :
    ∃ ast, ext_decode w s = .ok ast s ∧ _root_.Step.Matches (.LBU (rd w) (rs1 w) (immI w)) ast := by
  decode32_case

private theorem agree_LHU (w : BitVec 32)
    (hop : (Sail.BitVec.extractLsb w 6 0).toNat = 3)
    (h0 : (Sail.BitVec.extractLsb w 14 12).toNat = 5)
    (s : SailState) :
    ∃ ast, ext_decode w s = .ok ast s ∧ _root_.Step.Matches (.LHU (rd w) (rs1 w) (immI w)) ast := by
  decode32_case

private theorem agree_LWU (w : BitVec 32)
    (hop : (Sail.BitVec.extractLsb w 6 0).toNat = 3)
    (h0 : (Sail.BitVec.extractLsb w 14 12).toNat = 6)
    (s : SailState) :
    ∃ ast, ext_decode w s = .ok ast s ∧ _root_.Step.Matches (.LWU (rd w) (rs1 w) (immI w)) ast := by
  decode32_case

private theorem agree_SB (w : BitVec 32)
    (hop : (Sail.BitVec.extractLsb w 6 0).toNat = 35)
    (h0 : (Sail.BitVec.extractLsb w 14 12).toNat = 0)
    (s : SailState) :
    ∃ ast, ext_decode w s = .ok ast s ∧ _root_.Step.Matches (.SB (rs2 w) (rs1 w) (immS w)) ast := by
  decode32_case

private theorem agree_SH (w : BitVec 32)
    (hop : (Sail.BitVec.extractLsb w 6 0).toNat = 35)
    (h0 : (Sail.BitVec.extractLsb w 14 12).toNat = 1)
    (s : SailState) :
    ∃ ast, ext_decode w s = .ok ast s ∧ _root_.Step.Matches (.SH (rs2 w) (rs1 w) (immS w)) ast := by
  decode32_case

private theorem agree_SW (w : BitVec 32)
    (hop : (Sail.BitVec.extractLsb w 6 0).toNat = 35)
    (h0 : (Sail.BitVec.extractLsb w 14 12).toNat = 2)
    (s : SailState) :
    ∃ ast, ext_decode w s = .ok ast s ∧ _root_.Step.Matches (.SW (rs2 w) (rs1 w) (immS w)) ast := by
  decode32_case

private theorem agree_SD (w : BitVec 32)
    (hop : (Sail.BitVec.extractLsb w 6 0).toNat = 35)
    (h0 : (Sail.BitVec.extractLsb w 14 12).toNat = 3)
    (s : SailState) :
    ∃ ast, ext_decode w s = .ok ast s ∧ _root_.Step.Matches (.SD (rs2 w) (rs1 w) (immS w)) ast := by
  decode32_case

private theorem agree_ADDI (w : BitVec 32)
    (hop : (Sail.BitVec.extractLsb w 6 0).toNat = 19)
    (h0 : (Sail.BitVec.extractLsb w 14 12).toNat = 0)
    (s : SailState) :
    ∃ ast, ext_decode w s = .ok ast s ∧ _root_.Step.Matches (.ADDI (rd w) (rs1 w) (immI w)) ast := by
  decode32_case

private theorem agree_SLTI (w : BitVec 32)
    (hop : (Sail.BitVec.extractLsb w 6 0).toNat = 19)
    (h0 : (Sail.BitVec.extractLsb w 14 12).toNat = 2)
    (s : SailState) :
    ∃ ast, ext_decode w s = .ok ast s ∧ _root_.Step.Matches (.SLTI (rd w) (rs1 w) (immI w)) ast := by
  decode32_case

private theorem agree_SLTIU (w : BitVec 32)
    (hop : (Sail.BitVec.extractLsb w 6 0).toNat = 19)
    (h0 : (Sail.BitVec.extractLsb w 14 12).toNat = 3)
    (s : SailState) :
    ∃ ast, ext_decode w s = .ok ast s ∧ _root_.Step.Matches (.SLTIU (rd w) (rs1 w) (immI w)) ast := by
  decode32_case

private theorem agree_XORI (w : BitVec 32)
    (hop : (Sail.BitVec.extractLsb w 6 0).toNat = 19)
    (h0 : (Sail.BitVec.extractLsb w 14 12).toNat = 4)
    (s : SailState) :
    ∃ ast, ext_decode w s = .ok ast s ∧ _root_.Step.Matches (.XORI (rd w) (rs1 w) (immI w)) ast := by
  decode32_case

private theorem agree_ORI (w : BitVec 32)
    (hop : (Sail.BitVec.extractLsb w 6 0).toNat = 19)
    (h0 : (Sail.BitVec.extractLsb w 14 12).toNat = 6)
    (s : SailState) :
    ∃ ast, ext_decode w s = .ok ast s ∧ _root_.Step.Matches (.ORI (rd w) (rs1 w) (immI w)) ast := by
  decode32_case

private theorem agree_ANDI (w : BitVec 32)
    (hop : (Sail.BitVec.extractLsb w 6 0).toNat = 19)
    (h0 : (Sail.BitVec.extractLsb w 14 12).toNat = 7)
    (s : SailState) :
    ∃ ast, ext_decode w s = .ok ast s ∧ _root_.Step.Matches (.ANDI (rd w) (rs1 w) (immI w)) ast := by
  decode32_case

private theorem agree_SLLI (w : BitVec 32)
    (hop : (Sail.BitVec.extractLsb w 6 0).toNat = 19)
    (h0 : (Sail.BitVec.extractLsb w 14 12).toNat = 1)
    (h1 : Sail.BitVec.extractLsb w 31 26 = 0)
    (s : SailState) :
    ∃ ast, ext_decode w s = .ok ast s ∧ _root_.Step.Matches (.SLLI (rd w) (rs1 w) (w.extractLsb 25 20)) ast := by
  decode32_case

private theorem agree_SRLI (w : BitVec 32)
    (hop : (Sail.BitVec.extractLsb w 6 0).toNat = 19)
    (h0 : (Sail.BitVec.extractLsb w 14 12).toNat = 5)
    (h1 : (Sail.BitVec.extractLsb w 31 26).toNat = 0)
    (s : SailState) :
    ∃ ast, ext_decode w s = .ok ast s ∧ _root_.Step.Matches (.SRLI (rd w) (rs1 w) (w.extractLsb 25 20)) ast := by
  decode32_case

private theorem agree_SRAI (w : BitVec 32)
    (hop : (Sail.BitVec.extractLsb w 6 0).toNat = 19)
    (h0 : (Sail.BitVec.extractLsb w 14 12).toNat = 5)
    (h1 : (Sail.BitVec.extractLsb w 31 26).toNat = 16)
    (s : SailState) :
    ∃ ast, ext_decode w s = .ok ast s ∧ _root_.Step.Matches (.SRAI (rd w) (rs1 w) (w.extractLsb 25 20)) ast := by
  decode32_case

private theorem agree_ADDIW (w : BitVec 32)
    (hop : (Sail.BitVec.extractLsb w 6 0).toNat = 27)
    (h0 : (Sail.BitVec.extractLsb w 14 12).toNat = 0)
    (s : SailState) :
    ∃ ast, ext_decode w s = .ok ast s ∧ _root_.Step.Matches (.ADDIW (rd w) (rs1 w) (immI w)) ast := by
  decode32_case

private theorem agree_SLLIW (w : BitVec 32)
    (hop : (Sail.BitVec.extractLsb w 6 0).toNat = 27)
    (h0 : (Sail.BitVec.extractLsb w 14 12).toNat = 1)
    (h1 : (Sail.BitVec.extractLsb w 31 25).toNat = 0)
    (s : SailState) :
    ∃ ast, ext_decode w s = .ok ast s ∧ _root_.Step.Matches (.SLLIW (rd w) (rs1 w) (w.extractLsb 24 20)) ast := by
  decode32_case

private theorem agree_SRLIW (w : BitVec 32)
    (hop : (Sail.BitVec.extractLsb w 6 0).toNat = 27)
    (h0 : (Sail.BitVec.extractLsb w 14 12).toNat = 5)
    (h1 : (Sail.BitVec.extractLsb w 31 25).toNat = 0)
    (s : SailState) :
    ∃ ast, ext_decode w s = .ok ast s ∧ _root_.Step.Matches (.SRLIW (rd w) (rs1 w) (w.extractLsb 24 20)) ast := by
  decode32_case

private theorem agree_SRAIW (w : BitVec 32)
    (hop : (Sail.BitVec.extractLsb w 6 0).toNat = 27)
    (h0 : (Sail.BitVec.extractLsb w 14 12).toNat = 5)
    (h1 : (Sail.BitVec.extractLsb w 31 25).toNat = 32)
    (s : SailState) :
    ∃ ast, ext_decode w s = .ok ast s ∧ _root_.Step.Matches (.SRAIW (rd w) (rs1 w) (w.extractLsb 24 20)) ast := by
  decode32_case

private theorem agree_ADD (w : BitVec 32)
    (hop : (Sail.BitVec.extractLsb w 6 0).toNat = 51)
    (h0 : (Sail.BitVec.extractLsb w 14 12).toNat = 0)
    (h1 : (Sail.BitVec.extractLsb w 31 25).toNat = 0)
    (s : SailState) :
    ∃ ast, ext_decode w s = .ok ast s ∧ _root_.Step.Matches (.ADD (rd w) (rs1 w) (rs2 w)) ast := by
  decode32_case

private theorem agree_SUB (w : BitVec 32)
    (hop : (Sail.BitVec.extractLsb w 6 0).toNat = 51)
    (h0 : (Sail.BitVec.extractLsb w 14 12).toNat = 0)
    (h1 : (Sail.BitVec.extractLsb w 31 25).toNat = 32)
    (s : SailState) :
    ∃ ast, ext_decode w s = .ok ast s ∧ _root_.Step.Matches (.SUB (rd w) (rs1 w) (rs2 w)) ast := by
  decode32_case

private theorem agree_SLL (w : BitVec 32)
    (hop : (Sail.BitVec.extractLsb w 6 0).toNat = 51)
    (h0 : (Sail.BitVec.extractLsb w 14 12).toNat = 1)
    (h1 : (Sail.BitVec.extractLsb w 31 25).toNat = 0)
    (s : SailState) :
    ∃ ast, ext_decode w s = .ok ast s ∧ _root_.Step.Matches (.SLL (rd w) (rs1 w) (rs2 w)) ast := by
  decode32_case

private theorem agree_SLT (w : BitVec 32)
    (hop : (Sail.BitVec.extractLsb w 6 0).toNat = 51)
    (h0 : (Sail.BitVec.extractLsb w 14 12).toNat = 2)
    (h1 : (Sail.BitVec.extractLsb w 31 25).toNat = 0)
    (s : SailState) :
    ∃ ast, ext_decode w s = .ok ast s ∧ _root_.Step.Matches (.SLT (rd w) (rs1 w) (rs2 w)) ast := by
  decode32_case

private theorem agree_SLTU (w : BitVec 32)
    (hop : (Sail.BitVec.extractLsb w 6 0).toNat = 51)
    (h0 : (Sail.BitVec.extractLsb w 14 12).toNat = 3)
    (h1 : (Sail.BitVec.extractLsb w 31 25).toNat = 0)
    (s : SailState) :
    ∃ ast, ext_decode w s = .ok ast s ∧ _root_.Step.Matches (.SLTU (rd w) (rs1 w) (rs2 w)) ast := by
  decode32_case

private theorem agree_XOR (w : BitVec 32)
    (hop : (Sail.BitVec.extractLsb w 6 0).toNat = 51)
    (h0 : (Sail.BitVec.extractLsb w 14 12).toNat = 4)
    (h1 : (Sail.BitVec.extractLsb w 31 25).toNat = 0)
    (s : SailState) :
    ∃ ast, ext_decode w s = .ok ast s ∧ _root_.Step.Matches (.XOR (rd w) (rs1 w) (rs2 w)) ast := by
  decode32_case

private theorem agree_SRL (w : BitVec 32)
    (hop : (Sail.BitVec.extractLsb w 6 0).toNat = 51)
    (h0 : (Sail.BitVec.extractLsb w 14 12).toNat = 5)
    (h1 : (Sail.BitVec.extractLsb w 31 25).toNat = 0)
    (s : SailState) :
    ∃ ast, ext_decode w s = .ok ast s ∧ _root_.Step.Matches (.SRL (rd w) (rs1 w) (rs2 w)) ast := by
  decode32_case

private theorem agree_SRA (w : BitVec 32)
    (hop : (Sail.BitVec.extractLsb w 6 0).toNat = 51)
    (h0 : (Sail.BitVec.extractLsb w 14 12).toNat = 5)
    (h1 : (Sail.BitVec.extractLsb w 31 25).toNat = 32)
    (s : SailState) :
    ∃ ast, ext_decode w s = .ok ast s ∧ _root_.Step.Matches (.SRA (rd w) (rs1 w) (rs2 w)) ast := by
  decode32_case

private theorem agree_OR (w : BitVec 32)
    (hop : (Sail.BitVec.extractLsb w 6 0).toNat = 51)
    (h0 : (Sail.BitVec.extractLsb w 14 12).toNat = 6)
    (h1 : (Sail.BitVec.extractLsb w 31 25).toNat = 0)
    (s : SailState) :
    ∃ ast, ext_decode w s = .ok ast s ∧ _root_.Step.Matches (.OR (rd w) (rs1 w) (rs2 w)) ast := by
  decode32_case

private theorem agree_AND (w : BitVec 32)
    (hop : (Sail.BitVec.extractLsb w 6 0).toNat = 51)
    (h0 : (Sail.BitVec.extractLsb w 14 12).toNat = 7)
    (h1 : (Sail.BitVec.extractLsb w 31 25).toNat = 0)
    (s : SailState) :
    ∃ ast, ext_decode w s = .ok ast s ∧ _root_.Step.Matches (.AND (rd w) (rs1 w) (rs2 w)) ast := by
  decode32_case

private theorem agree_MUL (w : BitVec 32)
    (hop : (Sail.BitVec.extractLsb w 6 0).toNat = 51)
    (h0 : (Sail.BitVec.extractLsb w 14 12).toNat = 0)
    (h1 : (Sail.BitVec.extractLsb w 31 25).toNat = 1)
    (s : SailState)
    (hreset : s.regs.get? Register.misa = some resetMisa) :
    ∃ ast, ext_decode w s = .ok ast s ∧ _root_.Step.Matches (.MUL (rd w) (rs1 w) (rs2 w)) ast := by
  decode32_case

private theorem agree_MULH (w : BitVec 32)
    (hop : (Sail.BitVec.extractLsb w 6 0).toNat = 51)
    (h0 : (Sail.BitVec.extractLsb w 14 12).toNat = 1)
    (h1 : (Sail.BitVec.extractLsb w 31 25).toNat = 1)
    (s : SailState)
    (hreset : s.regs.get? Register.misa = some resetMisa) :
    ∃ ast, ext_decode w s = .ok ast s ∧ _root_.Step.Matches (.MULH (rd w) (rs1 w) (rs2 w)) ast := by
  decode32_case

private theorem agree_MULHSU (w : BitVec 32)
    (hop : (Sail.BitVec.extractLsb w 6 0).toNat = 51)
    (h0 : (Sail.BitVec.extractLsb w 14 12).toNat = 2)
    (h1 : (Sail.BitVec.extractLsb w 31 25).toNat = 1)
    (s : SailState)
    (hreset : s.regs.get? Register.misa = some resetMisa) :
    ∃ ast, ext_decode w s = .ok ast s ∧ _root_.Step.Matches (.MULHSU (rd w) (rs1 w) (rs2 w)) ast := by
  decode32_case

private theorem agree_MULHU (w : BitVec 32)
    (hop : (Sail.BitVec.extractLsb w 6 0).toNat = 51)
    (h0 : (Sail.BitVec.extractLsb w 14 12).toNat = 3)
    (h1 : (Sail.BitVec.extractLsb w 31 25).toNat = 1)
    (s : SailState)
    (hreset : s.regs.get? Register.misa = some resetMisa) :
    ∃ ast, ext_decode w s = .ok ast s ∧ _root_.Step.Matches (.MULHU (rd w) (rs1 w) (rs2 w)) ast := by
  decode32_case

private theorem agree_DIV (w : BitVec 32)
    (advice : BitVec 64)
    (hop : (Sail.BitVec.extractLsb w 6 0).toNat = 51)
    (h0 : (Sail.BitVec.extractLsb w 14 12).toNat = 4)
    (h1 : (Sail.BitVec.extractLsb w 31 25).toNat = 1)
    (s : SailState)
    (hreset : s.regs.get? Register.misa = some resetMisa) :
    ∃ ast, ext_decode w s = .ok ast s ∧ _root_.Step.Matches (.DIV (rd w) (rs1 w) (rs2 w) advice) ast := by
  decode32_case

private theorem agree_DIVU (w : BitVec 32)
    (advice : BitVec 64)
    (hop : (Sail.BitVec.extractLsb w 6 0).toNat = 51)
    (h0 : (Sail.BitVec.extractLsb w 14 12).toNat = 5)
    (h1 : (Sail.BitVec.extractLsb w 31 25).toNat = 1)
    (s : SailState)
    (hreset : s.regs.get? Register.misa = some resetMisa) :
    ∃ ast, ext_decode w s = .ok ast s ∧ _root_.Step.Matches (.DIVU (rd w) (rs1 w) (rs2 w) advice) ast := by
  decode32_case

private theorem agree_REM (w : BitVec 32)
    (advice : BitVec 64)
    (hop : (Sail.BitVec.extractLsb w 6 0).toNat = 51)
    (h0 : (Sail.BitVec.extractLsb w 14 12).toNat = 6)
    (h1 : (Sail.BitVec.extractLsb w 31 25).toNat = 1)
    (s : SailState)
    (hreset : s.regs.get? Register.misa = some resetMisa) :
    ∃ ast, ext_decode w s = .ok ast s ∧ _root_.Step.Matches (.REM (rd w) (rs1 w) (rs2 w) advice) ast := by
  decode32_case

private theorem agree_REMU (w : BitVec 32)
    (advice : BitVec 64)
    (hop : (Sail.BitVec.extractLsb w 6 0).toNat = 51)
    (h0 : (Sail.BitVec.extractLsb w 14 12).toNat = 7)
    (h1 : (Sail.BitVec.extractLsb w 31 25).toNat = 1)
    (s : SailState)
    (hreset : s.regs.get? Register.misa = some resetMisa) :
    ∃ ast, ext_decode w s = .ok ast s ∧ _root_.Step.Matches (.REMU (rd w) (rs1 w) (rs2 w) advice) ast := by
  decode32_case

private theorem agree_ADDW (w : BitVec 32)
    (hop : (Sail.BitVec.extractLsb w 6 0).toNat = 59)
    (h0 : (Sail.BitVec.extractLsb w 14 12).toNat = 0)
    (h1 : (Sail.BitVec.extractLsb w 31 25).toNat = 0)
    (s : SailState) :
    ∃ ast, ext_decode w s = .ok ast s ∧ _root_.Step.Matches (.ADDW (rd w) (rs1 w) (rs2 w)) ast := by
  decode32_case

private theorem agree_SUBW (w : BitVec 32)
    (hop : (Sail.BitVec.extractLsb w 6 0).toNat = 59)
    (h0 : (Sail.BitVec.extractLsb w 14 12).toNat = 0)
    (h1 : (Sail.BitVec.extractLsb w 31 25).toNat = 32)
    (s : SailState) :
    ∃ ast, ext_decode w s = .ok ast s ∧ _root_.Step.Matches (.SUBW (rd w) (rs1 w) (rs2 w)) ast := by
  decode32_case

private theorem agree_SLLW (w : BitVec 32)
    (hop : (Sail.BitVec.extractLsb w 6 0).toNat = 59)
    (h0 : (Sail.BitVec.extractLsb w 14 12).toNat = 1)
    (h1 : (Sail.BitVec.extractLsb w 31 25).toNat = 0)
    (s : SailState) :
    ∃ ast, ext_decode w s = .ok ast s ∧ _root_.Step.Matches (.SLLW (rd w) (rs1 w) (rs2 w)) ast := by
  decode32_case

private theorem agree_SRLW (w : BitVec 32)
    (hop : (Sail.BitVec.extractLsb w 6 0).toNat = 59)
    (h0 : (Sail.BitVec.extractLsb w 14 12).toNat = 5)
    (h1 : (Sail.BitVec.extractLsb w 31 25).toNat = 0)
    (s : SailState) :
    ∃ ast, ext_decode w s = .ok ast s ∧ _root_.Step.Matches (.SRLW (rd w) (rs1 w) (rs2 w)) ast := by
  decode32_case

private theorem agree_SRAW (w : BitVec 32)
    (hop : (Sail.BitVec.extractLsb w 6 0).toNat = 59)
    (h0 : (Sail.BitVec.extractLsb w 14 12).toNat = 5)
    (h1 : (Sail.BitVec.extractLsb w 31 25).toNat = 32)
    (s : SailState) :
    ∃ ast, ext_decode w s = .ok ast s ∧ _root_.Step.Matches (.SRAW (rd w) (rs1 w) (rs2 w)) ast := by
  decode32_case

private theorem agree_MULW (w : BitVec 32)
    (hop : (Sail.BitVec.extractLsb w 6 0).toNat = 59)
    (h0 : (Sail.BitVec.extractLsb w 14 12).toNat = 0)
    (h1 : (Sail.BitVec.extractLsb w 31 25).toNat = 1)
    (s : SailState)
    (hreset : s.regs.get? Register.misa = some resetMisa) :
    ∃ ast, ext_decode w s = .ok ast s ∧ _root_.Step.Matches (.MULW (rd w) (rs1 w) (rs2 w)) ast := by
  decode32_case

private theorem agree_DIVW (w : BitVec 32)
    (advice : BitVec 64)
    (hop : (Sail.BitVec.extractLsb w 6 0).toNat = 59)
    (h0 : (Sail.BitVec.extractLsb w 14 12).toNat = 4)
    (h1 : (Sail.BitVec.extractLsb w 31 25).toNat = 1)
    (s : SailState)
    (hreset : s.regs.get? Register.misa = some resetMisa) :
    ∃ ast, ext_decode w s = .ok ast s ∧ _root_.Step.Matches (.DIVW (rd w) (rs1 w) (rs2 w) advice) ast := by
  decode32_case

private theorem agree_DIVUW (w : BitVec 32)
    (advice : BitVec 64)
    (hop : (Sail.BitVec.extractLsb w 6 0).toNat = 59)
    (h0 : (Sail.BitVec.extractLsb w 14 12).toNat = 5)
    (h1 : (Sail.BitVec.extractLsb w 31 25).toNat = 1)
    (s : SailState)
    (hreset : s.regs.get? Register.misa = some resetMisa) :
    ∃ ast, ext_decode w s = .ok ast s ∧ _root_.Step.Matches (.DIVUW (rd w) (rs1 w) (rs2 w) advice) ast := by
  decode32_case

private theorem agree_REMW (w : BitVec 32)
    (advice : BitVec 64)
    (hop : (Sail.BitVec.extractLsb w 6 0).toNat = 59)
    (h0 : (Sail.BitVec.extractLsb w 14 12).toNat = 6)
    (h1 : (Sail.BitVec.extractLsb w 31 25).toNat = 1)
    (s : SailState)
    (hreset : s.regs.get? Register.misa = some resetMisa) :
    ∃ ast, ext_decode w s = .ok ast s ∧ _root_.Step.Matches (.REMW (rd w) (rs1 w) (rs2 w) advice) ast := by
  decode32_case

private theorem agree_REMUW (w : BitVec 32)
    (advice : BitVec 64)
    (hop : (Sail.BitVec.extractLsb w 6 0).toNat = 59)
    (h0 : (Sail.BitVec.extractLsb w 14 12).toNat = 7)
    (h1 : (Sail.BitVec.extractLsb w 31 25).toNat = 1)
    (s : SailState)
    (hreset : s.regs.get? Register.misa = some resetMisa) :
    ∃ ast, ext_decode w s = .ok ast s ∧ _root_.Step.Matches (.REMUW (rd w) (rs1 w) (rs2 w) advice) ast := by
  decode32_case

private theorem agree_FENCE (w : BitVec 32)
    (hop : (Sail.BitVec.extractLsb w 6 0).toNat = 15)
    (h0 : (Sail.BitVec.extractLsb w 14 12).toNat = 0)
    (s : SailState) :
    ∃ ast, ext_decode w s = .ok ast s ∧ _root_.Step.Matches (.FENCE) ast := by
  by_cases htso : w = 0x8330000f
  · subst w
    decode32_case
  · have hnotso : (w == (0x8330000f#32)) = false :=
      beq_eq_false_iff_ne.mpr htso
    clear htso
    decode32_case

private theorem agree_LR_W (w : BitVec 32)
    (hop : (Sail.BitVec.extractLsb w 6 0).toNat = 47)
    (h0 : (Sail.BitVec.extractLsb w 14 12).toNat = 2)
    (h1 : (Sail.BitVec.extractLsb w 31 27).toNat = 2)
    (h2 : Sail.BitVec.extractLsb w 24 20 = 0)
    (s : SailState)
    (hreset : s.regs.get? Register.misa = some resetMisa) :
    ∃ ast, ext_decode w s = .ok ast s ∧ _root_.Step.Matches (.LR_W (rd w) (rs1 w) (w.getLsbD 26) (w.getLsbD 25)) ast := by
  decode32_case

private theorem agree_LR_D (w : BitVec 32)
    (hop : (Sail.BitVec.extractLsb w 6 0).toNat = 47)
    (h0 : (Sail.BitVec.extractLsb w 14 12).toNat = 3)
    (h1 : (Sail.BitVec.extractLsb w 31 27).toNat = 2)
    (h2 : Sail.BitVec.extractLsb w 24 20 = 0)
    (s : SailState)
    (hreset : s.regs.get? Register.misa = some resetMisa) :
    ∃ ast, ext_decode w s = .ok ast s ∧ _root_.Step.Matches (.LR_D (rd w) (rs1 w) (w.getLsbD 26) (w.getLsbD 25)) ast := by
  decode32_case

private theorem agree_SC_W (w : BitVec 32)
    (hop : (Sail.BitVec.extractLsb w 6 0).toNat = 47)
    (h0 : (Sail.BitVec.extractLsb w 14 12).toNat = 2)
    (h1 : (Sail.BitVec.extractLsb w 31 27).toNat = 3)
    (s : SailState)
    (hreset : s.regs.get? Register.misa = some resetMisa) :
    ∃ ast, ext_decode w s = .ok ast s ∧ _root_.Step.Matches (.SC_W (rd w) (rs1 w) (rs2 w) (w.getLsbD 26) (w.getLsbD 25)) ast := by
  decode32_case

private theorem agree_SC_D (w : BitVec 32)
    (hop : (Sail.BitVec.extractLsb w 6 0).toNat = 47)
    (h0 : (Sail.BitVec.extractLsb w 14 12).toNat = 3)
    (h1 : (Sail.BitVec.extractLsb w 31 27).toNat = 3)
    (s : SailState)
    (hreset : s.regs.get? Register.misa = some resetMisa) :
    ∃ ast, ext_decode w s = .ok ast s ∧ _root_.Step.Matches (.SC_D (rd w) (rs1 w) (rs2 w) (w.getLsbD 26) (w.getLsbD 25)) ast := by
  decode32_case

private theorem agree_AMOSWAP_W (w : BitVec 32)
    (hop : (Sail.BitVec.extractLsb w 6 0).toNat = 47)
    (h0 : (Sail.BitVec.extractLsb w 14 12).toNat = 2)
    (h1 : (Sail.BitVec.extractLsb w 31 27).toNat = 1)
    (s : SailState)
    (hreset : s.regs.get? Register.misa = some resetMisa) :
    ∃ ast, ext_decode w s = .ok ast s ∧ _root_.Step.Matches (.AMOSWAP_W (rd w) (rs1 w) (rs2 w) (w.getLsbD 26) (w.getLsbD 25)) ast := by
  decode32_case

private theorem agree_AMOSWAP_D (w : BitVec 32)
    (hop : (Sail.BitVec.extractLsb w 6 0).toNat = 47)
    (h0 : (Sail.BitVec.extractLsb w 14 12).toNat = 3)
    (h1 : (Sail.BitVec.extractLsb w 31 27).toNat = 1)
    (s : SailState)
    (hreset : s.regs.get? Register.misa = some resetMisa) :
    ∃ ast, ext_decode w s = .ok ast s ∧ _root_.Step.Matches (.AMOSWAP_D (rd w) (rs1 w) (rs2 w) (w.getLsbD 26) (w.getLsbD 25)) ast := by
  decode32_case

private theorem agree_AMOADD_W (w : BitVec 32)
    (hop : (Sail.BitVec.extractLsb w 6 0).toNat = 47)
    (h0 : (Sail.BitVec.extractLsb w 14 12).toNat = 2)
    (h1 : (Sail.BitVec.extractLsb w 31 27).toNat = 0)
    (s : SailState)
    (hreset : s.regs.get? Register.misa = some resetMisa) :
    ∃ ast, ext_decode w s = .ok ast s ∧ _root_.Step.Matches (.AMOADD_W (rd w) (rs1 w) (rs2 w) (w.getLsbD 26) (w.getLsbD 25)) ast := by
  decode32_case

private theorem agree_AMOADD_D (w : BitVec 32)
    (hop : (Sail.BitVec.extractLsb w 6 0).toNat = 47)
    (h0 : (Sail.BitVec.extractLsb w 14 12).toNat = 3)
    (h1 : (Sail.BitVec.extractLsb w 31 27).toNat = 0)
    (s : SailState)
    (hreset : s.regs.get? Register.misa = some resetMisa) :
    ∃ ast, ext_decode w s = .ok ast s ∧ _root_.Step.Matches (.AMOADD_D (rd w) (rs1 w) (rs2 w) (w.getLsbD 26) (w.getLsbD 25)) ast := by
  decode32_case

private theorem agree_AMOAND_W (w : BitVec 32)
    (hop : (Sail.BitVec.extractLsb w 6 0).toNat = 47)
    (h0 : (Sail.BitVec.extractLsb w 14 12).toNat = 2)
    (h1 : (Sail.BitVec.extractLsb w 31 27).toNat = 12)
    (s : SailState)
    (hreset : s.regs.get? Register.misa = some resetMisa) :
    ∃ ast, ext_decode w s = .ok ast s ∧ _root_.Step.Matches (.AMOAND_W (rd w) (rs1 w) (rs2 w) (w.getLsbD 26) (w.getLsbD 25)) ast := by
  decode32_case

private theorem agree_AMOAND_D (w : BitVec 32)
    (hop : (Sail.BitVec.extractLsb w 6 0).toNat = 47)
    (h0 : (Sail.BitVec.extractLsb w 14 12).toNat = 3)
    (h1 : (Sail.BitVec.extractLsb w 31 27).toNat = 12)
    (s : SailState)
    (hreset : s.regs.get? Register.misa = some resetMisa) :
    ∃ ast, ext_decode w s = .ok ast s ∧ _root_.Step.Matches (.AMOAND_D (rd w) (rs1 w) (rs2 w) (w.getLsbD 26) (w.getLsbD 25)) ast := by
  decode32_case

private theorem agree_AMOOR_W (w : BitVec 32)
    (hop : (Sail.BitVec.extractLsb w 6 0).toNat = 47)
    (h0 : (Sail.BitVec.extractLsb w 14 12).toNat = 2)
    (h1 : (Sail.BitVec.extractLsb w 31 27).toNat = 8)
    (s : SailState)
    (hreset : s.regs.get? Register.misa = some resetMisa) :
    ∃ ast, ext_decode w s = .ok ast s ∧ _root_.Step.Matches (.AMOOR_W (rd w) (rs1 w) (rs2 w) (w.getLsbD 26) (w.getLsbD 25)) ast := by
  decode32_case

private theorem agree_AMOOR_D (w : BitVec 32)
    (hop : (Sail.BitVec.extractLsb w 6 0).toNat = 47)
    (h0 : (Sail.BitVec.extractLsb w 14 12).toNat = 3)
    (h1 : (Sail.BitVec.extractLsb w 31 27).toNat = 8)
    (s : SailState)
    (hreset : s.regs.get? Register.misa = some resetMisa) :
    ∃ ast, ext_decode w s = .ok ast s ∧ _root_.Step.Matches (.AMOOR_D (rd w) (rs1 w) (rs2 w) (w.getLsbD 26) (w.getLsbD 25)) ast := by
  decode32_case

private theorem agree_AMOXOR_W (w : BitVec 32)
    (hop : (Sail.BitVec.extractLsb w 6 0).toNat = 47)
    (h0 : (Sail.BitVec.extractLsb w 14 12).toNat = 2)
    (h1 : (Sail.BitVec.extractLsb w 31 27).toNat = 4)
    (s : SailState)
    (hreset : s.regs.get? Register.misa = some resetMisa) :
    ∃ ast, ext_decode w s = .ok ast s ∧ _root_.Step.Matches (.AMOXOR_W (rd w) (rs1 w) (rs2 w) (w.getLsbD 26) (w.getLsbD 25)) ast := by
  decode32_case

private theorem agree_AMOXOR_D (w : BitVec 32)
    (hop : (Sail.BitVec.extractLsb w 6 0).toNat = 47)
    (h0 : (Sail.BitVec.extractLsb w 14 12).toNat = 3)
    (h1 : (Sail.BitVec.extractLsb w 31 27).toNat = 4)
    (s : SailState)
    (hreset : s.regs.get? Register.misa = some resetMisa) :
    ∃ ast, ext_decode w s = .ok ast s ∧ _root_.Step.Matches (.AMOXOR_D (rd w) (rs1 w) (rs2 w) (w.getLsbD 26) (w.getLsbD 25)) ast := by
  decode32_case

private theorem agree_AMOMIN_W (w : BitVec 32)
    (hop : (Sail.BitVec.extractLsb w 6 0).toNat = 47)
    (h0 : (Sail.BitVec.extractLsb w 14 12).toNat = 2)
    (h1 : (Sail.BitVec.extractLsb w 31 27).toNat = 16)
    (s : SailState)
    (hreset : s.regs.get? Register.misa = some resetMisa) :
    ∃ ast, ext_decode w s = .ok ast s ∧ _root_.Step.Matches (.AMOMIN_W (rd w) (rs1 w) (rs2 w) (w.getLsbD 26) (w.getLsbD 25)) ast := by
  decode32_case

private theorem agree_AMOMIN_D (w : BitVec 32)
    (hop : (Sail.BitVec.extractLsb w 6 0).toNat = 47)
    (h0 : (Sail.BitVec.extractLsb w 14 12).toNat = 3)
    (h1 : (Sail.BitVec.extractLsb w 31 27).toNat = 16)
    (s : SailState)
    (hreset : s.regs.get? Register.misa = some resetMisa) :
    ∃ ast, ext_decode w s = .ok ast s ∧ _root_.Step.Matches (.AMOMIN_D (rd w) (rs1 w) (rs2 w) (w.getLsbD 26) (w.getLsbD 25)) ast := by
  decode32_case

private theorem agree_AMOMAX_W (w : BitVec 32)
    (hop : (Sail.BitVec.extractLsb w 6 0).toNat = 47)
    (h0 : (Sail.BitVec.extractLsb w 14 12).toNat = 2)
    (h1 : (Sail.BitVec.extractLsb w 31 27).toNat = 20)
    (s : SailState)
    (hreset : s.regs.get? Register.misa = some resetMisa) :
    ∃ ast, ext_decode w s = .ok ast s ∧ _root_.Step.Matches (.AMOMAX_W (rd w) (rs1 w) (rs2 w) (w.getLsbD 26) (w.getLsbD 25)) ast := by
  decode32_case

private theorem agree_AMOMAX_D (w : BitVec 32)
    (hop : (Sail.BitVec.extractLsb w 6 0).toNat = 47)
    (h0 : (Sail.BitVec.extractLsb w 14 12).toNat = 3)
    (h1 : (Sail.BitVec.extractLsb w 31 27).toNat = 20)
    (s : SailState)
    (hreset : s.regs.get? Register.misa = some resetMisa) :
    ∃ ast, ext_decode w s = .ok ast s ∧ _root_.Step.Matches (.AMOMAX_D (rd w) (rs1 w) (rs2 w) (w.getLsbD 26) (w.getLsbD 25)) ast := by
  decode32_case

private theorem agree_AMOMINU_W (w : BitVec 32)
    (hop : (Sail.BitVec.extractLsb w 6 0).toNat = 47)
    (h0 : (Sail.BitVec.extractLsb w 14 12).toNat = 2)
    (h1 : (Sail.BitVec.extractLsb w 31 27).toNat = 24)
    (s : SailState)
    (hreset : s.regs.get? Register.misa = some resetMisa) :
    ∃ ast, ext_decode w s = .ok ast s ∧ _root_.Step.Matches (.AMOMINU_W (rd w) (rs1 w) (rs2 w) (w.getLsbD 26) (w.getLsbD 25)) ast := by
  decode32_case

private theorem agree_AMOMINU_D (w : BitVec 32)
    (hop : (Sail.BitVec.extractLsb w 6 0).toNat = 47)
    (h0 : (Sail.BitVec.extractLsb w 14 12).toNat = 3)
    (h1 : (Sail.BitVec.extractLsb w 31 27).toNat = 24)
    (s : SailState)
    (hreset : s.regs.get? Register.misa = some resetMisa) :
    ∃ ast, ext_decode w s = .ok ast s ∧ _root_.Step.Matches (.AMOMINU_D (rd w) (rs1 w) (rs2 w) (w.getLsbD 26) (w.getLsbD 25)) ast := by
  decode32_case

private theorem agree_AMOMAXU_W (w : BitVec 32)
    (hop : (Sail.BitVec.extractLsb w 6 0).toNat = 47)
    (h0 : (Sail.BitVec.extractLsb w 14 12).toNat = 2)
    (h1 : (Sail.BitVec.extractLsb w 31 27).toNat = 28)
    (s : SailState)
    (hreset : s.regs.get? Register.misa = some resetMisa) :
    ∃ ast, ext_decode w s = .ok ast s ∧ _root_.Step.Matches (.AMOMAXU_W (rd w) (rs1 w) (rs2 w) (w.getLsbD 26) (w.getLsbD 25)) ast := by
  decode32_case

private theorem agree_AMOMAXU_D (w : BitVec 32)
    (hop : (Sail.BitVec.extractLsb w 6 0).toNat = 47)
    (h0 : (Sail.BitVec.extractLsb w 14 12).toNat = 3)
    (h1 : (Sail.BitVec.extractLsb w 31 27).toNat = 28)
    (s : SailState)
    (hreset : s.regs.get? Register.misa = some resetMisa) :
    ∃ ast, ext_decode w s = .ok ast s ∧ _root_.Step.Matches (.AMOMAXU_D (rd w) (rs1 w) (rs2 w) (w.getLsbD 26) (w.getLsbD 25)) ast := by
  decode32_case

private theorem agree_ECALL (w : BitVec 32)
    (hword : w = 115#32)
    (s : SailState) :
    ∃ ast, ext_decode w s = .ok ast s ∧ _root_.Step.Matches (.ECALL) ast := by
  decode32_case

private theorem agree_EBREAK (w : BitVec 32)
    (hword : w = 1048691#32)
    (s : SailState) :
    ∃ ast, ext_decode w s = .ok ast s ∧ _root_.Step.Matches (.EBREAK) ast := by
  decode32_case

private theorem agree_MRET (w : BitVec 32)
    (hword : w = 807403635#32)
    (s : SailState) :
    ∃ ast, ext_decode w s = .ok ast s ∧ _root_.Step.Matches (.MRET) ast := by
  decode32_case

private theorem csr_address (w : BitVec 32) (c : JoltISA.SystemCSR)
    (hc : csr w = some c) : immI w = c.address := by
  unfold csr at hc
  split at hc <;> simp_all only [Option.some.injEq, reduceCtorEq]
  all_goals subst c
  all_goals apply BitVec.eq_of_toNat_eq
  all_goals assumption

private theorem agree_CSRRW (w : BitVec 32) (c : JoltISA.SystemCSR)
    (hop : (Sail.BitVec.extractLsb w 6 0).toNat = 115)
    (h0 : (Sail.BitVec.extractLsb w 14 12).toNat = 1)
    (hc : csr w = some c) (s : SailState) :
    ∃ ast, ext_decode w s = .ok ast s ∧
      _root_.Step.Matches (.CSRRW (rd w) c (rs1 w)) ast := by
  have haddr : w.extractLsb 31 20 = c.address := csr_address w c hc
  decode32_case

private theorem agree_CSRRS (w : BitVec 32) (c : JoltISA.SystemCSR)
    (hop : (Sail.BitVec.extractLsb w 6 0).toNat = 115)
    (h0 : (Sail.BitVec.extractLsb w 14 12).toNat = 2)
    (hc : csr w = some c) (s : SailState) :
    ∃ ast, ext_decode w s = .ok ast s ∧
      _root_.Step.Matches (.CSRRS (rd w) c (rs1 w)) ast := by
  have haddr : w.extractLsb 31 20 = c.address := csr_address w c hc
  decode32_case

private theorem agree_CSRRC (w : BitVec 32) (c : JoltISA.SystemCSR)
    (hop : (Sail.BitVec.extractLsb w 6 0).toNat = 115)
    (h0 : (Sail.BitVec.extractLsb w 14 12).toNat = 3)
    (hc : csr w = some c) (s : SailState) :
    ∃ ast, ext_decode w s = .ok ast s ∧
      _root_.Step.Matches (.CSRRC (rd w) c (rs1 w)) ast := by
  have haddr : w.extractLsb 31 20 = c.address := csr_address w c hc
  decode32_case

private theorem agree_CSRRWI (w : BitVec 32) (c : JoltISA.SystemCSR)
    (hop : (Sail.BitVec.extractLsb w 6 0).toNat = 115)
    (h0 : (Sail.BitVec.extractLsb w 14 12).toNat = 5)
    (hc : csr w = some c) (s : SailState) :
    ∃ ast, ext_decode w s = .ok ast s ∧
      _root_.Step.Matches (.CSRRWI (rd w) c (w.extractLsb 19 15)) ast := by
  have haddr : w.extractLsb 31 20 = c.address := csr_address w c hc
  decode32_case

private theorem agree_CSRRSI (w : BitVec 32) (c : JoltISA.SystemCSR)
    (hop : (Sail.BitVec.extractLsb w 6 0).toNat = 115)
    (h0 : (Sail.BitVec.extractLsb w 14 12).toNat = 6)
    (hc : csr w = some c) (s : SailState) :
    ∃ ast, ext_decode w s = .ok ast s ∧
      _root_.Step.Matches (.CSRRSI (rd w) c (w.extractLsb 19 15)) ast := by
  have haddr : w.extractLsb 31 20 = c.address := csr_address w c hc
  decode32_case

private theorem agree_CSRRCI (w : BitVec 32) (c : JoltISA.SystemCSR)
    (hop : (Sail.BitVec.extractLsb w 6 0).toNat = 115)
    (h0 : (Sail.BitVec.extractLsb w 14 12).toNat = 7)
    (hc : csr w = some c) (s : SailState) :
    ∃ ast, ext_decode w s = .ok ast s ∧
      _root_.Step.Matches (.CSRRCI (rd w) c (w.extractLsb 19 15)) ast := by
  have haddr : w.extractLsb 31 20 = c.address := csr_address w c hc
  decode32_case

open Lean Meta Elab Tactic in
private partial def finishDecoded : TacticM Unit := withMainContext do
  let g ← getMainGoal
  let t ← g.getType
  let body := t.getAppArgs[1]!.bindingBody!
  let matched := body.getAppArgs[1]!
  let i := matched.getAppArgs[0]!
  let key := i.getAppFn.constName!.getString!
  let cases : Array (String × Name) := #[
    ("LUI", ``agree_LUI),
    ("AUIPC", ``agree_AUIPC),
    ("JAL", ``agree_JAL),
    ("JALR", ``agree_JALR),
    ("BEQ", ``agree_BEQ),
    ("BNE", ``agree_BNE),
    ("BLT", ``agree_BLT),
    ("BGE", ``agree_BGE),
    ("BLTU", ``agree_BLTU),
    ("BGEU", ``agree_BGEU),
    ("LB", ``agree_LB),
    ("LH", ``agree_LH),
    ("LW", ``agree_LW),
    ("LD", ``agree_LD),
    ("LBU", ``agree_LBU),
    ("LHU", ``agree_LHU),
    ("LWU", ``agree_LWU),
    ("SB", ``agree_SB),
    ("SH", ``agree_SH),
    ("SW", ``agree_SW),
    ("SD", ``agree_SD),
    ("ADDI", ``agree_ADDI),
    ("SLTI", ``agree_SLTI),
    ("SLTIU", ``agree_SLTIU),
    ("XORI", ``agree_XORI),
    ("ORI", ``agree_ORI),
    ("ANDI", ``agree_ANDI),
    ("SLLI", ``agree_SLLI),
    ("SRLI", ``agree_SRLI),
    ("SRAI", ``agree_SRAI),
    ("ADDIW", ``agree_ADDIW),
    ("SLLIW", ``agree_SLLIW),
    ("SRLIW", ``agree_SRLIW),
    ("SRAIW", ``agree_SRAIW),
    ("ADD", ``agree_ADD),
    ("SUB", ``agree_SUB),
    ("SLL", ``agree_SLL),
    ("SLT", ``agree_SLT),
    ("SLTU", ``agree_SLTU),
    ("XOR", ``agree_XOR),
    ("SRL", ``agree_SRL),
    ("SRA", ``agree_SRA),
    ("OR", ``agree_OR),
    ("AND", ``agree_AND),
    ("MUL", ``agree_MUL),
    ("MULH", ``agree_MULH),
    ("MULHSU", ``agree_MULHSU),
    ("MULHU", ``agree_MULHU),
    ("DIV", ``agree_DIV),
    ("DIVU", ``agree_DIVU),
    ("REM", ``agree_REM),
    ("REMU", ``agree_REMU),
    ("ADDW", ``agree_ADDW),
    ("SUBW", ``agree_SUBW),
    ("SLLW", ``agree_SLLW),
    ("SRLW", ``agree_SRLW),
    ("SRAW", ``agree_SRAW),
    ("MULW", ``agree_MULW),
    ("DIVW", ``agree_DIVW),
    ("DIVUW", ``agree_DIVUW),
    ("REMW", ``agree_REMW),
    ("REMUW", ``agree_REMUW),
    ("FENCE", ``agree_FENCE),
    ("LR_W", ``agree_LR_W),
    ("LR_D", ``agree_LR_D),
    ("SC_W", ``agree_SC_W),
    ("SC_D", ``agree_SC_D),
    ("AMOSWAP_W", ``agree_AMOSWAP_W),
    ("AMOSWAP_D", ``agree_AMOSWAP_D),
    ("AMOADD_W", ``agree_AMOADD_W),
    ("AMOADD_D", ``agree_AMOADD_D),
    ("AMOAND_W", ``agree_AMOAND_W),
    ("AMOAND_D", ``agree_AMOAND_D),
    ("AMOOR_W", ``agree_AMOOR_W),
    ("AMOOR_D", ``agree_AMOOR_D),
    ("AMOXOR_W", ``agree_AMOXOR_W),
    ("AMOXOR_D", ``agree_AMOXOR_D),
    ("AMOMIN_W", ``agree_AMOMIN_W),
    ("AMOMIN_D", ``agree_AMOMIN_D),
    ("AMOMAX_W", ``agree_AMOMAX_W),
    ("AMOMAX_D", ``agree_AMOMAX_D),
    ("AMOMINU_W", ``agree_AMOMINU_W),
    ("AMOMINU_D", ``agree_AMOMINU_D),
    ("AMOMAXU_W", ``agree_AMOMAXU_W),
    ("AMOMAXU_D", ``agree_AMOMAXU_D),
    ("ECALL", ``agree_ECALL),
    ("EBREAK", ``agree_EBREAK),
    ("MRET", ``agree_MRET),
    ("CSRRW", ``agree_CSRRW),
    ("CSRRS", ``agree_CSRRS),
    ("CSRRC", ``agree_CSRRC),
    ("CSRRWI", ``agree_CSRRWI),
    ("CSRRSI", ``agree_CSRRSI),
    ("CSRRCI", ``agree_CSRRCI) ]
  let some (_, name) := cases.find? (fun p => p.1 == key)
    | throwError "unknown accepted instruction {key}"
  evalTactic (← `(tactic| apply $(mkIdent name)))
  evalTactic (← `(tactic| all_goals first | assumption | rfl))

open Lean Elab Tactic in
elab "finish_decoded" : tactic => finishDecoded

/-- Every standard word accepted by Jolt at `b65455e6d` has a Sail AST representing
that instruction. For example, ADDI x1,x0,1 decodes to Sail ITYPE ADDI.
The immutable misa register has Jolt's RV64IMAC reset value, enabling M and A. -/
theorem joltDecode_agrees (w : BitVec 32) (advice : BitVec 64) (i : RiscvInstruction)
    (hi : joltDecode w advice = some i) (s : SailState) (hinv : _root_.Step.StepInvariant s)
    (hreset : s.regs.get? Register.misa = some resetMisa) :
    ∃ ast, ext_decode w s = .ok ast s ∧ _root_.Step.Matches i ast := by
  unfold joltDecode at hi
  dsimp only at hi
  simp only [Option.map] at hi
  repeat' first
    | split at hi
    | simp only [Option.some.injEq, reduceCtorEq] at hi
  all_goals subst i
  all_goals finish_decoded

end Decode
