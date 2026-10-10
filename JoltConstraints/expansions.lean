/-
Each source instruction's final Jolt rows, as Rust's `expand_instruction` produces
them. Natives (everything Rust's `is_source_only` leaves out) are one row through
`rewriteNative`. Source-only instructions use the bytecode project's programs.
-/
import JoltConstraints.expansion_helpers

set_option autoImplicit false

open Sail PreSail LeanRV64D.Functions

-- The final rows for one source instruction; none where Lean has no expansion yet.
-- See : jolt/crates/jolt-program/src/expand/mod.rs:126-170 (expand_source_instruction_with_provider)
--       jolt/crates/jolt-program/src/expand/grammar.rs:388-450 (is_source_only)
def SourceInstruction.expand : SourceInstruction → Option ExpandedSource
  | .riscv instruction =>
    match instruction with
    -- RV64I
    | .LUI rd imm => some (.ofNative (.LUI (.xreg rd) (JoltISA.luiValue imm)))
    | .AUIPC rd imm => some (.ofNative (JoltISA.Encoded.AUIPC (.xreg rd) imm))
    | .JAL rd imm => some (.ofNative (JoltISA.Encoded.JAL (.xreg rd) imm))
    | .JALR rd rs1 imm => some (.ofNative (JoltISA.Encoded.JALR (.xreg rd) (.xreg rs1) imm))
    | .BEQ rs1 rs2 imm => some (.ofNative (JoltISA.Encoded.BEQ (.xreg rs1) (.xreg rs2) imm))
    | .BNE rs1 rs2 imm => some (.ofNative (JoltISA.Encoded.BNE (.xreg rs1) (.xreg rs2) imm))
    | .BLT rs1 rs2 imm => some (.ofNative (JoltISA.Encoded.BLT (.xreg rs1) (.xreg rs2) imm))
    | .BGE rs1 rs2 imm => some (.ofNative (JoltISA.Encoded.BGE (.xreg rs1) (.xreg rs2) imm))
    | .BLTU rs1 rs2 imm => some (.ofNative (JoltISA.Encoded.BLTU (.xreg rs1) (.xreg rs2) imm))
    | .BGEU rs1 rs2 imm => some (.ofNative (JoltISA.Encoded.BGEU (.xreg rs1) (.xreg rs2) imm))
    | .LB rd rs1 imm => some (.ofProgram (JoltISA.lbProgramAuto rd rs1 imm))
    | .LH rd rs1 imm => some (.ofProgram (JoltISA.lhProgramAuto rd rs1 imm))
    | .LW rd rs1 imm => some (.ofProgram (JoltISA.lwProgramAuto rd rs1 imm))
    | .LBU rd rs1 imm => some (.ofProgram (JoltISA.lbuProgramAuto rd rs1 imm))
    | .LHU rd rs1 imm => some (.ofProgram (JoltISA.lhuProgramAuto rd rs1 imm))
    | .SB rs2 rs1 imm => some (.ofProgram (JoltISA.sbProgramAuto rs1 rs2 imm))
    | .SH rs2 rs1 imm => some (.ofProgram (JoltISA.shProgramAuto rs1 rs2 imm))
    | .SW rs2 rs1 imm => some (.ofProgram (JoltISA.swProgramAuto rs1 rs2 imm))
    | .ADDI rd rs1 imm => some (.ofNative (JoltISA.Encoded.ADDI (.xreg rd) (.xreg rs1) imm))
    | .SLTI rd rs1 imm => some (.ofNative (JoltISA.Encoded.SLTI (.xreg rd) (.xreg rs1) imm))
    | .SLTIU rd rs1 imm => some (.ofNative (JoltISA.Encoded.SLTIU (.xreg rd) (.xreg rs1) imm))
    | .XORI rd rs1 imm => some (.ofNative (JoltISA.Encoded.XORI (.xreg rd) (.xreg rs1) imm))
    | .ORI rd rs1 imm => some (.ofNative (JoltISA.Encoded.ORI (.xreg rd) (.xreg rs1) imm))
    | .ANDI rd rs1 imm => some (.ofNative (JoltISA.Encoded.ANDI (.xreg rd) (.xreg rs1) imm))
    | .SLLI rd rs1 shamt => some (.ofPureProgram rd (JoltISA.slliProgramAuto rd rs1 shamt))
    | .SRLI rd rs1 shamt => some (.ofPureProgram rd (JoltISA.srliProgramAuto rd rs1 shamt))
    | .SRAI rd rs1 shamt => some (.ofPureProgram rd (JoltISA.sraiProgramAuto rd rs1 shamt))
    | .ADD rd rs1 rs2 => some (.ofNative (.ADD (.xreg rd) (.xreg rs1) (.xreg rs2)))
    | .SUB rd rs1 rs2 => some (.ofNative (.SUB (.xreg rd) (.xreg rs1) (.xreg rs2)))
    | .SLL rd rs1 rs2 => some (.ofPureProgram rd (JoltISA.sllProgramAuto rd rs1 rs2))
    | .SLT rd rs1 rs2 => some (.ofNative (.SLT (.xreg rd) (.xreg rs1) (.xreg rs2)))
    | .SLTU rd rs1 rs2 => some (.ofNative (.SLTU (.xreg rd) (.xreg rs1) (.xreg rs2)))
    | .XOR rd rs1 rs2 => some (.ofNative (.XOR (.xreg rd) (.xreg rs1) (.xreg rs2)))
    | .SRL rd rs1 rs2 => some (.ofPureProgram rd (JoltISA.srlProgramAuto rd rs1 rs2))
    | .SRA rd rs1 rs2 => some (.ofPureProgram rd (JoltISA.sraProgramAuto rd rs1 rs2))
    | .OR rd rs1 rs2 => some (.ofNative (.OR (.xreg rd) (.xreg rs1) (.xreg rs2)))
    | .AND rd rs1 rs2 => some (.ofNative (.AND (.xreg rd) (.xreg rs1) (.xreg rs2)))
    | .ANDN rd rs1 rs2 => some (.ofNative (.ANDN (.xreg rd) (.xreg rs1) (.xreg rs2)))
    | .FENCE => some (.ofNative .FENCE)
    | .ECALL => some (.ofProgram JoltISA.ecallProgram)
    | .EBREAK => some (.ofProgram JoltISA.ebreakProgram)
    -- RV64I additions
    | .LWU rd rs1 imm => some (.ofProgram (JoltISA.lwuProgramAuto rd rs1 imm))
    | .LD rd rs1 imm => some (.ofNative (JoltISA.Encoded.LD .normal (.xreg rd) (.xreg rs1) imm))
    | .SD rs2 rs1 imm => some (.ofNative (JoltISA.Encoded.SD (.xreg rs1) (.xreg rs2) imm))
    | .ADDIW rd rs1 imm => some (.ofNative (JoltISA.Encoded.ADDIW (.xreg rd) (.xreg rs1) imm))
    | .SLLIW rd rs1 shamt => some (.ofPureProgram rd (JoltISA.slliwProgramAuto rd rs1 shamt))
    | .SRLIW rd rs1 shamt => some (.ofPureProgram rd (JoltISA.srliwProgramAuto rd rs1 shamt))
    | .SRAIW rd rs1 shamt => some (.ofPureProgram rd (JoltISA.sraiwProgramAuto rd rs1 shamt))
    | .ADDW rd rs1 rs2 => some (.ofNative (.ADDW (.xreg rd) (.xreg rs1) (.xreg rs2)))
    | .SUBW rd rs1 rs2 => some (.ofNative (.SUBW (.xreg rd) (.xreg rs1) (.xreg rs2)))
    | .SLLW rd rs1 rs2 => some (.ofPureProgram rd (JoltISA.sllwProgramAuto rd rs1 rs2))
    | .SRLW rd rs1 rs2 => some (.ofPureProgram rd (JoltISA.srlwProgramAuto rd rs1 rs2))
    | .SRAW rd rs1 rs2 => some (.ofPureProgram rd (JoltISA.srawProgramAuto rd rs1 rs2))
    -- M
    | .MUL rd rs1 rs2 => some (.ofNative (.MUL (.xreg rd) (.xreg rs1) (.xreg rs2)))
    | .MULH rd rs1 rs2 => some (.ofPureProgram rd (JoltISA.mulhProgramAuto rd rs1 rs2))
    | .MULHU rd rs1 rs2 => some (.ofNative (.MULHU (.xreg rd) (.xreg rs1) (.xreg rs2)))
    | .MULHSU rd rs1 rs2 => some (.ofPureProgram rd (JoltISA.mulhsuProgramAuto rd rs1 rs2))
    | .DIV rd rs1 rs2 q => some (.ofPureProgram rd (JoltISA.divProgramAuto rd rs1 rs2 q))
    | .DIVU rd rs1 rs2 q => some (.ofPureProgram rd (JoltISA.divuProgramAuto rd rs1 rs2 q))
    | .REM rd rs1 rs2 q => some (.ofPureProgram rd (JoltISA.remProgramAuto rd rs1 rs2 q))
    | .REMU rd rs1 rs2 q => some (.ofPureProgram rd (JoltISA.remuProgramAuto rd rs1 rs2 q))
    | .MULW rd rs1 rs2 => some (.ofNative (.MULW (.xreg rd) (.xreg rs1) (.xreg rs2)))
    | .DIVW rd rs1 rs2 q => some (.ofPureProgram rd (JoltISA.divwProgramAuto rd rs1 rs2 q))
    | .DIVUW rd rs1 rs2 q => some (.ofPureProgram rd (JoltISA.divuwProgramAuto rd rs1 rs2 q))
    | .REMW rd rs1 rs2 q => some (.ofPureProgram rd (JoltISA.remwProgramAuto rd rs1 rs2 q))
    | .REMUW rd rs1 rs2 q => some (.ofPureProgram rd (JoltISA.remuwProgramAuto rd rs1 rs2 q))
    -- A
    -- The generated LR programs take an rs2 they do not use.
    | .LR_W rd rs1 _ _ => some (.ofProgram (JoltISA.lrwProgramAuto rd rs1 (regidx.Regidx 0)))
    -- PR #2039 computes SC success from reservation registers, without advice.
    | .SC_W rd rs1 rs2 _ _ => some (.ofProgram (JoltISA.scwProgramAuto rd rs1 rs2))
    | .AMOSWAP_W rd rs1 rs2 _ _ => some (.ofProgram (JoltISA.amoswapwProgramAuto rd rs1 rs2))
    | .AMOADD_W rd rs1 rs2 _ _ => some (.ofProgram (JoltISA.amoaddwProgramAuto rd rs1 rs2))
    | .AMOXOR_W rd rs1 rs2 _ _ => some (.ofProgram (JoltISA.amoxorwProgramAuto rd rs1 rs2))
    | .AMOAND_W rd rs1 rs2 _ _ => some (.ofProgram (JoltISA.amoandwProgramAuto rd rs1 rs2))
    | .AMOOR_W rd rs1 rs2 _ _ => some (.ofProgram (JoltISA.amoorwProgramAuto rd rs1 rs2))
    | .AMOMIN_W rd rs1 rs2 _ _ => some (.ofProgram (JoltISA.amominwProgramAuto rd rs1 rs2))
    | .AMOMAX_W rd rs1 rs2 _ _ => some (.ofProgram (JoltISA.amomaxwProgramAuto rd rs1 rs2))
    | .AMOMINU_W rd rs1 rs2 _ _ => some (.ofProgram (JoltISA.amominuwProgramAuto rd rs1 rs2))
    | .AMOMAXU_W rd rs1 rs2 _ _ => some (.ofProgram (JoltISA.amomaxuwProgramAuto rd rs1 rs2))
    | .LR_D rd rs1 _ _ => some (.ofProgram (JoltISA.lrdProgramAuto rd rs1 (regidx.Regidx 0)))
    | .SC_D rd rs1 rs2 _ _ => some (.ofProgram (JoltISA.scdProgramAuto rd rs1 rs2))
    | .AMOSWAP_D rd rs1 rs2 _ _ => some (.ofProgram (JoltISA.amoswapdProgramAuto rd rs1 rs2))
    | .AMOADD_D rd rs1 rs2 _ _ => some (.ofProgram (JoltISA.amoadddProgramAuto rd rs1 rs2))
    | .AMOXOR_D rd rs1 rs2 _ _ => some (.ofProgram (JoltISA.amoxordProgramAuto rd rs1 rs2))
    | .AMOAND_D rd rs1 rs2 _ _ => some (.ofProgram (JoltISA.amoanddProgramAuto rd rs1 rs2))
    | .AMOOR_D rd rs1 rs2 _ _ => some (.ofProgram (JoltISA.amoordProgramAuto rd rs1 rs2))
    | .AMOMIN_D rd rs1 rs2 _ _ => some (.ofProgram (JoltISA.amomindProgramAuto rd rs1 rs2))
    | .AMOMAX_D rd rs1 rs2 _ _ => some (.ofProgram (JoltISA.amomaxdProgramAuto rd rs1 rs2))
    | .AMOMINU_D rd rs1 rs2 _ _ => some (.ofProgram (JoltISA.amominudProgramAuto rd rs1 rs2))
    | .AMOMAXU_D rd rs1 rs2 _ _ => some (.ofProgram (JoltISA.amomaxudProgramAuto rd rs1 rs2))
    -- Zicsr and machine mode
    | .CSRRW rd csr rs1 => some (.ofProgram (JoltISA.csrrwProgram csr rs1 rd))
    | .CSRRS rd csr rs1 => some (.ofProgram (JoltISA.csrrsProgram csr rs1 rd))
    | .MRET => some (.ofProgram JoltISA.mretProgram)
  | .jolt instruction =>
    match instruction with
    | .AdviceLB rd => some (.ofProgram (JoltISA.advicelbProgramAuto rd))
    | .AdviceLH rd => some (.ofProgram (JoltISA.advicelhProgramAuto rd))
    | .AdviceLW rd => some (.ofProgram (JoltISA.advicelwProgramAuto rd))
    | .AdviceLD rd => some (.ofProgram (JoltISA.adviceldProgramAuto rd))
    -- FormatI immediates are sign-extended (jolt/tracer/src/instruction/format/format_i.rs:18-24).
    | .VirtualAdviceLen rd rs1 imm =>
        some (.ofNative (.VirtualAdviceLen (.xreg rd) (.xreg rs1) (sign_extend (m := 64) imm)))
    | .VirtualRev8W rd rs1 => some (.ofNative (.VirtualRev8W (.xreg rd) (.xreg rs1)))
    | .VirtualAssertEQ rs1 rs2 imm =>
        some (.ofNative (JoltISA.Encoded.VirtualAssertEQ (.xreg rs1) (.xreg rs2) imm))
    | .VirtualHostIO rd rs1 imm =>
        some (.ofNative (.VirtualHostIO (.xreg rd) (.xreg rs1) (sign_extend (m := 64) imm)))
