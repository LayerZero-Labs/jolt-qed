import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.trace
import JoltBytecode.JoltISA.Values

set_option autoImplicit false

namespace HonestWitness

-- Rust: [per-instruction lookup outputs](/Users/ari.biswas/Work-with-A16z/jolt/crates/jolt-lookup-tables/src/instructions).
-- Reuse the pure calculations called by execInstr, including when rd = x0
-- discards the computed value. Jumps output their target, not their link value.
-- Advice is the exception: Rust explicitly reads the captured post-state rd.
noncomputable def rowLookupOutput {program : JoltProgram}
    (row : JoltTraceRow program) : BitVec 64 :=
  let bytecodeRow := getElem program.expandedBytecode row.rowIndex.val row.rowIndex.isLt
  let instruction := bytecodeRow.instruction
  let source := fun src => JoltISA.sourceValue src row.preState
  match instruction with
  | .ADDI _ src imm => BitVec.ofNat 64 (JoltISA.addWide (source src) imm)
  | .ADDIW _ src imm => jolt_addiw_value64 (source src) imm
  | .ANDI _ src imm => Riscv.andi (source src) imm
  | .ORI _ src imm => Riscv.ori (source src) imm
  | .XORI _ src imm => jolt_xor_value (source src) imm
  | .SLTI _ src imm => jolt_slt_value (source src) imm
  | .SLTIU _ src imm => jolt_sltu_value (source src) imm
  | .LUI _ imm => imm
  | .AUIPC _ imm =>
      BitVec.ofNat 64 (JoltISA.addWide bytecodeRow.address imm)
  | .JAL _ imm => BitVec.ofNat 64 (JoltISA.addWide bytecodeRow.address imm)
  | .JALR _ base imm => jolt_jalr_target64 (source base) imm
  | .BEQ lhs rhs _ | .BNE lhs rhs _ | .BLT lhs rhs _ | .BGE lhs rhs _
  | .BLTU lhs rhs _ | .BGEU lhs rhs _ =>
      if JoltISA.branchDecisionPure instruction (source lhs) (source rhs) then 1 else 0
  | .ADD _ lhs rhs => BitVec.ofNat 64 (JoltISA.addWide (source lhs) (source rhs))
  | .ADDW _ lhs rhs => jolt_addw_value (source lhs) (source rhs)
  | .SUB _ lhs rhs => BitVec.ofNat 64 (JoltISA.subWide (source lhs) (source rhs))
  | .SUBW _ lhs rhs => jolt_subw_value (source lhs) (source rhs)
  | .MUL _ lhs rhs => BitVec.ofNat 64 (JoltISA.mulWide (source lhs) (source rhs))
  | .MULW _ lhs rhs => jolt_mulw_value (source lhs) (source rhs)
  | .MULHU _ lhs rhs => jolt_mulhu_value (source lhs) (source rhs)
  | .ANDN _ lhs rhs => jolt_andn_value (source lhs) (source rhs)
  | .OR _ lhs rhs => Riscv.ori (source lhs) (source rhs)
  | .XOR _ lhs rhs => jolt_xor_value (source lhs) (source rhs)
  | .AND _ lhs rhs => Riscv.andi (source lhs) (source rhs)
  | .SLT _ lhs rhs => jolt_slt_value (source lhs) (source rhs)
  | .SLTU _ lhs rhs => jolt_sltu_value (source lhs) (source rhs)
  | .VirtualMULI _ src imm => jolt_virtual_muli_value (source src) imm
  | .VirtualMULIW _ src imm => jolt_virtual_muliw_value (source src) imm
  | .VirtualPow2 _ src _ => jolt_virtual_pow2_value (source src)
  | .VirtualPow2W _ src _ => jolt_virtual_pow2w_value (source src)
  | .VirtualPow2I _ imm => jolt_virtual_pow2i_value imm
  | .VirtualPow2IW _ imm => jolt_virtual_pow2iw_value imm
  | .VirtualShiftRightBitmask _ src _ => jolt_virtual_shift_right_bitmask_value (source src)
  | .VirtualShiftRightBitmaskI _ imm => jolt_virtual_shift_right_bitmaski_value imm
  | .VirtualShiftRightBitmaskW _ src _ => jolt_virtual_shift_right_bitmaskw_value (source src)
  | .VirtualSRLI _ src mask => jolt_virtual_srli_value (source src) mask
  | .VirtualSRAI _ src mask => jolt_virtual_srai_value (source src) mask
  | .VirtualSRLIW _ src mask => jolt_virtual_srliw_value (source src) mask
  | .VirtualSRAIW _ src mask => jolt_virtual_sraiw_value (source src) mask
  | .VirtualSRL _ src mask => jolt_virtual_srl_value (source src) (source mask)
  | .VirtualSRA _ src mask => jolt_virtual_sra_value (source src) (source mask)
  | .VirtualSRLW _ src mask => jolt_virtual_srlw_value (source src) (source mask)
  | .VirtualSRAW _ src mask => jolt_virtual_sraw_value (source src) (source mask)
  | .VirtualROTRI _ src mask => jolt_virtual_rotri_value (source src) mask
  | .VirtualROTRIW _ src mask => jolt_virtual_rotriw_value (source src) mask
  | .VirtualRev8W _ src _ => jolt_virtual_rev8w_value (source src)
  | .VirtualXORROT32 _ lhs rhs => jolt_virtual_xorrot_value 32 (source lhs) (source rhs)
  | .VirtualXORROT24 _ lhs rhs => jolt_virtual_xorrot_value 24 (source lhs) (source rhs)
  | .VirtualXORROT16 _ lhs rhs => jolt_virtual_xorrot_value 16 (source lhs) (source rhs)
  | .VirtualXORROT63 _ lhs rhs => jolt_virtual_xorrot_value 63 (source lhs) (source rhs)
  | .VirtualXORROTL1 _ lhs rhs => jolt_virtual_xorrotl1_value (source lhs) (source rhs)
  | .VirtualXORROTW16 _ lhs rhs => jolt_virtual_xorrotw_value 16 (source lhs) (source rhs)
  | .VirtualXORROTW12 _ lhs rhs => jolt_virtual_xorrotw_value 12 (source lhs) (source rhs)
  | .VirtualXORROTW8 _ lhs rhs => jolt_virtual_xorrotw_value 8 (source lhs) (source rhs)
  | .VirtualXORROTW7 _ lhs rhs => jolt_virtual_xorrotw_value 7 (source lhs) (source rhs)
  | .VirtualXORROTW22 _ lhs rhs => jolt_virtual_xorrotw_value 22 (source lhs) (source rhs)
  | .VirtualXORROTW19 _ lhs rhs => jolt_virtual_xorrotw_value 19 (source lhs) (source rhs)
  | .VirtualXORROTW6 _ lhs rhs => jolt_virtual_xorrotw_value 6 (source lhs) (source rhs)
  | .VirtualAlignAddr _ base imm => jolt_virtual_align_addr_value64 (source base) imm
  | .VirtualWindowMaskB _ base imm => jolt_virtual_window_mask_b_value64 (source base) imm
  | .VirtualWindowMaskH _ base imm => jolt_virtual_window_mask_h_value64 (source base) imm
  | .VirtualWindowMaskW _ base imm => jolt_virtual_window_mask_w_value64 (source base) imm
  | .VirtualPext _ src mask => jolt_virtual_pext_value (source src) (source mask)
  | .VirtualPextSigned _ src mask => jolt_virtual_pext_signed_value (source src) (source mask)
  | .VirtualShiftDataB _ src address => jolt_virtual_shift_data_b_value (source src) (source address)
  | .VirtualShiftDataH _ src address => jolt_virtual_shift_data_h_value (source src) (source address)
  | .VirtualShiftDataW _ src address => jolt_virtual_shift_data_w_value (source src) (source address)
  | .VirtualSignExtendWord _ src _ => jolt_virtual_sign_extend_word_value (source src)
  | .VirtualZeroExtendWord _ src _ => jolt_virtual_zero_extend_word_value (source src)
  | .VirtualMovsign _ src _ => jolt_movsign_value (source src)
  | .VirtualNegateIf _ sign src => jolt_virtual_negate_if_value (source sign) (source src)
  | .VirtualAdvice dst _ _ | .VirtualAdviceLoad dst _ | .VirtualAdviceLen dst _ _ =>
      let register : JoltISA.Src := match dst with
        | .xreg r => .xreg r
        | .vreg r => .vreg r
      JoltISA.sourceValue register row.postState
  -- row.executes certifies success, so these enforced assertions hold.
  | .VirtualAssertHalfwordAlignment .. | .VirtualAssertWordAlignment ..
  | .VirtualAssertValidDiv0 .. | .VirtualAssertValidUnsignedRemainder ..
  | .VirtualAssertMulUNoOverflow .. | .VirtualAssertLTE .. => 1
  -- Rust permits a nonzero immediate to suppress this assertion. Such a row
  -- can retire with unequal operands; its lookup output must still be zero.
  | .VirtualAssertEQ lhs rhs _ => if jolt_assert_eq (source lhs) (source rhs) then 1 else 0
  | .FENCE | .LD .. | .SD .. | .VirtualHostIO .. => 0

-- Rust: [LookupOutput](/Users/ari.biswas/Work-with-A16z/jolt/crates/jolt-witness/src/witnesses/lookups.rs:23).
-- Cast the unsigned 64-bit result into F. The no-op padding output is zero.
noncomputable def LookupOutput {F : Type} [Field F] (p : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program) : Fin p.traceLength → F :=
  fun t =>
    if inBounds : t.val < trace.rows.size then
      ((rowLookupOutput (getElem trace.rows t.val inBounds)).toNat : F)
    else 0

end HonestWitness
