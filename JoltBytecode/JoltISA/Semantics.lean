/-
Copyright (c) 2026 Ari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ari 
-/
import JoltBytecode.JoltISA.Instruction
import JoltBytecode.JoltISA.RegisterAccess
import JoltBytecode.JoltISA.Values
import JoltBytecode.JoltISA.semantic_helpers
import JoltBytecode.JoltISA.DeviceMemory
import JoltBytecode.JoltISA.AdviceTape

/-!
# Jolt ISA semantics

This file tells us how to run a program. 
By run we mean how each intruction does state transition on Jolt CPU. 
The exec logic should be matched against the fn exec block in the corresponding 
rust code

`execInstr` gives each Jolt-ISA instruction its monadic meaning over
`SailJoltState`.  `execProgram` is the small interpreter used by generated
Rust expansion lists.
-/

set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions
open virtaddr MemoryAccessType mem_payload

set_option autoImplicit true

noncomputable section

namespace JoltISA

def execInstr : Instr → JoltMonad ExecutionResult
  | .ADDI dst src imm => do
      let x ← readSrc src
      writeDst dst (BitVec.ofNat 64 (addWide x imm))
      pure RETIRE_SUCCESS
  | .ADDIW dst src imm => do
      let x ← readSrc src
      writeDst dst (jolt_addiw_value64 x imm)
      pure RETIRE_SUCCESS
  | .ANDI dst src imm => do
      let x ← readSrc src
      writeDst dst (Riscv.andi x imm)
      pure RETIRE_SUCCESS
  | .ORI dst src imm => do
      let x ← readSrc src
      writeDst dst (Riscv.ori x imm)
      pure RETIRE_SUCCESS
  | .XORI dst src imm => do
      let x ← readSrc src
      writeDst dst (jolt_xor_value x imm)
      pure RETIRE_SUCCESS
  | .SLTI dst src imm => do
      let x ← readSrc src
      let y := imm
      writeDst dst (jolt_slt_value x y)
      pure RETIRE_SUCCESS
  | .SLTIU dst src imm => do
      let x ← readSrc src
      let y := imm
      writeDst dst (jolt_sltu_value x y)
      pure RETIRE_SUCCESS
  | .LUI dst imm => do
      writeDst dst imm
      pure RETIRE_SUCCESS
  | .AUIPC dst imm => do
      let pc ← liftSail (get_arch_pc ())
      let off := imm
      writeDst dst (BitVec.ofNat 64 (addWide pc off))
      pure RETIRE_SUCCESS
  | .JAL dst imm => do
      -- Rust: tracer/src/instruction/jal.rs::JAL::exec.
      -- At the instruction-body boundary, Sail PC represents self.address
      -- (the decoded instruction's address), and Sail nextPC represents cpu.pc
      -- (already advanced by the source instruction's length before exec).
      -- This is a state representation, not a claim that Rust has a nextPC field.
      let rustPC ← liftSail (Sail.readReg Register.nextPC)
      let instructionAddress ← liftSail (Sail.readReg Register.PC)
      -- Rust writes the old cpu.pc to rd first; writeDst discards writes to x0.
      -- Rust's diagnostic track_call bookkeeping is outside this architectural model.
      writeDst dst rustPC
      -- Rust: cpu.pc = self.address.wrapping_add(imm).
      -- BitVec addition wraps at 64 bits; Rust performs no alignment check here.
      -- Update nextPC, which represents cpu.pc, leaving the instruction address intact.
      liftSail (Sail.writeReg Register.nextPC (instructionAddress + imm))
      pure RETIRE_SUCCESS
  | .JALR dst base imm => do
      let link ← liftSail (get_next_pc ())
      let target ← readSrc base
      match ← liftSail (jump_to (jolt_jalr_target64 target imm)) with
      | .Retire_Success () =>
          writeDst dst link
          pure RETIRE_SUCCESS
      | other => pure other
  | .BEQ lhs rhs imm => do
      let x ← readSrc lhs
      let y ← readSrc rhs
      if branchDecisionPure (.BEQ lhs rhs imm) x y then
        let pc ← liftSail (Sail.readReg Register.PC)
        liftSail (jump_to (pc + imm.setWidth 64))
      else
        pure RETIRE_SUCCESS
  | .BNE lhs rhs imm => do
      let x ← readSrc lhs
      let y ← readSrc rhs
      if branchDecisionPure (.BNE lhs rhs imm) x y then
        let pc ← liftSail (Sail.readReg Register.PC)
        liftSail (jump_to (pc + imm.setWidth 64))
      else
        pure RETIRE_SUCCESS
  | .BLT lhs rhs imm => do
      let x ← readSrc lhs
      let y ← readSrc rhs
      if branchDecisionPure (.BLT lhs rhs imm) x y then
        let pc ← liftSail (Sail.readReg Register.PC)
        liftSail (jump_to (pc + imm.setWidth 64))
      else
        pure RETIRE_SUCCESS
  | .BGE lhs rhs imm => do
      let x ← readSrc lhs
      let y ← readSrc rhs
      if branchDecisionPure (.BGE lhs rhs imm) x y then
        let pc ← liftSail (Sail.readReg Register.PC)
        liftSail (jump_to (pc + imm.setWidth 64))
      else
        pure RETIRE_SUCCESS
  | .BLTU lhs rhs imm => do
      let x ← readSrc lhs
      let y ← readSrc rhs
      if branchDecisionPure (.BLTU lhs rhs imm) x y then
        let pc ← liftSail (Sail.readReg Register.PC)
        liftSail (jump_to (pc + imm.setWidth 64))
      else
        pure RETIRE_SUCCESS
  | .BGEU lhs rhs imm => do
      let x ← readSrc lhs
      let y ← readSrc rhs
      if branchDecisionPure (.BGEU lhs rhs imm) x y then
        let pc ← liftSail (Sail.readReg Register.PC)
        liftSail (jump_to (pc + imm.setWidth 64))
      else
        pure RETIRE_SUCCESS
  | .FENCE =>
      pure RETIRE_SUCCESS
  | .ADD dst lhs rhs => do
      let x ← readSrc lhs
      let y ← readSrc rhs
      writeDst dst (BitVec.ofNat 64 (addWide x y))
      pure RETIRE_SUCCESS
  | .ADDW dst lhs rhs => do
      let x ← readSrc lhs
      let y ← readSrc rhs
      writeDst dst (jolt_addw_value x y)
      pure RETIRE_SUCCESS
  | .SUB dst lhs rhs => do
      let x ← readSrc lhs
      let y ← readSrc rhs
      writeDst dst (BitVec.ofNat 64 (subWide x y))
      pure RETIRE_SUCCESS
  | .SUBW dst lhs rhs => do
      let x ← readSrc lhs
      let y ← readSrc rhs
      writeDst dst (jolt_subw_value x y)
      pure RETIRE_SUCCESS
  | .MUL dst lhs rhs => do
      let x ← readSrc lhs
      let y ← readSrc rhs
      writeDst dst (BitVec.ofNat 64 (mulWide x y))
      pure RETIRE_SUCCESS
  | .MULW dst lhs rhs => do
      let x ← readSrc lhs
      let y ← readSrc rhs
      writeDst dst (jolt_mulw_value x y)
      pure RETIRE_SUCCESS
  | .MULHU dst lhs rhs => do
      let x ← readSrc lhs
      let y ← readSrc rhs
      writeDst dst (jolt_mulhu_value x y)
      pure RETIRE_SUCCESS
  | .ANDN dst lhs rhs => do
      let x ← readSrc lhs
      let y ← readSrc rhs
      writeDst dst (jolt_andn_value x y)
      pure RETIRE_SUCCESS
  | .VirtualMULI dst src imm => do
      let x ← readSrc src
      writeDst dst (jolt_virtual_muli_value x imm)
      pure RETIRE_SUCCESS
  | .VirtualMULIW dst src imm => do
      let x ← readSrc src
      writeDst dst (jolt_virtual_muliw_value x imm)
      pure RETIRE_SUCCESS
  | .VirtualPow2 dst src _ => do
      let x ← readSrc src
      writeDst dst (jolt_virtual_pow2_value x)
      pure RETIRE_SUCCESS
  | .VirtualPow2W dst src _ => do
      let x ← readSrc src
      writeDst dst (jolt_virtual_pow2w_value x)
      pure RETIRE_SUCCESS
  | .VirtualPow2I dst imm => do
      writeDst dst (jolt_virtual_pow2i_value imm)
      pure RETIRE_SUCCESS
  | .VirtualPow2IW dst imm => do
      writeDst dst (jolt_virtual_pow2iw_value imm)
      pure RETIRE_SUCCESS
  | .VirtualShiftRightBitmask dst src _ => do
      let x ← readSrc src
      writeDst dst (jolt_virtual_shift_right_bitmask_value x)
      pure RETIRE_SUCCESS
  | .VirtualShiftRightBitmaskI dst imm => do
      writeDst dst (jolt_virtual_shift_right_bitmaski_value imm)
      pure RETIRE_SUCCESS
  | .VirtualShiftRightBitmaskW dst src _ => do
      let x ← readSrc src
      writeDst dst (jolt_virtual_shift_right_bitmaskw_value x)
      pure RETIRE_SUCCESS
  | .VirtualSRLI dst src bitmask => do
      let x ← readSrc src
      writeDst dst (jolt_virtual_srli_value x bitmask)
      pure RETIRE_SUCCESS
  | .VirtualSRAI dst src bitmask => do
      let x ← readSrc src
      writeDst dst (jolt_virtual_srai_value x bitmask)
      pure RETIRE_SUCCESS
  | .VirtualSRLIW dst src bitmask => do
      let x ← readSrc src
      writeDst dst (jolt_virtual_srliw_value x bitmask)
      pure RETIRE_SUCCESS
  | .VirtualSRAIW dst src bitmask => do
      let x ← readSrc src
      writeDst dst (jolt_virtual_sraiw_value x bitmask)
      pure RETIRE_SUCCESS
  | .VirtualSRL dst value bitmask => do
      let x ← readSrc value
      let b ← readSrc bitmask
      writeDst dst (jolt_virtual_srl_value x b)
      pure RETIRE_SUCCESS
  | .VirtualSRA dst value bitmask => do
      let x ← readSrc value
      let b ← readSrc bitmask
      writeDst dst (jolt_virtual_sra_value x b)
      pure RETIRE_SUCCESS
  | .VirtualSRLW dst value bitmask => do
      let x ← readSrc value
      let b ← readSrc bitmask
      writeDst dst (jolt_virtual_srlw_value x b)
      pure RETIRE_SUCCESS
  | .VirtualSRAW dst value bitmask => do
      let x ← readSrc value
      let b ← readSrc bitmask
      writeDst dst (jolt_virtual_sraw_value x b)
      pure RETIRE_SUCCESS
  | .VirtualROTRI dst src bitmask => do
      let x ← readSrc src
      writeDst dst (jolt_virtual_rotri_value x bitmask)
      pure RETIRE_SUCCESS
  | .VirtualROTRIW dst src bitmask => do
      let x ← readSrc src
      writeDst dst (jolt_virtual_rotriw_value x bitmask)
      pure RETIRE_SUCCESS
  | .VirtualRev8W dst src _ => do
      let x ← readSrc src
      writeDst dst (jolt_virtual_rev8w_value x)
      pure RETIRE_SUCCESS
  | .VirtualXORROT32 dst lhs rhs => do
      let x ← readSrc lhs
      let y ← readSrc rhs
      writeDst dst (jolt_virtual_xorrot_value 32 x y)
      pure RETIRE_SUCCESS
  | .VirtualXORROT24 dst lhs rhs => do
      let x ← readSrc lhs
      let y ← readSrc rhs
      writeDst dst (jolt_virtual_xorrot_value 24 x y)
      pure RETIRE_SUCCESS
  | .VirtualXORROT16 dst lhs rhs => do
      let x ← readSrc lhs
      let y ← readSrc rhs
      writeDst dst (jolt_virtual_xorrot_value 16 x y)
      pure RETIRE_SUCCESS
  | .VirtualXORROT63 dst lhs rhs => do
      let x ← readSrc lhs
      let y ← readSrc rhs
      writeDst dst (jolt_virtual_xorrot_value 63 x y)
      pure RETIRE_SUCCESS
  | .VirtualXORROTL1 dst lhs rhs => do
      let x ← readSrc lhs
      let y ← readSrc rhs
      writeDst dst (jolt_virtual_xorrotl1_value x y)
      pure RETIRE_SUCCESS
  | .VirtualXORROTW16 dst lhs rhs => do
      let x ← readSrc lhs
      let y ← readSrc rhs
      writeDst dst (jolt_virtual_xorrotw_value 16 x y)
      pure RETIRE_SUCCESS
  | .VirtualXORROTW12 dst lhs rhs => do
      let x ← readSrc lhs
      let y ← readSrc rhs
      writeDst dst (jolt_virtual_xorrotw_value 12 x y)
      pure RETIRE_SUCCESS
  | .VirtualXORROTW8 dst lhs rhs => do
      let x ← readSrc lhs
      let y ← readSrc rhs
      writeDst dst (jolt_virtual_xorrotw_value 8 x y)
      pure RETIRE_SUCCESS
  | .VirtualXORROTW7 dst lhs rhs => do
      let x ← readSrc lhs
      let y ← readSrc rhs
      writeDst dst (jolt_virtual_xorrotw_value 7 x y)
      pure RETIRE_SUCCESS
  | .VirtualXORROTW22 dst lhs rhs => do
      let x ← readSrc lhs
      let y ← readSrc rhs
      writeDst dst (jolt_virtual_xorrotw_value 22 x y)
      pure RETIRE_SUCCESS
  | .VirtualXORROTW19 dst lhs rhs => do
      let x ← readSrc lhs
      let y ← readSrc rhs
      writeDst dst (jolt_virtual_xorrotw_value 19 x y)
      pure RETIRE_SUCCESS
  | .VirtualXORROTW6 dst lhs rhs => do
      let x ← readSrc lhs
      let y ← readSrc rhs
      writeDst dst (jolt_virtual_xorrotw_value 6 x y)
      pure RETIRE_SUCCESS
  | .OR dst lhs rhs => do
      let x ← readSrc lhs
      let y ← readSrc rhs
      writeDst dst (Riscv.ori x y)
      pure RETIRE_SUCCESS
  | .XOR dst lhs rhs => do
      let x ← readSrc lhs
      let y ← readSrc rhs
      writeDst dst (jolt_xor_value x y)
      pure RETIRE_SUCCESS
  | .AND dst lhs rhs => do
      let x ← readSrc lhs
      let y ← readSrc rhs
      writeDst dst (Riscv.andi x y)
      pure RETIRE_SUCCESS
  | .SLT dst lhs rhs => do
      let x ← readSrc lhs
      let y ← readSrc rhs
      writeDst dst (jolt_slt_value x y)
      pure RETIRE_SUCCESS
  | .SLTU dst lhs rhs => do
      let x ← readSrc lhs
      let y ← readSrc rhs
      writeDst dst (jolt_sltu_value x y)
      pure RETIRE_SUCCESS
  | .VirtualAlignAddr dst base imm => do
      let baseValue ← readSrc base
      writeDst dst (jolt_virtual_align_addr_value64 baseValue imm)
      pure RETIRE_SUCCESS
  | .VirtualWindowMaskB dst base imm => do
      let baseValue ← readSrc base
      writeDst dst (jolt_virtual_window_mask_b_value64 baseValue imm)
      pure RETIRE_SUCCESS
  | .VirtualWindowMaskH dst base imm => do
      let baseValue ← readSrc base
      writeDst dst (jolt_virtual_window_mask_h_value64 baseValue imm)
      pure RETIRE_SUCCESS
  | .VirtualWindowMaskW dst base imm => do
      let baseValue ← readSrc base
      writeDst dst (jolt_virtual_window_mask_w_value64 baseValue imm)
      pure RETIRE_SUCCESS
  | .VirtualPext dst value mask => do
      let x ← readSrc value
      let y ← readSrc mask
      writeDst dst (jolt_virtual_pext_value x y)
      pure RETIRE_SUCCESS
  | .VirtualPextSigned dst value mask => do
      let x ← readSrc value
      let y ← readSrc mask
      writeDst dst (jolt_virtual_pext_signed_value x y)
      pure RETIRE_SUCCESS
  | .VirtualShiftDataB dst value address => do
      let x ← readSrc value
      let ea ← readSrc address
      writeDst dst (jolt_virtual_shift_data_b_value x ea)
      pure RETIRE_SUCCESS
  | .VirtualShiftDataH dst value address => do
      let x ← readSrc value
      let ea ← readSrc address
      writeDst dst (jolt_virtual_shift_data_h_value x ea)
      pure RETIRE_SUCCESS
  | .VirtualShiftDataW dst value address => do
      let x ← readSrc value
      let ea ← readSrc address
      writeDst dst (jolt_virtual_shift_data_w_value x ea)
      pure RETIRE_SUCCESS
  | .VirtualSignExtendWord dst src _ => do
      let x ← readSrc src
      writeDst dst (jolt_virtual_sign_extend_word_value x)
      pure RETIRE_SUCCESS
  | .VirtualZeroExtendWord dst src _ => do
      let x ← readSrc src
      writeDst dst (jolt_virtual_zero_extend_word_value x)
      pure RETIRE_SUCCESS
  | .VirtualMovsign dst src _ => do
      let x ← readSrc src
      writeDst dst (jolt_movsign_value x)
      pure RETIRE_SUCCESS
  | .VirtualAssertHalfwordAlignment base imm fault => do
      let baseValue ← readSrc base
      let addr := BitVec.ofNat 64 (addWide baseValue imm)
      if addr &&& (1 : BitVec 64) = 0 then
        pure RETIRE_SUCCESS
      else
        pure (ExecutionResult.Memory_Exception (Virtaddr addr, fault))
  | .VirtualAssertWordAlignment base imm fault => do
      let baseValue ← readSrc base
      let addr := BitVec.ofNat 64 (addWide baseValue imm)
      if addr &&& (3 : BitVec 64) = 0 then
        pure RETIRE_SUCCESS
      else
        pure (ExecutionResult.Memory_Exception (Virtaddr addr, fault))
  | .LD faultClass dst base imm => do
      let baseValue ← readSrc base
      let addr := (baseValue + imm)
      if addr &&& (7 : BitVec 64) = 0 then
        match ← readMemoryWord addr with
        | .Ok dword =>
            writeDst dst dword
            pure RETIRE_SUCCESS
        | .Err e => pure e
      else
        pure (ExecutionResult.Memory_Exception
          (Virtaddr addr, LoadFaultClass.alignFault faultClass))
  | .SD base value imm => do
      let baseValue ← readSrc base
      let addr := (baseValue + imm)
      let stored ← readSrc value
      if addr &&& (7 : BitVec 64) = 0 then
        match ← writeMemoryWord addr stored with
        | .Ok _ => pure RETIRE_SUCCESS
        | .Err e => pure e
      else
        pure (ExecutionResult.Memory_Exception
          (Virtaddr addr, ExceptionType.E_SAMO_Addr_Align ()))
  | .VirtualAdvice dst value _ => do
      writeDst dst value
      pure RETIRE_SUCCESS
  | .VirtualAdviceLoad dst byteCount => fun state =>
      match readAdviceTape state.adviceTape byteCount with
      | none => .error (Error.Assertion "VirtualAdviceLoad: invalid width or exhausted advice tape") state
      | some (value, tape) =>
          (do
            writeDst dst value
            pure RETIRE_SUCCESS) { state with adviceTape := tape }
  -- Rust: [VirtualAdviceLen::exec](/Users/ari.biswas/Work-with-A16z/jolt/tracer/src/instruction/virtual_advice_len.rs:18).
  | .VirtualAdviceLen dst _ _ => do
      let state ← get
      let remaining :=
        state.adviceTape.bytes.size - state.adviceTape.readPosition
      writeDst dst (BitVec.ofNat 64 remaining)
      pure RETIRE_SUCCESS
  | .VirtualHostIO _ _ _ =>
      pure RETIRE_SUCCESS
  | .VirtualAssertEQ lhs rhs imm => do
      if imm = 0#128 then
        let x ← readSrc lhs
        let y ← readSrc rhs
        if jolt_assert_eq x y then pure RETIRE_SUCCESS
        else throw (Error.Assertion "VirtualAssertEQ")
      else
        -- WARNING: Rust only logs a warning here; logs are not modeled in execution state.
        -- Unclear why Rust source does this, but this models the Rust code
        pure RETIRE_SUCCESS
  | .VirtualAssertValidDiv0 divisor quotient _ => do
      let d ← readSrc divisor
      let q ← readSrc quotient
      if d = 0#64 ∧ q ≠ (-1 : BitVec 64) then
        throw (Error.Assertion "VirtualAssertValidDiv0: divisor = 0 but quotient ≠ -1")
      else
        pure RETIRE_SUCCESS
  | .VirtualNegateIf dst signSource value => do
      let sign ← readSrc signSource
      let x ← readSrc value
      writeDst dst (jolt_virtual_negate_if_value sign x)
      pure RETIRE_SUCCESS
  | .VirtualAssertValidUnsignedRemainder remainder divisor _ => do
      let r ← readSrc remainder
      let d ← readSrc divisor
      if d = 0#64 ∨ r.toNat < d.toNat then
        pure RETIRE_SUCCESS
      else
        throw (Error.Assertion "VirtualAssertValidUnsignedRemainder: r ≥ d ∧ d ≠ 0")
  | .VirtualAssertMulUNoOverflow lhs rhs _ => do
      let x ← readSrc lhs
      let y ← readSrc rhs
      if mulWide x y < 2^64 then
        pure RETIRE_SUCCESS
      else
        throw (Error.Assertion "VirtualAssertMulUNoOverflow")
  | .VirtualAssertLTE lhs rhs _ => do
      let x ← readSrc lhs
      let y ← readSrc rhs
      if x.toNat ≤ y.toNat then
        pure RETIRE_SUCCESS
      else
        throw (Error.Assertion "VirtualAssertLTE")

/-
NOTE: Delete this in the final public facing publish of main, but keep them in the paper branch. 

  `match ← execInstr instr with`
  does not mean “run execInstr and match on both success and error.”
  It means:

  ```
  EStateM.bind (execInstr instr) fun result =>
    match result with
    | .Retire_Success () => execProgram rest
    | result => pure result
  ```
  And `EStateM.bind` handles errors by short-circuiting. Operationally:

  ```
  match execInstr instr s with
  | .ok result s' =>
      match result with
      | .Retire_Success () => execProgram rest s'
      | result => .ok result s'

  | .error e s' =>
      .error e s'
  ```
-/ 
def execProgram : Program → JoltMonad ExecutionResult
  | .done result => pure result
  | .instr instr rest => do
      match ← execInstr instr with
      | .Retire_Success () => execProgram rest
      -- If any instruction does not complete succesfully
      -- then return Result.ok result s' 
      -- Do not run the rest of the instructions in program.
      | result => pure result

/-- The two execution shapes on the Jolt side: native final instructions run
through `execInstr`; expanded source instructions run through `execProgram`. -/
inductive JoltExecution where
  | nativeInstr (instr : Instr)
  | expandedInstr (program : Program)
  deriving Repr

noncomputable def JoltExecution.run : JoltExecution → JoltMonad ExecutionResult
  | .nativeInstr instr => execInstr instr
  | .expandedInstr program => execProgram program

end JoltISA

end
