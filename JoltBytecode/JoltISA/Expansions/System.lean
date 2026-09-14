/-
Copyright (c) 2026 Ari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ari 
-/


import JoltBytecode.JoltISA.Instruction
import JoltBytecode.JoltISA.SystemCSR

/-!
# System-instruction Jolt expansion programs

These are literal transcriptions of the Rust `inline_sequence` implementations
in `tracer/src/instruction/{ecall,ebreak,mret,csrrw,csrrs}.rs`.

The reserved virtual registers follow `tracer/src/utils/virtual_registers.rs`:

* `v32`: word reservation address
* `v33`: doubleword reservation address
* `v34`: trap handler / `mtvec`
* `v35`: `mscratch`
* `v36`: `mepc`
* `v37`: `mcause`
* `v38`: `mtval`
* `v39`: `mstatus`
* `v40`: first scratch register allocated for an instruction expansion
-/

open Sail PreSail LeanRV64D.Functions

namespace JoltISA

/-- Rust's first `allocate()` result for system expansions. -/
def systemScratchVReg : VReg := inlineTmp0

/-- Rust `VirtualRegisterAllocator::csr_to_virtual_register` for the supported
ZeroOS CSR whitelist. A `none` result is not a supported proof target: Rust
emits `NoOp` for default-constructed CSR `0` and panics for other unsupported
CSRs. -/
def systemCSR? (csr : BitVec 12) : Option SystemCSR :=
  if csr = SystemCSR.address .mstatus then some .mstatus
  else if csr = SystemCSR.address .mtvec then some .mtvec
  else if csr = SystemCSR.address .mscratch then some .mscratch
  else if csr = SystemCSR.address .mepc then some .mepc
  else if csr = SystemCSR.address .mcause then some .mcause
  else if csr = SystemCSR.address .mtval then some .mtval
  else none

/-- Boolean architectural-register equality used by Rust's `rd == rs1` CSR
clobber cases. The generated `regidx` wrapper does not provide a direct
`DecidableEq` instance. -/
def sameXReg (lhs rhs : regidx) : Bool :=
  match lhs, rhs with
  | regidx.Regidx l, regidx.Regidx r => decide (l = r)

/-- Rust `expand_ecall`: materialize virtual trap CSRs and jump to `mtvec`. -/
def ecallProgram : Program :=
  -- Rust: `AUIPC ecall_addr, 0`.
  -- Jolt: `ecall_addr` is the first instruction-local scratch register, v40.
  .instr (.AUIPC (.vreg systemScratchVReg) (0 : BitVec 20)) <|
  -- Rust: `ADDI mepc, ecall_addr, 0`.
  -- Jolt: write the current PC into the virtual `mepc` CSR, v36.
  .instr (.ADDI (.vreg mepcVReg) (.vreg systemScratchVReg) (0 : BitVec 12)) <|
  -- Rust: `ADDI mcause, x0, MCAUSE_ECALL_FROM_MMODE`.
  -- Jolt: write machine-mode ECALL cause 11 into virtual `mcause`, v37.
  .instr (.ADDI (.vreg mcauseVReg) (.xreg (regidx.Regidx 0)) (11 : BitVec 12)) <|
  -- Rust: `ADDI mtval, x0, 0`.
  -- Jolt: machine-mode ECALL has no trap value, so virtual `mtval`, v38, is 0.
  .instr (.ADDI (.vreg mtvalVReg) (.xreg (regidx.Regidx 0)) (0 : BitVec 12)) <|
  -- Rust: `ADDI three, x0, 3`.
  -- Jolt: reuse v40 after `ecall_addr` is dropped.
  .instr (.ADDI (.vreg systemScratchVReg) (.xreg (regidx.Regidx 0)) (3 : BitVec 12)) <|
  -- Rust source row: `SLLI mstatus, three, 11`.
  -- Jolt final row: `SLLI` lowers to `VirtualMULI` by `2^11 = 2048`.
  .instr (.VirtualMULI (.vreg mstatusVReg) (.vreg systemScratchVReg) (2048 : BitVec 64)) <|
  -- Rust: `JALR jalr_rd, trap_handler, 0`.
  -- Jolt: jump through virtual `mtvec`, v34, and discard the link in v40.
  .instr (.JALR (.vreg systemScratchVReg) (.vreg trapHandlerVReg) (0 : BitVec 12)) <|
  .done RETIRE_SUCCESS

/-- Rust `expand_ebreak`: emit `JAL scratch, 0`, a self-loop termination marker. -/
def ebreakProgram : Program :=
  .instr (.JAL (.vreg systemScratchVReg) (0 : BitVec 21)) <|
  .done RETIRE_SUCCESS

/-- Rust `MRET::inline_sequence`: jump through virtual `mepc`.

Rust allocates one instruction-local scratch register for the `JALR` destination
and discards the link value. The architectural return target is read directly
from the reserved virtual `mepc` register, v36. -/
def mretProgram : Program :=
  .instr (.JALR (.vreg systemScratchVReg) (.vreg mepcVReg) (0 : BitVec 12)) <|
  .done RETIRE_SUCCESS

/-- Rust `CSRRW::inline_sequence` for the supported virtual CSR whitelist.

Cases match Rust exactly:

* `rd = x0`: write `rs1` directly to the CSR virtual register.
* `rd = rs1`: preserve `rs1` in the first instruction-local scratch register,
  then read the old CSR and write the preserved value back to the CSR.
* otherwise: read the old CSR into `rd`, then write `rs1` to the CSR. -/
def csrrwProgram (csr : SystemCSR) (rs1 rd : regidx) : Program :=
  let vr := SystemCSR.vreg csr
  if isX0 rd then
    .instr (.ADDI (.vreg vr) (.xreg rs1) (0 : BitVec 12)) <|
    .done RETIRE_SUCCESS
  else if sameXReg rd rs1 then
    .instr (.ADDI (.vreg systemScratchVReg) (.xreg rs1) (0 : BitVec 12)) <|
    .instr (.ADDI (.xreg rd) (.vreg vr) (0 : BitVec 12)) <|
    .instr (.ADDI (.vreg vr) (.vreg systemScratchVReg) (0 : BitVec 12)) <|
    .done RETIRE_SUCCESS
  else
    .instr (.ADDI (.xreg rd) (.vreg vr) (0 : BitVec 12)) <|
    .instr (.ADDI (.vreg vr) (.xreg rs1) (0 : BitVec 12)) <|
    .done RETIRE_SUCCESS

/-- Rust `CSRRW::inline_sequence` after decoding a supported raw CSR immediate. -/
def csrrwProgram? (csr : BitVec 12) (rs1 rd : regidx) : Option Program :=
  match systemCSR? csr with
  | some supported => some (csrrwProgram supported rs1 rd)
  | none => none

/-- Rust `CSRRS::inline_sequence` for the supported virtual CSR whitelist.

Cases match Rust exactly:

* `rs1 = x0`: read the CSR virtual register into `rd`.
* `rs1 != x0`, `rd = x0`: set the CSR virtual register with `OR`.
* `rd = rs1`: preserve `rs1` in the first instruction-local scratch register,
  then read the old CSR and set using the preserved value.
* otherwise: read the old CSR into `rd`, then set using `rs1`. -/
def csrrsProgram (csr : SystemCSR) (rs1 rd : regidx) : Program :=
  let vr := SystemCSR.vreg csr
  if isX0 rs1 then
    .instr (.ADDI (.xreg rd) (.vreg vr) (0 : BitVec 12)) <|
    .done RETIRE_SUCCESS
  else if isX0 rd then
    .instr (.OR (.vreg vr) (.vreg vr) (.xreg rs1)) <|
    .done RETIRE_SUCCESS
  else if sameXReg rd rs1 then
    .instr (.ADDI (.vreg systemScratchVReg) (.xreg rs1) (0 : BitVec 12)) <|
    .instr (.ADDI (.xreg rd) (.vreg vr) (0 : BitVec 12)) <|
    .instr (.OR (.vreg vr) (.vreg vr) (.vreg systemScratchVReg)) <|
    .done RETIRE_SUCCESS
  else
    .instr (.ADDI (.xreg rd) (.vreg vr) (0 : BitVec 12)) <|
    .instr (.OR (.vreg vr) (.vreg vr) (.xreg rs1)) <|
    .done RETIRE_SUCCESS

/-- Rust `CSRRS::inline_sequence` after decoding a supported raw CSR immediate. -/
def csrrsProgram? (csr : BitVec 12) (rs1 rd : regidx) : Option Program :=
  match systemCSR? csr with
  | some supported => some (csrrsProgram supported rs1 rd)
  | none => none

end JoltISA
