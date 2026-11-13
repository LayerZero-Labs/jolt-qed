import JoltConstraints.WholeRun.Io
import JoltConstraints.WholeRun.Bundles
import JoltBytecode.InstructionEquivalence.Instructions.AtomicFamily.Amoaddd
import JoltBytecode.InstructionEquivalence.Instructions.AtomicFamily.Amoxord
import JoltBytecode.InstructionEquivalence.Instructions.AtomicFamily.Amoandd
import JoltBytecode.InstructionEquivalence.Instructions.AtomicFamily.Amoord
import JoltBytecode.InstructionEquivalence.Instructions.AtomicFamily.Amomind
import JoltBytecode.InstructionEquivalence.Instructions.AtomicFamily.Amomaxd
import JoltBytecode.InstructionEquivalence.Instructions.AtomicFamily.Amominud
import JoltBytecode.InstructionEquivalence.Instructions.AtomicFamily.Amomaxud
import JoltBytecode.InstructionEquivalence.Instructions.AtomicFamily.Amoswapd
import JoltBytecode.InstructionEquivalence.Instructions.AtomicFamily.Amoaddw
import JoltBytecode.InstructionEquivalence.Instructions.AtomicFamily.Amoxorw
import JoltBytecode.InstructionEquivalence.Instructions.AtomicFamily.Amoandw
import JoltBytecode.InstructionEquivalence.Instructions.AtomicFamily.Amoorw
import JoltBytecode.InstructionEquivalence.Instructions.AtomicFamily.Amominw
import JoltBytecode.InstructionEquivalence.Instructions.AtomicFamily.Amomaxw
import JoltBytecode.InstructionEquivalence.Instructions.AtomicFamily.Amominuw
import JoltBytecode.InstructionEquivalence.Instructions.AtomicFamily.Amomaxuw
import JoltBytecode.InstructionEquivalence.Instructions.AtomicFamily.Amoswapw

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail
  LeanRV64D LeanRV64D.Functions JoltISA

set_option autoImplicit false

noncomputable section

namespace RiscvInstruction

/-- The containing doubleword an atomic memory operation reads and writes: the word
atomics round their source address down to a multiple of eight, the doubleword atomics
use the source address itself. Other instructions have none.
For example, `AMOADD.W` at `0x40000004` accesses the doubleword at `0x40000000`. -/
def amoBase : RiscvInstruction → SailJoltState → Option (BitVec 64)
  | .AMOSWAP_W _ rs1 _ _ _, js | .AMOADD_W _ rs1 _ _ _, js
  | .AMOXOR_W _ rs1 _ _ _, js | .AMOAND_W _ rs1 _ _ _, js
  | .AMOOR_W _ rs1 _ _ _, js | .AMOMIN_W _ rs1 _ _ _, js
  | .AMOMAX_W _ rs1 _ _ _, js | .AMOMINU_W _ rs1 _ _ _, js
  | .AMOMAXU_W _ rs1 _ _ _, js =>
      some (amoWordBase (JoltISA.sourceValue (.xreg rs1) js))
  | .AMOSWAP_D _ rs1 _ _ _, js | .AMOADD_D _ rs1 _ _ _, js
  | .AMOXOR_D _ rs1 _ _ _, js | .AMOAND_D _ rs1 _ _ _, js
  | .AMOOR_D _ rs1 _ _ _, js | .AMOMIN_D _ rs1 _ _ _, js
  | .AMOMAX_D _ rs1 _ _ _, js | .AMOMINU_D _ rs1 _ _ _, js
  | .AMOMAXU_D _ rs1 _ _ _, js =>
      some (JoltISA.sourceValue (.xreg rs1) js)
  | _, _ => none

/-- Documented deviation (`docs/riscv-alignment.md`, section 2): an atomic memory
operation in the I/O window does not touch the panic and termination words.
Jolt's device turns a store of the panic word into the panic flag and drops every other
store to the termination word, and its load returns the flag, while Sail stores and
returns the bytes written. An atomic reads and then writes the whole containing
doubleword (`LD` and `SD`, or the word lane rows through the same doubleword access in
`tracer/src/emulator/mmu.rs`, `Mmu::load_doubleword` and `Mmu::store_doubleword`), so no
byte of that doubleword may be a flag byte.
For example, `AMOADD.D` at the panic address violates it; at the first output
doubleword it holds. -/
def AmoNoFlagWord (i : RiscvInstruction) (js : SailJoltState) : Prop :=
  ∀ a, i.amoBase js = some a →
    ∀ k < 8, WholeRun.IsFlagWord js.jolt_device (a.toNat + k) = false

end RiscvInstruction

namespace WholeRun

attribute [local instance] Classical.propDecidable

local macro "blockHelper%" n:ident : term =>
  pure (Lean.mkIdent (Lean.mkPrivateNameCore `JoltConstraints.WholeRun.BlockStep
    (`WholeRun ++ n.getId)))
local macro "bundleHelper%" n:ident : term =>
  pure (Lean.mkIdent (Lean.mkPrivateNameCore `JoltConstraints.WholeRun.Bundles
    (`WholeRun ++ n.getId)))
local macro "ioHelper%" n:ident : term =>
  pure (Lean.mkIdent (Lean.mkPrivateNameCore `JoltConstraints.WholeRun.Io
    (`WholeRun ++ n.getId)))
local macro "storeHelper%" n:ident : term =>
  pure (Lean.mkIdent (Lean.mkPrivateNameCore
    `JoltBytecode.InstructionEquivalence.Instructions.StoreFamily.ProgramBlocks
    (`StoreProgramBlocks ++ n.getId)))

/-- Platform premise: the instruction is one of the atomic memory operations AMOSWAP,
AMOADD, AMOXOR, AMOAND, AMOOR, AMOMIN, AMOMAX, AMOMINU, AMOMAXU, in the word or
doubleword form, and the doubleword it accesses lies below `RAM_START_ADDRESS`, in
Sail's I/O window and Jolt's device.
For example, `AMOADD.D` through a register holding `0x40000010` satisfies it, and the
same instruction through `0x80000010` does not. -/
def IoAmoAccess (i : RiscvInstruction) (js : SailJoltState) : Prop :=
  ∃ a, i.amoBase js = some a ∧ a.toNat < JoltISA.RAM_START_ADDRESS

/-- Sail's PMP and PMA checks accept an aligned atomic inside the I/O window.
For example, an `AMOADD` doubleword at 0x40000010 passes the atomic check, which the
I/O region grants for the arithmetic operations. -/
private theorem io_atomic_checks (s : SailState) (addr : BitVec 64) (n : Nat)
    (hpma : s.regs.get? Register.pma_regions = some platformPma)
    (hlo : 0x40000000 ≤ addr.toNat) (hn : 0 < n) (hwidth : n ≤ 8)
    (hhi : addr.toNat + n ≤ JoltISA.RAM_START_ADDRESS)
    (halign : addr.toNat % n = 0) (op : amoop) (hop : (op == .AMOCAS) = false) :
    Assumptions.AtomicPmpOk op addr n s := by
  have hread := readReg_eq_of_get? Register.pma_regions s _ hpma
  have hmatch := (ioHelper% io_matching) addr n hlo hn hwidth hhi
  have hal := (ioHelper% aligned_paddr) addr n halign
  simp [Assumptions.AtomicPmpOk,
    phys_access_check, HartConfig.pmpCheck_run, pmaCheck, hread, hmatch, ioRegion, hal,
    pma_allows_atomic_op, bne, hop,
    LeanRV64D.sail_assert, Sail.ConcurrencyInterfaceV1.PreSail.sail_assert,
    LeanRV64D.Functions.not, bind, EStateM.bind, pure, EStateM.pure]

/-! ### Sail's atomic pipeline on the I/O window -/

section twins

open AtomicFamily MemoryAccessType mem_payload virtaddr physaddr

/-- The checked AMO dword read reduces to the canonical loaded dword when PMP
and readable-MMIO checks accept the access, as they do in the I/O window.
For example, an `AMOADD.D` at `0x40000010` reads the stored eight bytes. -/
theorem io_amo_dword_checked_mem_read_eq_loaded_dword
    (op : amoop) (addr : BitVec 64) (s : SailState)
    (hbytes : MemBytesPresentAt s addr 8)
    (h_no_ovf : addr.toNat + 7 < 2 ^ 64)
    (hatomic_pmp : Assumptions.AtomicPmpOk op addr 8 s)
    (hread_mmio : within_mmio_readable (physaddr.Physaddr addr) 8 s = .ok false s) :
    checked_mem_read (Atomic (op, Data, Data)) Privilege.Machine
      (physaddr.Physaddr addr) 8 false false true false s =
    .ok (Ok (loaded_dword_at s addr hbytes h_no_ovf, default_meta)) s := by
  unfold checked_mem_read
  simp only [bind, EStateM.bind, pure, EStateM.pure, hatomic_pmp, hread_mmio,
    Bool.false_eq_true, ite_false]
  unfold read_kind_of_flags
  simp only [pure, EStateM.pure]
  rw [amo_dword_read_ram_reserved_eq_loaded_dword addr s hbytes h_no_ovf]

/-- A full AMO dword memory read reduces through privilege, alignment, PMP, and
PMA checks to the canonical loaded dword.
For example, an `AMOADD.D` at `0x40000010` reads the stored eight bytes. -/
theorem io_amo_dword_mem_read_eq_loaded_dword
    (op : amoop) (addr : BitVec 64) (s : SailState)
    (hpriv : Assumptions.CurPrivilegeMachine s)
    (hmprv : Assumptions.MstatusMprvZero s)
    (h_no_ovf : addr.toNat + 7 < 2 ^ 64)
    (h_align : addr &&& (7 : BitVec 64) = 0)
    (hbytes : MemBytesPresentAt s addr 8)
    (hatomic_pmp : Assumptions.AtomicPmpOk op addr 8 s)
    (hread_mmio : within_mmio_readable (physaddr.Physaddr addr) 8 s = .ok false s) :
    mem_read (Atomic (op, Data, Data))
      (physaddr.Physaddr addr) 8 false false true s =
    .ok (Ok (loaded_dword_at s addr hbytes h_no_ovf)) s := by
  obtain ⟨mval, h_ms_regs, h_mprv⟩ := hmprv.value
  have h_ms_read := readReg_eq Register.mstatus s mval h_ms_regs
  have h_priv := readReg_eq Register.cur_privilege s Privilege.Machine hpriv.value
  have h_paddr_aligned := amo_dword_is_aligned_paddr_true addr h_align
  have h_mpp_check : decide (0#1 = 1#1) = false := by decide
  unfold mem_read mem_read_priv
  simp only [bind, EStateM.bind, pure, EStateM.pure, h_ms_read, h_priv]
  unfold effectivePrivilege
  simp only [h_mprv, bne, BEq.beq, instBEqMemoryAccessType.beq,
    Bool.not_false, h_mpp_check, Bool.and_false, Bool.false_eq_true, ite_false]
  unfold mem_read_priv_meta
  simp only [bind, EStateM.bind, pure, EStateM.pure,
    Bool.false_or, Bool.true_and, h_paddr_aligned]
  unfold LeanRV64D.Functions.not
  simp only [Bool.not_true, Bool.false_eq_true, ite_false]
  rw [io_amo_dword_checked_mem_read_eq_loaded_dword
    op addr s hbytes h_no_ovf hatomic_pmp hread_mmio]
  rfl

/-- A full AMO dword memory-value write reduces through privilege, alignment,
PMP, and PMA checks to the canonical dword store.
For example, an `AMOADD.D` at `0x40000010` stores the sum there. -/
theorem io_amo_dword_mem_write_value_eq_state_after_dword_store
    (op : amoop) (addr data : BitVec 64) (s : SailState)
    (hpriv : Assumptions.CurPrivilegeMachine s)
    (hmprv : Assumptions.MstatusMprvZero s)
    (h_align : addr &&& (7 : BitVec 64) = 0)
    (hatomic_pmp : Assumptions.AtomicPmpOk op addr 8 s)
    (hwrite_mmio : within_mmio_writable (physaddr.Physaddr addr) 8 s = .ok false s) :
    mem_write_value (physaddr.Physaddr addr) 8 data
      (Atomic (op, Data, Data)) false false true s =
    .ok (Ok true) (state_after_dword_store s addr data) := by
  obtain ⟨mval, h_ms_regs, h_mprv⟩ := hmprv.value
  have h_ms_read := readReg_eq Register.mstatus s mval h_ms_regs
  have h_priv := readReg_eq Register.cur_privilege s Privilege.Machine hpriv.value
  have h_paddr_aligned := amo_dword_is_aligned_paddr_true addr h_align
  have h_mpp_check : decide (0#1 = 1#1) = false := by decide
  unfold mem_write_value mem_write_value_meta mem_write_value_priv_meta
    checked_mem_write
  simp only [bind, EStateM.bind, pure, h_ms_read, h_priv]
  unfold effectivePrivilege
  simp only [h_mprv, bne, BEq.beq, instBEqMemoryAccessType.beq,
    Bool.not_false, h_mpp_check, Bool.and_false, Bool.false_eq_true, ite_false]
  simp only [Bool.false_or, Bool.true_and, h_paddr_aligned]
  unfold LeanRV64D.Functions.not
  simp only [Bool.not_true, Bool.false_eq_true, ite_false]
  change
    (EStateM.bind
      (EStateM.bind
        (phys_access_check (Atomic (op, Data, Data)) Privilege.Machine
          (physaddr.Physaddr addr) 8 true)
        (fun result =>
          match result with
          | some e => EStateM.pure (Err e)
          | none =>
              EStateM.bind
                (within_mmio_writable (physaddr.Physaddr addr) 8)
                (fun isMmio =>
                  if isMmio = true then
                    mmio_write (physaddr.Physaddr addr) 8 data
                  else
                    EStateM.bind
                      (write_kind_of_flags false false true)
                      (fun wk =>
                        EStateM.bind
                          (LeanRV64D.Functions.write_ram wk
                            (physaddr.Physaddr addr) 8 data default_meta)
                          (fun ok => EStateM.pure (Ok ok))))))
      (fun result => EStateM.pure result)) s =
    .ok (Ok true) (state_after_dword_store s addr data)
  simp only [EStateM.bind, hatomic_pmp]
  simp only [hwrite_mmio]
  simp only [Bool.false_eq_true, ite_false]
  unfold write_kind_of_flags
  simp only [EStateM.bind, pure, EStateM.pure]
  rw [amo_dword_write_ram_conditional_eq_state_after_dword_store addr data s]

/-- The Sail AMO write of the computed dword result reduces to the canonical
hashmap dword store.
For example, `AMOXOR.D` at `0x40000010` stores `rs2 ^^^ old` as eight bytes there. -/
theorem io_amo_dword_mem_write_value_sail_result
    (op : amoop) (addr rs2Val result old : BitVec 64) (js : SailJoltState)
    (hpriv : Assumptions.CurPrivilegeMachine js.sail)
    (hmprv : Assumptions.MstatusMprvZero js.sail)
    (hatomic_pmp : Assumptions.AtomicPmpOk op addr 8 js.sail)
    (hwrite_mmio : within_mmio_writable (physaddr.Physaddr addr) 8 js.sail = .ok false js.sail)
    (h_align : addr &&& (7 : BitVec 64) = 0)
    (hresult :
      amoDwordSailResult op
        (show BitVec (8 * 8) from
          trunc (m := (((8 : Nat) : Int) * (8 : Int)).toNat) rs2Val)
        (BitVec.setWidth (8 * 8) old) =
      result) :
    mem_write_value (physaddr.Physaddr addr) 8
      (sign_extend (m := ((8 : Int) * ((8 : Nat) : Int)).toNat)
        (amoDwordSailResult op
          (show BitVec (8 * 8) from
            trunc (m := (((8 : Nat) : Int) * (8 : Int)).toNat) rs2Val)
          (BitVec.setWidth (8 * 8) old)))
      (Atomic (op, Data, Data)) false false true js.sail =
    .ok (Ok true) (state_after_dword_store js.sail addr result) := by
  rw [hresult]
  change
    mem_write_value (physaddr.Physaddr addr) 8
      (sign_extend (m := 8 * 8) result)
      (Atomic (op, Data, Data)) false false true js.sail =
    .ok (Ok true) (state_after_dword_store js.sail addr result)
  rw [amo_dword_sign_extend_8x8_eq_self]
  exact
    io_amo_dword_mem_write_value_eq_state_after_dword_store
      op addr result js.sail hpriv hmprv h_align hatomic_pmp hwrite_mmio

/-- Shared Sail-side aligned reduction for 64-bit non-CAS AMOs.

The generated Sail code reads `rd` while evaluating the AMOCAS guard, even when
`op` is later shown not to be AMOCAS. Callers therefore supply `hrd`.
For example, `AMOADD.D` at `0x40000010` with an aligned address and an accepting PMA. -/
theorem io_execute_AMO_dword_non_cas_aligned
    (op : amoop) (rs2 rs1 rd : regidx) (js : SailJoltState)
    (hpriv : Assumptions.CurPrivilegeMachine js.sail)
    (hmprv : Assumptions.MstatusMprvZero js.sail)
    (addr rs2Val result : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
    (hrd : ∃ rdVal, rX_bits rd js.sail = .ok rdVal js.sail)
    (hbytes : MemBytesPresentAt js.sail addr 8)
    (hatomic_pmp : Assumptions.AtomicPmpOk op addr 8 js.sail)
    (hread_mmio : within_mmio_readable (physaddr.Physaddr addr) 8 js.sail = .ok false js.sail)
    (hwrite_mmio : within_mmio_writable (physaddr.Physaddr addr) 8 js.sail = .ok false js.sail)
    (h_align : addr &&& (7 : BitVec 64) = 0)
    (hnot_cas : (op == amoop.AMOCAS) = false)
    (hresult :
      amoDwordSailResult op
        (show BitVec (8 * 8) from
          trunc (m := (((8 : Nat) : Int) * (8 : Int)).toNat) rs2Val)
        (BitVec.setWidth (8 * 8)
          (loaded_dword_at js.sail addr hbytes
            (amo_dword_aligned_no_ovf addr h_align))) =
      result) :
    (execute_AMO op false false rs2 rs1 8 rd).run js.sail =
      .ok RETIRE_SUCCESS
        (amoDwordFinalSailState rd js.sail addr result
          (loaded_dword_at js.sail addr hbytes
            (amo_dword_aligned_no_ovf addr h_align))) := by
  let old : BitVec 64 :=
    loaded_dword_at js.sail addr hbytes (amo_dword_aligned_no_ovf addr h_align)
  obtain ⟨rdVal, hrd_read⟩ := hrd
  obtain ⟨writebackState, hwriteback, hwriteback_state⟩ :=
    amo_dword_writeback_old_shape rd js.sail addr result old
  exact
    execute_AMO_dword_non_cas_aligned_core
      op rs2 rs1 rd js addr rs2Val result old rdVal writebackState
      hrs1 hrs2 hrd_read hnot_cas
      (amo_dword_is_aligned_vaddr_true addr h_align)
      (translateAddr_atomic_data_of_machine_mprv_zero op addr js.sail hpriv hmprv)
      (amo_dword_mem_write_ea_ok addr js.sail h_align)
      (io_amo_dword_mem_read_eq_loaded_dword op addr js.sail hpriv hmprv
        (amo_dword_aligned_no_ovf addr h_align) h_align hbytes
        hatomic_pmp hread_mmio)
      (io_amo_dword_mem_write_value_sail_result
        op addr rs2Val result old js hpriv hmprv hatomic_pmp hwrite_mmio
        h_align hresult)
      (amo_dword_writeback_loaded_direct
        rd js.sail writebackState addr result old hwriteback)
      hwriteback_state

/-- The checked AMO word read reduces to the canonical loaded word when PMP
and readable-MMIO checks accept the access, as they do in the I/O window.
For example, an `AMOADD.W` at `0x40000014` reads the stored upper word. -/
theorem io_amo_word_checked_mem_read_eq_loaded_word
    (op : amoop) (addr : BitVec 64) (s : SailState)
    (hbytes : MemBytesPresentAt s addr 4)
    (h_no_ovf : addr.toNat + 3 < 2 ^ 64)
    (hatomic_pmp : Assumptions.AtomicPmpOk op addr 4 s)
    (hread_mmio : within_mmio_readable (physaddr.Physaddr addr) 4 s = .ok false s) :
    checked_mem_read (Atomic (op, Data, Data)) Privilege.Machine
      (physaddr.Physaddr addr) 4 false false true false s =
    .ok (Ok (loaded_word_at s addr hbytes h_no_ovf, default_meta)) s := by
  unfold checked_mem_read
  simp only [bind, EStateM.bind, pure, EStateM.pure, hatomic_pmp, hread_mmio,
    Bool.false_eq_true, ite_false]
  unfold read_kind_of_flags
  simp only [pure, EStateM.pure]
  rw [amo_word_read_ram_reserved_eq_loaded_word addr s hbytes h_no_ovf]

/-- A full AMO word memory read reduces through privilege, alignment, PMP, and
PMA checks to the canonical loaded word.
For example, an `AMOADD.W` at `0x40000014` reads the stored upper word. -/
theorem io_amo_word_mem_read_eq_loaded_word
    (op : amoop) (addr : BitVec 64) (s : SailState)
    (hpriv : Assumptions.CurPrivilegeMachine s)
    (hmprv : Assumptions.MstatusMprvZero s)
    (h_no_ovf : addr.toNat + 3 < 2 ^ 64)
    (h_align : addr &&& (3 : BitVec 64) = 0)
    (hbytes : MemBytesPresentAt s addr 4)
    (hatomic_pmp : Assumptions.AtomicPmpOk op addr 4 s)
    (hread_mmio : within_mmio_readable (physaddr.Physaddr addr) 4 s = .ok false s) :
    mem_read (Atomic (op, Data, Data))
      (physaddr.Physaddr addr) 4 false false true s =
    .ok (Ok (loaded_word_at s addr hbytes h_no_ovf)) s := by
  obtain ⟨mval, h_ms_regs, h_mprv⟩ := hmprv.value
  have h_ms_read := readReg_eq Register.mstatus s mval h_ms_regs
  have h_priv := readReg_eq Register.cur_privilege s Privilege.Machine hpriv.value
  have h_paddr_aligned := amo_word_is_aligned_paddr_true addr h_align
  have h_mpp_check : decide (0#1 = 1#1) = false := by decide
  unfold mem_read mem_read_priv
  simp only [bind, EStateM.bind, pure, EStateM.pure, h_ms_read, h_priv]
  unfold effectivePrivilege
  simp only [h_mprv, bne, BEq.beq, instBEqMemoryAccessType.beq,
    Bool.not_false, h_mpp_check, Bool.and_false, Bool.false_eq_true, ite_false]
  unfold mem_read_priv_meta
  simp only [bind, EStateM.bind, pure, EStateM.pure,
    Bool.false_or, Bool.true_and, h_paddr_aligned]
  unfold LeanRV64D.Functions.not
  simp only [Bool.not_true, Bool.false_eq_true, ite_false]
  rw [io_amo_word_checked_mem_read_eq_loaded_word
    op addr s hbytes h_no_ovf hatomic_pmp hread_mmio]
  rfl

/-- A full AMO word memory-value write reduces through privilege, alignment,
PMP, and PMA checks to the canonical word store.
For example, an `AMOADD.W` at `0x40000014` stores the sum in the upper word. -/
theorem io_amo_word_mem_write_value_eq_state_after_word_store
    (op : amoop) (addr : BitVec 64) (data : BitVec 32) (s : SailState)
    (hpriv : Assumptions.CurPrivilegeMachine s)
    (hmprv : Assumptions.MstatusMprvZero s)
    (h_align : addr &&& (3 : BitVec 64) = 0)
    (hatomic_pmp : Assumptions.AtomicPmpOk op addr 4 s)
    (hwrite_mmio : within_mmio_writable (physaddr.Physaddr addr) 4 s = .ok false s) :
    mem_write_value (physaddr.Physaddr addr) 4 data
      (Atomic (op, Data, Data)) false false true s =
    .ok (Ok true) (state_after_word_store s addr data) := by
  obtain ⟨mval, h_ms_regs, h_mprv⟩ := hmprv.value
  have h_ms_read := readReg_eq Register.mstatus s mval h_ms_regs
  have h_priv := readReg_eq Register.cur_privilege s Privilege.Machine hpriv.value
  have h_paddr_aligned := amo_word_is_aligned_paddr_true addr h_align
  have h_mpp_check : decide (0#1 = 1#1) = false := by decide
  unfold mem_write_value mem_write_value_meta mem_write_value_priv_meta
    checked_mem_write
  simp only [bind, EStateM.bind, pure, h_ms_read, h_priv]
  unfold effectivePrivilege
  simp only [h_mprv, bne, BEq.beq, instBEqMemoryAccessType.beq,
    Bool.not_false, h_mpp_check, Bool.and_false, Bool.false_eq_true, ite_false]
  simp only [Bool.false_or, Bool.true_and, h_paddr_aligned]
  unfold LeanRV64D.Functions.not
  simp only [Bool.not_true, Bool.false_eq_true, ite_false]
  change
    (EStateM.bind
      (EStateM.bind
        (phys_access_check (Atomic (op, Data, Data)) Privilege.Machine
          (physaddr.Physaddr addr) 4 true)
        (fun result =>
          match result with
          | some e => EStateM.pure (Err e)
          | none =>
              EStateM.bind
                (within_mmio_writable (physaddr.Physaddr addr) 4)
                (fun isMmio =>
                  if isMmio = true then
                    mmio_write (physaddr.Physaddr addr) 4 data
                  else
                    EStateM.bind
                      (write_kind_of_flags false false true)
                      (fun wk =>
                        EStateM.bind
                          (LeanRV64D.Functions.write_ram wk
                            (physaddr.Physaddr addr) 4 data default_meta)
                          (fun ok => EStateM.pure (Ok ok))))))
      (fun result => EStateM.pure result)) s =
    .ok (Ok true) (state_after_word_store s addr data)
  simp only [EStateM.bind, hatomic_pmp]
  simp only [hwrite_mmio]
  simp only [Bool.false_eq_true, ite_false]
  unfold write_kind_of_flags
  simp only [EStateM.bind, pure, EStateM.pure]
  rw [amo_word_write_ram_conditional_eq_state_after_word_store addr data s]

/-- The Sail AMO write of the computed word result reduces to the canonical
hashmap word store.
For example, `AMOXOR.W` at `0x40000014` stores the low word of `rs2 ^^^ old` there. -/
theorem io_amo_word_mem_write_value_sail_result
    (op : amoop) (addr rs2Val : BitVec 64) (result old : BitVec 32)
    (js : SailJoltState)
    (hpriv : Assumptions.CurPrivilegeMachine js.sail)
    (hmprv : Assumptions.MstatusMprvZero js.sail)
    (hatomic_pmp : Assumptions.AtomicPmpOk op addr 4 js.sail)
    (hwrite_mmio : within_mmio_writable (physaddr.Physaddr addr) 4 js.sail = .ok false js.sail)
    (h_align : addr &&& (3 : BitVec 64) = 0)
    (hresult :
      amoWordSailResult op
        (show BitVec (4 * 8) from
          trunc (m := (((4 : Nat) : Int) * (8 : Int)).toNat) rs2Val)
        (BitVec.setWidth (4 * 8) old) =
      result) :
    mem_write_value (physaddr.Physaddr addr) 4
      (sign_extend (m := ((8 : Int) * ((4 : Nat) : Int)).toNat)
        (amoWordSailResult op
          (show BitVec (4 * 8) from
            trunc (m := (((4 : Nat) : Int) * (8 : Int)).toNat) rs2Val)
          (BitVec.setWidth (4 * 8) old)))
      (Atomic (op, Data, Data)) false false true js.sail =
    .ok (Ok true) (state_after_word_store js.sail addr result) := by
  rw [hresult]
  change
    mem_write_value (physaddr.Physaddr addr) 4
      (sign_extend (m := 4 * 8) result)
      (Atomic (op, Data, Data)) false false true js.sail =
    .ok (Ok true) (state_after_word_store js.sail addr result)
  rw [amo_word_sign_extend_4x8_eq_self result]
  exact
    io_amo_word_mem_write_value_eq_state_after_word_store
      op addr result js.sail hpriv hmprv h_align hatomic_pmp hwrite_mmio

/-- Shared Sail-side aligned reduction for 32-bit non-CAS AMOs.

The generated Sail code reads `rd` while evaluating the AMOCAS guard, even when
`op` is later shown not to be AMOCAS. Callers therefore supply `hrd`.
For example, `AMOADD.W` at `0x40000014` with an aligned address and an accepting PMA. -/
theorem io_execute_AMO_word_non_cas_aligned
    (op : amoop) (rs2 rs1 rd : regidx) (js : SailJoltState)
    (hpriv : Assumptions.CurPrivilegeMachine js.sail)
    (hmprv : Assumptions.MstatusMprvZero js.sail)
    (addr rs2Val : BitVec 64) (result : BitVec 32)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
    (hrd : ∃ rdVal, rX_bits rd js.sail = .ok rdVal js.sail)
    (hbytes : MemBytesPresentAt js.sail addr 4)
    (hatomic_pmp : Assumptions.AtomicPmpOk op addr 4 js.sail)
    (hread_mmio : within_mmio_readable (physaddr.Physaddr addr) 4 js.sail = .ok false js.sail)
    (hwrite_mmio : within_mmio_writable (physaddr.Physaddr addr) 4 js.sail = .ok false js.sail)
    (h_align : addr &&& (3 : BitVec 64) = 0)
    (hnot_cas : (op == amoop.AMOCAS) = false)
    (hresult :
      amoWordSailResult op
        (show BitVec (4 * 8) from
          trunc (m := (((4 : Nat) : Int) * (8 : Int)).toNat) rs2Val)
        (BitVec.setWidth (4 * 8)
          (loaded_word_at js.sail addr hbytes
            (amo_word_aligned_no_ovf addr (amo_word_base_no_ovf addr) h_align))) =
      result) :
    (execute_AMO op false false rs2 rs1 4 rd).run js.sail =
      .ok RETIRE_SUCCESS
        (amoWordFinalSailState rd js.sail addr result
          (loaded_word_at js.sail addr hbytes
            (amo_word_aligned_no_ovf addr (amo_word_base_no_ovf addr) h_align))) := by
  have h_base_no_ovf := amo_word_base_no_ovf addr
  have h_no_ovf := amo_word_aligned_no_ovf addr h_base_no_ovf h_align
  let old : BitVec 32 := loaded_word_at js.sail addr hbytes h_no_ovf
  obtain ⟨rdVal, hrd_read⟩ := hrd
  obtain ⟨writebackState, hwriteback, hwriteback_state⟩ :=
    amo_word_writeback_old_shape rd js.sail addr result old
  exact
    execute_AMO_word_non_cas_aligned_core
      op rs2 rs1 rd js addr rs2Val rdVal result old writebackState
      hrs1 hrs2 hrd_read hnot_cas
      (amo_word_is_aligned_vaddr_true addr h_align)
      (translateAddr_atomic_data_of_machine_mprv_zero op addr js.sail hpriv hmprv)
      (amo_word_mem_write_ea_ok addr js.sail h_align)
      (io_amo_word_mem_read_eq_loaded_word op addr js.sail hpriv hmprv
        h_no_ovf h_align hbytes hatomic_pmp hread_mmio)
      (io_amo_word_mem_write_value_sail_result
        op addr rs2Val result old js hpriv hmprv hatomic_pmp hwrite_mmio
        h_align hresult)
      (amo_word_writeback_loaded_direct
        rd js.sail writebackState addr result old hwriteback)
      hwriteback_state


end twins

/-! ### Jolt's doubleword rows -/

/-- A retiring `LD` of an AMO expansion is an aligned doubleword load into its scratch
register.
For example, if the `LD` retires at the I/O address `0x40000008`, the address is
8-aligned, `load_doubleword` returned some `D` and the register holds `D`. -/
private theorem ld_amo_inv (oldReg : JoltISA.VReg) (hw : WritableVReg oldReg) (rs1 : regidx)
    (A : BitVec 64) (js js1 : SailJoltState) (hread : rX_bits rs1 js.sail = .ok A js.sail)
    (hlt : A.toNat < JoltISA.RAM_START_ADDRESS)
    (hrun : (JoltISA.execInstr (JoltISA.Encoded.LD .amo (.vreg oldReg) (.xreg rs1) 0)).run js =
      .ok RETIRE_SUCCESS js1) :
    A &&& (7 : BitVec 64) = 0 ∧
      ∃ D, JoltISA.read_doubleword? (JoltISA.Mmu.load_raw? js) A.toNat = some D ∧
        js1 = stateAfterVRegWrite js oldReg D := by
  have hz : sign_extend (m := 64) (0 : BitVec 12) = (0 : BitVec 64) := by decide
  simp only [hz, JoltISA.execInstr, JoltISA.readSrc, liftSail, bind,
    EStateM.bind, EStateM.run, hread, add_zero] at hrun
  by_cases halign : A &&& (7 : BitVec 64) = 0
  · simp only [halign, ↓reduceIte] at hrun
    refine ⟨halign, ?_⟩
    cases hl : JoltISA.Mmu.load_doubleword A js with
    | ok r s' =>
      obtain ⟨-, D, hr, hs, hrd⟩ := (ioHelper% load_doubleword_inv) A js s' r hlt hl
      subst hr
      subst hs
      refine ⟨D, hrd, ?_⟩
      have hnl : ¬ oldReg.toNat < 32 := hw
      simp only [EStateM.bind, hl, JoltISA.writeDst, writeVReg, hnl, ite_false, modify,
        modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, pure, EStateM.pure,
        EStateM.Result.ok.injEq, true_and] at hrun
      subst hrun
      rfl
    | error e s' =>
      exfalso
      simp [EStateM.bind, hl] at hrun
  · exfalso
    simp only [halign, ↓reduceIte] at hrun
    simp only [pure, EStateM.pure, EStateM.Result.ok.injEq] at hrun
    have := hrun.1
    simp [RETIRE_SUCCESS] at this


/-- A retiring `SD` of an AMO expansion is an aligned doubleword store of its source.
For example, `SD` of the register holding `V` at an aligned I/O address retires only if
`store_doubleword` of `V` there does. -/
private theorem sd_amo_inv (rs1 : regidx) (src : JoltISA.Src) (A V : BitVec 64)
    (js gp : SailJoltState) (hr1 : rX_bits rs1 js.sail = .ok A js.sail)
    (hsrc : JoltISA.readSrc src js = .ok V js)
    (hlt : A.toNat < JoltISA.RAM_START_ADDRESS)
    (hrun : (JoltISA.execInstr (JoltISA.Encoded.SD (.xreg rs1) src 0)).run js =
      .ok RETIRE_SUCCESS gp) :
    A &&& (7 : BitVec 64) = 0 ∧ JoltISA.Mmu.store_doubleword A V js = .ok (.Ok true) gp := by
  have hz : sign_extend (m := 64) (0 : BitVec 12) = (0 : BitVec 64) := by decide
  simp only [hz, JoltISA.execInstr, JoltISA.readSrc, liftSail, bind, EStateM.bind, EStateM.run,
    hr1, add_zero] at hrun
  simp only [JoltISA.readSrc] at hsrc
  by_cases halign : A &&& (7 : BitVec 64) = 0
  · refine ⟨halign, ?_⟩
    simp only [hsrc, halign, ↓reduceIte] at hrun
    change EStateM.bind (JoltISA.Mmu.store_doubleword A V) _ js = _ at hrun
    cases hs : JoltISA.Mmu.store_doubleword A V js with
    | ok r s' =>
      obtain ⟨-, hr, -⟩ := (ioHelper% store_doubleword_below_inv) A V js s' r hlt hs
      subst hr
      simp only [EStateM.bind, hs, pure, EStateM.pure, EStateM.Result.ok.injEq, true_and] at hrun
      rw [hrun]
    | error e s' =>
      exfalso
      simp [EStateM.bind, hs] at hrun
  · exfalso
    simp only [hsrc, halign, ↓reduceIte, pure, EStateM.pure, EStateM.Result.ok.injEq] at hrun
    have := hrun.1
    simp [RETIRE_SUCCESS] at this


/-- Reading a writable virtual register as an operand gives its contents.
For example, reading `v40` gives the value stored there. -/
private theorem readSrc_vreg (vr : JoltISA.VReg) (js : SailJoltState) :
    JoltISA.readSrc (.vreg vr) js = .ok (js.vregs vr) js := rfl

/-- The access premises of an AMO on a doubleword in the I/O window rule out every
write that is not to the output buffer: a store of the doubleword at `A` that is not a
flag-word store lies in the output buffer, and so at or above the lowest address.
For example, an `AMOADD.D` at the output buffer's first doubleword stores there, while
the same instruction at the panic word is excluded by `AmoNoFlagWord`. -/
private theorem amo_store_low (js_m js_sd : SailJoltState) (A V : BitVec 64)
    (hmem : MemRel js_m.jolt_device js_m.sail)
    (hlt : A.toNat < JoltISA.RAM_START_ADDRESS)
    (hflag : ∀ k < 8, IsFlagWord js_m.jolt_device (A.toNat + k) = false)
    (hst : JoltISA.Mmu.store_doubleword A V js_m = .ok (.Ok true) js_sd) :
    memLow js_m.jolt_device ≤ A.toNat ∧ js_sd.vregs = js_m.vregs ∧ js_sd.sail = js_m.sail := by
  have hgeo := IoGeo.of_layout _ hmem.layout
  obtain ⟨-, hc⟩ := (ioHelper% store_effect) js_m js_sd A V hmem hlt hst
  have hf0 := hflag 0 (by norm_num)
  simp only [IsFlagWord, Bool.and_eq_false_iff, decide_eq_false_iff_not, not_le, not_lt,
    Nat.add_zero] at hf0
  obtain ⟨hlow, hla, hlo, hoa, hp, hma, ht, he, hbd, -, -, -, -⟩ := hgeo
  rcases hc with ⟨h1, h2, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, rfl⟩
  · exact ⟨by omega, rfl, rfl⟩
  · exfalso; omega
  · exfalso; omega


/-- A doubleword AMO whose row sequence is `LD`, a pure middle, `SD`, `ADDI` agrees with
Sail's `execute_AMO` on an aligned doubleword in the I/O window.
The middle is any run of rows that writes no memory and leaves a value `res rs2Val D`
in `src`, where `D` is the loaded doubleword; Sail stores that value and returns `D`.
For example, with the middle `ADD new old rs2` at `0x40000008` it stores `rs2 + D`. -/
private theorem io_amo_dword (op : amoop) (hnot_cas : (op == amoop.AMOCAS) = false)
    (rs2 rs1 rd : regidx) (oldReg : JoltISA.VReg) (hold : WritableVReg oldReg)
    (mid : JoltISA.Program → JoltISA.Program) (src : JoltISA.Src)
    (res : BitVec 64 → BitVec 64 → BitVec 64)
    (hres : ∀ rs2Val D : BitVec 64,
      AtomicFamily.amoDwordSailResult op
        (show BitVec (8 * 8) from trunc (m := (((8 : Nat) : Int) * (8 : Int)).toNat) rs2Val)
        (BitVec.setWidth (8 * 8) D) = res rs2Val D)
    (js gp : SailJoltState)
    (hmiddle : ∀ (rs2Val D : BitVec 64) (js_l : SailJoltState),
      rX_bits rs2 js.sail = .ok rs2Val js.sail → js_l.sail = js.sail → js_l.vregs oldReg = D →
      ∃ js_m : SailJoltState,
        (∀ tail, (JoltISA.execProgram (mid tail)).run js_l =
          (JoltISA.execProgram tail).run js_m) ∧
        js_m.sail = js_l.sail ∧ js_m.vregs oldReg = D ∧
        JoltISA.readSrc src js_m = .ok (res rs2Val D) js_m)
    (hNS : (bundleHelper% NoStoreProgram) (mid (.done RETIRE_SUCCESS)))
    (hinv : Step.StepInvariant js.sail) (hlink : System.systemProject js = js.sail)
    (hmstatus : js.vregs mstatusVReg &&& ~~~(0x88 : BitVec 64) = 0)
    (hmem : MemRel js.jolt_device js.sail)
    (hpma : js.sail.regs.get? Register.pma_regions = some platformPma)
    (hhtif : js.sail.regs.get? Register.htif_tohost_base = some none)
    (hlt : (JoltISA.sourceValue (.xreg rs1) js).toNat < JoltISA.RAM_START_ADDRESS)
    (hflag : ∀ k < 8,
      IsFlagWord js.jolt_device ((JoltISA.sourceValue (.xreg rs1) js).toNat + k) = false)
    (hproj : Projection.ProjectedVRegsPreserved js gp)
    (hrun : (JoltISA.execProgram
      (.instr (JoltISA.Encoded.LD .amo (.vreg oldReg) (.xreg rs1) 0) <|
        mid <|
        .instr (JoltISA.Encoded.SD (.xreg rs1) src 0) <|
        .instr (JoltISA.Encoded.ADDI (JoltISA.amoDstFor rd) (.vreg oldReg) 0) <|
        .done RETIRE_SUCCESS)).run js = .ok RETIRE_SUCCESS gp) :
    ∃ t : SailState, (execute_AMO op false false rs2 rs1 8 rd).run js.sail =
        .ok RETIRE_SUCCESS t ∧
      t.regs = (System.systemProject gp).regs ∧
      (∀ a, RAM_START_ADDRESS ≤ a → Mmu.ram_byte t.mem a = Mmu.ram_byte gp.sail.mem a) ∧
      MemRel gp.jolt_device t := by
  have hr1 := (bundleHelper% source_read) js hinv rs1
  have hr2 := (bundleHelper% source_read) js hinv rs2
  have hrdr := (bundleHelper% source_read) js hinv rd
  have hpriv : Assumptions.CurPrivilegeMachine js.sail := ⟨hinv.machine⟩
  have hmprv := (bundleHelper% mprv_zero) js hlink hmstatus
  generalize JoltISA.sourceValue (.xreg rs1) js = A at hr1 hlt hflag
  generalize JoltISA.sourceValue (.xreg rs2) js = rs2Val at hr2
  obtain ⟨js1, hld, hrest⟩ := JoltISA.execProgram_instr_run_retire_inv _ _ _ _ hrun
  obtain ⟨hal, D, hread, hjs1⟩ := ld_amo_inv oldReg hold rs1 A js js1 hr1 hlt hld
  have hs1 : js1.sail = js.sail := by rw [hjs1]; rfl
  have hv1 : js1.vregs oldReg = D := by rw [hjs1]; simp [stateAfterVRegWrite]
  have hd1 : js1.jolt_device = js.jolt_device := by rw [hjs1]; rfl
  obtain ⟨js_m, hmid, hms, hmo, hsrc⟩ := hmiddle rs2Val D js1 hr2 hs1 hv1
  rw [hmid] at hrest
  have hdev : js_m.jolt_device = js.jolt_device := by
    have := (bundleHelper% noStoreProgram_device) _ hNS js1 js_m RETIRE_SUCCESS
      ((hmid (.done RETIRE_SUCCESS)).trans rfl)
    rw [this, hd1]
  have hsm : js_m.sail = js.sail := hms.trans hs1
  have hmem_m : MemRel js_m.jolt_device js_m.sail := by rw [hdev, hsm]; exact hmem
  obtain ⟨js_sd, hsd, hrest2⟩ := JoltISA.execProgram_instr_run_retire_inv _ _ _ _ hrest
  have hr1m : rX_bits rs1 js_m.sail = .ok A js_m.sail := by rw [hsm]; exact hr1
  obtain ⟨hal7, hst⟩ := sd_amo_inv rs1 src A _ js_m js_sd hr1m hsrc hlt hsd
  have hflag_m : ∀ k < 8, IsFlagWord js_m.jolt_device (A.toNat + k) = false := by
    rw [hdev]; exact hflag
  obtain ⟨hlow, hvsd, hssd⟩ := amo_store_low js_m js_sd A _ hmem_m hlt hflag_m hst
  obtain ⟨hlo40, hhi8⟩ := (ioHelper% store_bounds) js_m js_sd A _ hmem_m hlt hst
  have hmod := (ioHelper% mod_of_and7) A hal7
  have hlow' : memLow js.jolt_device ≤ A.toNat := by rw [hdev] at hlow; exact hlow
  obtain ⟨hb, no, hD⟩ := (ioHelper% io_dword_eq) js A D hmem hmod hlow' hlt hflag hread
  have hnm := (ioHelper% not_mmio_io) js.sail A 8 hlo40 hhtif
  have hatomic := io_atomic_checks js.sail A 8 hpma hlo40 (by norm_num) (by norm_num)
    (by omega) hmod op hnot_cas
  have hsail := io_execute_AMO_dword_non_cas_aligned op rs2 rs1 rd js hpriv hmprv A rs2Val
    (res rs2Val D) hr1 hr2 ⟨_, hrdr⟩ hb hatomic hnm.1 hnm.2 hal7 hnot_cas
    (by simpa only [hD] using hres rs2Val D)
  -- the writeback
  obtain ⟨js_w, hadd, hdone⟩ := JoltISA.execProgram_instr_run_retire_inv _ _ _ _ hrest2
  have hgw : gp = js_w := by
    have : (JoltISA.execProgram (.done RETIRE_SUCCESS)).run js_w = .ok RETIRE_SUCCESS js_w := rfl
    rw [this] at hdone
    exact (EStateM.Result.ok.inj hdone).2.symm
  subst hgw
  have hv_sd : js_sd.vregs oldReg = D := by rw [hvsd]; exact hmo
  obtain ⟨js_w', hadd', hsw'⟩ := AtomicFamily.amo_dword_addi_writeback_old_run_from oldReg rd
    js_sd D hv_sd
  have hww : gp = js_w' := by
    rw [hadd] at hadd'
    exact (EStateM.Result.ok.inj hadd').2
  have hdev_w : gp.jolt_device = js_sd.jolt_device :=
    (bundleHelper% noStoreRow_device) _ (by trivial) js_sd gp RETIRE_SUCCESS hadd
  have hsail_gp : gp.sail = stateAfterWrite js.sail rd D := by
    rw [hww, hsw', hssd, hsm]
  -- the memory
  obtain ⟨hgs, hmemT⟩ := (ioHelper% store_finish) js js_m js_sd
    (state_after_dword_store js.sail A (res rs2Val D)) A (res rs2Val D) A (res rs2Val D) D 8
    hmem hsm hdev (by norm_num) (by omega) (by omega)
    (fun k hk h => by exfalso; apply h; omega)
    (fun k hk => by rw [ite_eq_left (by omega), hmod, Nat.sub_zero]) hlt hst
    ((ioHelper% sailStore_dword) js.sail A _)
    (fun h => by
      exfalso
      have hf0 := hflag 0 (by norm_num)
      have hg := IoGeo.of_layout _ hmem.layout
      obtain ⟨-, -, -, -, hp, -, ht, he, -, -, -, -, -⟩ := hg
      simp only [IsFlagWord, Bool.and_eq_false_iff, decide_eq_false_iff_not, not_le,
        not_lt, Nat.add_zero] at hf0
      omega)
  have hsst := (ioHelper% sailStore_dword) js.sail A (res rs2Val D)
  refine ⟨AtomicFamily.amoDwordFinalSailState rd js.sail A (res rs2Val D) D, ?_, ?_, ?_, ?_⟩
  · simpa only [hD] using hsail
  · rw [(Projection.systemProject_stateAfterWrite_of_projected_vregs_preserved js gp rd D
      hsail_gp hproj), hlink]
    change wX_update_regs rd _ _ = wX_update_regs rd _ _
    rw [hsst.1]
  · intro a ha
    rw [hsail_gp]
    simp only [AtomicFamily.amoDwordFinalSailState, stateAfterWrite, Mmu.ram_byte]
    rw [hsst.2 a, ite_eq_right]
    simp only [JoltISA.RAM_START_ADDRESS, RAM_START_ADDRESS] at ha hhi8
    omega
  · rw [hdev_w]
    exact hmemT.of_mem_eq rfl


/-- The state facts every I/O AMO core takes: the step invariant, the link between Sail's
state and Jolt's, the platform registers, the memory relation, and that the doubleword
at `a` is in the I/O window and holds no flag byte.
For example, for `AMOADD.D` through `0x40000010`, `a` is `0x40000010`. -/
structure IoAmoCtx (js : SailJoltState) (a : BitVec 64) : Prop where
  inv : Step.StepInvariant js.sail
  link : System.systemProject js = js.sail
  mstatus : js.vregs mstatusVReg &&& ~~~(0x88 : BitVec 64) = 0
  mem : MemRel js.jolt_device js.sail
  pma : js.sail.regs.get? Register.pma_regions = some platformPma
  htif : js.sail.regs.get? Register.htif_tohost_base = some none
  lt : a.toNat < JoltISA.RAM_START_ADDRESS
  flag : ∀ k < 8, IsFlagWord js.jolt_device (a.toNat + k) = false

/-- What one AMO must achieve on the I/O window: Sail's `execute_AMO` retires to a state
whose registers are the projection of Jolt's, whose RAM is Jolt's and whose memory
satisfies the memory relation with Jolt's device.
For example, for `AMOADD.D` at `0x40000008` the new memory holds the sum there. -/
def IoAmoEffect (op : amoop) (w : Nat) (rs2 rs1 rd : regidx) (js gp : SailJoltState) : Prop :=
  ∃ t : SailState, (execute_AMO op false false rs2 rs1 w rd).run js.sail =
      .ok RETIRE_SUCCESS t ∧
    t.regs = (System.systemProject gp).regs ∧
    (∀ a, RAM_START_ADDRESS ≤ a → Mmu.ram_byte t.mem a = Mmu.ram_byte gp.sail.mem a) ∧
    MemRel gp.jolt_device t

private theorem binop_old_writable (rd : regidx) :
    WritableVReg (JoltISA.amoDoubleBinopOldVRegFor rd) := by
  unfold JoltISA.amoDoubleBinopOldVRegFor JoltISA.amoVRegFor WritableVReg
  split <;> decide

private theorem binop_new_writable (rd : regidx) :
    WritableVReg (JoltISA.amoDoubleBinopNewVRegFor rd) := by
  unfold JoltISA.amoDoubleBinopNewVRegFor JoltISA.amoVRegFor WritableVReg
  split <;> decide

private theorem binop_old_ne_new (rd : regidx) :
    JoltISA.amoDoubleBinopOldVRegFor rd ≠ JoltISA.amoDoubleBinopNewVRegFor rd := by
  unfold JoltISA.amoDoubleBinopOldVRegFor JoltISA.amoDoubleBinopNewVRegFor
    JoltISA.amoVRegFor
  split <;> decide

/-- The doubleword AMOs that combine the memory value and `rs2` in one row (ADD, XOR,
AND, OR) agree with Sail on an aligned doubleword in the I/O window.
For example, `AMOADD.D` at `0x40000008` stores `rs2 + D` there and returns `D`. -/
private theorem io_amo_dword_binop (op : amoop) (hnot_cas : (op == amoop.AMOCAS) = false)
    (binop : JoltISA.Dst → JoltISA.Src → JoltISA.Src → JoltISA.Instr)
    (res : BitVec 64 → BitVec 64 → BitVec 64)
    (hres : ∀ rs2Val D : BitVec 64,
      AtomicFamily.amoDwordSailResult op
        (show BitVec (8 * 8) from trunc (m := (((8 : Nat) : Int) * (8 : Int)).toNat) rs2Val)
        (BitVec.setWidth (8 * 8) D) = res rs2Val D)
    (hNSb : ∀ d l r, (bundleHelper% NoStoreRow) (binop d l r))
    (hbin : ∀ (rs2 : regidx) (js : SailJoltState) (rs2Val old : BitVec 64),
      rX_bits rs2 js.sail = .ok rs2Val js.sail →
      ∀ oldReg newReg : JoltISA.VReg, WritableVReg newReg → oldReg ≠ newReg →
        ∀ js_l : SailJoltState, js_l.sail = js.sail → js_l.vregs oldReg = old →
          ∃ js_m : SailJoltState,
            AtomicFamily.AmoDwordMiddleStepInto newReg oldReg
              (binop (.vreg newReg) (.vreg oldReg) (.xreg rs2)) old (res rs2Val old) js_l js_m)
    (rs2 rs1 rd : regidx) (js gp : SailJoltState)
    (hc : IoAmoCtx js (JoltISA.sourceValue (.xreg rs1) js))
    (hproj : Projection.ProjectedVRegsPreserved js gp)
    (hrun : (JoltISA.execProgram (JoltISA.amoDoubleBinopProgram binop rs2 rs1 rd)).run js =
      .ok RETIRE_SUCCESS gp) :
    IoAmoEffect op 8 rs2 rs1 rd js gp := by
  refine io_amo_dword op hnot_cas rs2 rs1 rd (JoltISA.amoDoubleBinopOldVRegFor rd)
    (binop_old_writable rd)
    (fun tail => .instr (binop (.vreg (JoltISA.amoDoubleBinopNewVRegFor rd))
      (.vreg (JoltISA.amoDoubleBinopOldVRegFor rd)) (.xreg rs2)) tail)
    (.vreg (JoltISA.amoDoubleBinopNewVRegFor rd)) res hres js gp ?_ ⟨hNSb _ _ _, trivial⟩
    hc.inv hc.link hc.mstatus hc.mem hc.pma hc.htif hc.lt hc.flag hproj hrun
  intro rs2Val D js_l hrs2 hsail hold
  obtain ⟨js_m, hm⟩ := hbin rs2 js rs2Val D hrs2 _ _ (binop_new_writable rd)
    (binop_old_ne_new rd) js_l hsail hold
  refine ⟨js_m, fun tail => ?_, hm.sail, hm.old_vreg, ?_⟩
  · exact JoltISA.execProgram_instr_run_retire _ _ _ _ hm.run
  · rw [readSrc_vreg, hm.result_vreg]

/-- The doubleword min/max AMOs (signed and unsigned) agree with Sail on an aligned
doubleword in the I/O window.
For example, `AMOMINU.D` at `0x40000008` stores the smaller of `rs2` and `D` there and
returns `D`. -/
private theorem io_amo_dword_select (op : amoop) (hnot_cas : (op == amoop.AMOCAS) = false)
    (cmp : JoltISA.Dst → JoltISA.Src → JoltISA.Src → JoltISA.Instr)
    (lhs rhs : regidx → regidx → JoltISA.Src)
    (res : BitVec 64 → BitVec 64 → BitVec 64)
    (hres : ∀ rs2Val D : BitVec 64,
      AtomicFamily.amoDwordSailResult op
        (show BitVec (8 * 8) from trunc (m := (((8 : Nat) : Int) * (8 : Int)).toNat) rs2Val)
        (BitVec.setWidth (8 * 8) D) = res rs2Val D)
    (hNSc : ∀ d l r, (bundleHelper% NoStoreRow) (cmp d l r))
    (hsel : ∀ (rd rs2 : regidx) (js : SailJoltState) (rs2Val old : BitVec 64),
      rX_bits rs2 js.sail = .ok rs2Val js.sail →
      ∀ js_l : SailJoltState, js_l.sail = js.sail →
        js_l.vregs (JoltISA.amoOldVRegFor rd) = old →
        ∃ js_m : SailJoltState,
          AtomicFamily.AmoDwordSelectMiddleStepInto
            (JoltISA.amoNewVRegFor rd) (JoltISA.amoTmpVRegFor rd) (JoltISA.amoOldVRegFor rd)
            cmp (lhs rs2 rd) (rhs rs2 rd) rs2 old (res rs2Val old) js_l js_m)
    (rs2 rs1 rd : regidx) (js gp : SailJoltState)
    (hc : IoAmoCtx js (JoltISA.sourceValue (.xreg rs1) js))
    (hproj : Projection.ProjectedVRegsPreserved js gp)
    (hrun : (JoltISA.execProgram
      (JoltISA.amoDoubleSelectProgram cmp (lhs rs2 rd) (rhs rs2 rd) rs2 rs1 rd)).run js =
      .ok RETIRE_SUCCESS gp) :
    IoAmoEffect op 8 rs2 rs1 rd js gp := by
  refine io_amo_dword op hnot_cas rs2 rs1 rd (JoltISA.amoOldVRegFor rd)
    (JoltISA.amoOldVRegFor_writable rd)
    (fun tail => AtomicFamily.amoDwordSelectMiddleProgramInto
      (JoltISA.amoNewVRegFor rd) (JoltISA.amoTmpVRegFor rd) (JoltISA.amoOldVRegFor rd)
      cmp (lhs rs2 rd) (rhs rs2 rd) rs2 tail)
    (.vreg (JoltISA.amoNewVRegFor rd)) res hres js gp ?_ ?_
    hc.inv hc.link hc.mstatus hc.mem hc.pma hc.htif hc.lt hc.flag hproj hrun
  · intro rs2Val D js_l hrs2 hsail hold
    obtain ⟨js_m, hm⟩ := hsel rd rs2 js rs2Val D hrs2 js_l hsail hold
    refine ⟨js_m, hm.run, hm.sail, hm.old_vreg, ?_⟩
    rw [readSrc_vreg, hm.result_vreg]
  · unfold AtomicFamily.amoDwordSelectMiddleProgramInto
      AtomicFamily.amoDwordSelectComparePhaseInto AtomicFamily.amoDwordSelectTailPhaseInto
    exact ⟨hNSc _ _ _, trivial, trivial, trivial, trivial⟩

/-- `AMOSWAP.D` agrees with Sail on an aligned doubleword in the I/O window.
For example, at `0x40000008` it stores `rs2` there and returns `D`. -/
private theorem io_amo_dword_swap (rs2 rs1 rd : regidx) (js gp : SailJoltState)
    (hc : IoAmoCtx js (JoltISA.sourceValue (.xreg rs1) js))
    (hproj : Projection.ProjectedVRegsPreserved js gp)
    (hrun : (JoltISA.execProgram
      (.instr (JoltISA.Encoded.LD .amo (.vreg (JoltISA.amoOldVRegFor rd)) (.xreg rs1) 0) <|
        .instr (JoltISA.Encoded.SD (.xreg rs1) (.xreg rs2) 0) <|
        .instr (JoltISA.Encoded.ADDI (JoltISA.amoDstFor rd) (.vreg (JoltISA.amoOldVRegFor rd)) 0)
          <| .done RETIRE_SUCCESS)).run js = .ok RETIRE_SUCCESS gp) :
    IoAmoEffect amoop.AMOSWAP 8 rs2 rs1 rd js gp := by
  refine io_amo_dword amoop.AMOSWAP (by decide) rs2 rs1 rd (JoltISA.amoOldVRegFor rd)
    (JoltISA.amoOldVRegFor_writable rd) (fun tail => tail) (.xreg rs2) (fun v _ => v)
    (fun v D => by unfold AtomicFamily.amoDwordSailResult; unfold trunc Sail.BitVec.truncate; rfl)
    js gp ?_ trivial hc.inv hc.link hc.mstatus hc.mem hc.pma hc.htif hc.lt hc.flag hproj hrun
  intro rs2Val D js_l hrs2 hsail hold
  refine ⟨js_l, fun tail => rfl, rfl, hold, ?_⟩
  cases js_l
  dsimp only at hsail
  subst hsail
  simp only [JoltISA.readSrc, liftSail, hrs2]


/-- `AMOADD.D` agrees with Sail on an aligned doubleword in the I/O window.
For example, at `0x40000008` it stores `rs2 + old` there, where `old` is the doubleword read, and returns `old`. -/
private theorem io_amoadd_d (rs2 rs1 rd : regidx) (js gp : SailJoltState)
    (hc : IoAmoCtx js (JoltISA.sourceValue (.xreg rs1) js))
    (hrun : (JoltISA.execProgram (JoltISA.amoadddProgramAuto rd rs1 rs2)).run js =
      .ok RETIRE_SUCCESS gp) :
    IoAmoEffect amoop.AMOADD 8 rs2 rs1 rd js gp := by
  have hproj := Projection.execProgram_preserves_projected_vregs_of_no_protected_writes
    (AtomicFamily.amoadddProgram_doesNotWriteProtectedVRegs rs2 rs1 rd) hrun
  have hcore : JoltISA.amoadddProgramAuto rd rs1 rs2 =
      JoltISA.amoDoubleBinopProgram (fun dst lhs rhs => .ADD dst lhs rhs) rs2 rs1 rd := by
    cases hrd : JoltISA.isX0 rd <;>
      simp only [JoltISA.amoadddProgramAuto, JoltISA.amoDoubleBinopProgram, JoltISA.amoDoubleBinopOldVRegFor, JoltISA.amoDoubleBinopNewVRegFor, JoltISA.amoVRegFor, JoltISA.amoDstFor, JoltISA.sideEffectingRdZeroDst, JoltISA.rdZeroRewriteVReg, hrd, Bool.false_eq_true, ite_false, ite_true] <;> rfl
  rw [hcore] at hrun
  exact io_amo_dword_binop amoop.AMOADD (by decide)
    (fun dst lhs rhs => .ADD dst lhs rhs) (fun rs2Val D => rs2Val + D)
    AtomicFamily.amoaddd_sail_result (fun _ _ _ => trivial)
    (fun rs2 js rs2Val old h oldReg newReg hn hne js_l hs ho =>
      AtomicFamily.amo_dword_add_middle_after_load_into rs2 js 0 rs2Val old h oldReg newReg hn
        hne js_l hs ho)
    rs2 rs1 rd js gp hc hproj hrun

/-- `AMOXOR.D` agrees with Sail on an aligned doubleword in the I/O window.
For example, at `0x40000008` it stores `rs2 ^^^ old` there, where `old` is the doubleword read, and returns `old`. -/
private theorem io_amoxor_d (rs2 rs1 rd : regidx) (js gp : SailJoltState)
    (hc : IoAmoCtx js (JoltISA.sourceValue (.xreg rs1) js))
    (hrun : (JoltISA.execProgram (JoltISA.amoxordProgramAuto rd rs1 rs2)).run js =
      .ok RETIRE_SUCCESS gp) :
    IoAmoEffect amoop.AMOXOR 8 rs2 rs1 rd js gp := by
  have hproj := Projection.execProgram_preserves_projected_vregs_of_no_protected_writes
    (AtomicFamily.amoxordProgram_doesNotWriteProtectedVRegs rs2 rs1 rd) hrun
  have hcore : JoltISA.amoxordProgramAuto rd rs1 rs2 =
      JoltISA.amoDoubleBinopProgram (fun dst lhs rhs => .XOR dst lhs rhs) rs2 rs1 rd := by
    cases hrd : JoltISA.isX0 rd <;>
      simp only [JoltISA.amoxordProgramAuto, JoltISA.amoDoubleBinopProgram, JoltISA.amoDoubleBinopOldVRegFor, JoltISA.amoDoubleBinopNewVRegFor, JoltISA.amoVRegFor, JoltISA.amoDstFor, JoltISA.sideEffectingRdZeroDst, JoltISA.rdZeroRewriteVReg, hrd, Bool.false_eq_true, ite_false, ite_true] <;> rfl
  rw [hcore] at hrun
  exact io_amo_dword_binop amoop.AMOXOR (by decide)
    (fun dst lhs rhs => .XOR dst lhs rhs) (fun rs2Val D => rs2Val ^^^ D)
    AtomicFamily.amoxord_sail_result (fun _ _ _ => trivial)
    (fun rs2 js rs2Val old h oldReg newReg hn hne js_l hs ho =>
      AtomicFamily.amo_dword_xor_middle_after_load_into rs2 js 0 rs2Val old h oldReg newReg hn
        hne js_l hs ho)
    rs2 rs1 rd js gp hc hproj hrun

/-- `AMOAND.D` agrees with Sail on an aligned doubleword in the I/O window.
For example, at `0x40000008` it stores `rs2 &&& old` there, where `old` is the doubleword read, and returns `old`. -/
private theorem io_amoand_d (rs2 rs1 rd : regidx) (js gp : SailJoltState)
    (hc : IoAmoCtx js (JoltISA.sourceValue (.xreg rs1) js))
    (hrun : (JoltISA.execProgram (JoltISA.amoanddProgramAuto rd rs1 rs2)).run js =
      .ok RETIRE_SUCCESS gp) :
    IoAmoEffect amoop.AMOAND 8 rs2 rs1 rd js gp := by
  have hproj := Projection.execProgram_preserves_projected_vregs_of_no_protected_writes
    (AtomicFamily.amoanddProgram_doesNotWriteProtectedVRegs rs2 rs1 rd) hrun
  have hcore : JoltISA.amoanddProgramAuto rd rs1 rs2 =
      JoltISA.amoDoubleBinopProgram (fun dst lhs rhs => .AND dst lhs rhs) rs2 rs1 rd := by
    cases hrd : JoltISA.isX0 rd <;>
      simp only [JoltISA.amoanddProgramAuto, JoltISA.amoDoubleBinopProgram, JoltISA.amoDoubleBinopOldVRegFor, JoltISA.amoDoubleBinopNewVRegFor, JoltISA.amoVRegFor, JoltISA.amoDstFor, JoltISA.sideEffectingRdZeroDst, JoltISA.rdZeroRewriteVReg, hrd, Bool.false_eq_true, ite_false, ite_true] <;> rfl
  rw [hcore] at hrun
  exact io_amo_dword_binop amoop.AMOAND (by decide)
    (fun dst lhs rhs => .AND dst lhs rhs) (fun rs2Val D => rs2Val &&& D)
    AtomicFamily.amoandd_sail_result (fun _ _ _ => trivial)
    (fun rs2 js rs2Val old h oldReg newReg hn hne js_l hs ho =>
      AtomicFamily.amo_dword_and_middle_after_load_into rs2 js 0 rs2Val old h oldReg newReg hn
        hne js_l hs ho)
    rs2 rs1 rd js gp hc hproj hrun

/-- `AMOOR.D` agrees with Sail on an aligned doubleword in the I/O window.
For example, at `0x40000008` it stores `rs2 ||| old` there, where `old` is the doubleword read, and returns `old`. -/
private theorem io_amoor_d (rs2 rs1 rd : regidx) (js gp : SailJoltState)
    (hc : IoAmoCtx js (JoltISA.sourceValue (.xreg rs1) js))
    (hrun : (JoltISA.execProgram (JoltISA.amoordProgramAuto rd rs1 rs2)).run js =
      .ok RETIRE_SUCCESS gp) :
    IoAmoEffect amoop.AMOOR 8 rs2 rs1 rd js gp := by
  have hproj := Projection.execProgram_preserves_projected_vregs_of_no_protected_writes
    (AtomicFamily.amoordProgram_doesNotWriteProtectedVRegs rs2 rs1 rd) hrun
  have hcore : JoltISA.amoordProgramAuto rd rs1 rs2 =
      JoltISA.amoDoubleBinopProgram (fun dst lhs rhs => .OR dst lhs rhs) rs2 rs1 rd := by
    cases hrd : JoltISA.isX0 rd <;>
      simp only [JoltISA.amoordProgramAuto, JoltISA.amoDoubleBinopProgram, JoltISA.amoDoubleBinopOldVRegFor, JoltISA.amoDoubleBinopNewVRegFor, JoltISA.amoVRegFor, JoltISA.amoDstFor, JoltISA.sideEffectingRdZeroDst, JoltISA.rdZeroRewriteVReg, hrd, Bool.false_eq_true, ite_false, ite_true] <;> rfl
  rw [hcore] at hrun
  exact io_amo_dword_binop amoop.AMOOR (by decide)
    (fun dst lhs rhs => .OR dst lhs rhs) (fun rs2Val D => rs2Val ||| D)
    AtomicFamily.amoord_sail_result (fun _ _ _ => trivial)
    (fun rs2 js rs2Val old h oldReg newReg hn hne js_l hs ho =>
      AtomicFamily.amo_dword_or_middle_after_load_into rs2 js 0 rs2Val old h oldReg newReg hn
        hne js_l hs ho)
    rs2 rs1 rd js gp hc hproj hrun

/-- `AMOMIN.D` agrees with Sail on an aligned doubleword in the I/O window.
For example, at `0x40000008` it stores the signed minimum of `rs2` and `old` there, where `old` is the doubleword read, and returns `old`. -/
private theorem io_amomin_d (rs2 rs1 rd : regidx) (js gp : SailJoltState)
    (hc : IoAmoCtx js (JoltISA.sourceValue (.xreg rs1) js))
    (hrun : (JoltISA.execProgram (JoltISA.amomindProgramAuto rd rs1 rs2)).run js =
      .ok RETIRE_SUCCESS gp) :
    IoAmoEffect amoop.AMOMIN 8 rs2 rs1 rd js gp := by
  have hproj := Projection.execProgram_preserves_projected_vregs_of_no_protected_writes
    (AtomicFamily.amomindProgram_doesNotWriteProtectedVRegs rs2 rs1 rd) hrun
  have hcore : JoltISA.amomindProgramAuto rd rs1 rs2 =
      JoltISA.amoDoubleSelectProgram (fun dst lhs rhs => .SLT dst lhs rhs)
        (.xreg rs2) (.vreg (JoltISA.amoOldVRegFor rd)) rs2 rs1 rd := by
    cases hrd : JoltISA.isX0 rd <;>
      simp only [JoltISA.amomindProgramAuto, JoltISA.amoDoubleSelectProgram, JoltISA.amoOldVRegFor, JoltISA.amoNewVRegFor, JoltISA.amoTmpVRegFor, JoltISA.amoVRegFor, JoltISA.amoDstFor, JoltISA.sideEffectingRdZeroDst, JoltISA.rdZeroRewriteVReg, hrd, Bool.false_eq_true, ite_false, ite_true] <;> rfl
  rw [hcore] at hrun
  exact io_amo_dword_select amoop.AMOMIN (by decide) (fun dst lhs rhs => .SLT dst lhs rhs)
    (fun rs2 _ => .xreg rs2) (fun _ rd => .vreg (JoltISA.amoOldVRegFor rd))
    (fun rs2Val D => if (zopz0zI_s rs2Val D : Bool) then rs2Val else D)
    AtomicFamily.amomind_sail_result (fun _ _ _ => trivial)
    (fun rd rs2 js rs2Val old h js_l hs ho =>
      AtomicFamily.amo_dword_min_middle_after_load_for rd rs2 js 0 rs2Val old h js_l hs ho)
    rs2 rs1 rd js gp hc hproj hrun

/-- `AMOMAX.D` agrees with Sail on an aligned doubleword in the I/O window.
For example, at `0x40000008` it stores the signed maximum of `rs2` and `old` there, where `old` is the doubleword read, and returns `old`. -/
private theorem io_amomax_d (rs2 rs1 rd : regidx) (js gp : SailJoltState)
    (hc : IoAmoCtx js (JoltISA.sourceValue (.xreg rs1) js))
    (hrun : (JoltISA.execProgram (JoltISA.amomaxdProgramAuto rd rs1 rs2)).run js =
      .ok RETIRE_SUCCESS gp) :
    IoAmoEffect amoop.AMOMAX 8 rs2 rs1 rd js gp := by
  have hproj := Projection.execProgram_preserves_projected_vregs_of_no_protected_writes
    (AtomicFamily.amomaxdProgram_doesNotWriteProtectedVRegs rs2 rs1 rd) hrun
  have hcore : JoltISA.amomaxdProgramAuto rd rs1 rs2 =
      JoltISA.amoDoubleSelectProgram (fun dst lhs rhs => .SLT dst lhs rhs)
        (.vreg (JoltISA.amoOldVRegFor rd)) (.xreg rs2) rs2 rs1 rd := by
    cases hrd : JoltISA.isX0 rd <;>
      simp only [JoltISA.amomaxdProgramAuto, JoltISA.amoDoubleSelectProgram, JoltISA.amoOldVRegFor, JoltISA.amoNewVRegFor, JoltISA.amoTmpVRegFor, JoltISA.amoVRegFor, JoltISA.amoDstFor, JoltISA.sideEffectingRdZeroDst, JoltISA.rdZeroRewriteVReg, hrd, Bool.false_eq_true, ite_false, ite_true] <;> rfl
  rw [hcore] at hrun
  exact io_amo_dword_select amoop.AMOMAX (by decide) (fun dst lhs rhs => .SLT dst lhs rhs)
    (fun _ rd => .vreg (JoltISA.amoOldVRegFor rd)) (fun rs2 _ => .xreg rs2)
    (fun rs2Val D => if (zopz0zK_s rs2Val D : Bool) then rs2Val else D)
    AtomicFamily.amomaxd_sail_result (fun _ _ _ => trivial)
    (fun rd rs2 js rs2Val old h js_l hs ho =>
      AtomicFamily.amo_dword_max_middle_after_load_for rd rs2 js 0 rs2Val old h js_l hs ho)
    rs2 rs1 rd js gp hc hproj hrun

/-- `AMOMINU.D` agrees with Sail on an aligned doubleword in the I/O window.
For example, at `0x40000008` it stores the unsigned minimum of `rs2` and `old` there, where `old` is the doubleword read, and returns `old`. -/
private theorem io_amominu_d (rs2 rs1 rd : regidx) (js gp : SailJoltState)
    (hc : IoAmoCtx js (JoltISA.sourceValue (.xreg rs1) js))
    (hrun : (JoltISA.execProgram (JoltISA.amominudProgramAuto rd rs1 rs2)).run js =
      .ok RETIRE_SUCCESS gp) :
    IoAmoEffect amoop.AMOMINU 8 rs2 rs1 rd js gp := by
  have hproj := Projection.execProgram_preserves_projected_vregs_of_no_protected_writes
    (AtomicFamily.amominudProgram_doesNotWriteProtectedVRegs rs2 rs1 rd) hrun
  have hcore : JoltISA.amominudProgramAuto rd rs1 rs2 =
      JoltISA.amoDoubleSelectProgram (fun dst lhs rhs => .SLTU dst lhs rhs)
        (.xreg rs2) (.vreg (JoltISA.amoOldVRegFor rd)) rs2 rs1 rd := by
    cases hrd : JoltISA.isX0 rd <;>
      simp only [JoltISA.amominudProgramAuto, JoltISA.amoDoubleSelectProgram, JoltISA.amoOldVRegFor, JoltISA.amoNewVRegFor, JoltISA.amoTmpVRegFor, JoltISA.amoVRegFor, JoltISA.amoDstFor, JoltISA.sideEffectingRdZeroDst, JoltISA.rdZeroRewriteVReg, hrd, Bool.false_eq_true, ite_false, ite_true] <;> rfl
  rw [hcore] at hrun
  exact io_amo_dword_select amoop.AMOMINU (by decide) (fun dst lhs rhs => .SLTU dst lhs rhs)
    (fun rs2 _ => .xreg rs2) (fun _ rd => .vreg (JoltISA.amoOldVRegFor rd))
    (fun rs2Val D => if (zopz0zI_u rs2Val D : Bool) then rs2Val else D)
    AtomicFamily.amominud_sail_result (fun _ _ _ => trivial)
    (fun rd rs2 js rs2Val old h js_l hs ho =>
      AtomicFamily.amo_dword_minu_middle_after_load_for rd rs2 js 0 rs2Val old h js_l hs ho)
    rs2 rs1 rd js gp hc hproj hrun

/-- `AMOMAXU.D` agrees with Sail on an aligned doubleword in the I/O window.
For example, at `0x40000008` it stores the unsigned maximum of `rs2` and `old` there, where `old` is the doubleword read, and returns `old`. -/
private theorem io_amomaxu_d (rs2 rs1 rd : regidx) (js gp : SailJoltState)
    (hc : IoAmoCtx js (JoltISA.sourceValue (.xreg rs1) js))
    (hrun : (JoltISA.execProgram (JoltISA.amomaxudProgramAuto rd rs1 rs2)).run js =
      .ok RETIRE_SUCCESS gp) :
    IoAmoEffect amoop.AMOMAXU 8 rs2 rs1 rd js gp := by
  have hproj := Projection.execProgram_preserves_projected_vregs_of_no_protected_writes
    (AtomicFamily.amomaxudProgram_doesNotWriteProtectedVRegs rs2 rs1 rd) hrun
  have hcore : JoltISA.amomaxudProgramAuto rd rs1 rs2 =
      JoltISA.amoDoubleSelectProgram (fun dst lhs rhs => .SLTU dst lhs rhs)
        (.vreg (JoltISA.amoOldVRegFor rd)) (.xreg rs2) rs2 rs1 rd := by
    cases hrd : JoltISA.isX0 rd <;>
      simp only [JoltISA.amomaxudProgramAuto, JoltISA.amoDoubleSelectProgram, JoltISA.amoOldVRegFor, JoltISA.amoNewVRegFor, JoltISA.amoTmpVRegFor, JoltISA.amoVRegFor, JoltISA.amoDstFor, JoltISA.sideEffectingRdZeroDst, JoltISA.rdZeroRewriteVReg, hrd, Bool.false_eq_true, ite_false, ite_true] <;> rfl
  rw [hcore] at hrun
  exact io_amo_dword_select amoop.AMOMAXU (by decide) (fun dst lhs rhs => .SLTU dst lhs rhs)
    (fun _ rd => .vreg (JoltISA.amoOldVRegFor rd)) (fun rs2 _ => .xreg rs2)
    (fun rs2Val D => if (zopz0zK_u rs2Val D : Bool) then rs2Val else D)
    AtomicFamily.amomaxud_sail_result (fun _ _ _ => trivial)
    (fun rd rs2 js rs2Val old h js_l hs ho =>
      AtomicFamily.amo_dword_maxu_middle_after_load_for rd rs2 js 0 rs2Val old h js_l hs ho)
    rs2 rs1 rd js gp hc hproj hrun

/-- `AMOSWAP.D` agrees with Sail on an aligned doubleword in the I/O window.
For example, at `0x40000008` it stores `rs2` there, where `old` is the doubleword read, and returns `old`. -/
private theorem io_amoswap_d (rs2 rs1 rd : regidx) (js gp : SailJoltState)
    (hc : IoAmoCtx js (JoltISA.sourceValue (.xreg rs1) js))
    (hrun : (JoltISA.execProgram (JoltISA.amoswapdProgramAuto rd rs1 rs2)).run js =
      .ok RETIRE_SUCCESS gp) :
    IoAmoEffect amoop.AMOSWAP 8 rs2 rs1 rd js gp := by
  have hproj := Projection.execProgram_preserves_projected_vregs_of_no_protected_writes
    (AtomicFamily.amoswapdProgram_doesNotWriteProtectedVRegs rs2 rs1 rd) hrun
  have hcore : JoltISA.amoswapdProgramAuto rd rs1 rs2 =
      (.instr (JoltISA.Encoded.LD .amo (.vreg (JoltISA.amoOldVRegFor rd)) (.xreg rs1) 0) <|
        .instr (JoltISA.Encoded.SD (.xreg rs1) (.xreg rs2) 0) <|
        .instr (JoltISA.Encoded.ADDI (JoltISA.amoDstFor rd) (.vreg (JoltISA.amoOldVRegFor rd)) 0)
          <| .done RETIRE_SUCCESS) := by
    cases hrd : JoltISA.isX0 rd <;>
      simp only [JoltISA.amoswapdProgramAuto, JoltISA.amoOldVRegFor, JoltISA.amoVRegFor, JoltISA.amoDstFor, JoltISA.sideEffectingRdZeroDst, JoltISA.rdZeroRewriteVReg, hrd, Bool.false_eq_true, ite_false, ite_true] <;> rfl
  rw [hcore] at hrun
  exact io_amo_dword_swap rs2 rs1 rd js gp hc hproj hrun

/-! ### Jolt's word rows -/

/-- A word AMO whose rows are the shared lane window around a pure middle agrees with
Sail's `execute_AMO` on a word in the I/O window.
The window loads the containing doubleword, extracts the old word, runs a middle that writes
no memory and leaves a value `res rs2Val oldWord` in `source`, then splices the low word of
that value into the doubleword and stores it. Sail stores the low word and returns the old
word.
For example, `AMOADD.W` at `0x40000004` stores `rs2 + old` in the upper word of the
doubleword at `0x40000000` and returns the old upper word. -/
private theorem io_amo_word (op : amoop) (hnot_cas : (op == amoop.AMOCAS) = false)
    (rs2 rs1 rd : regidx) (middle : JoltISA.Program) (source : JoltISA.Src)
    (res : BitVec 64 → BitVec 32 → BitVec 64)
    (hres : ∀ (rs2Val : BitVec 64) (ow : BitVec 32),
      (Sail.BitVec.extractLsb (res rs2Val ow) 31 0 : BitVec 32) =
        AtomicFamily.amoWordSailResult op (Sail.BitVec.extractLsb rs2Val 31 0) ow)
    (js gp : SailJoltState)
    (hmiddle : ∀ (addr rs2Val D : BitVec 64) (pre : SailJoltState),
      rX_bits rs1 js.sail = .ok addr js.sail → rX_bits rs2 js.sail = .ok rs2Val js.sail →
      pre.sail = js.sail →
      pre.vregs (JoltISA.amoWordDwordVRegFor rd) = D →
      pre.vregs (JoltISA.amoWordLaneVRegFor rd) = AtomicFamily.amoWordLaneMask addr →
      pre.vregs (JoltISA.amoWordOldVRegFor rd) = sign_extend (m := 64)
        (word_of_dword D (addr &&& (7 : BitVec 64)).toNat) →
      ∃ after, AtomicFamily.AmoWordWindowStep rd middle source
        (word_of_dword D (addr &&& (7 : BitVec 64)).toNat) D (AtomicFamily.amoWordLaneMask addr)
        (res rs2Val (word_of_dword D (addr &&& (7 : BitVec 64)).toNat)) pre after)
    (hNS : (bundleHelper% NoStoreProgram) middle)
    (hc : IoAmoCtx js (amoWordBase (JoltISA.sourceValue (.xreg rs1) js)))
    (hproj : Projection.ProjectedVRegsPreserved js gp)
    (hrun : (JoltISA.execProgram (AtomicFamily.amoWordWindowProgram middle source rs1 rd)).run
      js = .ok RETIRE_SUCCESS gp) :
    IoAmoEffect op 4 rs2 rs1 rd js gp := by
  obtain ⟨hinv, hlink, hmstatus, hmem, hpma, hhtif, hlt, hflag⟩ := hc
  have hr1 := (bundleHelper% source_read) js hinv rs1
  have hr2 := (bundleHelper% source_read) js hinv rs2
  have hrdr := (bundleHelper% source_read) js hinv rd
  have hpriv : Assumptions.CurPrivilegeMachine js.sail := ⟨hinv.machine⟩
  have hmprv := (bundleHelper% mprv_zero) js hlink hmstatus
  generalize JoltISA.sourceValue (.xreg rs1) js = addr at hr1 hlt hflag
  generalize JoltISA.sourceValue (.xreg rs2) js = rs2Val at hr2
  have hregs : WritableVReg (JoltISA.amoWordDwordVRegFor rd) ∧
      WritableVReg (JoltISA.amoWordLaneVRegFor rd) ∧
      WritableVReg (JoltISA.amoWordOldVRegFor rd) ∧
      JoltISA.amoWordDwordVRegFor rd ≠ JoltISA.amoWordLaneVRegFor rd ∧
      JoltISA.amoWordOldVRegFor rd ≠ JoltISA.amoWordDwordVRegFor rd ∧
      JoltISA.amoWordOldVRegFor rd ≠ JoltISA.amoWordLaneVRegFor rd := by
    dsimp [JoltISA.amoWordOldVRegFor, JoltISA.amoWordDwordVRegFor,
      JoltISA.amoWordLaneVRegFor, JoltISA.amoVRegFor, WritableVReg]
    split <;> decide
  set old := JoltISA.amoWordOldVRegFor rd with hold_def
  set dword := JoltISA.amoWordDwordVRegFor rd with hdword_def
  set lane := JoltISA.amoWordLaneVRegFor rd with hlane_def
  obtain ⟨hwd, hwl, hwo, hdl, hod, hol⟩ := hregs
  -- the first row
  obtain ⟨T, hT⟩ : ∃ T, AtomicFamily.amoWordWindowProgram middle source rs1 rd =
      .instr (.VirtualLoadW .amo (.vreg dword) (.xreg rs1) 0
        (ExceptionType.E_SAMO_Addr_Align ())) T := ⟨_, rfl⟩
  have hrun1 := hrun
  rw [hT] at hrun1
  obtain ⟨js1, h1, -⟩ := JoltISA.execProgram_instr_run_retire_inv _ _ _ _ hrun1
  have hbase_eq : (addr + 0) &&& ~~~(7 : BitVec 64) = amoWordBase addr := by
    rw [add_zero, (ioHelper% neg8_eq)]
  have hlt' : ((addr + 0) &&& ~~~(7 : BitVec 64)).toNat < JoltISA.RAM_START_ADDRESS := by
    rw [hbase_eq]; exact hlt
  obtain ⟨hal0, D, hload0⟩ := (ioHelper% floorLoad_inv) .word dword rs1 0 addr .amo
    (ExceptionType.E_SAMO_Addr_Align ()) js js1 hr1 hlt' h1
  rw [hbase_eq] at hload0
  have halign : addr &&& (3 : BitVec 64) = 0 := by
    simpa [LoadFamily.alignmentMask] using hal0
  obtain ⟨hmod8, D', hrD, -, hread⟩ := (ioHelper% load_doubleword_inv) _ js js _ hlt hload0
  cases hrD
  -- the opened lane
  have hpre := AtomicFamily.amo_word_lane_pre_run rs1 old dword lane js addr D hr1 halign
    hload0 hwd hwl hwo hdl
  set pre := stateAfterVRegWrite (stateAfterVRegWrite (stateAfterVRegWrite js dword D) lane
    (AtomicFamily.amoWordLaneMask addr)) old (AtomicFamily.amoWordLaneOld addr D) with hpre_def
  have hpre_sail : pre.sail = js.sail := rfl
  have hpre_dev : pre.jolt_device = js.jolt_device := rfl
  have hpre_dw : pre.vregs dword = D := by
    simp [pre, stateAfterVRegWrite, Ne.symm hod, hdl]
  have hpre_lane : pre.vregs lane = AtomicFamily.amoWordLaneMask addr := by
    simp [pre, stateAfterVRegWrite, Ne.symm hol]
  have hpre_old : pre.vregs old = sign_extend (m := 64)
      (word_of_dword D (addr &&& (7 : BitVec 64)).toNat) := by
    rw [← AtomicFamily.amo_word_lane_old_eq addr D halign]
    simp [pre, stateAfterVRegWrite]
  have hrest : (JoltISA.execProgram (middle.append
      (JoltISA.amoWordMergeProgram rs1 rd source dword lane old))).run pre =
      .ok RETIRE_SUCCESS gp := by
    have hprog : AtomicFamily.amoWordWindowProgram middle source rs1 rd =
        (JoltISA.amoPre64ProgramWithScratch rs1 old dword lane (.done RETIRE_SUCCESS)).append
          (middle.append (JoltISA.amoWordMergeProgram rs1 rd source dword lane old)) := rfl
    rw [hprog, JoltISA.execProgram_append_of_first_succeeds _ _ js _ hpre] at hrun
    exact hrun
  -- the middle
  obtain ⟨after, hm⟩ := hmiddle addr rs2Val D pre hr1 hr2 hpre_sail hpre_dw hpre_lane hpre_old
  rw [JoltISA.execProgram_append_of_first_succeeds _ _ _ _ hm.run] at hrest
  have hsail_a : after.sail = js.sail := hm.sail.trans hpre_sail
  have hdev_a : after.jolt_device = js.jolt_device :=
    (bundleHelper% noStoreProgram_device) _ hNS pre after RETIRE_SUCCESS hm.run
  have hao : after.vregs old = sign_extend (m := 64)
      (word_of_dword D (addr &&& (7 : BitVec 64)).toNat) := hm.old_vreg
  set ow := word_of_dword D (addr &&& (7 : BitVec 64)).toNat with how
  set value := res rs2Val ow with hvalue
  -- the merge
  set mask := AtomicFamily.amoWordLaneMask addr with hmask
  let cleared := stateAfterVRegWrite after dword (D &&& ~~~mask)
  let shifted := stateAfterVRegWrite cleared lane (jolt_virtual_shift_data_w_value value addr)
  let merged := AtomicFamily.amoWordLaneMergeState after dword lane addr D value
  have hclear : (JoltISA.execInstr (.ANDN (.vreg dword) (.vreg dword) (.vreg lane))).run
      after = .ok RETIRE_SUCCESS cleared := by
    have h := JoltISA.andn_run_vreg_vreg_vreg dword dword lane after hwd
    rw [show after.vregs dword = D from hm.dword_vreg,
      show after.vregs lane = mask from hm.lane_vreg] at h
    exact h
  have hshift := AtomicFamily.amo_word_shift_data_run lane source rs1 cleared value addr
    hm.value_read (by rw [show cleared.sail = js.sail from hsail_a]; exact hr1) hwl
  have hadd : (JoltISA.execInstr (.ADD (.vreg dword) (.vreg dword) (.vreg lane))).run shifted =
      .ok RETIRE_SUCCESS merged := by
    simpa [shifted, cleared, merged, AtomicFamily.amoWordLaneMergeState, stateAfterVRegWrite,
      hdl, AtomicFamily.amoWordLaneMerged] using
      JoltISA.add_run_vreg_vreg_vreg dword dword lane shifted hwd
  change (JoltISA.execProgram (.instr (.ANDN (.vreg dword) (.vreg dword) (.vreg lane))
    (.instr (.VirtualShiftDataW (.vreg lane) source (.xreg rs1) 0)
      (.instr (.ADD (.vreg dword) (.vreg dword) (.vreg lane))
        (.instr (.VirtualStoreW (.xreg rs1) (.vreg dword) 0
          (ExceptionType.E_SAMO_Addr_Align ()))
          (.instr (JoltISA.Encoded.ADDI (JoltISA.amoDstFor rd) (.vreg old) 0)
            (.done RETIRE_SUCCESS))))))).run after = _ at hrest
  rw [JoltISA.execProgram_instr_run_retire _ _ _ _ hclear,
    JoltISA.execProgram_instr_run_retire _ _ _ _ hshift,
    JoltISA.execProgram_instr_run_retire _ _ _ _ hadd] at hrest
  obtain ⟨js_sd, hsd, hrest2⟩ := JoltISA.execProgram_instr_run_retire_inv _ _ _ _ hrest
  have hms : merged.sail = js.sail := hsail_a
  have hmd : merged.jolt_device = js.jolt_device := hdev_a
  have hmv : merged.vregs dword = AtomicFamily.amoWordLaneMerged addr D value := by
    simp [merged, AtomicFamily.amoWordLaneMergeState, stateAfterVRegWrite]
  have hr1m : rX_bits rs1 merged.sail = .ok addr merged.sail := by rw [hms]; exact hr1
  have hst := (ioHelper% floorStore_inv) .word rs1 dword 0 addr
    (ExceptionType.E_SAMO_Addr_Align ()) merged js_sd hr1m hlt' hal0 hsd
  rw [hbase_eq, hmv] at hst
  have hmem_m : MemRel merged.jolt_device merged.sail := by rw [hms, hmd]; exact hmem
  have hflag_m : ∀ k < 8,
      IsFlagWord merged.jolt_device ((amoWordBase addr).toNat + k) = false := by
    rw [hmd]; exact hflag
  obtain ⟨hlow, hvsd, hssd⟩ := amo_store_low merged js_sd (amoWordBase addr) _ hmem_m hlt
    hflag_m hst
  obtain ⟨hlo40, hhi8⟩ := (ioHelper% store_bounds) merged js_sd _ _ hmem_m hlt hst
  have hlow' : memLow js.jolt_device ≤ (amoWordBase addr).toNat := by rw [hmd] at hlow; exact hlow
  obtain ⟨hb, no, hD⟩ := (ioHelper% io_dword_eq) js (amoWordBase addr) D hmem hmod8 hlow' hlt
    hflag hread
  have hA : (amoWordBase addr).toNat = addr.toNat / 8 * 8 := (ioHelper% toNat_and_neg8) addr
  have hmod4 := (ioHelper% mod_of_and3) addr halign
  have hnm := (ioHelper% not_mmio_io) js.sail addr 4 (by omega) hhtif
  have hatomic := io_atomic_checks js.sail addr 4 hpma (by omega) (by norm_num) (by norm_num)
    (by omega) hmod4 op hnot_cas
  have hbase_no := AtomicFamily.amo_word_base_no_ovf addr
  have hoff : (addr &&& (7 : BitVec 64)).toNat + 4 ≤ 8 := by
    rcases write_word_offset_cases addr halign with h | h <;> omega
  have haddr : amoWordBase addr + BitVec.ofNat 64 (addr &&& (7 : BitVec 64)).toNat = addr :=
    addr_split_aligned_offset addr
  have hbytes : MemBytesPresentAt js.sail addr 4 := by
    rw [← haddr]
    exact memBytesPresentAt_subaccess hb hoff (by omega)
  have hold : loaded_word_at js.sail addr hbytes
      (AtomicFamily.amo_word_aligned_no_ovf addr hbase_no halign) = ow := by
    rw [loaded_word_in_dword js.sail addr halign hb no hbytes _, hD]
  have hsail := io_execute_AMO_word_non_cas_aligned op rs2 rs1 rd js hpriv hmprv addr rs2Val
    (Sail.BitVec.extractLsb value 31 0) hr1 hr2 ⟨_, hrdr⟩ hbytes hatomic hnm.1 hnm.2 halign
    hnot_cas
    (by rw [AtomicFamily.amo_word_trunc_4x8_eq_extract, AtomicFamily.amo_word_setWidth_4x8_eq_self,
          hold]
        exact (hres rs2Val ow).symm)
  rw [hold] at hsail
  -- the writeback
  obtain ⟨js_w, hadd1, hdone⟩ := JoltISA.execProgram_instr_run_retire_inv _ _ _ _ hrest2
  have hgw : gp = js_w := by
    have : (JoltISA.execProgram (.done RETIRE_SUCCESS)).run js_w = .ok RETIRE_SUCCESS js_w := rfl
    rw [this] at hdone
    exact (EStateM.Result.ok.inj hdone).2.symm
  subst hgw
  have hv_sd : js_sd.vregs old = sign_extend (m := 64) ow := by
    rw [hvsd]
    simp only [merged, AtomicFamily.amoWordLaneMergeState, stateAfterVRegWrite, ite_eq_right hod,
      ite_eq_right hol]
    exact hao
  obtain ⟨js_w', hadd', hsw'⟩ := AtomicFamily.amo_dword_addi_writeback_old_run_from old rd
    js_sd (sign_extend (m := 64) ow) hv_sd
  have hww : gp = js_w' := by
    rw [hadd1] at hadd'
    exact (EStateM.Result.ok.inj hadd').2
  have hdev_w : gp.jolt_device = js_sd.jolt_device :=
    (bundleHelper% noStoreRow_device) _ (by trivial) js_sd gp RETIRE_SUCCESS hadd1
  have hsail_gp : gp.sail = stateAfterWrite js.sail rd (sign_extend (m := 64) ow) := by
    rw [hww, hsw', hssd, hms]
  -- the memory
  have hwin : addr.toNat % 8 + 4 ≤ 8 := by omega
  obtain ⟨hgs, hmemT⟩ := (ioHelper% store_finish) js merged js_sd
    (state_after_word_store js.sail addr (Sail.BitVec.extractLsb value 31 0))
    (amoWordBase addr) (AtomicFamily.amoWordLaneMerged addr D value) addr value D 4
    hmem hms hmd (by norm_num) hA hwin
    (fun k hk _ => by
      rw [(ioHelper% load_raw_load) js _ _
        (by simp only [JoltISA.RAM_START_ADDRESS] at hhi8 ⊢; omega)
        ((ioHelper% read_doubleword_bytes) hread k hk)]
      rfl)
    (fun k hk => by
      have hlea : load_effective_address addr (0 : BitVec 12) = addr :=
        AtomicFamily.amo_word_zero_offset_addr addr
      have := (ioHelper% fusedSplice_byte_w) D value addr 0 (by rw [hlea]; exact halign) k hk
      rw [hlea] at this
      exact this)
    hlt hst ((ioHelper% sailStore_word) js.sail addr value)
    (fun h => by
      exfalso
      have hf0 := hflag 0 (by norm_num)
      have hg := IoGeo.of_layout _ hmem.layout
      obtain ⟨-, -, -, -, hp, -, ht, he, -, -, -, -, -⟩ := hg
      simp only [IsFlagWord, Bool.and_eq_false_iff, decide_eq_false_iff_not, not_le,
        not_lt, Nat.add_zero] at hf0
      omega)
  have hsst := (ioHelper% sailStore_word) js.sail addr value
  refine ⟨AtomicFamily.amoWordFinalSailState rd js.sail addr (Sail.BitVec.extractLsb value 31 0)
    ow, hsail, ?_, ?_, ?_⟩
  · rw [(Projection.systemProject_stateAfterWrite_of_projected_vregs_preserved js gp rd
      (sign_extend (m := 64) ow) hsail_gp hproj), hlink]
    change wX_update_regs rd _ _ = wX_update_regs rd _ _
    rw [hsst.1]
  · intro a ha
    rw [hsail_gp]
    simp only [AtomicFamily.amoWordFinalSailState, stateAfterWrite, Mmu.ram_byte]
    rw [hsst.2 a, ite_eq_right]
    simp only [JoltISA.RAM_START_ADDRESS, RAM_START_ADDRESS] at ha hhi8
    omega
  · rw [hdev_w]
    exact hmemT.of_mem_eq rfl


private theorem io_word_regs (rd : regidx) :
    WritableVReg (JoltISA.amoWordNewVRegFor rd) ∧
      JoltISA.amoWordOldVRegFor rd ≠ JoltISA.amoWordNewVRegFor rd ∧
      JoltISA.amoWordDwordVRegFor rd ≠ JoltISA.amoWordNewVRegFor rd ∧
      JoltISA.amoWordLaneVRegFor rd ≠ JoltISA.amoWordNewVRegFor rd := by
  dsimp [JoltISA.amoWordOldVRegFor, JoltISA.amoWordNewVRegFor, JoltISA.amoWordDwordVRegFor,
    JoltISA.amoWordLaneVRegFor, JoltISA.amoVRegFor, WritableVReg]
  split <;> decide

/-- The word AMOs that combine the memory word and `rs2` in one row (ADD, XOR, AND, OR)
agree with Sail on a word in the I/O window.
For example, `AMOXOR.W` at `0x40000004` stores `rs2 ^^^ old` in the upper word and returns
`old`. -/
private theorem io_amo_word_binop (op : amoop) (hnot_cas : (op == amoop.AMOCAS) = false)
    (binop : JoltISA.Dst → JoltISA.Src → JoltISA.Src → JoltISA.Instr)
    (value : BitVec 64 → BitVec 64 → BitVec 64)
    (hNSb : ∀ d l r, (bundleHelper% NoStoreRow) (binop d l r))
    (hrow : ∀ (new old dword lane : JoltISA.VReg) (rs2 : regidx)
      (js : SailJoltState) (rs2Val oldVal dwordVal laneVal : BitVec 64),
      rX_bits rs2 js.sail = .ok rs2Val js.sail →
      js.vregs old = oldVal → js.vregs dword = dwordVal → js.vregs lane = laneVal →
      WritableVReg new → old ≠ new → dword ≠ new → lane ≠ new →
      ∃ after, AtomicFamily.AmoWordMiddleStepInto new old dword lane
        (binop (.vreg new) (.vreg old) (.xreg rs2))
        oldVal dwordVal laneVal (value rs2Val oldVal) js after)
    (hvalue : ∀ (new : BitVec 64) (old : BitVec 32),
      (Sail.BitVec.extractLsb (value new (sign_extend (m := 64) old)) 31 0 : BitVec 32) =
        AtomicFamily.amoWordSailResult op (Sail.BitVec.extractLsb new 31 0) old)
    (rs2 rs1 rd : regidx) (js gp : SailJoltState)
    (hc : IoAmoCtx js (amoWordBase (JoltISA.sourceValue (.xreg rs1) js)))
    (hproj : Projection.ProjectedVRegsPreserved js gp)
    (hrun : (JoltISA.execProgram (JoltISA.amoWordBinopProgram binop rs2 rs1 rd)).run js =
      .ok RETIRE_SUCCESS gp) :
    IoAmoEffect op 4 rs2 rs1 rd js gp := by
  obtain ⟨hnw, hon, hdn, hln⟩ := io_word_regs rd
  refine io_amo_word op hnot_cas rs2 rs1 rd
    (.instr (binop (.vreg (JoltISA.amoWordNewVRegFor rd))
      (.vreg (JoltISA.amoWordOldVRegFor rd)) (.xreg rs2)) (.done RETIRE_SUCCESS))
    (.vreg (JoltISA.amoWordNewVRegFor rd))
    (fun rs2Val ow => value rs2Val (sign_extend (m := 64) ow)) hvalue js gp ?_
    ⟨hNSb _ _ _, trivial⟩ hc hproj hrun
  intro addr rs2Val D pre hr1 hr2 hsail hdw hlane hold
  obtain ⟨after, hm⟩ := hrow (JoltISA.amoWordNewVRegFor rd) (JoltISA.amoWordOldVRegFor rd)
    (JoltISA.amoWordDwordVRegFor rd) (JoltISA.amoWordLaneVRegFor rd) rs2 pre rs2Val _ D _
    (by rw [hsail]; exact hr2) hold hdw hlane hnw hon hdn hln
  refine ⟨after, ⟨(JoltISA.execProgram_instr_run_retire _ _ _ _ hm.run).trans rfl, hm.sail,
    hm.old_vreg, hm.dword_vreg, hm.shift_vreg, ?_⟩⟩
  have h : (stateAfterVRegWrite after (JoltISA.amoWordDwordVRegFor rd)
      (D &&& ~~~AtomicFamily.amoWordLaneMask addr)).vregs (JoltISA.amoWordNewVRegFor rd) =
      value rs2Val (sign_extend (m := 64)
        (word_of_dword D (addr &&& (7 : BitVec 64)).toNat)) := by
    simp only [stateAfterVRegWrite, ite_eq_right (Ne.symm hdn)]
    exact hm.result_vreg
  change JoltISA.readSrc (.vreg (JoltISA.amoWordNewVRegFor rd)) _ = _
  rw [readSrc_vreg, h]

/-- The word min/max AMOs (signed and unsigned) agree with Sail on a word in the I/O
window.
For example, `AMOMAXU.W` at `0x40000000` stores the larger of `rs2` and the old lower word
there and returns the old word. -/
private theorem io_amo_word_select (op : amoop) (hnot_cas : (op == amoop.AMOCAS) = false)
    (cmp : JoltISA.Dst → JoltISA.Src → JoltISA.Src → JoltISA.Instr)
    (less : BitVec 64 → BitVec 64 → Bool) (reverse : Bool)
    (hNSc : ∀ d l r, (bundleHelper% NoStoreRow) (cmp d l r))
    (hcmp : ∀ dst lhs rhs js, WritableVReg dst →
      (JoltISA.execInstr (cmp (.vreg dst) (.vreg lhs) (.vreg rhs))).run js =
        .ok RETIRE_SUCCESS (stateAfterVRegWrite js dst
          (zero_extend (m := 64) (bool_to_bit (less (js.vregs lhs) (js.vregs rhs))))))
    (hselect : ∀ (new : BitVec 64) (old : BitVec 32),
      (if AtomicFamily.amoWordSelectFlag less reverse
          (sign_extend (m := 64) (Sail.BitVec.extractLsb new 31 0 : BitVec 32))
          (sign_extend (m := 64) old)
        then (Sail.BitVec.extractLsb new 31 0 : BitVec 32) else old) =
      AtomicFamily.amoWordSailResult op (Sail.BitVec.extractLsb new 31 0) old)
    (rs2 rs1 rd : regidx) (js gp : SailJoltState)
    (hc : IoAmoCtx js (amoWordBase (JoltISA.sourceValue (.xreg rs1) js)))
    (hproj : Projection.ProjectedVRegsPreserved js gp)
    (hrun : (JoltISA.execProgram (AtomicFamily.amoWordWindowProgram
      (AtomicFamily.amoWordSelectLaneMiddle cmp reverse rs2 rd)
      (.vreg (JoltISA.amoWordNewVRegFor rd)) rs1 rd)).run js = .ok RETIRE_SUCCESS gp) :
    IoAmoEffect op 4 rs2 rs1 rd js gp := by
  refine io_amo_word op hnot_cas rs2 rs1 rd
    (AtomicFamily.amoWordSelectLaneMiddle cmp reverse rs2 rd)
    (.vreg (JoltISA.amoWordNewVRegFor rd))
    (fun rs2Val ow =>
      if AtomicFamily.amoWordSelectFlag less reverse
          (sign_extend (m := 64) (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32))
          (sign_extend (m := 64) ow)
        then rs2Val else sign_extend (m := 64) ow)
    (fun rs2Val ow => by
      rw [AtomicFamily.amo_word_extract_select_result,
        show (Sail.BitVec.extractLsb (sign_extend (m := 64) ow) 31 0 : BitVec 32) = ow from
          AtomicFamily.sign_extend_64_setWidth_32 ow]
      exact hselect rs2Val ow)
    js gp ?_ ?_ hc hproj hrun
  · intro addr rs2Val D pre hr1 hr2 hsail hdw hlane hold
    exact AtomicFamily.amo_word_select_lane_middle_run cmp less hcmp reverse rs2 rd pre rs2Val
      _ _ _ (by rw [hsail]; exact hr2) hold hdw hlane
  · unfold AtomicFamily.amoWordSelectLaneMiddle AtomicFamily.amoWordSelectLaneTail
    exact ⟨trivial, hNSc _ _ _, trivial, trivial, trivial, trivial⟩

/-- `AMOSWAP.W` agrees with Sail on a word in the I/O window.
For example, at `0x40000004` it stores the low word of `rs2` in the upper word and returns
the old upper word. -/
private theorem io_amo_word_swap (rs2 rs1 rd : regidx) (js gp : SailJoltState)
    (hc : IoAmoCtx js (amoWordBase (JoltISA.sourceValue (.xreg rs1) js)))
    (hproj : Projection.ProjectedVRegsPreserved js gp)
    (hrun : (JoltISA.execProgram (AtomicFamily.amoWordWindowProgram (.done RETIRE_SUCCESS)
      (.xreg rs2) rs1 rd)).run js = .ok RETIRE_SUCCESS gp) :
    IoAmoEffect amoop.AMOSWAP 4 rs2 rs1 rd js gp := by
  refine io_amo_word amoop.AMOSWAP (by decide) rs2 rs1 rd (.done RETIRE_SUCCESS) (.xreg rs2)
    (fun rs2Val _ => rs2Val) (fun rs2Val ow => rfl) js gp ?_ trivial hc hproj hrun
  intro addr rs2Val D pre hr1 hr2 hsail hdw hlane hold
  refine ⟨pre, rfl, rfl, hold, hdw, hlane, ?_⟩
  exact JoltISA.readSrc_xreg_run_of_read rs2 _ rs2Val (by
    change rX_bits rs2 pre.sail = .ok rs2Val pre.sail
    rw [hsail]; exact hr2)

/-- `AMOADD.W` agrees with Sail on a word in the I/O window.
For example, at `0x40000004` it stores `rs2 + old` there, where `old` is the word read, and returns `old`. -/
private theorem io_amoadd_w (rs2 rs1 rd : regidx) (js gp : SailJoltState)
    (hc : IoAmoCtx js (amoWordBase (JoltISA.sourceValue (.xreg rs1) js)))
    (hrun : (JoltISA.execProgram (JoltISA.amoaddwProgramAuto rd rs1 rs2)).run js =
      .ok RETIRE_SUCCESS gp) :
    IoAmoEffect amoop.AMOADD 4 rs2 rs1 rd js gp := by
  have hproj := Projection.execProgram_preserves_projected_vregs_of_no_protected_writes
    (AtomicFamily.amoaddwProgram_doesNotWriteProtectedVRegs rs2 rs1 rd) hrun
  have hcore : JoltISA.amoaddwProgramAuto rd rs1 rs2 =
      JoltISA.amoWordBinopProgram (fun dst lhs rhs => .ADD dst lhs rhs) rs2 rs1 rd := by
    cases hrd : JoltISA.isX0 rd <;>
      simp only [JoltISA.amoaddwProgramAuto, JoltISA.amoWordBinopProgram, JoltISA.amoPre64Program, JoltISA.amoPre64ProgramWithScratch, JoltISA.amoWordMergeProgram, JoltISA.laneWindowOpen, JoltISA.laneWindowExtract, JoltISA.laneWindowMerge, JoltISA.amoWordOldVRegFor, JoltISA.amoWordNewVRegFor, JoltISA.amoWordDwordVRegFor, JoltISA.amoWordLaneVRegFor, JoltISA.amoVRegFor, JoltISA.amoDstFor, JoltISA.sideEffectingRdZeroDst, hrd, Bool.false_eq_true, ite_false, ite_true] <;> rfl
  rw [hcore] at hrun
  exact io_amo_word_binop amoop.AMOADD (by decide)
    (fun dst lhs rhs => .ADD dst lhs rhs) (fun new old => new + old)
    (fun _ _ _ => trivial) AtomicFamily.amo_word_add_middle_run_into
    (by intro new old; rw [AtomicFamily.amo_word_extract_add_low]
        exact congrArg (fun word => (Sail.BitVec.extractLsb new 31 0 : BitVec 32) + word)
          (AtomicFamily.sign_extend_64_setWidth_32 old))
    rs2 rs1 rd js gp hc hproj hrun

/-- `AMOXOR.W` agrees with Sail on a word in the I/O window.
For example, at `0x40000004` it stores `rs2 ^^^ old` there, where `old` is the word read, and returns `old`. -/
private theorem io_amoxor_w (rs2 rs1 rd : regidx) (js gp : SailJoltState)
    (hc : IoAmoCtx js (amoWordBase (JoltISA.sourceValue (.xreg rs1) js)))
    (hrun : (JoltISA.execProgram (JoltISA.amoxorwProgramAuto rd rs1 rs2)).run js =
      .ok RETIRE_SUCCESS gp) :
    IoAmoEffect amoop.AMOXOR 4 rs2 rs1 rd js gp := by
  have hproj := Projection.execProgram_preserves_projected_vregs_of_no_protected_writes
    (AtomicFamily.amoxorwProgram_doesNotWriteProtectedVRegs rs2 rs1 rd) hrun
  have hcore : JoltISA.amoxorwProgramAuto rd rs1 rs2 =
      JoltISA.amoWordBinopProgram (fun dst lhs rhs => .XOR dst lhs rhs) rs2 rs1 rd := by
    cases hrd : JoltISA.isX0 rd <;>
      simp only [JoltISA.amoxorwProgramAuto, JoltISA.amoWordBinopProgram, JoltISA.amoPre64Program, JoltISA.amoPre64ProgramWithScratch, JoltISA.amoWordMergeProgram, JoltISA.laneWindowOpen, JoltISA.laneWindowExtract, JoltISA.laneWindowMerge, JoltISA.amoWordOldVRegFor, JoltISA.amoWordNewVRegFor, JoltISA.amoWordDwordVRegFor, JoltISA.amoWordLaneVRegFor, JoltISA.amoVRegFor, JoltISA.amoDstFor, JoltISA.sideEffectingRdZeroDst, hrd, Bool.false_eq_true, ite_false, ite_true] <;> rfl
  rw [hcore] at hrun
  exact io_amo_word_binop amoop.AMOXOR (by decide)
    (fun dst lhs rhs => .XOR dst lhs rhs) (fun new old => new ^^^ old)
    (fun _ _ _ => trivial) AtomicFamily.amo_word_xor_middle_run_into
    (by intro new old; rw [AtomicFamily.amo_word_extract_xor_low]
        exact congrArg (fun word => (Sail.BitVec.extractLsb new 31 0 : BitVec 32) ^^^ word)
          (AtomicFamily.sign_extend_64_setWidth_32 old))
    rs2 rs1 rd js gp hc hproj hrun

/-- `AMOAND.W` agrees with Sail on a word in the I/O window.
For example, at `0x40000004` it stores `rs2 &&& old` there, where `old` is the word read, and returns `old`. -/
private theorem io_amoand_w (rs2 rs1 rd : regidx) (js gp : SailJoltState)
    (hc : IoAmoCtx js (amoWordBase (JoltISA.sourceValue (.xreg rs1) js)))
    (hrun : (JoltISA.execProgram (JoltISA.amoandwProgramAuto rd rs1 rs2)).run js =
      .ok RETIRE_SUCCESS gp) :
    IoAmoEffect amoop.AMOAND 4 rs2 rs1 rd js gp := by
  have hproj := Projection.execProgram_preserves_projected_vregs_of_no_protected_writes
    (AtomicFamily.amoandwProgram_doesNotWriteProtectedVRegs rs2 rs1 rd) hrun
  have hcore : JoltISA.amoandwProgramAuto rd rs1 rs2 =
      JoltISA.amoWordBinopProgram (fun dst lhs rhs => .AND dst lhs rhs) rs2 rs1 rd := by
    cases hrd : JoltISA.isX0 rd <;>
      simp only [JoltISA.amoandwProgramAuto, JoltISA.amoWordBinopProgram, JoltISA.amoPre64Program, JoltISA.amoPre64ProgramWithScratch, JoltISA.amoWordMergeProgram, JoltISA.laneWindowOpen, JoltISA.laneWindowExtract, JoltISA.laneWindowMerge, JoltISA.amoWordOldVRegFor, JoltISA.amoWordNewVRegFor, JoltISA.amoWordDwordVRegFor, JoltISA.amoWordLaneVRegFor, JoltISA.amoVRegFor, JoltISA.amoDstFor, JoltISA.sideEffectingRdZeroDst, hrd, Bool.false_eq_true, ite_false, ite_true] <;> rfl
  rw [hcore] at hrun
  exact io_amo_word_binop amoop.AMOAND (by decide)
    (fun dst lhs rhs => .AND dst lhs rhs) (fun new old => new &&& old)
    (fun _ _ _ => trivial) AtomicFamily.amo_word_and_middle_run_into
    (by intro new old; rw [AtomicFamily.amo_word_extract_and_low]
        exact congrArg (fun word => (Sail.BitVec.extractLsb new 31 0 : BitVec 32) &&& word)
          (AtomicFamily.sign_extend_64_setWidth_32 old))
    rs2 rs1 rd js gp hc hproj hrun

/-- `AMOOR.W` agrees with Sail on a word in the I/O window.
For example, at `0x40000004` it stores `rs2 ||| old` there, where `old` is the word read, and returns `old`. -/
private theorem io_amoor_w (rs2 rs1 rd : regidx) (js gp : SailJoltState)
    (hc : IoAmoCtx js (amoWordBase (JoltISA.sourceValue (.xreg rs1) js)))
    (hrun : (JoltISA.execProgram (JoltISA.amoorwProgramAuto rd rs1 rs2)).run js =
      .ok RETIRE_SUCCESS gp) :
    IoAmoEffect amoop.AMOOR 4 rs2 rs1 rd js gp := by
  have hproj := Projection.execProgram_preserves_projected_vregs_of_no_protected_writes
    (AtomicFamily.amoorwProgram_doesNotWriteProtectedVRegs rs2 rs1 rd) hrun
  have hcore : JoltISA.amoorwProgramAuto rd rs1 rs2 =
      JoltISA.amoWordBinopProgram (fun dst lhs rhs => .OR dst lhs rhs) rs2 rs1 rd := by
    cases hrd : JoltISA.isX0 rd <;>
      simp only [JoltISA.amoorwProgramAuto, JoltISA.amoWordBinopProgram, JoltISA.amoPre64Program, JoltISA.amoPre64ProgramWithScratch, JoltISA.amoWordMergeProgram, JoltISA.laneWindowOpen, JoltISA.laneWindowExtract, JoltISA.laneWindowMerge, JoltISA.amoWordOldVRegFor, JoltISA.amoWordNewVRegFor, JoltISA.amoWordDwordVRegFor, JoltISA.amoWordLaneVRegFor, JoltISA.amoVRegFor, JoltISA.amoDstFor, JoltISA.sideEffectingRdZeroDst, hrd, Bool.false_eq_true, ite_false, ite_true] <;> rfl
  rw [hcore] at hrun
  exact io_amo_word_binop amoop.AMOOR (by decide)
    (fun dst lhs rhs => .OR dst lhs rhs) (fun new old => new ||| old)
    (fun _ _ _ => trivial) AtomicFamily.amo_word_or_middle_run_into
    (by intro new old; rw [AtomicFamily.amo_word_extract_or_low]
        exact congrArg (fun word => (Sail.BitVec.extractLsb new 31 0 : BitVec 32) ||| word)
          (AtomicFamily.sign_extend_64_setWidth_32 old))
    rs2 rs1 rd js gp hc hproj hrun

/-- `AMOMIN.W` agrees with Sail on a word in the I/O window.
For example, at `0x40000004` it stores the signed minimum of `rs2` and `old` there, where `old` is the word read, and returns `old`. -/
private theorem io_amomin_w (rs2 rs1 rd : regidx) (js gp : SailJoltState)
    (hc : IoAmoCtx js (amoWordBase (JoltISA.sourceValue (.xreg rs1) js)))
    (hrun : (JoltISA.execProgram (JoltISA.amominwProgramAuto rd rs1 rs2)).run js =
      .ok RETIRE_SUCCESS gp) :
    IoAmoEffect amoop.AMOMIN 4 rs2 rs1 rd js gp := by
  have hproj := Projection.execProgram_preserves_projected_vregs_of_no_protected_writes
    (AtomicFamily.amominwProgram_doesNotWriteProtectedVRegs rs2 rs1 rd) hrun
  have hcore : JoltISA.amominwProgramAuto rd rs1 rs2 =
      JoltISA.amoWordSelectRustProgram
        (fun dst src => .VirtualSignExtendWord dst src)
        (fun dst lhs rhs => .SLT dst lhs rhs)
        (.vreg (JoltISA.amoWordNewVRegFor rd))
        (.vreg (JoltISA.amoWordOldVRegFor rd)) rs2 rs1 rd := by
    cases hrd : JoltISA.isX0 rd <;>
      simp only [JoltISA.amominwProgramAuto, JoltISA.amoWordSelectRustProgram, JoltISA.amoPre64Program, JoltISA.amoPre64ProgramWithScratch, JoltISA.amoWordMergeProgram, JoltISA.laneWindowOpen, JoltISA.laneWindowExtract, JoltISA.laneWindowMerge, JoltISA.amoWordOldVRegFor, JoltISA.amoWordNewVRegFor, JoltISA.amoWordDwordVRegFor, JoltISA.amoWordLaneVRegFor, JoltISA.amoWordTakeVRegFor, JoltISA.amoVRegFor, JoltISA.amoDstFor, JoltISA.sideEffectingRdZeroDst, hrd, Bool.false_eq_true, ite_false, ite_true] <;> rfl
  rw [hcore] at hrun
  exact io_amo_word_select amoop.AMOMIN (by decide)
    (fun dst lhs rhs => .SLT dst lhs rhs) zopz0zI_s false (fun _ _ _ => trivial)
    AtomicFamily.amo_word_slt_run_vreg_vreg_vreg
    (by
      intro new old
      simp only [AtomicFamily.amoWordSelectFlag, Bool.false_eq_true, ite_false,
        AtomicFamily.amoWordSailResult, zopz0zI_s, AtomicFamily.amo_word_toInt_signExtend32_64]
      rfl)
    rs2 rs1 rd js gp hc hproj hrun

/-- `AMOMAX.W` agrees with Sail on a word in the I/O window.
For example, at `0x40000004` it stores the signed maximum of `rs2` and `old` there, where `old` is the word read, and returns `old`. -/
private theorem io_amomax_w (rs2 rs1 rd : regidx) (js gp : SailJoltState)
    (hc : IoAmoCtx js (amoWordBase (JoltISA.sourceValue (.xreg rs1) js)))
    (hrun : (JoltISA.execProgram (JoltISA.amomaxwProgramAuto rd rs1 rs2)).run js =
      .ok RETIRE_SUCCESS gp) :
    IoAmoEffect amoop.AMOMAX 4 rs2 rs1 rd js gp := by
  have hproj := Projection.execProgram_preserves_projected_vregs_of_no_protected_writes
    (AtomicFamily.amomaxwProgram_doesNotWriteProtectedVRegs rs2 rs1 rd) hrun
  have hcore : JoltISA.amomaxwProgramAuto rd rs1 rs2 =
      JoltISA.amoWordSelectRustProgram
        (fun dst src => .VirtualSignExtendWord dst src)
        (fun dst lhs rhs => .SLT dst lhs rhs)
        (.vreg (JoltISA.amoWordOldVRegFor rd))
        (.vreg (JoltISA.amoWordNewVRegFor rd)) rs2 rs1 rd := by
    cases hrd : JoltISA.isX0 rd <;>
      simp only [JoltISA.amomaxwProgramAuto, JoltISA.amoWordSelectRustProgram, JoltISA.amoPre64Program, JoltISA.amoPre64ProgramWithScratch, JoltISA.amoWordMergeProgram, JoltISA.laneWindowOpen, JoltISA.laneWindowExtract, JoltISA.laneWindowMerge, JoltISA.amoWordOldVRegFor, JoltISA.amoWordNewVRegFor, JoltISA.amoWordDwordVRegFor, JoltISA.amoWordLaneVRegFor, JoltISA.amoWordTakeVRegFor, JoltISA.amoVRegFor, JoltISA.amoDstFor, JoltISA.sideEffectingRdZeroDst, hrd, Bool.false_eq_true, ite_false, ite_true] <;> rfl
  rw [hcore] at hrun
  exact io_amo_word_select amoop.AMOMAX (by decide)
    (fun dst lhs rhs => .SLT dst lhs rhs) zopz0zI_s true (fun _ _ _ => trivial)
    AtomicFamily.amo_word_slt_run_vreg_vreg_vreg
    (by
      intro new old
      simp only [AtomicFamily.amoWordSelectFlag, ite_true,
        AtomicFamily.amoWordSailResult, zopz0zI_s, zopz0zK_s,
        AtomicFamily.amo_word_toInt_signExtend32_64]
      rfl)
    rs2 rs1 rd js gp hc hproj hrun

/-- `AMOMINU.W` agrees with Sail on a word in the I/O window.
For example, at `0x40000004` it stores the unsigned minimum of `rs2` and `old` there, where `old` is the word read, and returns `old`. -/
private theorem io_amominu_w (rs2 rs1 rd : regidx) (js gp : SailJoltState)
    (hc : IoAmoCtx js (amoWordBase (JoltISA.sourceValue (.xreg rs1) js)))
    (hrun : (JoltISA.execProgram (JoltISA.amominuwProgramAuto rd rs1 rs2)).run js =
      .ok RETIRE_SUCCESS gp) :
    IoAmoEffect amoop.AMOMINU 4 rs2 rs1 rd js gp := by
  have hproj := Projection.execProgram_preserves_projected_vregs_of_no_protected_writes
    (AtomicFamily.amominuwProgram_doesNotWriteProtectedVRegs rs2 rs1 rd) hrun
  have hcore : JoltISA.amominuwProgramAuto rd rs1 rs2 =
      JoltISA.amoWordSelectRustProgram
        (fun dst src => .VirtualSignExtendWord dst src)
        (fun dst lhs rhs => .SLTU dst lhs rhs)
        (.vreg (JoltISA.amoWordNewVRegFor rd))
        (.vreg (JoltISA.amoWordOldVRegFor rd)) rs2 rs1 rd := by
    cases hrd : JoltISA.isX0 rd <;>
      simp only [JoltISA.amominuwProgramAuto, JoltISA.amoWordSelectRustProgram, JoltISA.amoPre64Program, JoltISA.amoPre64ProgramWithScratch, JoltISA.amoWordMergeProgram, JoltISA.laneWindowOpen, JoltISA.laneWindowExtract, JoltISA.laneWindowMerge, JoltISA.amoWordOldVRegFor, JoltISA.amoWordNewVRegFor, JoltISA.amoWordDwordVRegFor, JoltISA.amoWordLaneVRegFor, JoltISA.amoWordTakeVRegFor, JoltISA.amoVRegFor, JoltISA.amoDstFor, JoltISA.sideEffectingRdZeroDst, hrd, Bool.false_eq_true, ite_false, ite_true] <;> rfl
  rw [hcore] at hrun
  exact io_amo_word_select amoop.AMOMINU (by decide)
    (fun dst lhs rhs => .SLTU dst lhs rhs) zopz0zI_u false (fun _ _ _ => trivial)
    AtomicFamily.amo_word_sltu_run_vreg_vreg_vreg
    (by
      intro new old
      simp only [AtomicFamily.amoWordSelectFlag, Bool.false_eq_true, ite_false,
        AtomicFamily.amo_word_sltu_sign_extend, AtomicFamily.amoWordSailResult])
    rs2 rs1 rd js gp hc hproj hrun

/-- `AMOMAXU.W` agrees with Sail on a word in the I/O window.
For example, at `0x40000004` it stores the unsigned maximum of `rs2` and `old` there, where `old` is the word read, and returns `old`. -/
private theorem io_amomaxu_w (rs2 rs1 rd : regidx) (js gp : SailJoltState)
    (hc : IoAmoCtx js (amoWordBase (JoltISA.sourceValue (.xreg rs1) js)))
    (hrun : (JoltISA.execProgram (JoltISA.amomaxuwProgramAuto rd rs1 rs2)).run js =
      .ok RETIRE_SUCCESS gp) :
    IoAmoEffect amoop.AMOMAXU 4 rs2 rs1 rd js gp := by
  have hproj := Projection.execProgram_preserves_projected_vregs_of_no_protected_writes
    (AtomicFamily.amomaxuwProgram_doesNotWriteProtectedVRegs rs2 rs1 rd) hrun
  have hcore : JoltISA.amomaxuwProgramAuto rd rs1 rs2 =
      JoltISA.amoWordSelectRustProgram
        (fun dst src => .VirtualSignExtendWord dst src)
        (fun dst lhs rhs => .SLTU dst lhs rhs)
        (.vreg (JoltISA.amoWordOldVRegFor rd))
        (.vreg (JoltISA.amoWordNewVRegFor rd)) rs2 rs1 rd := by
    cases hrd : JoltISA.isX0 rd <;>
      simp only [JoltISA.amomaxuwProgramAuto, JoltISA.amoWordSelectRustProgram, JoltISA.amoPre64Program, JoltISA.amoPre64ProgramWithScratch, JoltISA.amoWordMergeProgram, JoltISA.laneWindowOpen, JoltISA.laneWindowExtract, JoltISA.laneWindowMerge, JoltISA.amoWordOldVRegFor, JoltISA.amoWordNewVRegFor, JoltISA.amoWordDwordVRegFor, JoltISA.amoWordLaneVRegFor, JoltISA.amoWordTakeVRegFor, JoltISA.amoVRegFor, JoltISA.amoDstFor, JoltISA.sideEffectingRdZeroDst, hrd, Bool.false_eq_true, ite_false, ite_true] <;> rfl
  rw [hcore] at hrun
  exact io_amo_word_select amoop.AMOMAXU (by decide)
    (fun dst lhs rhs => .SLTU dst lhs rhs) zopz0zI_u true (fun _ _ _ => trivial)
    AtomicFamily.amo_word_sltu_run_vreg_vreg_vreg
    (by
      intro new old
      simp only [AtomicFamily.amoWordSelectFlag, ite_true,
        AtomicFamily.amo_word_sltu_sign_extend, AtomicFamily.amoWordSailResult]
      rfl)
    rs2 rs1 rd js gp hc hproj hrun

/-- `AMOSWAP.W` agrees with Sail on a word in the I/O window.
For example, at `0x40000004` it stores `rs2` there, where `old` is the word read, and returns `old`. -/
private theorem io_amoswap_w (rs2 rs1 rd : regidx) (js gp : SailJoltState)
    (hc : IoAmoCtx js (amoWordBase (JoltISA.sourceValue (.xreg rs1) js)))
    (hrun : (JoltISA.execProgram (JoltISA.amoswapwProgramAuto rd rs1 rs2)).run js =
      .ok RETIRE_SUCCESS gp) :
    IoAmoEffect amoop.AMOSWAP 4 rs2 rs1 rd js gp := by
  have hproj := Projection.execProgram_preserves_projected_vregs_of_no_protected_writes
    (AtomicFamily.amoswapwProgram_doesNotWriteProtectedVRegs rs2 rs1 rd) hrun
  have hcore : JoltISA.amoswapwProgramAuto rd rs1 rs2 =
      AtomicFamily.amoWordWindowProgram (.done RETIRE_SUCCESS) (.xreg rs2) rs1 rd := by
    cases hrd : JoltISA.isX0 rd <;>
      simp only [JoltISA.amoswapwProgramAuto, AtomicFamily.amoWordWindowProgram,
        JoltISA.amoPre64Program, JoltISA.amoPre64ProgramWithScratch,
        JoltISA.amoWordMergeProgram, JoltISA.laneWindowOpen, JoltISA.laneWindowExtract,
        JoltISA.laneWindowMerge, JoltISA.amoWordOldVRegFor, JoltISA.amoWordDwordVRegFor,
        JoltISA.amoWordLaneVRegFor, JoltISA.amoVRegFor, JoltISA.amoDstFor,
        JoltISA.sideEffectingRdZeroDst, hrd, Bool.false_eq_true, ite_false, ite_true] <;> rfl
  rw [hcore] at hrun
  exact io_amo_word_swap rs2 rs1 rd js gp hc hproj hrun

/-! ### The effect of one I/O atomic -/

/-- The facts every I/O AMO core takes follow from the premises on the instruction and the
state.
For example, `AMOADD.D` through `0x40000010` with no flag byte in the doubleword yields a
context for the address `0x40000010`. -/
private theorem io_amo_ctx (i : RiscvInstruction) (js : SailJoltState)
    (hio : IoAmoAccess i js) (hflag : i.AmoNoFlagWord js)
    (hlink : System.systemProject js = js.sail) (hinv : Step.StepInvariant js.sail)
    (hmstatus : js.vregs mstatusVReg &&& ~~~(0x88 : BitVec 64) = 0)
    (hmem : MemRel js.jolt_device js.sail)
    (hpma : js.sail.regs.get? Register.pma_regions = some platformPma)
    (hhtif : js.sail.regs.get? Register.htif_tohost_base = some none) :
    ∃ a, i.amoBase js = some a ∧ IoAmoCtx js a := by
  obtain ⟨a, ha, hlt⟩ := hio
  exact ⟨a, ha, ⟨hinv, hlink, hmstatus, hmem, hpma, hhtif, hlt, hflag a ha⟩⟩

/-- An I/O AMO's effect on Sail's `execute_AMO` is its effect on `execute` of the matching
instruction, which ignores the acquire and release bits.
For example, `AMOADD.D` with both bits set runs like the same instruction with none. -/
private theorem io_amo_conv (op : amoop) (aq rl : Bool) (rs2 rs1 rd : regidx) (w : Nat)
    (js gp : SailJoltState) (h : IoAmoEffect op w rs2 rs1 rd js gp) :
    ∃ t : SailState, execute (.AMO (op, aq, rl, rs2, rs1, w, rd)) js.sail =
        .ok RETIRE_SUCCESS t ∧
      t.regs = (System.systemProject gp).regs ∧
      (∀ a, RAM_START_ADDRESS ≤ a → Mmu.ram_byte t.mem a = Mmu.ram_byte gp.sail.mem a) ∧
      MemRel gp.jolt_device t := by
  obtain ⟨t, h1, h2, h3, h4⟩ := h
  refine ⟨t, ?_, h2, h3, h4⟩
  have h5 := congrFun (Step.execute_AMO_flags op aq rl rs2 rs1 w rd) js.sail
  exact h5.trans h1

/-- One atomic memory operation in Sail's I/O window agrees with Jolt's rows.
From Jolt's retiring run of the instruction's rows, Sail's `execute` retires to a state
whose registers are the projection of Jolt's, whose RAM is Jolt's and whose memory
satisfies the memory relation with Jolt's device.
For example, `AMOADD.D` at `0x40000010` yields the Sail state with the sum stored there. -/
private theorem io_amo_core (i : RiscvInstruction) (ast : instruction)
    (hm : RiscvInstruction.Matches i ast) (js gp : SailJoltState)
    (hio : IoAmoAccess i js) (hflag : i.AmoNoFlagWord js)
    (hlink : System.systemProject js = js.sail) (hinv : Step.StepInvariant js.sail)
    (hmstatus : js.vregs mstatusVReg &&& ~~~(0x88 : BitVec 64) = 0)
    (hmem : MemRel js.jolt_device js.sail)
    (hpma : js.sail.regs.get? Register.pma_regions = some platformPma)
    (hhtif : js.sail.regs.get? Register.htif_tohost_base = some none)
    (hrun : RiscvInstruction.joltRun (honestInstr i js) js = .ok RETIRE_SUCCESS gp) :
    ∃ t : SailState, execute ast js.sail = .ok RETIRE_SUCCESS t ∧
      t.regs = (System.systemProject gp).regs ∧
      (∀ a, RAM_START_ADDRESS ≤ a → Mmu.ram_byte t.mem a = Mmu.ram_byte gp.sail.mem a) ∧
      MemRel gp.jolt_device t := by
  have hctx := io_amo_ctx i js hio hflag hlink hinv hmstatus hmem hpma hhtif
  clear hio hflag
  cases i with
  | AMOSWAP_W rd rs1 rs2 aq rl =>
    have hm' : ast = .AMO (amoop.AMOSWAP, aq, rl, rs2, rs1, 4, rd) := hm
    subst hm'
    obtain ⟨a, ha, hc⟩ := hctx
    simp only [RiscvInstruction.amoBase, Option.some.injEq] at ha
    subst ha
    change (JoltISA.execProgram (JoltISA.amoswapwProgramAuto rd rs1 rs2)).run js = _ at hrun
    exact io_amo_conv _ aq rl _ _ _ _ js gp (io_amoswap_w rs2 rs1 rd js gp hc hrun)
  | AMOADD_W rd rs1 rs2 aq rl =>
    have hm' : ast = .AMO (amoop.AMOADD, aq, rl, rs2, rs1, 4, rd) := hm
    subst hm'
    obtain ⟨a, ha, hc⟩ := hctx
    simp only [RiscvInstruction.amoBase, Option.some.injEq] at ha
    subst ha
    change (JoltISA.execProgram (JoltISA.amoaddwProgramAuto rd rs1 rs2)).run js = _ at hrun
    exact io_amo_conv _ aq rl _ _ _ _ js gp (io_amoadd_w rs2 rs1 rd js gp hc hrun)
  | AMOXOR_W rd rs1 rs2 aq rl =>
    have hm' : ast = .AMO (amoop.AMOXOR, aq, rl, rs2, rs1, 4, rd) := hm
    subst hm'
    obtain ⟨a, ha, hc⟩ := hctx
    simp only [RiscvInstruction.amoBase, Option.some.injEq] at ha
    subst ha
    change (JoltISA.execProgram (JoltISA.amoxorwProgramAuto rd rs1 rs2)).run js = _ at hrun
    exact io_amo_conv _ aq rl _ _ _ _ js gp (io_amoxor_w rs2 rs1 rd js gp hc hrun)
  | AMOAND_W rd rs1 rs2 aq rl =>
    have hm' : ast = .AMO (amoop.AMOAND, aq, rl, rs2, rs1, 4, rd) := hm
    subst hm'
    obtain ⟨a, ha, hc⟩ := hctx
    simp only [RiscvInstruction.amoBase, Option.some.injEq] at ha
    subst ha
    change (JoltISA.execProgram (JoltISA.amoandwProgramAuto rd rs1 rs2)).run js = _ at hrun
    exact io_amo_conv _ aq rl _ _ _ _ js gp (io_amoand_w rs2 rs1 rd js gp hc hrun)
  | AMOOR_W rd rs1 rs2 aq rl =>
    have hm' : ast = .AMO (amoop.AMOOR, aq, rl, rs2, rs1, 4, rd) := hm
    subst hm'
    obtain ⟨a, ha, hc⟩ := hctx
    simp only [RiscvInstruction.amoBase, Option.some.injEq] at ha
    subst ha
    change (JoltISA.execProgram (JoltISA.amoorwProgramAuto rd rs1 rs2)).run js = _ at hrun
    exact io_amo_conv _ aq rl _ _ _ _ js gp (io_amoor_w rs2 rs1 rd js gp hc hrun)
  | AMOMIN_W rd rs1 rs2 aq rl =>
    have hm' : ast = .AMO (amoop.AMOMIN, aq, rl, rs2, rs1, 4, rd) := hm
    subst hm'
    obtain ⟨a, ha, hc⟩ := hctx
    simp only [RiscvInstruction.amoBase, Option.some.injEq] at ha
    subst ha
    change (JoltISA.execProgram (JoltISA.amominwProgramAuto rd rs1 rs2)).run js = _ at hrun
    exact io_amo_conv _ aq rl _ _ _ _ js gp (io_amomin_w rs2 rs1 rd js gp hc hrun)
  | AMOMAX_W rd rs1 rs2 aq rl =>
    have hm' : ast = .AMO (amoop.AMOMAX, aq, rl, rs2, rs1, 4, rd) := hm
    subst hm'
    obtain ⟨a, ha, hc⟩ := hctx
    simp only [RiscvInstruction.amoBase, Option.some.injEq] at ha
    subst ha
    change (JoltISA.execProgram (JoltISA.amomaxwProgramAuto rd rs1 rs2)).run js = _ at hrun
    exact io_amo_conv _ aq rl _ _ _ _ js gp (io_amomax_w rs2 rs1 rd js gp hc hrun)
  | AMOMINU_W rd rs1 rs2 aq rl =>
    have hm' : ast = .AMO (amoop.AMOMINU, aq, rl, rs2, rs1, 4, rd) := hm
    subst hm'
    obtain ⟨a, ha, hc⟩ := hctx
    simp only [RiscvInstruction.amoBase, Option.some.injEq] at ha
    subst ha
    change (JoltISA.execProgram (JoltISA.amominuwProgramAuto rd rs1 rs2)).run js = _ at hrun
    exact io_amo_conv _ aq rl _ _ _ _ js gp (io_amominu_w rs2 rs1 rd js gp hc hrun)
  | AMOMAXU_W rd rs1 rs2 aq rl =>
    have hm' : ast = .AMO (amoop.AMOMAXU, aq, rl, rs2, rs1, 4, rd) := hm
    subst hm'
    obtain ⟨a, ha, hc⟩ := hctx
    simp only [RiscvInstruction.amoBase, Option.some.injEq] at ha
    subst ha
    change (JoltISA.execProgram (JoltISA.amomaxuwProgramAuto rd rs1 rs2)).run js = _ at hrun
    exact io_amo_conv _ aq rl _ _ _ _ js gp (io_amomaxu_w rs2 rs1 rd js gp hc hrun)
  | AMOSWAP_D rd rs1 rs2 aq rl =>
    have hm' : ast = .AMO (amoop.AMOSWAP, aq, rl, rs2, rs1, 8, rd) := hm
    subst hm'
    obtain ⟨a, ha, hc⟩ := hctx
    simp only [RiscvInstruction.amoBase, Option.some.injEq] at ha
    subst ha
    change (JoltISA.execProgram (JoltISA.amoswapdProgramAuto rd rs1 rs2)).run js = _ at hrun
    exact io_amo_conv _ aq rl _ _ _ _ js gp (io_amoswap_d rs2 rs1 rd js gp hc hrun)
  | AMOADD_D rd rs1 rs2 aq rl =>
    have hm' : ast = .AMO (amoop.AMOADD, aq, rl, rs2, rs1, 8, rd) := hm
    subst hm'
    obtain ⟨a, ha, hc⟩ := hctx
    simp only [RiscvInstruction.amoBase, Option.some.injEq] at ha
    subst ha
    change (JoltISA.execProgram (JoltISA.amoadddProgramAuto rd rs1 rs2)).run js = _ at hrun
    exact io_amo_conv _ aq rl _ _ _ _ js gp (io_amoadd_d rs2 rs1 rd js gp hc hrun)
  | AMOXOR_D rd rs1 rs2 aq rl =>
    have hm' : ast = .AMO (amoop.AMOXOR, aq, rl, rs2, rs1, 8, rd) := hm
    subst hm'
    obtain ⟨a, ha, hc⟩ := hctx
    simp only [RiscvInstruction.amoBase, Option.some.injEq] at ha
    subst ha
    change (JoltISA.execProgram (JoltISA.amoxordProgramAuto rd rs1 rs2)).run js = _ at hrun
    exact io_amo_conv _ aq rl _ _ _ _ js gp (io_amoxor_d rs2 rs1 rd js gp hc hrun)
  | AMOAND_D rd rs1 rs2 aq rl =>
    have hm' : ast = .AMO (amoop.AMOAND, aq, rl, rs2, rs1, 8, rd) := hm
    subst hm'
    obtain ⟨a, ha, hc⟩ := hctx
    simp only [RiscvInstruction.amoBase, Option.some.injEq] at ha
    subst ha
    change (JoltISA.execProgram (JoltISA.amoanddProgramAuto rd rs1 rs2)).run js = _ at hrun
    exact io_amo_conv _ aq rl _ _ _ _ js gp (io_amoand_d rs2 rs1 rd js gp hc hrun)
  | AMOOR_D rd rs1 rs2 aq rl =>
    have hm' : ast = .AMO (amoop.AMOOR, aq, rl, rs2, rs1, 8, rd) := hm
    subst hm'
    obtain ⟨a, ha, hc⟩ := hctx
    simp only [RiscvInstruction.amoBase, Option.some.injEq] at ha
    subst ha
    change (JoltISA.execProgram (JoltISA.amoordProgramAuto rd rs1 rs2)).run js = _ at hrun
    exact io_amo_conv _ aq rl _ _ _ _ js gp (io_amoor_d rs2 rs1 rd js gp hc hrun)
  | AMOMIN_D rd rs1 rs2 aq rl =>
    have hm' : ast = .AMO (amoop.AMOMIN, aq, rl, rs2, rs1, 8, rd) := hm
    subst hm'
    obtain ⟨a, ha, hc⟩ := hctx
    simp only [RiscvInstruction.amoBase, Option.some.injEq] at ha
    subst ha
    change (JoltISA.execProgram (JoltISA.amomindProgramAuto rd rs1 rs2)).run js = _ at hrun
    exact io_amo_conv _ aq rl _ _ _ _ js gp (io_amomin_d rs2 rs1 rd js gp hc hrun)
  | AMOMAX_D rd rs1 rs2 aq rl =>
    have hm' : ast = .AMO (amoop.AMOMAX, aq, rl, rs2, rs1, 8, rd) := hm
    subst hm'
    obtain ⟨a, ha, hc⟩ := hctx
    simp only [RiscvInstruction.amoBase, Option.some.injEq] at ha
    subst ha
    change (JoltISA.execProgram (JoltISA.amomaxdProgramAuto rd rs1 rs2)).run js = _ at hrun
    exact io_amo_conv _ aq rl _ _ _ _ js gp (io_amomax_d rs2 rs1 rd js gp hc hrun)
  | AMOMINU_D rd rs1 rs2 aq rl =>
    have hm' : ast = .AMO (amoop.AMOMINU, aq, rl, rs2, rs1, 8, rd) := hm
    subst hm'
    obtain ⟨a, ha, hc⟩ := hctx
    simp only [RiscvInstruction.amoBase, Option.some.injEq] at ha
    subst ha
    change (JoltISA.execProgram (JoltISA.amominudProgramAuto rd rs1 rs2)).run js = _ at hrun
    exact io_amo_conv _ aq rl _ _ _ _ js gp (io_amominu_d rs2 rs1 rd js gp hc hrun)
  | AMOMAXU_D rd rs1 rs2 aq rl =>
    have hm' : ast = .AMO (amoop.AMOMAXU, aq, rl, rs2, rs1, 8, rd) := hm
    subst hm'
    obtain ⟨a, ha, hc⟩ := hctx
    simp only [RiscvInstruction.amoBase, Option.some.injEq] at ha
    subst ha
    change (JoltISA.execProgram (JoltISA.amomaxudProgramAuto rd rs1 rs2)).run js = _ at hrun
    exact io_amo_conv _ aq rl _ _ _ _ js gp (io_amomaxu_d rs2 rs1 rd js gp hc hrun)
  | _ =>
    obtain ⟨a, ha, -⟩ := hctx
    simp [RiscvInstruction.amoBase] at ha

/-- The atomic access premises of a state hold in any state with the same source registers
and device.
For example, the prelude only changes the program counter, so the premises carry over. -/
private theorem amo_access_congr (i : RiscvInstruction) (s t : SailJoltState)
    (h : ∀ r, sourceValue (.xreg r) t = sourceValue (.xreg r) s)
    (hd : t.jolt_device = s.jolt_device) :
    (IoAmoAccess i s → IoAmoAccess i t) ∧ (i.AmoNoFlagWord s → i.AmoNoFlagWord t) := by
  have hb : i.amoBase t = i.amoBase s := by
    cases i <;> simp only [RiscvInstruction.amoBase, h]
  exact ⟨by simp only [IoAmoAccess, hb]; exact id,
    by simp only [RiscvInstruction.AmoNoFlagWord, hb, hd]; exact id⟩

/-- As `block_simulates_io_amo`, where Sail decodes the encoding to `cast` and `cast` executes
like the matching instruction `ast` (for a compressed parcel, its base expansion); with
`cast = ast` the bridge is trivial. The decoded instructions are part of `hinputs`. -/
theorem block_simulates_io_amo_via (program : Rv64ProgramImage SourceInstruction) (b : Block)
    (hruns : b.Runs program) (i : RiscvInstruction) (hrow : b.row.instruction = .riscv i)
    (hsys : SystemInv b.pre) (hio : IoAmoAccess i b.start)
    (hflag : i.AmoNoFlagWord b.start)
    (encoding : BlockEncoding) (hwidth : b.row.is_compressed = encoding.isCompressed)
    (hinputs : ∀ (s : SailState), Related b.pre s →
      ∀ (pc m : BitVec 64) (oldInc : Bool),
      b.pre.sail.regs.get? Register.nextPC = some pc →
      s.regs = (sailRegs b.pre pc m oldInc).regs →
      ∃ inc : Bool,
        should_inc_minstret .Machine s = .ok inc s ∧
        fetch () (Step.setReg s .minstret_increment inc) =
          .ok encoding.fetched (Step.setReg s .minstret_increment inc) ∧
        ∃ (ast cast : instruction), RiscvInstruction.Matches i ast ∧
        (∀ t, Step.StepInvariant t → Step.executeFull cast t = Step.executeFull ast t) ∧
        encoding.decode (Step.setReg s .minstret_increment inc) =
          .ok cast (Step.setReg s .minstret_increment inc)) :
    ∀ s, Related b.pre s → ∃ v s', try_step 0 false s = .ok v s' ∧ Related b.post s' := by
  intro s hrel
  obtain ⟨pc, m, oldInc, hnext, hregs⟩ := hrel.regs
  obtain ⟨inc, hinc, hfetch, ast, cast, hm, hbridge, hdecode⟩ :=
    hinputs s hrel pc m oldInc hnext hregs
  have hp : pc = b.row.address := Option.some.inj (hnext.symm.trans hruns.continues)
  let Gs := Step.preludeJolt { b.pre with sail := s } inc pc
    (if b.row.is_compressed then 2 else 4)
  have hshadow : Shadow ((blockHelper% overlayRows) b.pre.vregs m inc b.start) Gs :=
    (blockHelper% prelude_shadow) b s pc m oldInc inc hp hregs hrel.ram
  have hlift : i.Lifted := by
    clear hinputs hdecode hfetch
    obtain ⟨a, ha, _⟩ := hio
    cases i <;> simp_all [RiscvInstruction.amoBase, RiscvInstruction.Lifted]
  obtain ⟨instrs, hblock, hrun⟩ := hruns.executes
  have hadvice : blockInstrs b.row Gs = blockInstrs b.row b.start := by
    have he := ((blockHelper% advice_shadow) i _ _ hshadow).trans
      ((blockHelper% advice_overlayRows) i b.pre.vregs m inc b.start)
    simp only [blockInstrs, hrow, he]
  have hpatched := (blockHelper% execProgram_overlayRows) (Program.seq instrs)
    b.pre.vregs m inc b.start b.post hrun
  have hsync := execProgram_shadow (Program.seq instrs) _ _ hshadow
  rw [hpatched] at hsync
  obtain ⟨ghostPost, hghost, hpost, _, _⟩ := hsync.ok_exists
  have hrawG := blockInstrs_run i b.row.address b.row.is_compressed Gs instrs
    (by simpa only [← hrow] using hadvice.trans hblock)
  have hhonest : RiscvInstruction.joltRun (honestInstr i Gs) Gs = .ok RETIRE_SUCCESS ghostPost :=
    hrawG.symm.trans hghost
  have hGp : System.systemProject Gs = Step.preludeState s inc pc
      (if b.row.is_compressed then 2 else 4) := by
    dsimp only [Gs]
    rw [Step.systemProject_preludeJolt, (blockHelper% ghost_projects) hrel]
  have hlink : System.systemProject Gs = Gs.sail := hGp
  have hinvG : Step.StepInvariant Gs.sail := hrel.inv.preludeState inc pc _
  have hsources : ∀ r, sourceValue (.xreg r) Gs = sourceValue (.xreg r) b.start := fun r =>
    ((blockHelper% sourceValue_shadow) hshadow r).trans
      ((blockHelper% sourceValue_overlayRows) b.pre.vregs m inc b.start r)
  obtain ⟨hio', hflag'⟩ := amo_access_congr i b.start Gs hsources rfl
  have hmemG : MemRel Gs.jolt_device Gs.sail := hrel.memRel.of_mem_eq rfl
  have hpmaG : Gs.sail.regs.get? Register.pma_regions = some platformPma := by
    simp [Gs, Step.preludeJolt, Step.preludeState, Step.setReg, hregs,
      sailRegs, Std.ExtDHashMap.get?_insert]
  have hhtifG : Gs.sail.regs.get? Register.htif_tohost_base = some none := by
    simpa [Gs, Step.preludeJolt, Step.preludeState, Step.setReg,
      Std.ExtDHashMap.get?_insert] using hrel.htif
  obtain ⟨t, hexec, htregs, htram, htmem⟩ := io_amo_core i ast hm Gs ghostPost
    (hio' hio) (hflag' hflag) hlink hinvG hsys.mstatus_bits hmemG hpmaG hhtifG hhonest
  have hexec' : execute ast (System.systemProject Gs) = .ok RETIRE_SUCCESS t := by
    rw [hlink]; exact hexec
  have hinvPre : Step.StepInvariant (System.systemProject Gs) := by
    rw [hGp]
    exact hrel.inv.preludeState inc pc _
  have hframe := Step.execProgram_regFrame (Program.seq instrs) Gs
  rw [hghost] at hframe
  change Step.RegFrame Gs ghostPost at hframe
  have hinvPost := hinvPre.systemProject_regFrame hframe
  obtain ⟨next, hnextGhost⟩ := (hinvPost.present Register.nextPC).exists_value
  obtain ⟨hn, hcount, hcountInc⟩ :=
    (blockHelper% projected_reads) b.pre b.post ghostPost m inc hpost
  have hnextPost : b.post.sail.regs.get? Register.nextPC = some next := hn.symm.trans hnextGhost
  have hinvT : Step.StepInvariant t :=
    hinvPost.of_agree (fun r _ => by rw [htregs]) (fun r => by
      obtain ⟨v, hv⟩ := (hinvPost.present r).exists_value
      exact ⟨v, by rw [htregs]; exact hv⟩)
  let s' := (blockHelper% finishState) t next m inc
  have hfinish := (blockHelper% finish_run) t hinvT encoding.bits next m inc
    (by rw [htregs]; exact hnextGhost) (by rw [htregs]; exact hcount)
    (by rw [htregs]; exact hcountInc)
  have hfs : ∀ (s : SailState) (pc m : BitVec 64) (inc : Bool),
      (blockHelper% finishState) s pc m inc =
        if inc then Step.setReg (Step.setReg s .PC pc) .minstret (BitVec.addInt m 1)
        else Step.setReg s .PC pc := fun _ _ _ _ => rfl
  have hft : s'.regs = ((blockHelper% finishState) (System.systemProject ghostPost) next m inc).regs := by
    cases inc <;> simp [s', hfs, Step.setReg, htregs]
  have hpcS : s.regs.get? Register.PC = some pc := by
    simp [hregs, sailRegs, Step.setReg, Std.ExtDHashMap.get?_insert, System.systemProject]
  have htry := (blockHelper% encoding_try_step) encoding s hrel.inv inc hinc pc hpcS cast
    hfetch hdecode
  have hstep : try_step 0 false s = .ok false s' := by
    rw [htry]
    simp only [← hwidth]
    rw [← hGp, executeAndFinish_congr cast ast _ _ hinvPre hbridge]
    unfold Step.executeAndFinish Step.executeFull
    simp only [bind, EStateM.bind, hexec', RETIRE_SUCCESS, pure, EStateM.pure]
    exact hfinish
  refine ⟨false, s', hstep, ?_⟩
  have hmem' : s'.mem = t.mem := (blockHelper% finish_mem) t next m inc
  have hdev : ghostPost.jolt_device = b.post.jolt_device := hpost.device
  have hmemT : MemRel b.post.jolt_device s' := by
    rw [← hdev]
    exact htmem.of_mem_eq hmem'
  have hhtifT : (System.systemProject ghostPost).regs.get? Register.htif_tohost_base =
      some none := by
    rw [Step.systemProject_get?_of_not_overlaid _ (by simp [Step.Overlaid]),
      hframe.keep Register.htif_tohost_base (by simp [Step.JoltWritable])]
    change (Step.preludeState s inc pc _).regs.get? Register.htif_tohost_base = some none
    simpa [Step.preludeState, Step.setReg, Std.ExtDHashMap.get?_insert] using hrel.htif
  exact
    { regs := ⟨next, (if inc then BitVec.addInt m 1 else m), inc, hnextPost,
        hft.trans ((blockHelper% finish_regs) b.pre b.post ghostPost m next inc hpost)⟩
      inv := hinvT.stepFinish_retire encoding.bits hfinish
      htif := by
        change ((blockHelper% finishState) t next m inc).regs.get? Register.htif_tohost_base =
          some none
        rw [show ((blockHelper% finishState) t next m inc).regs =
          ((blockHelper% finishState) (System.systemProject ghostPost) next m inc).regs from hft]
        cases inc <;> simpa [hfs, Step.setReg,
          Std.ExtDHashMap.get?_insert] using hhtifT
      ram := fun a ha => by
        rw [hmem']
        exact (htram a ha).trans (hpost.ram a ha)
      present := hmemT.present
      io := hmemT.io
      panic := hmemT.panic
      layout := hmemT.layout
      outputs_size := hmemT.outputs_size }

/-- A block whose source instruction is an atomic memory operation on the doubleword below
`RAM_START_ADDRESS`, in the I/O window, is one Sail `try_step` that preserves the whole-run
relation `Related`.

The instruction is AMOSWAP, AMOADD, AMOXOR, AMOAND, AMOOR, AMOMIN, AMOMAX, AMOMINU or
AMOMAXU, in the word or doubleword form. Alignment and the address range are derived from
the block's retiring run `hruns`, not assumed: Jolt's rows fault on a misaligned address,
where Sail also faults, so a retiring block is aligned. For example, an `AMOADD.D` of `1`
at the first output doubleword is one `try_step` that appends the eight bytes of the old
value plus one to the device's outputs, and the memory relation after the step includes
`outputs_size` and the panic flag.

Premises, by class:
* invariant: `hsys`, the system invariant on the block's entry state.
* platform: `hio`, the accessed doubleword lies below `RAM_START_ADDRESS`.
* from decoding: `hrow`, `hm`, `hwidth` and `hinputs`, the decode-only facts that Sail
  fetches and decodes the instruction word `encoding` to `ast`.
* documented deviation (`docs/riscv-alignment.md`, section 2): `hflag` (`AmoNoFlagWord`).
  No premise on the lowest address or on the stored value is needed: a retiring store
  already lies at or above `memLow`, and the panic word is untouched. -/
theorem block_simulates_io_amo (program : Rv64ProgramImage SourceInstruction) (b : Block)
    (hruns : b.Runs program) (i : RiscvInstruction) (hrow : b.row.instruction = .riscv i)
    (hsys : SystemInv b.pre) (hio : IoAmoAccess i b.start)
    (hflag : i.AmoNoFlagWord b.start)
    (ast : instruction) (hm : RiscvInstruction.Matches i ast)
    (encoding : BlockEncoding) (hwidth : b.row.is_compressed = encoding.isCompressed)
    (hinputs : ∀ (s : SailState), Related b.pre s →
      ∀ (pc m : BitVec 64) (oldInc : Bool),
      b.pre.sail.regs.get? Register.nextPC = some pc →
      s.regs = (sailRegs b.pre pc m oldInc).regs →
      ∃ inc : Bool,
        should_inc_minstret .Machine s = .ok inc s ∧
        fetch () (Step.setReg s .minstret_increment inc) =
          .ok encoding.fetched (Step.setReg s .minstret_increment inc) ∧
        encoding.decode (Step.setReg s .minstret_increment inc) =
          .ok ast (Step.setReg s .minstret_increment inc)) :
    ∀ s, Related b.pre s → ∃ v s', try_step 0 false s = .ok v s' ∧ Related b.post s' := by
  refine block_simulates_io_amo_via program b hruns i hrow hsys hio hflag encoding hwidth ?_
  intro s hrel pc m oldInc hn hr
  obtain ⟨inc, hinc, hf, hd⟩ := hinputs s hrel pc m oldInc hn hr
  exact ⟨inc, hinc, hf, ast, ast, hm, fun _ _ => rfl, hd⟩

end WholeRun
