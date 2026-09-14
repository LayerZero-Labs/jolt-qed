import JoltBytecode.InstructionEquivalence.ProofSupport.BundleLemmas
import JoltBytecode.InstructionEquivalence.ProofSupport.Memory.Alignment
import JoltBytecode.InstructionEquivalence.ProofSupport.InstructionLemmas.LD
import Mathlib.Tactic

/-!
# Memory read pipeline reductions

This file contains exact read evidence records and lemmas that collapse Sail and
Jolt read paths to direct hashmap reads from `SailState.mem`.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option mvcgen.warning false

open Sail PreSail LeanRV64D.Functions
open Std.Do
open virtaddr MemoryAccessType mem_payload

set_option autoImplicit true

noncomputable section

-- ============================================================================
-- Reusable direct-memory collapse lemmas
-- ============================================================================

theorem readBytes_8_eq_loaded_dword (addr : BitVec 64) (s : SailState)
    (hbytes : MemBytesPresentAt s addr 8)
    (h_no_ovf : addr.toNat + 7 < 2 ^ 64) :
    (PreSail.readBytes 8 addr.toNat : SailM _) s =
    .ok (loaded_dword_at s addr hbytes h_no_ovf, none) s := by
  obtain ⟨b0, hb0'⟩ := hbytes 0 (by omega)
  obtain ⟨b1, hb1⟩ := hbytes 1 (by omega)
  obtain ⟨b2, hb2⟩ := hbytes 2 (by omega)
  obtain ⟨b3, hb3⟩ := hbytes 3 (by omega)
  obtain ⟨b4, hb4⟩ := hbytes 4 (by omega)
  obtain ⟨b5, hb5⟩ := hbytes 5 (by omega)
  obtain ⟨b6, hb6⟩ := hbytes 6 (by omega)
  obtain ⟨b7, hb7⟩ := hbytes 7 (by omega)
  have hb0 : s.mem.get? addr.toNat = some b0 := by simpa using hb0'
  simp only [PreSail.readBytes, PreSail.readByte,
             bind, EStateM.bind, pure, EStateM.pure,
             MonadStateOf.get, EStateM.get, getThe, get,
             hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7]
  unfold loaded_dword_at loaded_byte_at loaded_byte_at_nat
  simp only [hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7,
             show (addr + 1).toNat = addr.toNat + 1 from by apply BitVec.toNat_add_of_lt; simp; omega,
             show (addr + 2).toNat = addr.toNat + 2 from by apply BitVec.toNat_add_of_lt; simp; omega,
             show (addr + 3).toNat = addr.toNat + 3 from by apply BitVec.toNat_add_of_lt; simp; omega,
             show (addr + 4).toNat = addr.toNat + 4 from by apply BitVec.toNat_add_of_lt; simp; omega,
             show (addr + 5).toNat = addr.toNat + 5 from by apply BitVec.toNat_add_of_lt; simp; omega,
             show (addr + 6).toNat = addr.toNat + 6 from by apply BitVec.toNat_add_of_lt; simp; omega,
             show (addr + 7).toNat = addr.toNat + 7 from by apply BitVec.toNat_add_of_lt; simp; omega,
             Option.getD]
  rfl

theorem readBytes_1_eq_loaded_byte (addr : BitVec 64) (s : SailState)
    (hbytes : MemBytesPresentAt s addr 1) :
    (PreSail.readBytes 1 addr.toNat : SailM _) s =
    .ok (loaded_byte_at s addr (by simpa using hbytes 0 (by omega)), none) s := by
  obtain ⟨b0, hb0'⟩ := hbytes 0 (by omega)
  have hb0 : s.mem.get? addr.toNat = some b0 := by simpa using hb0'
  simp only [PreSail.readBytes, PreSail.readByte,
             bind, EStateM.bind, pure, EStateM.pure,
             MonadStateOf.get, EStateM.get, getThe, get,
             hb0]
  unfold loaded_byte_at loaded_byte_at_nat
  simp only [hb0, Option.get_some]

theorem readBytes_2_eq_loaded_halfword (addr : BitVec 64) (s : SailState)
    (hbytes : MemBytesPresentAt s addr 2)
    (h_no_ovf : addr.toNat + 1 < 2 ^ 64) :
    (PreSail.readBytes 2 addr.toNat : SailM _) s =
    .ok (loaded_halfword_at s addr hbytes h_no_ovf, none) s := by
  obtain ⟨b0, hb0'⟩ := hbytes 0 (by omega)
  obtain ⟨b1, hb1⟩ := hbytes 1 (by omega)
  have hb0 : s.mem.get? addr.toNat = some b0 := by simpa using hb0'
  simp only [PreSail.readBytes, PreSail.readByte,
             bind, EStateM.bind, pure, EStateM.pure,
             MonadStateOf.get, EStateM.get, getThe, get,
             hb0, hb1]
  unfold loaded_halfword_at loaded_byte_at loaded_byte_at_nat
  simp only [hb0, hb1,
             show (addr + 1).toNat = addr.toNat + 1 from by apply BitVec.toNat_add_of_lt; simp; omega,
             Option.get_some]
  rfl

theorem readBytes_4_eq_loaded_word (addr : BitVec 64) (s : SailState)
    (hbytes : MemBytesPresentAt s addr 4)
    (h_no_ovf : addr.toNat + 3 < 2 ^ 64) :
    (PreSail.readBytes 4 addr.toNat : SailM _) s =
    .ok (loaded_word_at s addr hbytes h_no_ovf, none) s := by
  obtain ⟨b0, hb0'⟩ := hbytes 0 (by omega)
  obtain ⟨b1, hb1⟩ := hbytes 1 (by omega)
  obtain ⟨b2, hb2⟩ := hbytes 2 (by omega)
  obtain ⟨b3, hb3⟩ := hbytes 3 (by omega)
  have hb0 : s.mem.get? addr.toNat = some b0 := by simpa using hb0'
  simp only [PreSail.readBytes, PreSail.readByte,
             bind, EStateM.bind, pure, EStateM.pure,
             MonadStateOf.get, EStateM.get, getThe, get,
             hb0, hb1, hb2, hb3]
  unfold loaded_word_at loaded_byte_at loaded_byte_at_nat
  simp only [hb0, hb1, hb2, hb3,
             show (addr + 1).toNat = addr.toNat + 1 from by apply BitVec.toNat_add_of_lt; simp; omega,
             show (addr + 2).toNat = addr.toNat + 2 from by apply BitVec.toNat_add_of_lt; simp; omega,
             show (addr + 3).toNat = addr.toNat + 3 from by apply BitVec.toNat_add_of_lt; simp; omega,
             Option.get_some]
  rfl

theorem read_ram_1_eq_loaded_byte (addr : BitVec 64) (s : SailState)
    (hbytes : MemBytesPresentAt s addr 1) :
    LeanRV64D.Functions.read_ram read_kind.Read_plain (physaddr.Physaddr addr) 1 false s =
    .ok (loaded_byte_at s addr (by simpa using hbytes 0 (by omega)), default_meta) s := by
  dsimp [LeanRV64D.Functions.read_ram,
         Sail.ConcurrencyInterfaceV1.sail_mem_read,
         PreSail.ConcurrencyInterfaceV1.sail_mem_read,
         default_meta]
  simp only [bind, EStateM.bind, pure, EStateM.pure]
  rw [readBytes_1_eq_loaded_byte addr s hbytes]
  simp [EStateM.pure]

theorem read_ram_2_eq_loaded_halfword (addr : BitVec 64) (s : SailState)
    (hbytes : MemBytesPresentAt s addr 2)
    (h_no_ovf : addr.toNat + 1 < 2 ^ 64) :
    LeanRV64D.Functions.read_ram read_kind.Read_plain (physaddr.Physaddr addr) 2 false s =
    .ok (loaded_halfword_at s addr hbytes h_no_ovf, default_meta) s := by
  dsimp [LeanRV64D.Functions.read_ram,
         Sail.ConcurrencyInterfaceV1.sail_mem_read,
         PreSail.ConcurrencyInterfaceV1.sail_mem_read,
         default_meta]
  simp only [bind, EStateM.bind, pure, EStateM.pure]
  rw [readBytes_2_eq_loaded_halfword addr s hbytes h_no_ovf]
  simp [EStateM.pure]

theorem read_ram_4_eq_loaded_word (addr : BitVec 64) (s : SailState)
    (hbytes : MemBytesPresentAt s addr 4)
    (h_no_ovf : addr.toNat + 3 < 2 ^ 64) :
    LeanRV64D.Functions.read_ram read_kind.Read_plain (physaddr.Physaddr addr) 4 false s =
    .ok (loaded_word_at s addr hbytes h_no_ovf, default_meta) s := by
  dsimp [LeanRV64D.Functions.read_ram,
         Sail.ConcurrencyInterfaceV1.sail_mem_read,
         PreSail.ConcurrencyInterfaceV1.sail_mem_read,
         default_meta]
  simp only [bind, EStateM.bind, pure, EStateM.pure]
  rw [readBytes_4_eq_loaded_word addr s hbytes h_no_ovf]
  simp [EStateM.pure]

theorem checked_mem_read_1_eq_loaded_byte (addr : BitVec 64) (s : SailState)
    (hbytes : MemBytesPresentAt s addr 1)
    (hpmp : Assumptions.LoadPmpOk addr 1 s)
    (hmmio : Assumptions.NotReadableMmio addr 1 s) :
    checked_mem_read (Load Data) Privilege.Machine (physaddr.Physaddr addr) 1 false false false false s =
    .ok (Ok (loaded_byte_at s addr (by simpa using hbytes 0 (by omega)), default_meta)) s := by
  unfold checked_mem_read
  simp only [bind, EStateM.bind, pure, EStateM.pure, hpmp, hmmio,
             Bool.false_eq_true, if_false]
  unfold read_kind_of_flags
  simp only [pure, EStateM.pure]
  rw [read_ram_1_eq_loaded_byte addr s hbytes]

theorem checked_mem_read_2_eq_loaded_halfword (addr : BitVec 64) (s : SailState)
    (hbytes : MemBytesPresentAt s addr 2)
    (h_no_ovf : addr.toNat + 1 < 2 ^ 64)
    (hpmp : Assumptions.LoadPmpOk addr 2 s)
    (hmmio : Assumptions.NotReadableMmio addr 2 s) :
    checked_mem_read (Load Data) Privilege.Machine (physaddr.Physaddr addr) 2 false false false false s =
    .ok (Ok (loaded_halfword_at s addr hbytes h_no_ovf, default_meta)) s := by
  unfold checked_mem_read
  simp only [bind, EStateM.bind, pure, EStateM.pure, hpmp, hmmio,
             Bool.false_eq_true, if_false]
  unfold read_kind_of_flags
  simp only [pure, EStateM.pure]
  rw [read_ram_2_eq_loaded_halfword addr s hbytes h_no_ovf]

theorem checked_mem_read_4_eq_loaded_word (addr : BitVec 64) (s : SailState)
    (hbytes : MemBytesPresentAt s addr 4)
    (h_no_ovf : addr.toNat + 3 < 2 ^ 64)
    (hpmp : Assumptions.LoadPmpOk addr 4 s)
    (hmmio : Assumptions.NotReadableMmio addr 4 s) :
    checked_mem_read (Load Data) Privilege.Machine (physaddr.Physaddr addr) 4 false false false false s =
    .ok (Ok (loaded_word_at s addr hbytes h_no_ovf, default_meta)) s := by
  unfold checked_mem_read
  simp only [bind, EStateM.bind, pure, EStateM.pure, hpmp, hmmio,
             Bool.false_eq_true, if_false]
  unfold read_kind_of_flags
  simp only [pure, EStateM.pure]
  rw [read_ram_4_eq_loaded_word addr s hbytes h_no_ovf]

theorem mem_read_1_eq_loaded_byte (addr : BitVec 64) (s : SailState)
    (hpriv : Assumptions.CurPrivilegeMachine s)
    (hmprv : Assumptions.MstatusMprvZero s)
    (hbytes : MemBytesPresentAt s addr 1)
    (hpmp : Assumptions.LoadPmpOk addr 1 s)
    (hmmio : Assumptions.NotReadableMmio addr 1 s) :
    mem_read (Load Data) (physaddr.Physaddr addr) 1 false false false s =
    .ok (Ok (loaded_byte_at s addr (by simpa using hbytes 0 (by omega)))) s := by
  obtain ⟨mval, h_ms_regs, h_mprv⟩ := hmprv.value
  have h_ms_read := readReg_eq Register.mstatus s mval h_ms_regs
  have h_priv := readReg_eq Register.cur_privilege s Privilege.Machine hpriv.value
  unfold mem_read mem_read_priv
  simp only [bind, EStateM.bind, pure, EStateM.pure, h_ms_read, h_priv]
  unfold effectivePrivilege
  simp only [h_mprv, bne, BEq.beq]
  unfold mem_read_priv_meta
  simp only [bind, EStateM.bind, pure, EStateM.pure,
             Bool.false_or, Bool.false_and, Bool.false_eq_true, ite_false]
  simp (config := { decide := true }) only [ite_false, EStateM.pure, MemoryOpResult_drop_meta]
  rw [checked_mem_read_1_eq_loaded_byte addr s hbytes hpmp hmmio]

theorem mem_read_2_eq_loaded_halfword (addr : BitVec 64) (s : SailState)
    (hpriv : Assumptions.CurPrivilegeMachine s)
    (hmprv : Assumptions.MstatusMprvZero s)
    (h_no_ovf : addr.toNat + 1 < 2 ^ 64)
    (hbytes : MemBytesPresentAt s addr 2)
    (hpmp : Assumptions.LoadPmpOk addr 2 s)
    (hmmio : Assumptions.NotReadableMmio addr 2 s) :
    mem_read (Load Data) (physaddr.Physaddr addr) 2 false false false s =
    .ok (Ok (loaded_halfword_at s addr hbytes h_no_ovf)) s := by
  obtain ⟨mval, h_ms_regs, h_mprv⟩ := hmprv.value
  have h_ms_read := readReg_eq Register.mstatus s mval h_ms_regs
  have h_priv := readReg_eq Register.cur_privilege s Privilege.Machine hpriv.value
  unfold mem_read mem_read_priv
  simp only [bind, EStateM.bind, pure, EStateM.pure, h_ms_read, h_priv]
  unfold effectivePrivilege
  simp only [h_mprv, bne, BEq.beq]
  unfold mem_read_priv_meta
  simp only [bind, EStateM.bind, pure, EStateM.pure,
             Bool.false_or, Bool.false_and, Bool.false_eq_true, ite_false]
  simp (config := { decide := true }) only [ite_false, EStateM.pure, MemoryOpResult_drop_meta]
  rw [checked_mem_read_2_eq_loaded_halfword addr s hbytes h_no_ovf hpmp hmmio]

theorem mem_read_4_eq_loaded_word (addr : BitVec 64) (s : SailState)
    (hpriv : Assumptions.CurPrivilegeMachine s)
    (hmprv : Assumptions.MstatusMprvZero s)
    (h_no_ovf : addr.toNat + 3 < 2 ^ 64)
    (hbytes : MemBytesPresentAt s addr 4)
    (hpmp : Assumptions.LoadPmpOk addr 4 s)
    (hmmio : Assumptions.NotReadableMmio addr 4 s) :
    mem_read (Load Data) (physaddr.Physaddr addr) 4 false false false s =
    .ok (Ok (loaded_word_at s addr hbytes h_no_ovf)) s := by
  obtain ⟨mval, h_ms_regs, h_mprv⟩ := hmprv.value
  have h_ms_read := readReg_eq Register.mstatus s mval h_ms_regs
  have h_priv := readReg_eq Register.cur_privilege s Privilege.Machine hpriv.value
  unfold mem_read mem_read_priv
  simp only [bind, EStateM.bind, pure, EStateM.pure, h_ms_read, h_priv]
  unfold effectivePrivilege
  simp only [h_mprv, bne, BEq.beq]
  unfold mem_read_priv_meta
  simp only [bind, EStateM.bind, pure, EStateM.pure,
             Bool.false_or, Bool.false_and, Bool.false_eq_true, ite_false]
  simp (config := { decide := true }) only [ite_false, EStateM.pure, MemoryOpResult_drop_meta]
  rw [checked_mem_read_4_eq_loaded_word addr s hbytes h_no_ovf hpmp hmmio]

theorem vmem_read_addr_byte_bridge (addr : BitVec 64) (offset : BitVec 64) (s : SailState)
    (hpriv : Assumptions.CurPrivilegeMachine s)
    (hmprv : Assumptions.MstatusMprvZero s)
    (ha : AlignedAccess addr 1)
    (value : BitVec 8)
    (h_mem :
      mem_read (Load Data) (physaddr.Physaddr addr) 1 false false false s =
        .ok (Ok value) s) :
    vmem_read_addr (Virtaddr addr) offset 1 (Load Data) false false false s =
    .ok (Ok value) s := by
  unfold vmem_read_addr
  simp only [ha.misalign, Bool.false_eq_true, if_false]
  unfold SailME.run PreSail.PreSailME.run
  have htranslate :=
    translateAddr_load_data_of_machine_mprv_zero addr s hpriv hmprv
  simp [bind, EStateM.bind, pure, EStateM.pure, EStateM.map,
        ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont,
        ExceptT.pure, ExceptT.lift, ExceptT.map, ExceptT.instMonadLift,
        MonadLift.monadLift, SailME.throw, PreSail.PreSailME.throw, MonadExceptOf.throw,
        Except.ok, Except.error,
        misaligned_order, sys_misaligned_order_decreasing,
        bits_of_virtaddr, Sail.assert, PreSail.assert,
        untilFuelM, untilFuelM.go, zeros, BitVec.zero, BitVec.addInt,
        Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange',
        liftM, monadLift, Functor.map,
        ha.split, htranslate, h_mem]
  change 0#8 ||| value.shiftLeft 0 = value
  rw [BitVec.shiftLeft_eq]
  rw [BitVec.shiftLeft_zero]
  rw [BitVec.zero_or]

theorem vmem_read_byte_reduces (imm : BitVec 12) (rs1 : regidx)
    (s : SailState)
    (hpriv : Assumptions.CurPrivilegeMachine s)
    (hmprv : Assumptions.MstatusMprvZero s)
    (v : BitVec 64) (hrx : rX_bits rs1 s = .ok v s)
    (ha : AlignedAccess (v + sign_extend (m := 64) imm) 1)
    (value : BitVec 8)
    (h_mem :
      mem_read (Load Data) (physaddr.Physaddr (v + sign_extend (m := 64) imm)) 1 false false false s =
        .ok (Ok value) s) :
    vmem_read rs1 (sign_extend (m := 64) imm) 1 (Load Data) false false false s =
    .ok (Ok value) s := by
  unfold vmem_read
  unfold SailME.run PreSail.PreSailME.run
  simp [bind, EStateM.bind, pure, EStateM.pure, EStateM.map,
        ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont,
        ExceptT.pure, ExceptT.lift,
        MonadLift.monadLift, liftM, monadLift, Functor.map,
        ext_data_get_addr, hrx,
        vmem_read_addr_byte_bridge _ _ s hpriv hmprv ha value h_mem]

theorem vmem_read_addr_halfword_bridge (addr : BitVec 64) (offset : BitVec 64) (s : SailState)
    (hpriv : Assumptions.CurPrivilegeMachine s)
    (hmprv : Assumptions.MstatusMprvZero s)
    (ha : AlignedAccess addr 2)
    (value : BitVec 16)
    (h_mem :
      mem_read (Load Data) (physaddr.Physaddr addr) 2 false false false s =
        .ok (Ok value) s) :
    vmem_read_addr (Virtaddr addr) offset 2 (Load Data) false false false s =
    .ok (Ok value) s := by
  unfold vmem_read_addr
  simp only [ha.misalign, Bool.false_eq_true, if_false]
  unfold SailME.run PreSail.PreSailME.run
  have htranslate :=
    translateAddr_load_data_of_machine_mprv_zero addr s hpriv hmprv
  simp [bind, EStateM.bind, pure, EStateM.pure, EStateM.map,
        ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont,
        ExceptT.pure, ExceptT.lift, ExceptT.map, ExceptT.instMonadLift,
        MonadLift.monadLift, SailME.throw, PreSail.PreSailME.throw, MonadExceptOf.throw,
        Except.ok, Except.error,
        misaligned_order, sys_misaligned_order_decreasing,
        bits_of_virtaddr, Sail.assert, PreSail.assert,
        untilFuelM, untilFuelM.go, zeros, BitVec.zero, BitVec.addInt,
        Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange',
        liftM, monadLift, Functor.map,
        ha.split, htranslate, h_mem]
  change 0#16 ||| value.shiftLeft 0 = value
  rw [BitVec.shiftLeft_eq]
  rw [BitVec.shiftLeft_zero]
  rw [BitVec.zero_or]

theorem vmem_read_addr_word_bridge (addr : BitVec 64) (offset : BitVec 64) (s : SailState)
    (hpriv : Assumptions.CurPrivilegeMachine s)
    (hmprv : Assumptions.MstatusMprvZero s)
    (ha : AlignedAccess addr 4)
    (value : BitVec 32)
    (h_mem :
      mem_read (Load Data) (physaddr.Physaddr addr) 4 false false false s =
        .ok (Ok value) s) :
    vmem_read_addr (Virtaddr addr) offset 4 (Load Data) false false false s =
    .ok (Ok value) s := by
  unfold vmem_read_addr
  simp only [ha.misalign, Bool.false_eq_true, if_false]
  unfold SailME.run PreSail.PreSailME.run
  have htranslate :=
    translateAddr_load_data_of_machine_mprv_zero addr s hpriv hmprv
  simp [bind, EStateM.bind, pure, EStateM.pure, EStateM.map,
        ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont,
        ExceptT.pure, ExceptT.lift, ExceptT.map, ExceptT.instMonadLift,
        MonadLift.monadLift, SailME.throw, PreSail.PreSailME.throw, MonadExceptOf.throw,
        Except.ok, Except.error,
        misaligned_order, sys_misaligned_order_decreasing,
        bits_of_virtaddr, Sail.assert, PreSail.assert,
        untilFuelM, untilFuelM.go, zeros, BitVec.zero, BitVec.addInt,
        Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange',
        liftM, monadLift, Functor.map,
        ha.split, htranslate, h_mem]
  change 0#32 ||| value.shiftLeft 0 = value
  rw [BitVec.shiftLeft_eq]
  rw [BitVec.shiftLeft_zero]
  rw [BitVec.zero_or]

theorem read_ram_eq_loaded_dword (addr : BitVec 64) (s : SailState)
    (hbytes : MemBytesPresentAt s addr 8)
    (h_no_ovf : addr.toNat + 7 < 2 ^ 64) :
    LeanRV64D.Functions.read_ram read_kind.Read_plain (physaddr.Physaddr addr) 8 false s =
    .ok (loaded_dword_at s addr hbytes h_no_ovf, default_meta) s := by
  dsimp [LeanRV64D.Functions.read_ram,
         Sail.ConcurrencyInterfaceV1.sail_mem_read,
         PreSail.ConcurrencyInterfaceV1.sail_mem_read,
         default_meta]
  simp only [bind, EStateM.bind, pure, EStateM.pure]
  rw [readBytes_8_eq_loaded_dword addr s hbytes h_no_ovf]
  simp [EStateM.pure]

theorem checked_mem_read_eq_loaded_dword (addr : BitVec 64) (s : SailState)
    (hbytes : MemBytesPresentAt s addr 8)
    (h_no_ovf : addr.toNat + 7 < 2 ^ 64)
    (hpmp : Assumptions.LoadPmpOk addr 8 s)
    (hmmio : Assumptions.NotReadableMmio addr 8 s) :
    checked_mem_read (Load Data) Privilege.Machine (physaddr.Physaddr addr) 8 false false false false s =
    .ok (Ok (loaded_dword_at s addr hbytes h_no_ovf, default_meta)) s := by
  unfold checked_mem_read
  simp only [bind, EStateM.bind, pure, EStateM.pure, hpmp, hmmio,
             Bool.false_eq_true, if_false]
  unfold read_kind_of_flags
  simp only [pure, EStateM.pure]
  rw [read_ram_eq_loaded_dword addr s hbytes h_no_ovf]

theorem mem_read_eq_loaded_dword (addr : BitVec 64) (s : SailState)
    (hpriv : Assumptions.CurPrivilegeMachine s)
    (hmprv : Assumptions.MstatusMprvZero s)
    (h_no_ovf : addr.toNat + 7 < 2 ^ 64)
    (hbytes : MemBytesPresentAt s addr 8)
    (hpmp : Assumptions.LoadPmpOk addr 8 s)
    (hmmio : Assumptions.NotReadableMmio addr 8 s) :
    mem_read (Load Data) (physaddr.Physaddr addr) 8 false false false s =
    .ok (Ok (loaded_dword_at s addr hbytes h_no_ovf)) s := by
  obtain ⟨mval, h_ms_regs, h_mprv⟩ := hmprv.value
  have h_ms_read := readReg_eq Register.mstatus s mval h_ms_regs
  have h_priv := readReg_eq Register.cur_privilege s Privilege.Machine hpriv.value
  unfold mem_read mem_read_priv
  simp only [bind, EStateM.bind, pure, EStateM.pure, h_ms_read, h_priv]
  unfold effectivePrivilege
  simp only [h_mprv, bne, BEq.beq]
  unfold mem_read_priv_meta
  simp only [bind, EStateM.bind, pure, EStateM.pure,
             Bool.false_or, Bool.false_and, Bool.false_eq_true, ite_false]
  simp (config := { decide := true }) only [ite_false, EStateM.pure, MemoryOpResult_drop_meta]
  rw [checked_mem_read_eq_loaded_dword addr s hbytes h_no_ovf hpmp hmmio]

theorem vmem_read_addr_pipeline_bridge (addr : BitVec 64) (s : SailState)
    (hpriv : Assumptions.CurPrivilegeMachine s)
    (hmprv : Assumptions.MstatusMprvZero s)
    (ha : AlignedAccess addr 8)
    (value : BitVec 64)
    (h_mem :
      mem_read (Load Data) (physaddr.Physaddr addr) 8 false false false s =
        .ok (Ok value) s) :
    vmem_read_addr (Virtaddr addr) 0 8 (Load Data) false false false s =
    .ok (Ok value) s := by
  unfold vmem_read_addr
  simp only [ha.misalign, Bool.false_eq_true, if_false]
  unfold SailME.run PreSail.PreSailME.run
  have htranslate :=
    translateAddr_load_data_of_machine_mprv_zero addr s hpriv hmprv
  simp [ExceptT.mk, ExceptT.run,
        SailME.throw, PreSail.PreSailME.throw, MonadExceptOf.throw,
        misaligned_order, sys_misaligned_order_decreasing,
        bits_of_virtaddr, Sail.assert, PreSail.assert,
        untilFuelM, untilFuelM.go, zeros, BitVec.zero, BitVec.addInt,
        ha.split]
  simp only [liftM, monadLift, MonadLift.monadLift,
             ExceptT.lift, ExceptT.mk,
             bind, EStateM.bind, EStateM.map,
             Functor.map, htranslate, h_mem,
             ExceptT.bind, ExceptT.bindCont, ExceptT.map,
             Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange']
  simp [pure, EStateM.pure, ExceptT.pure, ExceptT.mk]

theorem vmem_read_addr_dword_reduces (addr : BitVec 64) (s : SailState)
    (hpriv : Assumptions.CurPrivilegeMachine s)
    (hmprv : Assumptions.MstatusMprvZero s)
    (hda : AlignedDwordAccess addr)
    (hbytes : MemBytesPresentAt s addr 8)
    (hpmp : Assumptions.LoadPmpOk addr 8 s)
    (hmmio : Assumptions.NotReadableMmio addr 8 s) :
    vmem_read_addr (Virtaddr addr) 0 8 (Load Data) false false false s =
    .ok (Ok (loaded_dword_at s addr hbytes hda.no_ovf)) s :=
  vmem_read_addr_pipeline_bridge addr s hpriv hmprv hda.toAlignedAccess
    (loaded_dword_at s addr hbytes hda.no_ovf)
    (mem_read_eq_loaded_dword addr s hpriv hmprv hda.no_ovf hbytes hpmp hmmio)

theorem vmem_read_word_reduces (imm : BitVec 12) (rs1 : regidx)
    (s : SailState)
    (hpriv : Assumptions.CurPrivilegeMachine s)
    (hmprv : Assumptions.MstatusMprvZero s)
    (v : BitVec 64) (hrx : rX_bits rs1 s = .ok v s)
    (ha : AlignedAccess (v + sign_extend (m := 64) imm) 4)
    (value : BitVec 32)
    (h_mem :
      mem_read (Load Data) (physaddr.Physaddr (v + sign_extend (m := 64) imm)) 4 false false false s =
        .ok (Ok value) s) :
    vmem_read rs1 (sign_extend (m := 64) imm) 4 (Load Data) false false false s =
    .ok (Ok value) s := by
  unfold vmem_read
  unfold SailME.run PreSail.PreSailME.run
  simp [bind, EStateM.bind, pure, EStateM.pure, EStateM.map,
        ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont,
        ExceptT.pure, ExceptT.lift,
        MonadLift.monadLift, liftM, monadLift, Functor.map,
        ext_data_get_addr, hrx,
        vmem_read_addr_word_bridge _ _ s hpriv hmprv ha value h_mem]

theorem vmem_read_halfword_reduces (imm : BitVec 12) (rs1 : regidx)
    (s : SailState)
    (hpriv : Assumptions.CurPrivilegeMachine s)
    (hmprv : Assumptions.MstatusMprvZero s)
    (v : BitVec 64) (hrx : rX_bits rs1 s = .ok v s)
    (ha : AlignedAccess (v + sign_extend (m := 64) imm) 2)
    (value : BitVec 16)
    (h_mem :
      mem_read (Load Data) (physaddr.Physaddr (v + sign_extend (m := 64) imm)) 2 false false false s =
        .ok (Ok value) s) :
    vmem_read rs1 (sign_extend (m := 64) imm) 2 (Load Data) false false false s =
    .ok (Ok value) s := by
  unfold vmem_read
  unfold SailME.run PreSail.PreSailME.run
  simp [bind, EStateM.bind, pure, EStateM.pure, EStateM.map,
        ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont,
        ExceptT.pure, ExceptT.lift,
        MonadLift.monadLift, liftM, monadLift, Functor.map,
        ext_data_get_addr, hrx,
        vmem_read_addr_halfword_bridge _ _ s hpriv hmprv ha value h_mem]

/-- Under exact aligned-dword facts, Sail's virtual-memory read pipeline
reduces to a direct dword read from the hash-map model. -/
theorem aligned_dword_vmem_read_reduces (addr : BitVec 64) (s : SailState)
    (hpriv : Assumptions.CurPrivilegeMachine s)
    (hmprv : Assumptions.MstatusMprvZero s)
    (haligned : AlignedDwordAccess addr)
    (hbytes : MemBytesPresentAt s addr 8)
    (hpmp : Assumptions.LoadPmpOk addr 8 s)
    (hmmio : Assumptions.NotReadableMmio addr 8 s) :
    vmem_read_addr (Virtaddr addr) 0 8 (Load Data) false false false s =
      .ok (Ok (loaded_dword_at s addr hbytes haligned.no_ovf)) s := by
  exact
    vmem_read_addr_dword_reduces addr s hpriv hmprv haligned hbytes hpmp hmmio

/-- Specialised `vreg_LD` helper: if virtual source register `vs1` contains an
aligned dword address backed by exact flat-memory facts, then `vreg_LD` writes
the corresponding `loaded_dword_at` value into `vd`. -/
theorem vreg_LD_run_of_aligned_dword_phys
    {faultClass : JoltISA.LoadFaultClass}
    (vd vs1 : BitVec 7) (js : SailJoltState) (addr : BitVec 64)
    (hvs1 : js.vregs vs1 = addr)
    (hpriv : Assumptions.CurPrivilegeMachine js.sail)
    (hmprv : Assumptions.MstatusMprvZero js.sail)
    (haligned : AlignedDwordAccess addr)
    (hbytes : MemBytesPresentAt js.sail addr 8)
    (hpmp : Assumptions.LoadPmpOk addr 8 js.sail)
    (hmmio : Assumptions.NotReadableMmio addr 8 js.sail)
    (hvd : WritableVReg vd) :
    (JoltISA.execInstr (.LD faultClass (.vreg vd) (.vreg vs1) 0)).run js = .ok RETIRE_SUCCESS
      { sail := js.sail
        vregs := fun r =>
          if r = vd then loaded_dword_at js.sail addr hbytes haligned.no_ovf else js.vregs r } := by
  have hread :
      vmem_read_addr (Virtaddr (js.vregs vs1 + sign_extend (m := 64) (0 : BitVec 12))) 0 8
        (Load Data) false false false js.sail =
      .ok (Ok (loaded_dword_at js.sail addr hbytes haligned.no_ovf)) js.sail := by
    have h0 : sign_extend (m := 64) (0 : BitVec 12) = (0 : BitVec 64) := by decide
    rw [hvs1, h0]
    have haddr : addr + (0 : BitVec 64) = addr := by simp
    rw [haddr]
    exact aligned_dword_vmem_read_reduces addr js.sail hpriv hmprv haligned hbytes hpmp hmmio
  have halign :
      (js.vregs vs1 + sign_extend (m := 64) (0 : BitVec 12)) &&& (7 : BitVec 64) = 0 := by
    have h0 : sign_extend (m := 64) (0 : BitVec 12) = (0 : BitVec 64) := by decide
    rw [hvs1, h0]
    have haddr : addr + (0 : BitVec 64) = addr := by simp
    rw [haddr]
    exact haligned.align
  exact
    JoltISA.ld_run_vreg_vreg_from_memory_read
      vd vs1 0 js (loaded_dword_at js.sail addr hbytes haligned.no_ovf) halign hread hvd

end
