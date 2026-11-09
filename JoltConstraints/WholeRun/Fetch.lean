import JoltBytecode.Step.TryStep

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail
  LeanRV64D LeanRV64D.Functions

set_option autoImplicit false

noncomputable section

namespace WholeRun

/-- The byte at `a` in Sail's memory, using zero when absent as Jolt's RAM does.
For example, two absent bytes give a zero parcel in `memParcel`.
Sail's fetch itself requires the bytes it reads to be present. -/
def memByte (s : SailState) (a : Nat) : BitVec 8 := (s.mem.get? a).getD 0

/-- The 16-bit parcel at `a`, with the low byte first in memory.
For example, bytes `0x13` and `0x01` give `0x0113`. -/
def memParcel (s : SailState) (a : Nat) : BitVec 16 := memByte s (a + 1) ++ memByte s a

/-- The compressed parcel or base word beginning at `a`.
For example, a low parcel ending in binary `11` selects a 32-bit base word. -/
def fetchedAt (s : SailState) (a : Nat) : FetchResult :=
  let lo := memParcel s a
  if lo.extractLsb 1 0 = 0b11#2 then .F_Base (memParcel s (a + 2) ++ lo) else .F_RVC lo

/-- Fetch translation in M-mode is the identity, even when MPRV is set.
For example, the virtual PC `0x80000000` translates to that physical address. -/
theorem translateAddr_fetch_of_machine (addr : BitVec 64) (s : SailState)
    (hmachine : s.regs.get? Register.cur_privilege = some Privilege.Machine)
    (hmstatus : Assumptions.SailRegReadable Register.mstatus s) :
    translateAddr (.Virtaddr addr) (.InstructionFetch ()) s =
      .ok (.Ok (.Physaddr addr, init_ext_ptw)) s := by
  obtain ⟨ms, hms⟩ := Step.readReg_present Register.mstatus s hmstatus
  have hpriv := readReg_eq_of_get? Register.cur_privilege s _ hmachine
  unfold translateAddr SailME.run Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.run
  simp (config := { decide := true }) [bind, EStateM.bind, pure, EStateM.pure, EStateM.map,
    ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont,
    ExceptT.pure, ExceptT.lift, MonadLift.monadLift, liftM, monadLift, Functor.map,
    effectivePrivilege, translationMode, is_shadow_stack_access,
    hms, hpriv, bits_of_virtaddr, BEq.beq]
  rfl

private theorem matching_ram (addr : BitVec 64) (ram : PMA_Region)
    (hbase : ram.base = 0x80000000)
    (hlo : JoltISA.RAM_START_ADDRESS ≤ addr.toNat)
    (hhi : addr.toNat + 2 ≤ JoltISA.RAM_START_ADDRESS + ram.size.toNat) :
    matching_pma [ram] (.Physaddr addr) 2 = some ram := by
  have hsub : (addr - (0x80000000 : BitVec 64)).toNat = addr.toNat - 0x80000000 :=
    BitVec.toNat_sub_of_le (by simpa [BitVec.le_def, JoltISA.RAM_START_ADDRESS] using hlo)
  have hadd : addr + 2#64 - (0x80000000 : BitVec 64) =
      (addr - (0x80000000 : BitVec 64)) + 2#64 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.add_comm (2#64)]
  have hsum : (addr - (0x80000000 : BitVec 64)).toNat + (2#64).toNat < 2 ^ 64 := by
    change (addr - (0x80000000 : BitVec 64)).toNat + 2 < 2 ^ 64
    rw [hsub]
    have := addr.isLt
    simp only [JoltISA.RAM_START_ADDRESS] at hlo
    omega
  have hend : (0x80000000 : BitVec 64) + ram.size - 0x80000000 = ram.size := by
    rw [BitVec.add_comm]
    exact BitVec.add_sub_cancel _ _
  have hsubset : range_subset addr 2#64 (0x80000000 : BitVec 64) ram.size = true := by
    simp only [range_subset, hend, hadd, zopz0zIzJ_u, Sail.BitVec.toNatInt,
      BitVec.toNat_add_of_lt hsum, hsub, show (2#64).toNat = 2 by rfl,
      Bool.and_eq_true, decide_eq_true_eq]
    simp only [Int.ofNat_eq_natCast, Int.ofNat_le]
    simp only [JoltISA.RAM_START_ADDRESS] at hlo hhi
    omega
  have hzero : zero_extend (m := 64) addr = addr := BitVec.setWidth_eq addr
  have htwo : to_bits (l := 64) 2 = 2#64 := by rfl
  simp only [matching_pma, matching_pma_bits_range, bits_of_physaddr,
    hzero, htwo, hbase, hsubset, ↓reduceIte]

private theorem read_ram_parcel (s : SailState) (a : BitVec 64)
    (hbytes : ∀ i < 2, ∃ b, s.mem.get? (a.toNat + i) = some b) :
    read_ram .Read_plain (.Physaddr a) 2 false s = .ok (memParcel s a.toNat, default_meta) s := by
  obtain ⟨b0, hb0⟩ := hbytes 0 (by omega)
  obtain ⟨b1, hb1⟩ := hbytes 1 (by omega)
  simp only [Nat.add_zero] at hb0
  dsimp [LeanRV64D.Functions.read_ram, LeanRV64D.ConcurrencyInterfaceV1.sail_mem_read,
    Sail.ConcurrencyInterfaceV1.PreSail.sail_mem_read, default_meta]
  simp only [bind, EStateM.bind, pure, EStateM.pure,
    readBytes, readByte, MonadStateOf.get, EStateM.get, getThe, get, hb0, hb1,
    memParcel, memByte, Option.getD_some]
  rfl

private theorem not_mmio_ram (s : SailState) (addr : BitVec 64)
    (hram : JoltISA.RAM_START_ADDRESS ≤ addr.toNat)
    (hhtif : s.regs.get? Register.htif_tohost_base = some none) :
    within_mmio_readable (.Physaddr addr) 2 s = .ok false s := by
  have hread := readReg_eq_of_get? Register.htif_tohost_base s _ hhtif
  have hclint : within_clint (.Physaddr addr) 2 s = .ok false s := by
    have hb : plat_clint_base = (0x2000000 : BitVec 64) := by rfl
    have hs : plat_clint_size = (0xc0000 : BitVec 64) := by rfl
    simp [within_clint, hb, hs, Sail.BitVec.toNatInt, pure, EStateM.pure]
    simp only [JoltISA.RAM_START_ADDRESS] at hram
    omega
  simp [within_mmio_readable, get_config_rvfi, hclint, within_htif_readable,
    within_htif_writable, hread, orM, toBool, bind, EStateM.bind, pure, EStateM.pure]

private theorem mem_read_fetch_parcel (s : SailState)
    (hmachine : s.regs.get? Register.cur_privilege = some Privilege.Machine)
    (hmstatus : Assumptions.SailRegReadable Register.mstatus s)
    (addr : BitVec 64) (regions : List PMA_Region) (ram : PMA_Region)
    (hpma : s.regs.get? Register.pma_regions = some regions)
    (hmatch : matching_pma regions (.Physaddr addr) 2 = some ram)
    (hexec : ram.attributes.executable = true)
    (hfault : ram.attributes.misaligned_fault = .NoFault)
    (hlo : JoltISA.RAM_START_ADDRESS ≤ addr.toNat)
    (hhtif : s.regs.get? Register.htif_tohost_base = some none)
    (hbytes : ∀ i < 2, ∃ b, s.mem.get? (addr.toNat + i) = some b) :
    mem_read (.InstructionFetch ()) (.Physaddr addr) 2 false false false s =
      .ok (.Ok (memParcel s addr.toNat)) s := by
  obtain ⟨ms, hms⟩ := Step.readReg_present Register.mstatus s hmstatus
  have hpriv := readReg_eq_of_get? Register.cur_privilege s _ hmachine
  have hpma_read := readReg_eq_of_get? Register.pma_regions s _ hpma
  have hpma_check : pmaCheck (.Physaddr addr) 2 (.InstructionFetch ()) false s = .ok none s := by
    simp [pmaCheck, hpma_read, hmatch, hexec, hfault,
      bind, EStateM.bind, pure, EStateM.pure]
  have hphys : phys_access_check (.InstructionFetch ()) .Machine (.Physaddr addr) 2 false s =
      .ok none s := by
    simp [phys_access_check, HartConfig.pmpCheck_run, hpma_check,
      bind, EStateM.bind, pure, EStateM.pure]
  have heff : effectivePrivilege (.InstructionFetch ()) ms .Machine s = .ok .Machine s := by
    rfl
  simp [mem_read, heff, hms, hpriv, mem_read_priv, mem_read_priv_meta,
    checked_mem_read, hphys, not_mmio_ram s addr hlo hhtif, read_kind_of_flags,
    read_ram_parcel s addr hbytes, MemoryOpResult_drop_meta,
    bind, EStateM.bind, pure, EStateM.pure]

/-- Sail fetch reads a compressed parcel or base word from the executable RAM region of
its PMA list and leaves all state unchanged, including memory and the PC.
Only the bytes of the instruction itself are needed: the two bytes of the first parcel and,
when its low bits are `11`, the two bytes of the second parcel (`hbase`).
For example, at `0x80000000` a parcel with low bits `11` selects four bytes, while a parcel
ending in `01` selects two, even where the next two bytes are absent.
`hmatch` says that `ram` is the PMA region `matching_pma` finds for each parcel read; it holds
for `[ram]` (`fetch_ram`) and for the platform list `[ioRegion, ramRegion]` of
`Relation.lean`. HTIF is disabled at reset (`hhtif`), so RAM cannot be intercepted by that
device. Sail reports `OutOfMemoryRange` for a missing byte, whereas `memByte` supplies Jolt's
zero default. The path is `fetch` in `LeanRV64D/Fetch.lean`, with the default
`ext_fetch_check_pc` hook in `LeanRV64D/AddrChecks.lean`. -/
theorem fetch_regions (s : SailState) (hinv : Step.StepInvariant s)
    (pc : BitVec 64) (hpc : s.regs.get? Register.PC = some pc)
    (halign : pc.getLsbD 0 = false)
    (regions : List PMA_Region) (ram : PMA_Region)
    (hpma : s.regs.get? Register.pma_regions = some regions)
    (hexec : ram.attributes.executable = true)
    (hfault : ram.attributes.misaligned_fault = .NoFault)
    (hlo : JoltISA.RAM_START_ADDRESS ≤ pc.toNat) (hhi : pc.toNat + 2 < 2 ^ 64)
    (hmatch : matching_pma regions (.Physaddr pc) 2 = some ram)
    (hhtif : s.regs.get? Register.htif_tohost_base = some none)
    (hparcel : ∀ i < 2, ∃ b, s.mem.get? (pc.toNat + i) = some b)
    (hbase : (memParcel s pc.toNat).extractLsb 1 0 = 0b11#2 →
      matching_pma regions (.Physaddr (pc + 2#64)) 2 = some ram ∧
      pc.toNat + 4 ≤ 2 ^ 64 ∧ ∀ i < 2, ∃ b, s.mem.get? (pc.toNat + 2 + i) = some b) :
    fetch () s = .ok (fetchedAt s pc.toNat) s := by
  have hpc_read := readReg_eq_of_get? Register.PC s _ hpc
  have hhi_nat : (pc + 2#64).toNat = pc.toNat + 2 := by
    apply BitVec.toNat_add_of_lt
    change pc.toNat + 2 < 2 ^ 64
    omega
  have hlo_read := mem_read_fetch_parcel s hinv.machine (hinv.present _) pc regions ram hpma
    hmatch hexec hfault hlo hhtif hparcel
  have hhi_read : (memParcel s pc.toNat).extractLsb 1 0 = 0b11#2 →
      mem_read (.InstructionFetch ()) (.Physaddr (pc + 2#64)) 2 false false false s =
        .ok (.Ok (memParcel s (pc.toNat + 2))) s := by
    intro hbits
    obtain ⟨hm, h4, hb⟩ := hbase hbits
    have := mem_read_fetch_parcel s hinv.machine (hinv.present _) (pc + 2#64) regions ram hpma
      hm hexec hfault (by omega) hhtif (by
        intro i hi
        simpa only [hhi_nat, Nat.add_assoc] using hb i hi)
    simpa only [hhi_nat] using this
  unfold fetch SailME.run Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.run
  by_cases hbits : (memParcel s pc.toNat).extractLsb 1 0 = 0b11#2 <;>
    cases hbit : pc.getLsbD 1 <;>
    simp [hbits, hbit, get_config_rvfi, hpc_read, ext_fetch_check_pc, Step.currentlyEnabled_Zca_run s hinv,
    BitVec.access, ← BitVec.getLsbD_eq_getElem, halign, translateAddr_fetch_of_machine _ s hinv.machine (hinv.present _),
    hlo_read, hhi_read, BitVec.addInt, isRVC, fetchedAt,
    Sail.BitVec.extractLsb, bind, EStateM.bind, pure, EStateM.pure, EStateM.map,
    ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont, ExceptT.pure, ExceptT.lift,
    MonadLift.monadLift, liftM, monadLift, Functor.map, orM, andM, toBool, bne, BEq.beq, LeanRV64D.Functions.not]

/-- Sail fetch reads a compressed parcel or base word in executable RAM and leaves
all state unchanged, including memory and the PC.
For example, at `0x80000000` a parcel with low bits `11` selects four bytes.
`hpma`, `hbase`, `hexec` and `hfault` fix the RAM PMA fields needed for fetch;
other PMA attributes are unrestricted. `hram` uses its 64-bit size and includes a
nonwrapping bound for the four instruction bytes.
HTIF is disabled at reset (`hhtif`), so RAM cannot be intercepted by that device.
The four bytes must be present: Sail reports `OutOfMemoryRange` for missing bytes,
whereas `memByte` supplies Jolt's zero default.
The path is `fetch` in `LeanRV64D/Fetch.lean`, with the default
`ext_fetch_check_pc` hook in `LeanRV64D/AddrChecks.lean`. -/
theorem fetch_ram (s : SailState) (hinv : Step.StepInvariant s)
    (pc : BitVec 64) (hpc : s.regs.get? Register.PC = some pc)
    (halign : pc.getLsbD 0 = false)
    (ram : PMA_Region) (hpma : s.regs.get? Register.pma_regions = some [ram])
    (hbase : ram.base = 0x80000000)
    (hexec : ram.attributes.executable = true)
    (hfault : ram.attributes.misaligned_fault = .NoFault)
    (hram : JoltISA.RAM_START_ADDRESS ≤ pc.toNat ∧
      pc.toNat + 4 ≤ JoltISA.RAM_START_ADDRESS + ram.size.toNat ∧
      pc.toNat + 4 ≤ 2 ^ 64)
    (hhtif : s.regs.get? Register.htif_tohost_base = some none)
    (hbytes : ∀ i < 4, ∃ b, s.mem.get? (pc.toNat + i) = some b) :
    fetch () s = .ok (fetchedAt s pc.toNat) s := by
  have hhi_nat : (pc + 2#64).toNat = pc.toNat + 2 := by
    apply BitVec.toNat_add_of_lt
    change pc.toNat + 2 < 2 ^ 64
    omega
  refine fetch_regions s hinv pc hpc halign [ram] ram hpma hexec hfault hram.1 (by omega)
    (matching_ram pc ram hbase hram.1 (by omega)) hhtif (fun i hi => hbytes i (by omega))
    (fun _ => ⟨matching_ram _ ram hbase (by omega) (by omega), hram.2.2, fun i hi => ?_⟩)
  · simpa only [Nat.add_assoc] using hbytes (2 + i) (by omega)

end WholeRun
