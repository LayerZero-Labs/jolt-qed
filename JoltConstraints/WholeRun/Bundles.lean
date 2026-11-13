import JoltConstraints.WholeRun.SystemInv
import JoltConstraints.WholeRun.Relation
import JoltConstraints.WholeRun.Bridge
import JoltConstraints.nextpc_frame
import JoltConstraints.layout_facts

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail
  LeanRV64D LeanRV64D.Functions

set_option autoImplicit false

noncomputable section

namespace RiscvInstruction

/-- From decoding: jumps relative to PC and conditional branches have an even signed offset:
bit zero of their immediate is false. Other instructions impose no condition.
For example, `JAL x1, 2` satisfies this predicate, whereas `JAL x1, 1` does not.
Sail's ordinary and compressed decoders construct offsets with this property. -/
def EvenOffsets : RiscvInstruction → Prop
  | .JAL _ imm => imm.getLsbD 0 = false
  | .BEQ _ _ imm | .BNE _ _ imm | .BLT _ _ imm
  | .BGE _ _ imm | .BLTU _ _ imm | .BGEU _ _ imm => imm.getLsbD 0 = false
  | _ => True

end RiscvInstruction

namespace WholeRun

open MemoryAccessType mem_payload

/-- The doubleword an instruction accesses belongs to Jolt's RAM, whose first
address is `JoltISA.RAM_START_ADDRESS`.
Loads and stores use their base register plus signed immediate, rounded down to
eight bytes; word atomics round their source address down, while doubleword
atomics use that address itself.
For example, `LB` from `0x80000003` accesses the doubleword at `0x80000000`.
Instructions without a memory access satisfy this predicate unconditionally.
These are the addresses used by Jolt's tracer in `tracer/src/emulator/mmu.rs`
(`Mmu::load_doubleword`, `Mmu::store_doubleword`) at `5def437f`.
-/
def RamAccess : RiscvInstruction → SailJoltState → Prop
  | .LB _ rs1 imm, js | .LH _ rs1 imm, js | .LW _ rs1 imm, js
  | .LBU _ rs1 imm, js | .LHU _ rs1 imm, js | .LWU _ rs1 imm, js
  | .LD _ rs1 imm, js
  | .SB _ rs1 imm, js | .SH _ rs1 imm, js | .SW _ rs1 imm, js
  | .SD _ rs1 imm, js =>
      JoltISA.RAM_START_ADDRESS ≤
        (compute_aligned_dword_base_address
          (JoltISA.sourceValue (.xreg rs1) js) imm).toNat
  | .LR_W _ rs1 _ _, js | .SC_W _ rs1 _ _ _, js
  | .AMOSWAP_W _ rs1 _ _ _, js | .AMOADD_W _ rs1 _ _ _, js
  | .AMOXOR_W _ rs1 _ _ _, js | .AMOAND_W _ rs1 _ _ _, js
  | .AMOOR_W _ rs1 _ _ _, js | .AMOMIN_W _ rs1 _ _ _, js
  | .AMOMAX_W _ rs1 _ _ _, js | .AMOMINU_W _ rs1 _ _ _, js
  | .AMOMAXU_W _ rs1 _ _ _, js =>
      JoltISA.RAM_START_ADDRESS ≤
        (amoWordBase (JoltISA.sourceValue (.xreg rs1) js)).toNat
  | .LR_D _ rs1 _ _, js | .SC_D _ rs1 _ _ _, js
  | .AMOSWAP_D _ rs1 _ _ _, js | .AMOADD_D _ rs1 _ _ _, js
  | .AMOXOR_D _ rs1 _ _ _, js | .AMOAND_D _ rs1 _ _ _, js
  | .AMOOR_D _ rs1 _ _ _, js | .AMOMIN_D _ rs1 _ _ _, js
  | .AMOMAX_D _ rs1 _ _ _, js | .AMOMINU_D _ rs1 _ _ _, js
  | .AMOMAXU_D _ rs1 _ _ _, js =>
      JoltISA.RAM_START_ADDRESS ≤ (JoltISA.sourceValue (.xreg rs1) js).toNat
  | _, _ => True


/-- A state fixed by the system projection supplies every linked-register
assumption without source-register reads.
For example, its Sail reservation address is the value of Jolt's v32. -/
private def noSource (js : SailJoltState)
    (hlink : System.systemProject js = js.sail) : NoSourceReadWithLinkedCSRs js := by
  refine
    { mstatus_matches := ⟨?_⟩
      mtvec_matches := ⟨?_⟩
      mscratch_matches := ⟨?_⟩
      mepc_matches := ⟨?_⟩
      mcause_matches := ⟨?_⟩
      mtval_matches := ⟨?_⟩
      reservation_matches := ⟨?_, ?_, ?_⟩ }
  all_goals
    rw [← hlink]
    simp [System.systemProject, Std.ExtDHashMap.get?_insert]

private theorem source_read (js : SailJoltState) (hinv : Step.StepInvariant js.sail)
    (r : regidx) :
    rX_bits r js.sail = .ok (JoltISA.sourceValue (.xreg r) js) js.sail := by
  have hp : AllRegistersPresent js.sail := fun r =>
    Option.isSome_iff_exists.mpr (hinv.present r).exists_value
  obtain ⟨v, hv⟩ := (readable_of_present js.sail hp r).exists_value
  have hr : JoltISA.readSrc (.xreg r) js = .ok v js := by
    simp only [JoltISA.readSrc, liftSail, hv]
  have he := (lookup_readSrc_value (.xreg r) js js v hr).2
  exact he ▸ hv

private def unarySource (js : SailJoltState) (hinv : Step.StepInvariant js.sail)
    (hlink : System.systemProject js = js.sail) (r : regidx) :
    UnarySourceReadWithLinkedCSRs r js :=
  { noSource js hlink with
    rs1_val := JoltISA.sourceValue (.xreg r) js
    rs1_read := source_read js hinv r }

private def binarySource (js : SailJoltState) (hinv : Step.StepInvariant js.sail)
    (hlink : System.systemProject js = js.sail) (r2 r1 : regidx) :
    BinarySourceReadWithLinkedCSRs r2 r1 js :=
  { noSource js hlink with
    rs1_val := JoltISA.sourceValue (.xreg r1) js
    rs1_read := source_read js hinv r1
    rs2_val := JoltISA.sourceValue (.xreg r2) js
    rs2_read := source_read js hinv r2 }

private theorem mprv_zero (js : SailJoltState)
    (hlink : System.systemProject js = js.sail)
    (hmstatus : js.vregs JoltISA.mstatusVReg &&& ~~~(0x88 : BitVec 64) = 0) :
    Assumptions.MstatusMprvZero js.sail := by
  refine ⟨js.vregs JoltISA.mstatusVReg ||| 0x1800#64,
    (noSource js hlink).linkedCSRs.1.value_eq, ?_⟩
  change (js.vregs JoltISA.mstatusVReg ||| 0x1800#64).extractLsb' 17 1 = 0
  have hb := congrArg (fun v : BitVec 64 => v.extractLsb' 17 1) hmstatus
  simp only [BitVec.extractLsb'_and, BitVec.reduceNot, BitVec.reduceExtractLsb'] at hb
  change (js.vregs JoltISA.mstatusVReg).extractLsb' 17 1 &&& BitVec.allOnes 1 = 0 at hb
  simpa only [BitVec.and_allOnes, BitVec.extractLsb'_or, BitVec.reduceExtractLsb',
    BitVec.or_zero] using hb

private theorem range_subset_nat (addr base size : BitVec 64) (n : Nat)
    (hbase : base.toNat ≤ addr.toNat) (hn : n < 2 ^ 64)
    (hsum : addr.toNat - base.toNat + n < 2 ^ 64) :
    range_subset addr (BitVec.ofNat 64 n) base size =
      decide (addr.toNat - base.toNat + n ≤ size.toNat) := by
  have hsub : (addr - base).toNat = addr.toNat - base.toNat := BitVec.toNat_sub_of_le (by simpa [BitVec.le_def] using hbase)
  have hadd : addr + BitVec.ofNat 64 n - base =
      (addr - base) + BitVec.ofNat 64 n := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 64 n)]
  have hsize : base + size - base = size := by
    rw [BitVec.add_comm]; exact BitVec.add_sub_cancel _ _
  have hnat : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hn
  have hsum' : (addr - base).toNat + (BitVec.ofNat 64 n).toNat < 2 ^ 64 := by
    simpa only [hsub, hnat] using hsum
  simp only [range_subset, hadd, hsize, zopz0zIzJ_u, Sail.BitVec.toNatInt,
    BitVec.toNat_add_of_lt hsum', hsub, hnat]
  simp only [Int.ofNat_eq_natCast, Int.ofNat_le]
  by_cases h : addr.toNat - base.toNat + n ≤ size.toNat
  · simp [h, show addr.toNat - base.toNat ≤ size.toNat by omega]
  · simp [h]

private theorem matching_platform_ram (addr : BitVec 64) (n : Nat)
    (hlo : JoltISA.RAM_START_ADDRESS ≤ addr.toNat)
    (hn : 0 < n) (hwidth : n ≤ 8) (hhi : addr.toNat + n ≤ 2 ^ 64) :
    matching_pma platformPma (.Physaddr addr) n = some ramRegion := by
  have haddr := addr.isLt
  simp only [JoltISA.RAM_START_ADDRESS] at hlo
  have hio := range_subset_nat addr 0x40000000 0x40000000 n (by simpa using (show 0x40000000 ≤ addr.toNat by omega))
    (by omega) (by change addr.toNat - 0x40000000 + n < 2 ^ 64; omega)
  have hram := range_subset_nat addr 0x80000000 0xFFFFFFFF80000000 n
    (by simpa using hlo) (by omega) (by change addr.toNat - 0x80000000 + n < 2 ^ 64; omega)
  have hno : ¬ (addr.toNat - 0x40000000 + n ≤ 0x40000000) := by omega
  have hyes : addr.toNat - 0x80000000 + n ≤ 0xFFFFFFFF80000000 := by omega
  simp only [show (0x40000000 : BitVec 64).toNat = 0x40000000 by rfl,
    show (0x80000000 : BitVec 64).toNat = 0x80000000 by rfl,
    show (0xFFFFFFFF80000000 : BitVec 64).toNat = 0xFFFFFFFF80000000 by rfl,
    hno, hyes, decide_false, decide_true] at hio hram
  change range_subset addr (BitVec.ofNat 64 n) 0x40000000#64 0x40000000#64 = false at hio
  change range_subset addr (BitVec.ofNat 64 n) 0x80000000#64 0xFFFFFFFF80000000#64 = true at hram
  have hzero : zero_extend (m := 64) addr = addr := by
    simpa only [zero_extend, Sail.BitVec.zeroExtend, BitVec.zeroExtend_eq_setWidth]
      using BitVec.setWidth_eq addr
  have hbits : to_bits (l := 64) n = BitVec.ofNat 64 n := by
    change (BitVec.ofInt 65 (n : Int)).extractLsb' 0 64 = _
    rw [← BitVec.setWidth_eq_extractLsb' (by decide)]
    simp
  simp only [platformPma, matching_pma, matching_pma_bits_range, bits_of_physaddr,
    hzero, hbits, ioRegion, ramRegion]
  rw [hio]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [hram]
  rfl

private theorem not_mmio_ram (s : SailState) (addr : BitVec 64) (n : Nat)
    (hram : JoltISA.RAM_START_ADDRESS ≤ addr.toNat)
    (hhtif : s.regs.get? Register.htif_tohost_base = some none) :
    within_mmio_readable (.Physaddr addr) n s = .ok false s ∧
      within_mmio_writable (.Physaddr addr) n s = .ok false s := by
  have hread := readReg_eq_of_get? Register.htif_tohost_base s _ hhtif
  have hclint : within_clint (.Physaddr addr) n s = .ok false s := by
    have hb : plat_clint_base = (0x2000000 : BitVec 64) := by rfl
    have hs : plat_clint_size = (0xc0000 : BitVec 64) := by rfl
    simp [within_clint, hb, hs, Sail.BitVec.toNatInt, pure, EStateM.pure]
    simp only [JoltISA.RAM_START_ADDRESS] at hram
    omega
  simp [within_mmio_readable, within_mmio_writable, get_config_rvfi, hclint,
    within_htif_readable, within_htif_writable, hread, orM, toBool,
    bind, EStateM.bind, pure, EStateM.pure]


private theorem ram_checks (s : SailState) (addr : BitVec 64) (n : Nat)
    (hpma : s.regs.get? Register.pma_regions = some platformPma)
    (hlo : JoltISA.RAM_START_ADDRESS ≤ addr.toNat)
    (hn : 0 < n) (hwidth : n ≤ 8) (hhi : addr.toNat + n ≤ 2 ^ 64)
    (op : amoop) (hop : (op == .AMOCAS) = false) :
    Assumptions.LoadPmpOk addr n s ∧ Assumptions.StorePmpOk addr n s ∧
      Assumptions.AtomicPmpOk op addr n s := by
  have hread := readReg_eq_of_get? Register.pma_regions s _ hpma
  have hmatch := matching_platform_ram addr n hlo hn hwidth hhi
  simp [Assumptions.LoadPmpOk, Assumptions.StorePmpOk, Assumptions.AtomicPmpOk,
    phys_access_check, HartConfig.pmpCheck_run, pmaCheck, hread, hmatch, ramRegion,
    pma_allows_atomic_op, bne, hop, LeanRV64D.sail_assert, Sail.ConcurrencyInterfaceV1.PreSail.sail_assert, LeanRV64D.Functions.not,
    bind, EStateM.bind, pure, EStateM.pure]

private theorem layout_memLow (js : SailJoltState)
    (hlayout : ∃ config, MemoryLayout.new config = some js.jolt_device.memory_layout) :
    memLow js.jolt_device ≤ JoltISA.RAM_START_ADDRESS := by
  obtain ⟨config, hb⟩ := hlayout
  change js.jolt_device.memory_layout.get_lowest_address.toNat ≤ _
  generalize he : js.jolt_device.memory_layout = layout at hb ⊢
  unfold MemoryLayout.new at hb
  repeat' (rw [bind_some_iff] at hb; obtain ⟨_, _, hb⟩ := hb)
  cases hb
  obtain ⟨hte, hue, horder, hstart, htebound, huebound⟩ := adviceRegions_some (by assumption)
  unfold MemoryLayout.get_lowest_address
  dsimp only at *
  split <;> simp only [BitVec.toNat_ofNat] at * <;> omega

private theorem ram_windows (js : SailJoltState) (base : BitVec 64)
    (hpma : js.sail.regs.get? Register.pma_regions = some platformPma)
    (hhtif : js.sail.regs.get? Register.htif_tohost_base = some none)
    (hlow : memLow js.jolt_device ≤ JoltISA.RAM_START_ADDRESS)
    (hpresent : ∀ a, memLow js.jolt_device ≤ a → a < memHigh js.jolt_device →
      ∃ b, js.sail.mem.get? a = some b)
    (hram : JoltISA.RAM_START_ADDRESS ≤ base.toNat)
    (hheap : base.toNat < js.jolt_device.memory_layout.heap_end.toNat)
    (hno_wrap : base.toNat + 8 ≤ 2 ^ 64)
    (op : amoop) (hop : (op == .AMOCAS) = false) :
    DwordAtomicWindowAssumptions op base js.sail := by
  have hsub : ∀ offset width : Nat, 0 < width → offset + width ≤ 8 →
      JoltISA.RAM_START_ADDRESS ≤ (base + BitVec.ofNat 64 offset).toNat ∧
      (base + BitVec.ofNat 64 offset).toNat + width ≤ 2 ^ 64 := by
    intro offset width hw hfits
    have heq := toNat_add_small_of_no_ovf base offset (by omega)
    rw [heq]
    omega
  have checks := fun offset width hw hfits =>
    ram_checks js.sail (base + BitVec.ofNat 64 offset) width hpma
      (hsub offset width hw hfits).1 hw (by omega) (hsub offset width hw hfits).2 op hop
  have mmio := fun offset width hw hfits =>
    not_mmio_ram js.sail (base + BitVec.ofNat 64 offset) width
      (hsub offset width hw hfits).1 hhtif
  refine
    { dword_present := ⟨?_⟩
      load_pmp := ⟨fun offset width hw hfits => (checks offset width hw hfits).1⟩
      store_pmp := ⟨fun offset width hw hfits => (checks offset width hw hfits).2.1⟩
      atomic_pmp := ⟨fun offset width hw hfits => (checks offset width hw hfits).2.2⟩
      not_readable_mmio := ⟨fun offset width hw hfits =>
        ⟨(hsub offset width hw hfits).1, (mmio offset width hw hfits).1⟩⟩
      not_writable_mmio := ⟨fun offset width hw hfits =>
        ⟨(hsub offset width hw hfits).1, (mmio offset width hw hfits).2⟩⟩ }
  have present : ∀ k : Fin 8, ∃ b, js.sail.mem.get? (base.toNat + k.val) = some b := by
    intro k
    apply hpresent
    · omega
    · simp only [memHigh]
      omega
  exact ⟨fun k => (present k).choose, fun k => (present k).choose_spec⟩

private def Frozen (s t : SailJoltState) : Prop :=
  t.sail.regs = s.sail.regs ∧ t.jolt_device = s.jolt_device

private theorem frozen_refl (s : SailJoltState) : Frozen s s := ⟨rfl, rfl⟩

private theorem frozen_trans (s t u : SailJoltState)
    (h : Frozen s t) (h' : Frozen t u) : Frozen s u :=
  ⟨h'.1.trans h.1, h'.2.trans h.2⟩

private theorem readSrc_frozen (src : JoltISA.Src) :
    StatePreservation.Preserves Frozen (JoltISA.readSrc src) := by
  intro s t v h
  obtain ⟨rfl, _⟩ := lookup_readSrc_value src s t v h
  exact ⟨rfl, rfl⟩

private theorem writeVReg_frozen (vr : JoltISA.VReg) (value : BitVec 64) :
    StatePreservation.Preserves Frozen (JoltISA.writeDst (.vreg vr) value) := by
  intro s t u h
  simp only [JoltISA.writeDst, writeVReg] at h
  split at h
  · cases h
  · cases h; exact ⟨rfl, rfl⟩

private theorem load_frozen (addr : BitVec 64) :
    StatePreservation.Preserves Frozen (JoltISA.Mmu.load_doubleword addr) := by
  intro s t v h
  rw [JoltISA.Mmu.load_doubleword_state h]
  exact frozen_refl s

-- Only this small classification is needed for the rows before a RAM store.
private def ScratchRow : JoltISA.Instr → Prop
  | .ADDI dst _ _ | .LUI dst _ | .SLTIU dst _ _
  | .ADD dst _ _ | .SUB dst _ _ | .MUL dst _ _
  | .ANDN dst _ _ | .AND dst _ _ | .OR dst _ _ | .XOR dst _ _
  | .SLT dst _ _ | .SLTU dst _ _ | .VirtualSignExtendWord dst _ _
  | .VirtualWindowMaskB dst _ _ | .VirtualWindowMaskH dst _ _
  | .VirtualWindowMaskW dst _ _ | .VirtualPext dst _ _ | .VirtualPextSigned dst _ _
  | .VirtualShiftDataB dst _ _ _ | .VirtualShiftDataH dst _ _ _
  | .VirtualShiftDataW dst _ _ _ | .LD _ dst _ _
  | .VirtualLoadB _ dst _ _ _ | .VirtualLoadH _ dst _ _ _
  | .VirtualLoadW _ dst _ _ _ => ∃ vr, dst = .vreg vr
  | .VirtualAssertLTE .. => True
  | _ => False

private theorem scratchRow_frozen (i : JoltISA.Instr) (hi : ScratchRow i) :
    StatePreservation.Preserves Frozen (JoltISA.execInstr i) := by
  cases i <;> simp only [ScratchRow] at hi
  case VirtualAssertLTE =>
    simp only [JoltISA.execInstr]
    preservation_auto [readSrc_frozen _, StatePreservation.pure_rule frozen_refl _,
      StatePreservation.throw_rule Frozen _] using (StatePreservation.bind_rule frozen_trans)
  all_goals rcases hi with ⟨vr, rfl⟩
  all_goals simp only [JoltISA.execInstr]
  all_goals preservation_auto [readSrc_frozen _, writeVReg_frozen _ _, load_frozen _,
    StatePreservation.pure_rule frozen_refl _, StatePreservation.throw_rule Frozen _]
    using (StatePreservation.bind_rule frozen_trans)

private def NoStoreRow : JoltISA.Instr → Prop
  | .SD .. | .VirtualStoreB .. | .VirtualStoreH .. | .VirtualStoreW .. => False
  | _ => True

private theorem noStoreRow_device (i : JoltISA.Instr) (hi : NoStoreRow i) :
    StatePreservation.Preserves (fun s t => t.jolt_device = s.jolt_device)
      (JoltISA.execInstr i) := by
  apply JoltIOSetupFrame.execInstr_rule_of_device_relation_for_store
    (fun a b => b = a) (fun _ => rfl) (fun _ _ _ h h' => h'.trans h)
  · intro base src imm heq
    subst i
    exact False.elim hi
  · intro base src imm fault heq
    rcases heq with rfl | rfl | rfl <;> exact False.elim hi

private def NoStoreProgram : JoltISA.Program → Prop
  | .done _ => True
  | .instr i rest => NoStoreRow i ∧ NoStoreProgram rest

private theorem noStoreProgram_device (p : JoltISA.Program) (hp : NoStoreProgram p) :
    StatePreservation.Preserves (fun s t => t.jolt_device = s.jolt_device)
      (JoltISA.execProgram p) := by
  induction p with
  | done _ => exact StatePreservation.pure_rule (fun (s : SailJoltState) => (rfl : s.jolt_device = s.jolt_device)) _
  | instr i rest ih =>
    simp only [JoltISA.execProgram]
    apply StatePreservation.bind_rule (fun _ _ _ h h' => h'.trans h)
      (noStoreRow_device i hp.1)
    intro result
    split
    · exact ih hp.2
    · exact StatePreservation.pure_rule (fun (s : SailJoltState) => (rfl : s.jolt_device = s.jolt_device)) _

private inductive AccessKind where
  | dword | byte | halfword | word

private def accessAddress (kind : AccessKind) (value imm : BitVec 64) : BitVec 64 :=
  match kind with
  | .dword => value + imm
  | _ => (value + imm) &&& (-8 : BitVec 64)

private def storeRow (kind : AccessKind) (rs : regidx) (value : JoltISA.Src)
    (imm : BitVec 64) : JoltISA.Instr :=
  match kind with
  | .dword => .SD (.xreg rs) value imm
  | .byte => .VirtualStoreB (.xreg rs) value imm (.E_SAMO_Addr_Align ())
  | .halfword => .VirtualStoreH (.xreg rs) value imm (.E_SAMO_Addr_Align ())
  | .word => .VirtualStoreW (.xreg rs) value imm (.E_SAMO_Addr_Align ())

private inductive StorePlan (kind : AccessKind) (rs : regidx) (imm : BitVec 64) :
    JoltISA.Program → Prop where
  | store (value : JoltISA.Src) (rest : JoltISA.Program) (htail : NoStoreProgram rest) :
      StorePlan kind rs imm (.instr (storeRow kind rs value imm) rest)
  | scratch (row : JoltISA.Instr) (rest : JoltISA.Program) (hrow : ScratchRow row)
      (htail : StorePlan kind rs imm rest) :
      StorePlan kind rs imm (.instr row rest)


private theorem bind_success {α β : Type} (m : JoltMonad α) (f : α → JoltMonad β)
    (s t : SailJoltState) (v : β) (h : (m >>= f) s = .ok v t) :
    ∃ a u, m s = .ok a u ∧ f a u = .ok v t := by
  cases hm : m s with
  | error e u => simp only [bind, EStateM.bind, hm] at h; cases h
  | ok a u => exact ⟨a, u, rfl, by simpa only [bind, EStateM.bind, hm] using h⟩

private theorem mmu_store_ram (addr value : BitVec 64) (s t : SailJoltState)
    (r : Result Bool ExecutionResult) (hram : JoltISA.RAM_START_ADDRESS ≤ addr.toNat)
    (hrun : JoltISA.Mmu.store_doubleword addr value s = .ok r t) :
    Assumptions.JoltRamStoreOk addr s ∧ t.jolt_device = s.jolt_device ∧ r = .Ok true := by
  simp only [JoltISA.Mmu.store_doubleword, if_pos hram] at hrun
  split at hrun
  · cases hrun
  · split at hrun
    · rename_i valid
      simp only [JoltISA.Mmu.effective_address_ok, if_neg (Nat.not_lt.mpr hram),
        ↓reduceIte, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at valid
      cases hrun
      exact ⟨⟨valid.2, valid.1⟩, rfl, rfl⟩
    · cases hrun

private theorem store_body_ram (addr value : BitVec 64) (s t : SailJoltState)
    (hram : JoltISA.RAM_START_ADDRESS ≤ addr.toNat)
    (hrun : (do
      match ← JoltISA.Mmu.store_doubleword addr value with
      | .Ok _ => pure RETIRE_SUCCESS
      | .Err e => pure e : JoltMonad ExecutionResult) s = .ok RETIRE_SUCCESS t) :
    Assumptions.JoltRamStoreOk addr s ∧ t.jolt_device = s.jolt_device := by
  obtain ⟨r, u, hm, ht⟩ := bind_success _ _ s t RETIRE_SUCCESS hrun
  obtain ⟨hb, hd, rfl⟩ := mmu_store_ram addr value s u r hram hm
  cases ht
  exact ⟨hb, hd⟩

private theorem sourceValue_regs (rs : regidx) (s t : SailJoltState)
    (h : t.sail.regs = s.sail.regs) :
    JoltISA.sourceValue (.xreg rs) t = JoltISA.sourceValue (.xreg rs) s := by
  cases rs
  simp only [JoltISA.sourceValue, h]

private theorem store_row_ram (kind : AccessKind) (rs : regidx) (value : JoltISA.Src)
    (imm : BitVec 64) (s t : SailJoltState)
    (hram : JoltISA.RAM_START_ADDRESS ≤
      (accessAddress kind (JoltISA.sourceValue (.xreg rs) s) imm).toNat)
    (hrun : JoltISA.execInstr (storeRow kind rs value imm) s = .ok RETIRE_SUCCESS t) :
    Assumptions.JoltRamStoreOk
      (accessAddress kind (JoltISA.sourceValue (.xreg rs) s) imm) s ∧
      t.jolt_device = s.jolt_device := by
  cases kind
  all_goals simp only [storeRow, JoltISA.execInstr] at hrun
  all_goals have hbase := lookup_read_bind (.xreg rs) _ s t RETIRE_SUCCESS hrun
  case dword =>
    have hv := lookup_read_bind value _ s t RETIRE_SUCCESS hbase
    split at hv
    · exact store_body_ram _ _ s t hram hv
    · cases hv
  case byte =>
    have hv := lookup_read_bind value _ s t RETIRE_SUCCESS hbase
    exact store_body_ram _ _ s t hram hv
  all_goals split at hbase
  all_goals first
    | cases hbase
    | exact store_body_ram _ _ s t hram
        (lookup_read_bind value _ s t RETIRE_SUCCESS hbase)

private theorem storePlan_ram (kind : AccessKind) (rs : regidx) (imm : BitVec 64)
    (p : JoltISA.Program) (hp : StorePlan kind rs imm p)
    (s t : SailJoltState)
    (hram : JoltISA.RAM_START_ADDRESS ≤
      (accessAddress kind (JoltISA.sourceValue (.xreg rs) s) imm).toNat)
    (hrun : JoltISA.execProgram p s = .ok RETIRE_SUCCESS t) :
    Assumptions.JoltRamStoreOk
      (accessAddress kind (JoltISA.sourceValue (.xreg rs) s) imm) s ∧
      t.jolt_device = s.jolt_device := by
  induction hp generalizing s t with
  | store value rest htail =>
    obtain ⟨u, hrow, hrest⟩ := JoltISA.execProgram_instr_run_retire_inv _ _ s t hrun
    obtain ⟨hb, hd⟩ := store_row_ram kind rs value imm s u hram hrow
    exact ⟨hb, (noStoreProgram_device rest htail u t _ hrest).trans hd⟩
  | scratch row rest hrow htail ih =>
    obtain ⟨u, hstep, hrest⟩ := JoltISA.execProgram_instr_run_retire_inv _ _ s t hrun
    obtain ⟨hregs, hdev⟩ := scratchRow_frozen row hrow s u _ hstep
    have heq := sourceValue_regs rs s u hregs
    obtain ⟨hb, hd⟩ := ih u t (by simpa only [heq] using hram) hrest
    refine ⟨?_, hd.trans hdev⟩
    exact ⟨by simpa only [heq, hdev] using hb.below_heap_end,
      by simpa only [heq, hdev] using hb.outside_canary⟩


private def loadRow (kind : AccessKind) (dst : JoltISA.Dst) (rs : regidx)
    (imm : BitVec 64) : JoltISA.Instr :=
  match kind with
  | .dword => .LD .normal dst (.xreg rs) imm
  | .byte => .VirtualLoadB .normal dst (.xreg rs) imm (.E_Load_Addr_Align ())
  | .halfword => .VirtualLoadH .normal dst (.xreg rs) imm (.E_Load_Addr_Align ())
  | .word => .VirtualLoadW .normal dst (.xreg rs) imm (.E_Load_Addr_Align ())

private theorem mmu_load_ram (addr : BitVec 64) (s t : SailJoltState)
    (r : Result (BitVec 64) ExecutionResult)
    (hram : JoltISA.RAM_START_ADDRESS ≤ addr.toNat)
    (hrun : JoltISA.Mmu.load_doubleword addr s = .ok r t) :
    Assumptions.JoltRamLoadOk addr s := by
  simp only [JoltISA.Mmu.load_doubleword, if_pos hram] at hrun
  split at hrun
  · cases hrun
  · split at hrun
    · rename_i valid
      refine ⟨?_⟩
      simpa only [JoltISA.Mmu.effective_address_ok,
        if_neg (Nat.not_lt.mpr hram), Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq] using valid
    · cases hrun

private theorem load_row_ram (kind : AccessKind) (dst : JoltISA.Dst) (rs : regidx)
    (imm : BitVec 64) (s t : SailJoltState)
    (hram : JoltISA.RAM_START_ADDRESS ≤
      ((JoltISA.sourceValue (.xreg rs) s + imm) &&& (-8 : BitVec 64)).toNat)
    (hrun : JoltISA.execInstr (loadRow kind dst rs imm) s = .ok RETIRE_SUCCESS t) :
    Assumptions.JoltRamLoadOk
      ((JoltISA.sourceValue (.xreg rs) s + imm) &&& (-8 : BitVec 64)) s := by
  cases kind
  all_goals simp only [loadRow, JoltISA.execInstr] at hrun
  all_goals have hbase := lookup_read_bind (.xreg rs) _ s t RETIRE_SUCCESS hrun
  case dword =>
    split at hbase
    · rename_i halign
      have hclear : (JoltISA.sourceValue (.xreg rs) s + imm) &&& (-8 : BitVec 64) =
          JoltISA.sourceValue (.xreg rs) s + imm :=
        BitVec.and_not_eq_self_of_and_eq_zero _ 7 halign
      rw [hclear] at hram ⊢
      obtain ⟨v, u, hm, _⟩ := bind_success _ _ s t RETIRE_SUCCESS hbase
      exact mmu_load_ram _ s u v hram hm
    · cases hbase
  case byte =>
    obtain ⟨v, u, hm, _⟩ := bind_success _ _ s t RETIRE_SUCCESS hbase
    exact mmu_load_ram _ s u v hram hm
  all_goals split at hbase
  all_goals first
    | cases hbase
    | (obtain ⟨v, u, hm, _⟩ := bind_success _ _ s t RETIRE_SUCCESS hbase
       exact mmu_load_ram _ s u v hram hm)

private theorem native_store_ram (rs : regidx) (value : JoltISA.Src)
    (imm : BitVec 64) (s t : SailJoltState)
    (hram : JoltISA.RAM_START_ADDRESS ≤
      ((JoltISA.sourceValue (.xreg rs) s + imm) &&& (-8 : BitVec 64)).toNat)
    (hrun : JoltISA.execInstr (.SD (.xreg rs) value imm) s = .ok RETIRE_SUCCESS t) :
    Assumptions.JoltRamStoreOk
      ((JoltISA.sourceValue (.xreg rs) s + imm) &&& (-8 : BitVec 64)) s ∧
      t.jolt_device = s.jolt_device := by
  simp only [JoltISA.execInstr] at hrun
  have hbase := lookup_read_bind (.xreg rs) _ s t RETIRE_SUCCESS hrun
  have hv := lookup_read_bind value _ s t RETIRE_SUCCESS hbase
  split at hv
  · rename_i halign
    have hclear : (JoltISA.sourceValue (.xreg rs) s + imm) &&& (-8 : BitVec 64) =
        JoltISA.sourceValue (.xreg rs) s + imm :=
      BitVec.and_not_eq_self_of_and_eq_zero _ 7 halign
    rw [hclear] at hram ⊢
    exact store_body_ram _ _ s t hram hv
  · cases hv


private theorem clear_bit_zero (x : BitVec 64) :
    BitVec.update x 0 0#1 = x &&& ~~~(1#64) := by
  simp [BitVec.update, Sail.BitVec.updateSubrange', BitVec.and_comm]

private theorem even_aligned (js : SailJoltState) (hinv : Step.StepInvariant js.sail)
    (x : BitVec 64) (hx : x.getLsbD 0 = false) :
    Assumptions.MepcReadAligned x js.sail := by
  have hlow : x &&& (1#64) = 0 := by
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    by_cases hz : k = 0
    · subst k; simp only [BitVec.getLsbD_and, BitVec.getLsbD_one,
        BitVec.getLsbD_zero, decide_true, Bool.and_true, Bool.false_and, hx]
      rfl
    · simp [hz]
  have hc : BitVec.update x 0 0#1 = x := by
    rw [clear_bit_zero]
    exact BitVec.and_not_eq_self_of_and_eq_zero x 1 hlow
  constructor
  simp [align_pc, Step.currentlyEnabled_Zca_run js.sail hinv, hc,
    bind, EStateM.bind, pure, EStateM.pure]

private theorem even_add (x y : BitVec 64)
    (hx : x.getLsbD 0 = false) (hy : y.getLsbD 0 = false) :
    (x + y).getLsbD 0 = false := by
  have hx' : x.setWidth 1 = 0 := by simp only [BitVec.setWidth_one, hx]; rfl
  have hy' : y.setWidth 1 = 0 := by simp only [BitVec.setWidth_one, hy]; rfl
  have hs : (x + y).setWidth 1 = 0 := by
    rw [BitVec.setWidth_add x y (by decide), hx', hy']; rfl
  have h := congrArg (fun v : BitVec 1 => v.getLsbD 0) hs
  simpa using h

private def jalBundle (js : SailJoltState) (hinv : Step.StepInvariant js.sail)
    (hlink : System.systemProject js = js.sail) (imm : BitVec 21)
    (heven : imm.getLsbD 0 = false)
    (hpc : ∀ pc, js.sail.regs.get? Register.PC = some pc → pc.getLsbD 0 = false) :
    JalInstrEqSailAssumptions imm js :=
  { noSource js hlink with
    nextPC_readable := hinv.present _
    pc_readable := hinv.present _
    target_aligned := even_aligned js hinv _ (even_add _ _
      (hpc _ (hinv.present Register.PC).exists_value.choose_spec)
      (by
        change (imm.signExtend 64).getLsbD 0 = false
        simpa only [BitVec.getLsbD_signExtend, Nat.reduceLT, decide_true, ↓reduceIte,
          Bool.true_and] using heven)) }

private def jalrBundle (js : SailJoltState) (hinv : Step.StepInvariant js.sail)
    (hlink : System.systemProject js = js.sail) (imm : BitVec 12) (rs1 : regidx) :
    JalrInstrEqSailAssumptions imm rs1 js :=
  { unarySource js hinv hlink rs1 with
    nextPC_readable := hinv.present _
    target_aligned := even_aligned js hinv _ (by rw [clear_bit_zero]; simp) }


private def reservedLoadRow (double : Bool) (dst : JoltISA.Dst) (rs1 : regidx) : JoltISA.Instr :=
  if double then .LD .amo dst (.xreg rs1) 0#64
  else .VirtualLoadW .amo dst (.xreg rs1) 0#64 (.E_SAMO_Addr_Align ())

private theorem reservedLoad_conditions (double : Bool) (dst : JoltISA.Dst) (rs1 : regidx)
    (s t : SailJoltState)
    (hram : JoltISA.RAM_START_ADDRESS ≤
      (SystemProofs.reservationBase double (JoltISA.sourceValue (.xreg rs1) s)).toNat)
    (hrun : JoltISA.execInstr (reservedLoadRow double dst rs1) s = .ok RETIRE_SUCCESS t) :
    JoltISA.sourceValue (.xreg rs1) s &&& (if double then 7#64 else 3#64) = 0#64 ∧
      Assumptions.JoltRamLoadOk
        (SystemProofs.reservationBase double (JoltISA.sourceValue (.xreg rs1) s)) s := by
  cases double with
  | false =>
    have hg := JoltConstraints.floor_load_access _ .amo dst (.xreg rs1) 0#64 3#64
      (.E_SAMO_Addr_Align ()) (Or.inr (Or.inr ⟨rfl, rfl⟩)) () s t hrun
    simp only [BitVec.add_zero] at hg
    obtain ⟨value, u, hload, _⟩ := bind_success _ _ s t RETIRE_SUCCESS hg.2
    exact ⟨hg.1, mmu_load_ram _ s u value hram hload⟩
  | true =>
    simp only [reservedLoadRow, ite_true, JoltISA.execInstr] at hrun
    have hb := lookup_read_bind (.xreg rs1) _ s t RETIRE_SUCCESS hrun
    simp only [BitVec.add_zero] at hb
    split at hb
    · rename_i ha
      obtain ⟨value, u, hload, _⟩ := bind_success _ _ s t RETIRE_SUCCESS hb
      exact ⟨ha, mmu_load_ram _ s u value hram hload⟩
    · cases hb

private inductive ReservationLoadPlan (double : Bool) (rs1 : regidx) : JoltISA.Program → Prop where
  | load (dst : JoltISA.Dst) (rest : JoltISA.Program) :
      ReservationLoadPlan double rs1 (.instr (reservedLoadRow double dst rs1) rest)
  | scratch (i : JoltISA.Instr) (rest : JoltISA.Program) (hi : ScratchRow i)
      (htail : ReservationLoadPlan double rs1 rest) :
      ReservationLoadPlan double rs1 (.instr i rest)

private theorem reservationLoadPlan_conditions (double : Bool) (rs1 : regidx)
    (p : JoltISA.Program) (hp : ReservationLoadPlan double rs1 p)
    (s t : SailJoltState)
    (hram : JoltISA.RAM_START_ADDRESS ≤
      (SystemProofs.reservationBase double (JoltISA.sourceValue (.xreg rs1) s)).toNat)
    (hrun : JoltISA.execProgram p s = .ok RETIRE_SUCCESS t) :
    JoltISA.sourceValue (.xreg rs1) s &&& (if double then 7#64 else 3#64) = 0#64 ∧
      Assumptions.JoltRamLoadOk
        (SystemProofs.reservationBase double (JoltISA.sourceValue (.xreg rs1) s)) s := by
  induction hp generalizing s t with
  | load dst rest =>
    obtain ⟨u, hload, _⟩ := JoltISA.execProgram_instr_run_retire_inv _ _ s t hrun
    exact reservedLoad_conditions double dst rs1 s u hram hload
  | scratch i rest hi htail ih =>
    obtain ⟨u, hstep, hrest⟩ := JoltISA.execProgram_instr_run_retire_inv _ _ s t hrun
    obtain ⟨hregs, hdev⟩ := scratchRow_frozen i hi s u _ hstep
    have heq := sourceValue_regs rs1 s u hregs
    obtain ⟨ha, hl⟩ := ih u t (by simpa only [heq] using hram) hrest
    exact ⟨by simpa only [heq] using ha,
      ⟨by simpa only [heq, hdev] using hl.below_heap_end⟩⟩

private theorem reservation_load_plan (store double : Bool) (rd rs1 rs2 : regidx) :
    ReservationLoadPlan double rs1 (if store then SystemProofs.scRows double rd rs1 rs2
      else SystemProofs.lrRows double rd rs1 rs2) := by
  cases store <;> cases double
  all_goals simp only [SystemProofs.scRows, SystemProofs.lrRows,
    Bool.false_eq_true, ite_true, ite_false]
  all_goals simp only [JoltISA.lrwProgramAuto, JoltISA.lrdProgramAuto,
    JoltISA.scwProgramAuto, JoltISA.scdProgramAuto]
  all_goals split
  all_goals repeat' first
    | exact ReservationLoadPlan.load _ _
    | apply ReservationLoadPlan.scratch _ _ (by simp [ScratchRow])

private theorem reservation_store_plan (double : Bool) (rd rs1 rs2 : regidx) :
    StorePlan (if double then .dword else .word) rs1 0#64
      (SystemProofs.scRows double rd rs1 rs2) := by
  cases double
  all_goals simp only [SystemProofs.scRows, Bool.false_eq_true, ite_true, ite_false,
    JoltISA.scwProgramAuto, JoltISA.scdProgramAuto]
  all_goals split
  all_goals repeat' first
    | exact StorePlan.store _ _ (by simp [NoStoreProgram, NoStoreRow])
    | apply StorePlan.scratch _ _ (by simp [ScratchRow])

/-- The memory conditions of an LR (`store = false`) or SC (`store = true`): the address in
`rs1` is aligned to the access width, Jolt's tracer accepts a load from the reservation's
doubleword, and for SC also a store to it. -/
structure ReservationMemory (store double : Bool) (rs1 : regidx)
    (js : SailJoltState) : Prop where
  align : JoltISA.sourceValue (.xreg rs1) js &&& (if double then 7#64 else 3#64) = 0#64
  load : Assumptions.JoltRamLoadOk
    (SystemProofs.reservationBase double (JoltISA.sourceValue (.xreg rs1) js)) js
  store_ok : if store then Assumptions.JoltRamStoreOk
    (SystemProofs.reservationBase double (JoltISA.sourceValue (.xreg rs1) js)) js else True

private theorem reservation_conditions (store double : Bool) (rd rs1 rs2 : regidx)
    (s t : SailJoltState)
    (hram : JoltISA.RAM_START_ADDRESS ≤
      (SystemProofs.reservationBase double (JoltISA.sourceValue (.xreg rs1) s)).toNat)
    (hrun : JoltISA.execProgram (if store then SystemProofs.scRows double rd rs1 rs2
      else SystemProofs.lrRows double rd rs1 rs2) s = .ok RETIRE_SUCCESS t) :
    ReservationMemory store double rs1 s ∧ t.jolt_device = s.jolt_device := by
  obtain ⟨ha, hl⟩ := reservationLoadPlan_conditions double rs1 _
    (reservation_load_plan store double rd rs1 rs2) s t hram hrun
  cases store with
  | false =>
    refine ⟨⟨ha, hl, trivial⟩, noStoreProgram_device _ ?_ s t _ hrun⟩
    cases double
    all_goals simp only [SystemProofs.lrRows, Bool.false_eq_true, ite_true, ite_false,
      JoltISA.lrwProgramAuto, JoltISA.lrdProgramAuto]
    all_goals split <;> simp [NoStoreProgram, NoStoreRow]
  | true =>
    have hs := storePlan_ram (if double then .dword else .word) rs1 0#64 _
      (reservation_store_plan double rd rs1 rs2) s t
    have heq : accessAddress (if double then .dword else .word)
        (JoltISA.sourceValue (.xreg rs1) s) 0#64 =
        SystemProofs.reservationBase double (JoltISA.sourceValue (.xreg rs1) s) := by
      cases double <;> simp [accessAddress, SystemProofs.reservationBase, amoWordBase]
    obtain ⟨hstore, hdev⟩ := hs (by simpa only [heq] using hram) hrun
    exact ⟨⟨ha, hl, by simpa only [heq, ite_true] using hstore⟩, hdev⟩

/-- The memory conditions of a RISC-V instruction in the Jolt state `js`: Jolt's tracer accepts the
load or store of the doubleword the instruction accesses (`Assumptions.JoltRamLoadOk`,
`Assumptions.JoltRamStoreOk`, `ReservationMemory`). Instructions that access no memory have no
condition.
For example, `LB rd rs1 imm` needs the load of the doubleword holding `rs1 + imm` to be accepted. -/
def MemoryConditions : RiscvInstruction → SailJoltState → Prop
  | .LB _ rs1 imm, js | .LH _ rs1 imm, js | .LW _ rs1 imm, js
  | .LBU _ rs1 imm, js | .LHU _ rs1 imm, js | .LWU _ rs1 imm, js
  | .LD _ rs1 imm, js =>
      Assumptions.JoltRamLoadOk
        (compute_aligned_dword_base_address (JoltISA.sourceValue (.xreg rs1) js) imm) js
  | .SB _ rs1 imm, js | .SH _ rs1 imm, js | .SW _ rs1 imm, js
  | .SD _ rs1 imm, js =>
      Assumptions.JoltRamStoreOk
        (compute_aligned_dword_base_address (JoltISA.sourceValue (.xreg rs1) js) imm) js
  | .AMOSWAP_W _ rs1 _ _ _, js | .AMOADD_W _ rs1 _ _ _, js
  | .AMOXOR_W _ rs1 _ _ _, js | .AMOAND_W _ rs1 _ _ _, js
  | .AMOOR_W _ rs1 _ _ _, js | .AMOMIN_W _ rs1 _ _ _, js
  | .AMOMAX_W _ rs1 _ _ _, js | .AMOMINU_W _ rs1 _ _ _, js
  | .AMOMAXU_W _ rs1 _ _ _, js =>
      Assumptions.JoltRamStoreOk (amoWordBase (JoltISA.sourceValue (.xreg rs1) js)) js
  | .AMOSWAP_D _ rs1 _ _ _, js | .AMOADD_D _ rs1 _ _ _, js
  | .AMOXOR_D _ rs1 _ _ _, js | .AMOAND_D _ rs1 _ _ _, js
  | .AMOOR_D _ rs1 _ _ _, js | .AMOMIN_D _ rs1 _ _ _, js
  | .AMOMAX_D _ rs1 _ _ _, js | .AMOMINU_D _ rs1 _ _ _, js
  | .AMOMAXU_D _ rs1 _ _ _, js =>
      Assumptions.JoltRamStoreOk (JoltISA.sourceValue (.xreg rs1) js) js
  | .LR_W _ rs1 _ _, js => ReservationMemory false false rs1 js
  | .LR_D _ rs1 _ _, js => ReservationMemory false true rs1 js
  | .SC_W _ rs1 _ _ _, js => ReservationMemory true false rs1 js
  | .SC_D _ rs1 _ _ _, js => ReservationMemory true true rs1 js
  | _, _ => True

private theorem loadProgram_ram (kind : AccessKind) (dst : JoltISA.Dst) (rs : regidx)
    (imm : BitVec 64) (rest : JoltISA.Program) (s t : SailJoltState)
    (htail : NoStoreProgram rest)
    (hram : JoltISA.RAM_START_ADDRESS ≤
      ((JoltISA.sourceValue (.xreg rs) s + imm) &&& (-8 : BitVec 64)).toNat)
    (hrun : JoltISA.execProgram (.instr (loadRow kind dst rs imm) rest) s =
      .ok RETIRE_SUCCESS t) :
    Assumptions.JoltRamLoadOk
      ((JoltISA.sourceValue (.xreg rs) s + imm) &&& (-8 : BitVec 64)) s ∧
      t.jolt_device = s.jolt_device := by
  obtain ⟨u, hload, hrest⟩ := JoltISA.execProgram_instr_run_retire_inv _ _ s t hrun
  refine ⟨load_row_ram kind dst rs imm s u hram hload, ?_⟩
  have hrow : NoStoreRow (loadRow kind dst rs imm) := by cases kind <;> trivial
  exact (noStoreProgram_device rest htail u t _ hrest).trans
    (noStoreRow_device _ hrow s u _ hload)

private theorem csrRead_noStore (csr : JoltISA.SystemCSR) (rd : regidx)
    (rest : JoltISA.Program) (h : NoStoreProgram rest) :
    NoStoreProgram (JoltISA.csrReadInto csr rd rest) := by
  unfold JoltISA.csrReadInto
  split_ifs <;> simp [NoStoreProgram, NoStoreRow, h]

private theorem csrSwap_noStore (csr : JoltISA.SystemCSR) (src : JoltISA.Src) :
    NoStoreProgram (JoltISA.csrSwapWrite csr src) := by
  cases csr <;> simp [JoltISA.csrSwapWrite, NoStoreProgram, NoStoreRow]

private theorem csrrw_noStore (csr : JoltISA.SystemCSR) (rs rd : regidx) :
    NoStoreProgram (JoltISA.csrrwProgram csr rs rd) := by
  unfold JoltISA.csrrwProgram
  split_ifs <;> simp only [NoStoreProgram, NoStoreRow, true_and]
  all_goals apply csrRead_noStore
  all_goals first | exact csrSwap_noStore _ _ | trivial

private theorem csrBit_noStore (clear : Bool) (csr : JoltISA.SystemCSR) (rs rd : regidx) :
    NoStoreProgram (JoltISA.csrBitUpdateProgram clear csr rs rd) := by
  unfold JoltISA.csrBitUpdateProgram
  split_ifs
  all_goals simp only [NoStoreProgram, NoStoreRow, true_and]
  all_goals first
    | exact csrRead_noStore _ _ _ (by cases clear <;> trivial)
    | simp [JoltISA.pureWritebackRdZeroProgram, NoStoreProgram, NoStoreRow]

private theorem csrrwi_noStore (csr : JoltISA.SystemCSR) (imm : BitVec 5) (rd : regidx) :
    NoStoreProgram (JoltISA.csrrwiProgram csr imm rd) := by
  unfold JoltISA.csrrwiProgram
  apply csrRead_noStore
  cases csr <;> simp only
  all_goals first
    | trivial
    | (split_ifs <;> trivial)

private theorem csrImmediateBit_noStore (clear : Bool) (csr : JoltISA.SystemCSR)
    (imm : BitVec 5) (rd : regidx) :
    NoStoreProgram (JoltISA.csrImmediateBitUpdateProgram clear csr imm rd) := by
  unfold JoltISA.csrImmediateBitUpdateProgram
  apply csrRead_noStore
  split_ifs <;> cases clear <;> trivial

private theorem retire_conditions (i : RiscvInstruction) (hi : i.Lifted)
    (s t : SailJoltState) (hram : RamAccess i s)
    (hrun : RiscvInstruction.joltRun (honestInstr i s) s = .ok RETIRE_SUCCESS t) :
    MemoryConditions i s ∧ t.jolt_device = s.jolt_device := by
  cases i
  case LB rd rs1 imm =>
    simp only [honestInstr, RiscvInstruction.joltRun, JoltISA.lbProgramAuto] at hrun
    split at hrun <;> exact loadProgram_ram .byte _ rs1 _ _ s t
      (by simp [NoStoreProgram, NoStoreRow]) hram hrun
  case LBU rd rs1 imm =>
    simp only [honestInstr, RiscvInstruction.joltRun, JoltISA.lbuProgramAuto] at hrun
    split at hrun <;> exact loadProgram_ram .byte _ rs1 _ _ s t
      (by simp [NoStoreProgram, NoStoreRow]) hram hrun
  case LH rd rs1 imm =>
    simp only [honestInstr, RiscvInstruction.joltRun, JoltISA.lhProgramAuto] at hrun
    split at hrun <;> exact loadProgram_ram .halfword _ rs1 _ _ s t
      (by simp [NoStoreProgram, NoStoreRow]) hram hrun
  case LHU rd rs1 imm =>
    simp only [honestInstr, RiscvInstruction.joltRun, JoltISA.lhuProgramAuto] at hrun
    split at hrun <;> exact loadProgram_ram .halfword _ rs1 _ _ s t
      (by simp [NoStoreProgram, NoStoreRow]) hram hrun
  case LW rd rs1 imm =>
    simp only [honestInstr, RiscvInstruction.joltRun, JoltISA.lwProgramAuto] at hrun
    split at hrun <;> exact loadProgram_ram .word _ rs1 _ _ s t
      (by simp [NoStoreProgram, NoStoreRow]) hram hrun
  case LWU rd rs1 imm =>
    simp only [honestInstr, RiscvInstruction.joltRun, JoltISA.lwuProgramAuto] at hrun
    split at hrun <;> exact loadProgram_ram .word _ rs1 _ _ s t
      (by simp [NoStoreProgram, NoStoreRow]) hram hrun
  case LD rd rs1 imm =>
    have hl := load_row_ram .dword (JoltISA.sideEffectingRdZeroDst rd) rs1
      (sign_extend (m := 64) imm) s t hram hrun
    exact ⟨hl, noStoreRow_device (JoltISA.ldNativeInstr rd rs1 imm) (by simp [NoStoreRow, JoltISA.ldNativeInstr]) s t _ hrun⟩
  case SD rs2 rs1 imm =>
    exact native_store_ram rs1 (.xreg rs2) _ s t hram hrun
  case SB rs2 rs1 imm =>
    exact storePlan_ram .byte rs1 (sign_extend (m := 64) imm) _
      (by
        simp only [JoltISA.sbProgramAuto]
        repeat' first
          | exact StorePlan.store _ _ (by simp [NoStoreProgram, NoStoreRow])
          | apply StorePlan.scratch _ _ (by simp [ScratchRow])) s t hram hrun
  case SH rs2 rs1 imm =>
    exact storePlan_ram .halfword rs1 (sign_extend (m := 64) imm) _
      (by
        simp only [JoltISA.shProgramAuto]
        repeat' first
          | exact StorePlan.store _ _ (by simp [NoStoreProgram, NoStoreRow])
          | apply StorePlan.scratch _ _ (by simp [ScratchRow])) s t hram hrun
  case SW rs2 rs1 imm =>
    exact storePlan_ram .word rs1 (sign_extend (m := 64) imm) _
      (by
        simp only [JoltISA.swProgramAuto]
        repeat' first
          | exact StorePlan.store _ _ (by simp [NoStoreProgram, NoStoreRow])
          | apply StorePlan.scratch _ _ (by simp [ScratchRow])) s t hram hrun
  case AMOSWAP_W rd rs1 rs2 aq rl =>
    simpa [MemoryConditions, accessAddress, amoWordBase] using
      storePlan_ram .word rs1 0 _
        (by
          simp only [JoltISA.amoswapwProgramAuto]
          split <;> repeat' first
            | exact StorePlan.store _ _ (by simp [NoStoreProgram, NoStoreRow])
            | apply StorePlan.scratch _ _ (by simp [ScratchRow])) s t
        (by simpa [RamAccess, accessAddress, amoWordBase] using hram) hrun
  case AMOADD_W rd rs1 rs2 aq rl =>
    simpa [MemoryConditions, accessAddress, amoWordBase] using
      storePlan_ram .word rs1 0 _
        (by
          simp only [JoltISA.amoaddwProgramAuto]
          split <;> repeat' first
            | exact StorePlan.store _ _ (by simp [NoStoreProgram, NoStoreRow])
            | apply StorePlan.scratch _ _ (by simp [ScratchRow])) s t
        (by simpa [RamAccess, accessAddress, amoWordBase] using hram) hrun
  case AMOXOR_W rd rs1 rs2 aq rl =>
    simpa [MemoryConditions, accessAddress, amoWordBase] using
      storePlan_ram .word rs1 0 _
        (by
          simp only [JoltISA.amoxorwProgramAuto]
          split <;> repeat' first
            | exact StorePlan.store _ _ (by simp [NoStoreProgram, NoStoreRow])
            | apply StorePlan.scratch _ _ (by simp [ScratchRow])) s t
        (by simpa [RamAccess, accessAddress, amoWordBase] using hram) hrun
  case AMOAND_W rd rs1 rs2 aq rl =>
    simpa [MemoryConditions, accessAddress, amoWordBase] using
      storePlan_ram .word rs1 0 _
        (by
          simp only [JoltISA.amoandwProgramAuto]
          split <;> repeat' first
            | exact StorePlan.store _ _ (by simp [NoStoreProgram, NoStoreRow])
            | apply StorePlan.scratch _ _ (by simp [ScratchRow])) s t
        (by simpa [RamAccess, accessAddress, amoWordBase] using hram) hrun
  case AMOOR_W rd rs1 rs2 aq rl =>
    simpa [MemoryConditions, accessAddress, amoWordBase] using
      storePlan_ram .word rs1 0 _
        (by
          simp only [JoltISA.amoorwProgramAuto]
          split <;> repeat' first
            | exact StorePlan.store _ _ (by simp [NoStoreProgram, NoStoreRow])
            | apply StorePlan.scratch _ _ (by simp [ScratchRow])) s t
        (by simpa [RamAccess, accessAddress, amoWordBase] using hram) hrun
  case AMOMIN_W rd rs1 rs2 aq rl =>
    simpa [MemoryConditions, accessAddress, amoWordBase] using
      storePlan_ram .word rs1 0 _
        (by
          simp only [JoltISA.amominwProgramAuto]
          split <;> repeat' first
            | exact StorePlan.store _ _ (by simp [NoStoreProgram, NoStoreRow])
            | apply StorePlan.scratch _ _ (by simp [ScratchRow])) s t
        (by simpa [RamAccess, accessAddress, amoWordBase] using hram) hrun
  case AMOMAX_W rd rs1 rs2 aq rl =>
    simpa [MemoryConditions, accessAddress, amoWordBase] using
      storePlan_ram .word rs1 0 _
        (by
          simp only [JoltISA.amomaxwProgramAuto]
          split <;> repeat' first
            | exact StorePlan.store _ _ (by simp [NoStoreProgram, NoStoreRow])
            | apply StorePlan.scratch _ _ (by simp [ScratchRow])) s t
        (by simpa [RamAccess, accessAddress, amoWordBase] using hram) hrun
  case AMOMINU_W rd rs1 rs2 aq rl =>
    simpa [MemoryConditions, accessAddress, amoWordBase] using
      storePlan_ram .word rs1 0 _
        (by
          simp only [JoltISA.amominuwProgramAuto]
          split <;> repeat' first
            | exact StorePlan.store _ _ (by simp [NoStoreProgram, NoStoreRow])
            | apply StorePlan.scratch _ _ (by simp [ScratchRow])) s t
        (by simpa [RamAccess, accessAddress, amoWordBase] using hram) hrun
  case AMOMAXU_W rd rs1 rs2 aq rl =>
    simpa [MemoryConditions, accessAddress, amoWordBase] using
      storePlan_ram .word rs1 0 _
        (by
          simp only [JoltISA.amomaxuwProgramAuto]
          split <;> repeat' first
            | exact StorePlan.store _ _ (by simp [NoStoreProgram, NoStoreRow])
            | apply StorePlan.scratch _ _ (by simp [ScratchRow])) s t
        (by simpa [RamAccess, accessAddress, amoWordBase] using hram) hrun
  case AMOSWAP_D rd rs1 rs2 aq rl =>
    simpa [MemoryConditions, accessAddress, amoWordBase] using
      storePlan_ram .dword rs1 0 _
        (by
          simp only [JoltISA.amoswapdProgramAuto]
          split <;> repeat' first
            | exact StorePlan.store _ _ (by simp [NoStoreProgram, NoStoreRow])
            | apply StorePlan.scratch _ _ (by simp [ScratchRow])) s t
        (by simpa [RamAccess, accessAddress, amoWordBase] using hram) hrun
  case AMOADD_D rd rs1 rs2 aq rl =>
    simpa [MemoryConditions, accessAddress, amoWordBase] using
      storePlan_ram .dword rs1 0 _
        (by
          simp only [JoltISA.amoadddProgramAuto]
          split <;> repeat' first
            | exact StorePlan.store _ _ (by simp [NoStoreProgram, NoStoreRow])
            | apply StorePlan.scratch _ _ (by simp [ScratchRow])) s t
        (by simpa [RamAccess, accessAddress, amoWordBase] using hram) hrun
  case AMOXOR_D rd rs1 rs2 aq rl =>
    simpa [MemoryConditions, accessAddress, amoWordBase] using
      storePlan_ram .dword rs1 0 _
        (by
          simp only [JoltISA.amoxordProgramAuto]
          split <;> repeat' first
            | exact StorePlan.store _ _ (by simp [NoStoreProgram, NoStoreRow])
            | apply StorePlan.scratch _ _ (by simp [ScratchRow])) s t
        (by simpa [RamAccess, accessAddress, amoWordBase] using hram) hrun
  case AMOAND_D rd rs1 rs2 aq rl =>
    simpa [MemoryConditions, accessAddress, amoWordBase] using
      storePlan_ram .dword rs1 0 _
        (by
          simp only [JoltISA.amoanddProgramAuto]
          split <;> repeat' first
            | exact StorePlan.store _ _ (by simp [NoStoreProgram, NoStoreRow])
            | apply StorePlan.scratch _ _ (by simp [ScratchRow])) s t
        (by simpa [RamAccess, accessAddress, amoWordBase] using hram) hrun
  case AMOOR_D rd rs1 rs2 aq rl =>
    simpa [MemoryConditions, accessAddress, amoWordBase] using
      storePlan_ram .dword rs1 0 _
        (by
          simp only [JoltISA.amoordProgramAuto]
          split <;> repeat' first
            | exact StorePlan.store _ _ (by simp [NoStoreProgram, NoStoreRow])
            | apply StorePlan.scratch _ _ (by simp [ScratchRow])) s t
        (by simpa [RamAccess, accessAddress, amoWordBase] using hram) hrun
  case AMOMIN_D rd rs1 rs2 aq rl =>
    simpa [MemoryConditions, accessAddress, amoWordBase] using
      storePlan_ram .dword rs1 0 _
        (by
          simp only [JoltISA.amomindProgramAuto]
          split <;> repeat' first
            | exact StorePlan.store _ _ (by simp [NoStoreProgram, NoStoreRow])
            | apply StorePlan.scratch _ _ (by simp [ScratchRow])) s t
        (by simpa [RamAccess, accessAddress, amoWordBase] using hram) hrun
  case AMOMAX_D rd rs1 rs2 aq rl =>
    simpa [MemoryConditions, accessAddress, amoWordBase] using
      storePlan_ram .dword rs1 0 _
        (by
          simp only [JoltISA.amomaxdProgramAuto]
          split <;> repeat' first
            | exact StorePlan.store _ _ (by simp [NoStoreProgram, NoStoreRow])
            | apply StorePlan.scratch _ _ (by simp [ScratchRow])) s t
        (by simpa [RamAccess, accessAddress, amoWordBase] using hram) hrun
  case AMOMINU_D rd rs1 rs2 aq rl =>
    simpa [MemoryConditions, accessAddress, amoWordBase] using
      storePlan_ram .dword rs1 0 _
        (by
          simp only [JoltISA.amominudProgramAuto]
          split <;> repeat' first
            | exact StorePlan.store _ _ (by simp [NoStoreProgram, NoStoreRow])
            | apply StorePlan.scratch _ _ (by simp [ScratchRow])) s t
        (by simpa [RamAccess, accessAddress, amoWordBase] using hram) hrun
  case AMOMAXU_D rd rs1 rs2 aq rl =>
    simpa [MemoryConditions, accessAddress, amoWordBase] using
      storePlan_ram .dword rs1 0 _
        (by
          simp only [JoltISA.amomaxudProgramAuto]
          split <;> repeat' first
            | exact StorePlan.store _ _ (by simp [NoStoreProgram, NoStoreRow])
            | apply StorePlan.scratch _ _ (by simp [ScratchRow])) s t
        (by simpa [RamAccess, accessAddress, amoWordBase] using hram) hrun
  case ECALL => exact False.elim hi
  case EBREAK => exact False.elim hi
  case LR_W rd rs1 aq rl => exact reservation_conditions false false rd rs1 zreg s t hram hrun
  case LR_D rd rs1 aq rl => exact reservation_conditions false true rd rs1 zreg s t hram hrun
  case SC_W rd rs1 rs2 aq rl => exact reservation_conditions true false rd rs1 rs2 s t hram hrun
  case SC_D rd rs1 rs2 aq rl => exact reservation_conditions true true rd rs1 rs2 s t hram hrun
  case MRET =>
    exact ⟨trivial, noStoreProgram_device _ (by trivial) s t _ hrun⟩
  case CSRRW => exact ⟨trivial, noStoreProgram_device _ (csrrw_noStore _ _ _) s t _ hrun⟩
  case CSRRS => exact ⟨trivial, noStoreProgram_device _ (csrBit_noStore false _ _ _) s t _ hrun⟩
  case CSRRC => exact ⟨trivial, noStoreProgram_device _ (csrBit_noStore true _ _ _) s t _ hrun⟩
  case CSRRWI => exact ⟨trivial, noStoreProgram_device _ (csrrwi_noStore _ _ _) s t _ hrun⟩
  case CSRRSI => exact ⟨trivial, noStoreProgram_device _ (csrImmediateBit_noStore false _ _ _) s t _ hrun⟩
  case CSRRCI => exact ⟨trivial, noStoreProgram_device _ (csrImmediateBit_noStore true _ _ _) s t _ hrun⟩

  all_goals
    refine ⟨True.intro, ?_⟩
    simp only [honestInstr, RiscvInstruction.joltRun, JoltISA.execLUI] at hrun
    first
    | apply noStoreRow_device _ ?_ s t _ hrun
      first
      | (unfold JoltISA.pureWritebackNativeInstr; split_ifs <;> trivial)
      | (unfold JoltISA.Instr.rewriteNative; trivial)
      | trivial
    | apply noStoreProgram_device _ ?_ s t _ hrun
      simp only [JoltISA.slliProgramAuto,
          JoltISA.srliProgramAuto,
          JoltISA.sraiProgramAuto,
          JoltISA.sllProgramAuto,
          JoltISA.srlProgramAuto,
          JoltISA.sraProgramAuto,
          JoltISA.slliwProgramAuto,
          JoltISA.srliwProgramAuto,
          JoltISA.sraiwProgramAuto,
          JoltISA.sllwProgramAuto,
          JoltISA.srlwProgramAuto,
          JoltISA.srawProgramAuto,
          JoltISA.mulhProgramAuto,
          JoltISA.mulhsuProgramAuto,
          JoltISA.divProgramAuto,
          JoltISA.divuProgramAuto,
          JoltISA.remProgramAuto,
          JoltISA.remuProgramAuto,
          JoltISA.divwProgramAuto,
          JoltISA.divuwProgramAuto,
          JoltISA.remwProgramAuto,
          JoltISA.remuwProgramAuto ]
      split <;> simp [NoStoreProgram, NoStoreRow]


private def loadBundle (js : SailJoltState) (hinv : Step.StepInvariant js.sail)
    (hlink : System.systemProject js = js.sail) (hmprv : Assumptions.MstatusMprvZero js.sail)
    (imm : BitVec 12) (rs1 : regidx)
    (hw : DwordReadWindowAssumptions
      (compute_aligned_dword_base_address (JoltISA.sourceValue (.xreg rs1) js) imm) js.sail)
    (hr : Assumptions.JoltRamLoadOk
      (compute_aligned_dword_base_address (JoltISA.sourceValue (.xreg rs1) js) imm) js) :
    LoadProgramEqSailAssumptions imm rs1 js :=
  { unarySource js hinv hlink rs1, hw with
    cur_privilege := ⟨hinv.machine⟩
    mstatus_mprv := hmprv
    jolt_ram := hr }

private def storeBundle (js : SailJoltState) (hinv : Step.StepInvariant js.sail)
    (hlink : System.systemProject js = js.sail) (hmprv : Assumptions.MstatusMprvZero js.sail)
    (imm : BitVec 12) (rs2 rs1 : regidx)
    (hw : DwordReadWriteWindowAssumptions
      (compute_aligned_dword_base_address (JoltISA.sourceValue (.xreg rs1) js) imm) js.sail)
    (hr : Assumptions.JoltRamStoreOk
      (compute_aligned_dword_base_address (JoltISA.sourceValue (.xreg rs1) js) imm) js) :
    StoreProgramEqSailAssumptions imm rs2 rs1 js :=
  { loadBundle js hinv hlink hmprv imm rs1 hw.toDwordReadWindowAssumptions
      ⟨hr.below_heap_end⟩, hw.toDwordWriteWindowAssumptions with
    rs2_val := JoltISA.sourceValue (.xreg rs2) js
    rs2_read := source_read js hinv rs2
    jolt_ram_store := hr }

private def amoWordBundle (js : SailJoltState) (hinv : Step.StepInvariant js.sail)
    (hlink : System.systemProject js = js.sail) (hmprv : Assumptions.MstatusMprvZero js.sail)
    (op : amoop) (rs2 rs1 rd : regidx)
    (hw : DwordAtomicWindowAssumptions op (amoWordBase (JoltISA.sourceValue (.xreg rs1) js)) js.sail)
    (hr : Assumptions.JoltRamStoreOk (amoWordBase (JoltISA.sourceValue (.xreg rs1) js)) js) :
    AmoWordProgramEqSailAssumptions op rs2 rs1 rd js :=
  { binarySource js hinv hlink rs2 rs1, hw with
    rd_readable := ⟨_, source_read js hinv rd⟩
    cur_privilege := ⟨hinv.machine⟩
    mstatus_mprv := hmprv
    jolt_ram_load := ⟨hr.below_heap_end⟩
    jolt_ram_store := hr }

private def amoDwordBundle (js : SailJoltState) (hinv : Step.StepInvariant js.sail)
    (hlink : System.systemProject js = js.sail) (hmprv : Assumptions.MstatusMprvZero js.sail)
    (op : amoop) (rs2 rs1 rd : regidx)
    (hw : DwordAtomicWindowAssumptions op (JoltISA.sourceValue (.xreg rs1) js) js.sail)
    (hr : Assumptions.JoltRamStoreOk (JoltISA.sourceValue (.xreg rs1) js) js) :
    AmoDwordProgramEqSailAssumptions op rs2 rs1 rd js :=
  { binarySource js hinv hlink rs2 rs1, hw with
    rd_readable := ⟨_, source_read js hinv rd⟩
    cur_privilege := ⟨hinv.machine⟩
    mstatus_mprv := hmprv
    jolt_ram_load := ⟨hr.below_heap_end⟩
    jolt_ram_store := hr }

private theorem reservation_checks (s : SailState) (double : Bool) (addr : BitVec 64)
    (hpma : s.regs.get? Register.pma_regions = some platformPma)
    (hlo : JoltISA.RAM_START_ADDRESS ≤ (SystemProofs.reservationBase double addr).toNat)
    (ha : addr &&& (if double then 7#64 else 3#64) = 0#64)
    (hhi : (SystemProofs.reservationBase double addr).toNat + 8 ≤ 2 ^ 64) :
    phys_access_check (LoadReserved Data) .Machine (.Physaddr addr)
        (if double then 8 else 4) true s = .ok none s ∧
    phys_access_check (StoreConditional Data) .Machine (.Physaddr addr)
        (if double then 8 else 4) true s = .ok none s := by
  obtain ⟨offset, hfits, heq⟩ := SystemProofs.reservation_subaccess double addr ha
  have hn : 0 < (if double then 8 else 4 : Nat) := by cases double <;> decide
  have hadd := toNat_add_small_of_no_ovf (SystemProofs.reservationBase double addr)
    offset (by omega)
  rw [heq] at hadd
  have hread := readReg_eq_of_get? Register.pma_regions s _ hpma
  have hmatch := matching_platform_ram addr (if double then 8 else 4)
    (by omega) hn (by omega) (by omega)
  simp [phys_access_check, HartConfig.pmpCheck_run, pmaCheck, hread, hmatch, ramRegion,
    bne, show (Reservability.RsrvEventual == Reservability.RsrvNone) = false by decide,
    LeanRV64D.sail_assert, Sail.ConcurrencyInterfaceV1.PreSail.sail_assert,
    LeanRV64D.Functions.not, bind, EStateM.bind, pure, EStateM.pure]

private def reservationWindow (js : SailJoltState) (double : Bool) (rs1 : regidx)
    (hinv : Step.StepInvariant js.sail) (hmprv : Assumptions.MstatusMprvZero js.sail)
    (hm : ReservationMemory false double rs1 js)
    (hw : DwordAtomicWindowAssumptions .AMOADD
      (SystemProofs.reservationBase double (JoltISA.sourceValue (.xreg rs1) js)) js.sail) :
    SystemProofs.ReservationWindow double (JoltISA.sourceValue (.xreg rs1) js) js :=
  { cur_privilege := ⟨hinv.machine⟩
    mstatus_mprv := hmprv
    align := hm.align
    dword_present := hw.dword_present
    not_readable_mmio := hw.not_readable_mmio
    jolt_ram := hm.load }

private def reservationReadBundle (js : SailJoltState) (double : Bool) (rs1 : regidx)
    (hlink : System.systemProject js = js.sail) (hinv : Step.StepInvariant js.sail)
    (hmprv : Assumptions.MstatusMprvZero js.sail)
    (hm : ReservationMemory false double rs1 js)
    (hw : DwordAtomicWindowAssumptions .AMOADD
      (SystemProofs.reservationBase double (JoltISA.sourceValue (.xreg rs1) js)) js.sail)
    (hpma : js.sail.regs.get? Register.pma_regions = some platformPma)
    (hlo : JoltISA.RAM_START_ADDRESS ≤
      (SystemProofs.reservationBase double (JoltISA.sourceValue (.xreg rs1) js)).toNat)
    (hhi : (SystemProofs.reservationBase double
      (JoltISA.sourceValue (.xreg rs1) js)).toNat + 8 ≤ 2 ^ 64) :
    SystemProofs.ReservationReadEqAssumptions double rs1 js :=
  { unarySource js hinv hlink rs1, reservationWindow js double rs1 hinv hmprv hm hw with
    reserved_access := (reservation_checks js.sail double _ hpma hlo hm.align hhi).1 }

private def reservationStoreBundle (js : SailJoltState) (double : Bool) (rs2 rs1 : regidx)
    (hlink : System.systemProject js = js.sail) (hinv : Step.StepInvariant js.sail)
    (hmprv : Assumptions.MstatusMprvZero js.sail)
    (hm : ReservationMemory true double rs1 js)
    (hw : DwordAtomicWindowAssumptions .AMOADD
      (SystemProofs.reservationBase double (JoltISA.sourceValue (.xreg rs1) js)) js.sail)
    (hpma : js.sail.regs.get? Register.pma_regions = some platformPma)
    (hlo : JoltISA.RAM_START_ADDRESS ≤
      (SystemProofs.reservationBase double (JoltISA.sourceValue (.xreg rs1) js)).toNat)
    (hhi : (SystemProofs.reservationBase double
      (JoltISA.sourceValue (.xreg rs1) js)).toNat + 8 ≤ 2 ^ 64)
    (hsys : SystemInv js) :
    SystemProofs.ReservationStoreEqAssumptions double rs2 rs1 js :=
  { binarySource js hinv hlink rs2 rs1,
    reservationWindow js double rs1 hinv hmprv ⟨hm.align, hm.load, trivial⟩ hw with
    not_writable_mmio := hw.not_writable_mmio
    jolt_ram_store := hm.store_ok
    conditional_access := (reservation_checks js.sail double _ hpma hlo hm.align hhi).2
    reservation_pair := hsys.reservation_pair }

private def csrBundle (js : SailJoltState) (hsys : SystemInv js)
    (hlink : System.systemProject js = js.sail) (hinv : Step.StepInvariant js.sail) :
    RiscvInstruction.CsrEqAssumptions js :=
  { invariant := hlink.symm ▸ hinv
    mstatus_bits := hsys.mstatus_bits
    mtvec_mode := hsys.mtvec_mode
    mepc_align := hsys.mepc_align }

private def csrRegBundle (js : SailJoltState) (rs1 : regidx) (hsys : SystemInv js)
    (hlink : System.systemProject js = js.sail) (hinv : Step.StepInvariant js.sail) :
    RiscvInstruction.CsrRegEqAssumptions rs1 js :=
  { csrBundle js hsys hlink hinv, unarySource js hinv hlink rs1 with }

/-- An instruction whose memory conditions hold (`MemoryConditions`) has the Sail equivalence
bundle and honest advice. The premises are those of `equivAssumptions_of_retire`, with the
memory conditions in place of a retiring Jolt run.
For example, an `LB` whose doubleword load Jolt's tracer accepts has its load bundle. -/
theorem equivAssumptions_of_conditions (i : RiscvInstruction) (hi : i.Lifted)
    (js : SailJoltState) (hsys : SystemInv js)
    (hlink : System.systemProject js = js.sail)
    (hinv : Step.StepInvariant js.sail)
    (hmstatus : js.vregs JoltISA.mstatusVReg &&& ~~~(0x88 : BitVec 64) = 0)
    (hlayout : ∃ config, MemoryLayout.new config = some js.jolt_device.memory_layout)
    (heven : i.EvenOffsets)
    (hpc : ∀ pc, js.sail.regs.get? Register.PC = some pc → pc.getLsbD 0 = false)
    (hheap : js.jolt_device.memory_layout.heap_end.toNat ≤ 2 ^ 64 - 8)
    (hpma : js.sail.regs.get? Register.pma_regions = some platformPma)
    (hhtif : js.sail.regs.get? Register.htif_tohost_base = some none)
    (hpresent : ∀ a, memLow js.jolt_device ≤ a → a < memHigh js.jolt_device →
      ∃ b, js.sail.mem.get? a = some b)
    (hram : RamAccess i js)
    (hc : MemoryConditions i js) :
    ∃ h : RiscvInstruction.equivAssumptions (honestInstr i js) js,
      RiscvInstruction.AdviceHonest (honestInstr i js) js h := by
  have hmprv := mprv_zero js hlink hmstatus
  have window (base : BitVec 64)
      (hram : JoltISA.RAM_START_ADDRESS ≤ base.toNat)
      (hbelow : base.toNat < js.jolt_device.memory_layout.heap_end.toNat)
      (op : amoop) (hop : (op == .AMOCAS) = false) :
      DwordAtomicWindowAssumptions op base js.sail :=
    ram_windows js base hpma hhtif (layout_memLow js hlayout) hpresent hram hbelow
      (by omega) op hop
  cases i
  case LUI rd imm => exact ⟨noSource js hlink, True.intro⟩
  case AUIPC rd imm => exact ⟨{ noSource js hlink with pc_readable := hinv.present _ }, True.intro⟩
  case JAL rd imm => exact ⟨jalBundle js hinv hlink imm heven hpc, True.intro⟩
  case JALR rd rs1 imm => exact ⟨jalrBundle js hinv hlink imm rs1, True.intro⟩
  case FENCE => exact ⟨{ noSource js hlink with cur_privilege := ⟨hinv.machine⟩ }, True.intro⟩
  case LB rd rs1 imm =>
    exact ⟨loadBundle js hinv hlink hmprv imm rs1
      (window _ hram hc.below_heap_end .AMOADD (by decide)).toDwordReadWindowAssumptions hc,
      True.intro⟩
  case LBU rd rs1 imm =>
    exact ⟨loadBundle js hinv hlink hmprv imm rs1
      (window _ hram hc.below_heap_end .AMOADD (by decide)).toDwordReadWindowAssumptions hc,
      True.intro⟩
  case LH rd rs1 imm =>
    exact ⟨loadBundle js hinv hlink hmprv imm rs1
      (window _ hram hc.below_heap_end .AMOADD (by decide)).toDwordReadWindowAssumptions hc,
      True.intro⟩
  case LHU rd rs1 imm =>
    exact ⟨loadBundle js hinv hlink hmprv imm rs1
      (window _ hram hc.below_heap_end .AMOADD (by decide)).toDwordReadWindowAssumptions hc,
      True.intro⟩
  case LW rd rs1 imm =>
    exact ⟨loadBundle js hinv hlink hmprv imm rs1
      (window _ hram hc.below_heap_end .AMOADD (by decide)).toDwordReadWindowAssumptions hc,
      True.intro⟩
  case LWU rd rs1 imm =>
    exact ⟨loadBundle js hinv hlink hmprv imm rs1
      (window _ hram hc.below_heap_end .AMOADD (by decide)).toDwordReadWindowAssumptions hc,
      True.intro⟩
  case LD rd rs1 imm =>
    exact ⟨loadBundle js hinv hlink hmprv imm rs1
      (window _ hram hc.below_heap_end .AMOADD (by decide)).toDwordReadWindowAssumptions hc,
      True.intro⟩
  case SB rs2 rs1 imm =>
    exact ⟨storeBundle js hinv hlink hmprv imm rs2 rs1
      (window _ hram hc.below_heap_end .AMOADD (by decide)).toDwordReadWriteWindowAssumptions hc,
      True.intro⟩
  case SH rs2 rs1 imm =>
    exact ⟨storeBundle js hinv hlink hmprv imm rs2 rs1
      (window _ hram hc.below_heap_end .AMOADD (by decide)).toDwordReadWriteWindowAssumptions hc,
      True.intro⟩
  case SW rs2 rs1 imm =>
    exact ⟨storeBundle js hinv hlink hmprv imm rs2 rs1
      (window _ hram hc.below_heap_end .AMOADD (by decide)).toDwordReadWriteWindowAssumptions hc,
      True.intro⟩
  case SD rs2 rs1 imm =>
    exact ⟨storeBundle js hinv hlink hmprv imm rs2 rs1
      (window _ hram hc.below_heap_end .AMOADD (by decide)).toDwordReadWriteWindowAssumptions hc,
      True.intro⟩
  case AMOSWAP_W rd rs1 rs2 aq rl =>
    exact ⟨amoWordBundle js hinv hlink hmprv .AMOSWAP rs2 rs1 rd
      (window _ hram hc.below_heap_end .AMOSWAP (by decide)) hc, True.intro⟩
  case AMOADD_W rd rs1 rs2 aq rl =>
    exact ⟨amoWordBundle js hinv hlink hmprv .AMOADD rs2 rs1 rd
      (window _ hram hc.below_heap_end .AMOADD (by decide)) hc, True.intro⟩
  case AMOXOR_W rd rs1 rs2 aq rl =>
    exact ⟨amoWordBundle js hinv hlink hmprv .AMOXOR rs2 rs1 rd
      (window _ hram hc.below_heap_end .AMOXOR (by decide)) hc, True.intro⟩
  case AMOAND_W rd rs1 rs2 aq rl =>
    exact ⟨amoWordBundle js hinv hlink hmprv .AMOAND rs2 rs1 rd
      (window _ hram hc.below_heap_end .AMOAND (by decide)) hc, True.intro⟩
  case AMOOR_W rd rs1 rs2 aq rl =>
    exact ⟨amoWordBundle js hinv hlink hmprv .AMOOR rs2 rs1 rd
      (window _ hram hc.below_heap_end .AMOOR (by decide)) hc, True.intro⟩
  case AMOMIN_W rd rs1 rs2 aq rl =>
    exact ⟨amoWordBundle js hinv hlink hmprv .AMOMIN rs2 rs1 rd
      (window _ hram hc.below_heap_end .AMOMIN (by decide)) hc, True.intro⟩
  case AMOMAX_W rd rs1 rs2 aq rl =>
    exact ⟨amoWordBundle js hinv hlink hmprv .AMOMAX rs2 rs1 rd
      (window _ hram hc.below_heap_end .AMOMAX (by decide)) hc, True.intro⟩
  case AMOMINU_W rd rs1 rs2 aq rl =>
    exact ⟨amoWordBundle js hinv hlink hmprv .AMOMINU rs2 rs1 rd
      (window _ hram hc.below_heap_end .AMOMINU (by decide)) hc, True.intro⟩
  case AMOMAXU_W rd rs1 rs2 aq rl =>
    exact ⟨amoWordBundle js hinv hlink hmprv .AMOMAXU rs2 rs1 rd
      (window _ hram hc.below_heap_end .AMOMAXU (by decide)) hc, True.intro⟩
  case AMOSWAP_D rd rs1 rs2 aq rl =>
    exact ⟨amoDwordBundle js hinv hlink hmprv .AMOSWAP rs2 rs1 rd
      (window _ hram hc.below_heap_end .AMOSWAP (by decide)) hc, True.intro⟩
  case AMOADD_D rd rs1 rs2 aq rl =>
    exact ⟨amoDwordBundle js hinv hlink hmprv .AMOADD rs2 rs1 rd
      (window _ hram hc.below_heap_end .AMOADD (by decide)) hc, True.intro⟩
  case AMOXOR_D rd rs1 rs2 aq rl =>
    exact ⟨amoDwordBundle js hinv hlink hmprv .AMOXOR rs2 rs1 rd
      (window _ hram hc.below_heap_end .AMOXOR (by decide)) hc, True.intro⟩
  case AMOAND_D rd rs1 rs2 aq rl =>
    exact ⟨amoDwordBundle js hinv hlink hmprv .AMOAND rs2 rs1 rd
      (window _ hram hc.below_heap_end .AMOAND (by decide)) hc, True.intro⟩
  case AMOOR_D rd rs1 rs2 aq rl =>
    exact ⟨amoDwordBundle js hinv hlink hmprv .AMOOR rs2 rs1 rd
      (window _ hram hc.below_heap_end .AMOOR (by decide)) hc, True.intro⟩
  case AMOMIN_D rd rs1 rs2 aq rl =>
    exact ⟨amoDwordBundle js hinv hlink hmprv .AMOMIN rs2 rs1 rd
      (window _ hram hc.below_heap_end .AMOMIN (by decide)) hc, True.intro⟩
  case AMOMAX_D rd rs1 rs2 aq rl =>
    exact ⟨amoDwordBundle js hinv hlink hmprv .AMOMAX rs2 rs1 rd
      (window _ hram hc.below_heap_end .AMOMAX (by decide)) hc, True.intro⟩
  case AMOMINU_D rd rs1 rs2 aq rl =>
    exact ⟨amoDwordBundle js hinv hlink hmprv .AMOMINU rs2 rs1 rd
      (window _ hram hc.below_heap_end .AMOMINU (by decide)) hc, True.intro⟩
  case AMOMAXU_D rd rs1 rs2 aq rl =>
    exact ⟨amoDwordBundle js hinv hlink hmprv .AMOMAXU rs2 rs1 rd
      (window _ hram hc.below_heap_end .AMOMAXU (by decide)) hc, True.intro⟩
  case ECALL => exact False.elim hi
  case EBREAK => exact False.elim hi
  case MRET =>
    exact ⟨⟨hlink.symm ▸ hinv, hsys.mstatus_bits, hsys.mepc_align⟩, trivial⟩
  case CSRRW | CSRRS | CSRRC => exact ⟨csrRegBundle js _ hsys hlink hinv, trivial⟩
  case CSRRWI | CSRRSI | CSRRCI => exact ⟨csrBundle js hsys hlink hinv, trivial⟩
  case LR_W rd rs1 aq rl =>
    exact ⟨reservationReadBundle js false rs1 hlink hinv hmprv hc
      (window _ hram hc.load.below_heap_end .AMOADD (by decide)) hpma hram (by
        have := hc.load.below_heap_end; dsimp [SystemProofs.reservationBase] at *; omega), trivial⟩
  case LR_D rd rs1 aq rl =>
    exact ⟨reservationReadBundle js true rs1 hlink hinv hmprv hc
      (window _ hram hc.load.below_heap_end .AMOADD (by decide)) hpma hram (by
        have := hc.load.below_heap_end; dsimp [SystemProofs.reservationBase] at *; omega), trivial⟩
  case SC_W rd rs1 rs2 aq rl =>
    exact ⟨reservationStoreBundle js false rs2 rs1 hlink hinv hmprv hc
      (window _ hram hc.load.below_heap_end .AMOADD (by decide)) hpma hram (by
        have := hc.load.below_heap_end; dsimp [SystemProofs.reservationBase] at *; omega) hsys, trivial⟩
  case SC_D rd rs1 rs2 aq rl =>
    exact ⟨reservationStoreBundle js true rs2 rs1 hlink hinv hmprv hc
      (window _ hram hc.load.below_heap_end .AMOADD (by decide)) hpma hram (by
        have := hc.load.below_heap_end; dsimp [SystemProofs.reservationBase] at *; omega) hsys, trivial⟩
  all_goals first
    | exact ⟨unarySource js hinv hlink _, True.intro⟩
    | exact ⟨binarySource js hinv hlink _ _, by first | exact True.intro | rfl⟩

/-- A retiring RAM instruction has the Sail equivalence bundle and honest advice.
For example, an honest `LB` run supplies its heap bound, while memory presence
supplies the eight bytes of the enclosing doubleword.
The additional premises are: `hsys` (invariant: legal persistent system values),
`hmstatus` (invariant: Jolt retains only MIE/MPIE),
`hlayout` (invariant: the device layout was constructed successfully),
`heven` (from decoding: relative offsets are even),
`hpc` (invariant: the current PC is even), and
`hheap` (platform: the heap leaves eight bytes before address wrap).
The run supplies the heap and stack-canary checks made by Jolt's tracer in
`tracer/src/emulator/mmu.rs` (`Mmu::assert_effective_address`) at `5def437f`. -/
theorem equivAssumptions_of_retire (i : RiscvInstruction) (hi : i.Lifted)
    (js : SailJoltState) (hsys : SystemInv js)
    (hlink : System.systemProject js = js.sail)
    (hinv : Step.StepInvariant js.sail)
    (hmstatus : js.vregs JoltISA.mstatusVReg &&& ~~~(0x88 : BitVec 64) = 0)
    (hlayout : ∃ config, MemoryLayout.new config = some js.jolt_device.memory_layout)
    (heven : i.EvenOffsets)
    (hpc : ∀ pc, js.sail.regs.get? Register.PC = some pc → pc.getLsbD 0 = false)
    (hheap : js.jolt_device.memory_layout.heap_end.toNat ≤ 2 ^ 64 - 8)
    (hpma : js.sail.regs.get? Register.pma_regions = some platformPma)
    (hhtif : js.sail.regs.get? Register.htif_tohost_base = some none)
    (hpresent : ∀ a, memLow js.jolt_device ≤ a → a < memHigh js.jolt_device →
      ∃ b, js.sail.mem.get? a = some b)
    (hram : RamAccess i js)
    (hok : ∃ js', RiscvInstruction.joltRun (honestInstr i js) js = .ok RETIRE_SUCCESS js') :
    ∃ h : RiscvInstruction.equivAssumptions (honestInstr i js) js,
      RiscvInstruction.AdviceHonest (honestInstr i js) js h := by
  obtain ⟨js', hrun⟩ := hok
  exact equivAssumptions_of_conditions i hi js hsys hlink hinv hmstatus hlayout heven hpc hheap
    hpma hhtif hpresent hram (retire_conditions i hi js js' hram hrun).1

/-- A retiring instruction whose doubleword access is in RAM preserves the
entire Jolt device, including its outputs and panic flag.
For example, `SD` into RAM updates Sail memory and leaves the device unchanged.
Jolt's tracer uses the RAM branch of `Mmu::store_doubleword_raw` in
`tracer/src/emulator/mmu.rs` at `5def437f`. -/
theorem joltRun_device_of_ram (i : RiscvInstruction) (hi : i.Lifted)
    (js js' : SailJoltState) (hram : RamAccess i js)
    (hrun : RiscvInstruction.joltRun (honestInstr i js) js = .ok RETIRE_SUCCESS js') :
    js'.jolt_device = js.jolt_device :=
  (retire_conditions i hi js js' hram hrun).2

end WholeRun
