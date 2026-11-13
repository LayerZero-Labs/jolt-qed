import JoltBytecode.Inlines.AdviceStores

/-!
# Runs of doubleword load and store blocks

Hash inlines start by loading their state and input into virtual registers and end by storing
the state back. This module runs such blocks in one step:

* `run_ldRows_iff`: a block of `LD d, off(r)` rows runs exactly when every load succeeds, and it
  sets each destination to the doubleword it loads (`ldFile`).
* `run_sdRows_iff`: a block of `SD r, x, off + 8k` rows runs exactly when every target doubleword
  is aligned and writable, and it writes the registers to consecutive doublewords
  (`writeDwords`).

* `run_ldPostRows_iff` and `run_sdPreRows_iff`: the same for blocks that run register rows
  after each load (SHA-256 splits and byte-swaps the words it loads) or before each store
  (SHA-256 packs two words into the doubleword it stores).
* `regRun_resets`: rows `ADDI vr(48 + k), x0, 0` reset a set of pool registers to zero.

All are parametric in the register lists, so BLAKE2, SHA-256 and Keccak can use them.
-/

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail LeanRV64D
  LeanRV64D.Functions

set_option autoImplicit false

noncomputable section

namespace JoltISA.Inlines

/-! ## Loads -/

/-- The rows `LD d, off(r)`, one for each `(d, off)` in `ds`.
Example: `ldRows x10 [(vr80, 0), (vr81, 8)]` loads the doublewords at `x10` and `x10 + 8`. -/
def ldRows (r : regidx) (ds : List (VReg × BitVec 64)) : List Instr :=
  ds.map fun p => .LD .normal (.vreg p.1) (.xreg r) p.2

/-- `ldRows` of a nonempty list starts with the load of its head.
Example: `ldRows x10 [(vr80, 0), (vr81, 8)]` is `LD vr80, 0(x10)` followed by `ldRows x10 [(vr81, 8)]`. -/
theorem ldRows_cons (r : regidx) (p : VReg × BitVec 64) (ds : List (VReg × BitVec 64)) :
    ldRows r (p :: ds) = .LD .normal (.vreg p.1) (.xreg r) p.2 :: ldRows r ds := rfl

/-- The register file `f` after loading, for each `(d, off)` in `ds` in order, the doubleword at
`base + off` of `s` into `d`; a failed load counts as `0`.
Example: `ldFile s base [(vr80, 0)] f = setV f vr80 v` when `loadDword? s base = some v`. -/
def ldFile (s : SailJoltState) (base : BitVec 64) (ds : List (VReg × BitVec 64))
    (f : VReg → BitVec 64) : VReg → BitVec 64 :=
  ds.foldl (fun f p => setV f p.1 ((loadDword? s (base + p.2)).getD 0)) f

/-- What the loads read does not depend on the registers.
Example: `ldFile { s with vregs := g } base ds f = ldFile s base ds f`. -/
@[simp] theorem ldFile_vregs (s : SailJoltState) (g : VReg → BitVec 64) (base : BitVec 64)
    (ds : List (VReg × BitVec 64)) (f : VReg → BitVec 64) :
    ldFile { s with vregs := g } base ds f = ldFile s base ds f := by
  simp only [ldFile, loadDword?_vregs]

/-- The loads keep every register that no load writes.
Example: `ldFile s base [(vr80, 0)] f vr10 = f vr10`. -/
theorem ldFile_apply_of_forall_ne (s : SailJoltState) (base : BitVec 64)
    (ds : List (VReg × BitVec 64)) (f : VReg → BitVec 64) (r : VReg)
    (h : ∀ p ∈ ds, p.1 ≠ r) : ldFile s base ds f r = f r := by
  induction ds generalizing f with
  | nil => rfl
  | cons p ds ih =>
    simp only [ldFile, List.foldl_cons] at ih ⊢
    rw [ih _ (fun q hq => h q (List.mem_cons_of_mem _ hq))]
    simp only [setV, ite_eq_right_iff]
    intro hr
    exact absurd hr.symm (h p List.mem_cons_self)

/-- `ldFile` of a nonempty list loads the head first.
Example: `ldFile s base [(vr80, 0), (vr81, 8)] f` is `ldFile s base [(vr81, 8)] (setV f vr80 w)`, where
`w` is the doubleword at `base`, or `0` when that load fails. -/
theorem ldFile_cons (s : SailJoltState) (base : BitVec 64) (p : VReg × BitVec 64)
    (ds : List (VReg × BitVec 64)) (f : VReg → BitVec 64) :
    ldFile s base (p :: ds) f = ldFile s base ds (setV f p.1 ((loadDword? s (base + p.2)).getD 0)) :=
  rfl

/-- With distinct destinations, a loaded register holds the doubleword loaded into it.
Example: `ldFile s base [(vr80, 0), (vr81, 8)] f vr81 = (loadDword? s (base + 8)).getD 0`. -/
theorem ldFile_apply_of_mem (s : SailJoltState) (base : BitVec 64) (ds : List (VReg × BitVec 64))
    (f : VReg → BitVec 64) (hnd : (ds.map Prod.fst).Nodup) {d : VReg} {off : BitVec 64}
    (hm : (d, off) ∈ ds) : ldFile s base ds f d = (loadDword? s (base + off)).getD 0 := by
  induction ds generalizing f with
  | nil => cases hm
  | cons p ds ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    rw [ldFile_cons]
    rcases List.mem_cons.1 hm with rfl | hm'
    · rw [ldFile_apply_of_forall_ne _ _ _ _ _
        (fun q hq he => hnd.1 (List.mem_map.2 ⟨q, hq, he⟩)), setV_same]
    · exact ih _ hnd.2 hm'

/-- **A block of loads.** If base register `r` reads `base`, a run of `ldRows r ds ++ rest` from
`s` is a run of `rest` from `s` with the loaded registers, and it exists only when every load
succeeds.
Example: with `x10` reading `0x8001_0000`, a run of `[LD vr80, 0(x10); rest]` is a run of
`rest` with `vr80` set to the doubleword at `0x8001_0000`. -/
theorem run_ldRows_iff {r : regidx} {base : BitVec 64} {s : SailJoltState} (hr : XReads s r base)
    (ds : List (VReg × BitVec 64)) (hds : ∀ p ∈ ds, 32 ≤ p.1.toNat) (rest : List Instr)
    (s' : SailJoltState) :
    (Program.seq (ldRows r ds ++ rest)).Run s s' ↔
      (∀ p ∈ ds, (loadDword? s (base + p.2)).isSome) ∧
        (Program.seq rest).Run { s with vregs := ldFile s base ds s.vregs } s' := by
  induction ds generalizing s with
  | nil =>
    simp only [ldRows, List.map_nil, List.nil_append, List.not_mem_nil, false_implies,
      implies_true, true_and]
    rfl
  | cons p ds ih =>
    obtain ⟨d, off⟩ := p
    have hd : 32 ≤ d.toNat := hds _ List.mem_cons_self
    have hds' : ∀ q ∈ ds, 32 ≤ q.1.toNat := fun q hq => hds q (List.mem_cons_of_mem _ hq)
    rw [ldRows_cons, List.cons_append, run_ld_iff hd hr]
    have key : ∀ v : BitVec 64,
        (Program.seq (ldRows r ds ++ rest)).Run { s with vregs := setV s.vregs d v } s' ↔
          (∀ q ∈ ds, (loadDword? s (base + q.2)).isSome) ∧
            (Program.seq rest).Run { s with vregs := ldFile s base ds (setV s.vregs d v) } s' := by
      intro v
      rw [ih (XReads.vregs _ hr) hds']
      simp only [loadDword?_vregs, ldFile_vregs]
    simp only [key, List.forall_mem_cons]
    constructor
    · rintro ⟨v, hv, hall, hrun⟩
      refine ⟨⟨by simp [hv], hall⟩, ?_⟩
      simpa only [ldFile, List.foldl_cons, hv, Option.getD_some] using hrun
    · rintro ⟨⟨h0, hall⟩, hrun⟩
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 h0
      refine ⟨v, hv, hall, ?_⟩
      simpa only [ldFile, List.foldl_cons, hv, Option.getD_some] using hrun

/-! ## Stores -/

/-- The rows `SD r, x, off + 8k` for the `k`-th register `x` of `xs`.
Example: `sdRows x10 0 [vr80, vr81]` stores `vr80` at `x10` and `vr81` at `x10 + 8`. -/
def sdRows (r : regidx) (off : Nat) : List VReg → List Instr
  | [] => []
  | x :: xs => .SD (.xreg r) (.vreg x) (BitVec.ofNat 64 off) :: sdRows r (off + 8) xs

/-- **A block of stores.** Let base register `r` read `C`, with the stores in RAM and no address
wrapping. A run of `sdRows r off xs ++ rest` from `s` is a run of `rest` from `s` with the
registers `xs` written to consecutive doublewords from `C + off`, and it exists only when every
target doubleword is aligned and writable.
Example: with `x10` reading `0x8001_0000`, a run of `sdRows x10 0 [vr80, vr81] ++ rest` is a run
of `rest` with `vr80` at `0x8001_0000` and `vr81` at `0x8001_0008`. -/
theorem run_sdRows_iff {r : regidx} {C : BitVec 64} (hC : RAM_START_ADDRESS ≤ C.toNat)
    (off : Nat) (xs : List VReg) (s : SailJoltState) (hr : XReads s r C)
    (hw : C.toNat + off + 8 * xs.length ≤ 2 ^ 64) (rest : List Instr) (s' : SailJoltState) :
    (Program.seq (sdRows r off xs ++ rest)).Run s s' ↔
      (∀ k < xs.length, DwordWritable s.jolt_device (C.toNat + off + 8 * k)) ∧
        (Program.seq rest).Run
          { s with sail := { s.sail with
              mem := writeDwords s.sail.mem (C.toNat + off) (xs.map s.vregs) } } s' := by
  induction xs generalizing off s with
  | nil =>
    simp only [sdRows, List.nil_append, List.length_nil, Nat.not_lt_zero, false_implies,
      implies_true, true_and, List.map_nil, writeDwords]
  | cons x xs ih =>
    simp only [List.length_cons] at hw
    have hoff : off < 2 ^ 64 := by omega
    have haddr : (C + BitVec.ofNat 64 off).toNat = C.toNat + off := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hoff,
        Nat.mod_eq_of_lt (by omega)]
    have hram : RAM_START_ADDRESS ≤ (C + BitVec.ofNat 64 off).toNat := by rw [haddr]; omega
    rw [sdRows, List.cons_append, run_sd_iff hr]
    have hr2 := XReads.of_regs (s := s)
      (t := ({ s with sail := { s.sail with
        mem := Mmu.write_ram_doubleword s.sail.mem (C.toNat + off) (s.vregs x) } } :
          SailJoltState)) rfl hr
    have hih := ih (off + 8) _ hr2 (by omega)
    rw [show C.toNat + (off + 8) = C.toNat + off + 8 by omega] at hih
    simp only [List.length_cons, List.map_cons, writeDwords]
    constructor
    · rintro ⟨t, ht, hrun⟩
      obtain ⟨hal, hok, rfl⟩ := storeDword?_ram_inv hram ht
      rw [haddr] at hal hok hrun
      obtain ⟨hall, hrest⟩ := hih.1 hrun
      refine ⟨fun k hk => ?_, hrest⟩
      cases k with
      | zero => exact ⟨by simpa using hal, by simpa using hok⟩
      | succ k =>
        have h := hall k (by omega)
        rwa [show C.toNat + off + 8 * (k + 1) = C.toNat + off + 8 + 8 * k by omega]
    · rintro ⟨hall, hrest⟩
      have h0 := hall 0 (by omega)
      simp only [Nat.mul_zero, Nat.add_zero] at h0
      refine ⟨_, storeDword?_ram _ (by rw [haddr]; exact h0.1) hram
        (by rw [haddr]; exact h0.2), ?_⟩
      rw [haddr]
      refine hih.2 ⟨fun k hk => ?_, hrest⟩
      have h := hall (k + 1) (by omega)
      rwa [show C.toNat + off + 8 * (k + 1) = C.toNat + off + 8 + 8 * k by omega] at h

/-! ## Loads followed by register rows -/

/-- For each `(d, off, post)` in `gs`, the row `LD d, off(r)` and then the register rows `post`.
Example: `ldPostRows x11 [(vr56, 0, [VirtualRev8W vr56 vr56 0])]` loads the doubleword at `x11`
into `vr56`, then reverses the bytes of each of its words. -/
def ldPostRows (r : regidx) (gs : List (VReg × BitVec 64 × List Instr)) : List Instr :=
  gs.flatMap fun g => .LD .normal (.vreg g.1) (.xreg r) g.2.1 :: g.2.2

/-- The register file `f` after `ldPostRows r gs` with `base` in `r`: in order, each load sets
its destination to the doubleword at `base + off` of `s` (`0` when that load fails), and then
its register rows run. It is `none` when a register row has no register semantics.
Example: `ldPostFile s base [(vr56, 0, [])] f = some (setV f vr56 v)` when
`loadDword? s base = some v`. -/
def ldPostFile (s : SailJoltState) (base : BitVec 64) :
    List (VReg × BitVec 64 × List Instr) → (VReg → BitVec 64) → Option (VReg → BitVec 64)
  | [], f => some f
  | g :: gs, f =>
    (regRun g.2.2 (setV f g.1 ((loadDword? s (base + g.2.1)).getD 0))).bind (ldPostFile s base gs)

/-- What the loads read does not depend on the registers.
Example: `ldPostFile { s with vregs := g } base gs f = ldPostFile s base gs f`. -/
@[simp] theorem ldPostFile_vregs (s : SailJoltState) (g : VReg → BitVec 64) (base : BitVec 64)
    (gs : List (VReg × BitVec 64 × List Instr)) (f : VReg → BitVec 64) :
    ldPostFile { s with vregs := g } base gs f = ldPostFile s base gs f := by
  induction gs generalizing f with
  | nil => rfl
  | cons p gs ih =>
    obtain ⟨d, off, post⟩ := p
    simp only [ldPostFile, loadDword?_vregs, ih]

/-- `ldPostFile` of a concatenation runs the first part, then the second.
Example: `ldPostFile s base (gs ++ []) f = ldPostFile s base gs f`. -/
theorem ldPostFile_append (s : SailJoltState) (base : BitVec 64)
    (gs₁ gs₂ : List (VReg × BitVec 64 × List Instr)) (f : VReg → BitVec 64) :
    ldPostFile s base (gs₁ ++ gs₂) f = (ldPostFile s base gs₁ f).bind (ldPostFile s base gs₂) := by
  induction gs₁ generalizing f with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.cons_append, ldPostFile]
    cases regRun g.2.2 (setV f g.1 ((loadDword? s (base + g.2.1)).getD 0)) with
    | none => rfl
    | some f₁ => simp only [Option.bind_some, ih]

/-- **A block of loads with register rows.** If base register `r` reads `base` and the block
evaluates to `F` from the register file of `s`, a run of `ldPostRows r gs ++ rest` from `s` is
a run of `rest` from `s` with register file `F`, and it exists only when every load succeeds.
Example: with `x11` reading `0x8001_0000`, a run of `[LD vr56, 0(x11); VirtualRev8W vr56 vr56;
rest]` is a run of `rest` with `vr56` set to the byte-swapped doubleword at `0x8001_0000`. -/
theorem run_ldPostRows_iff {r : regidx} {base : BitVec 64} {s : SailJoltState}
    (hr : XReads s r base) (gs : List (VReg × BitVec 64 × List Instr))
    (hgs : ∀ g ∈ gs, 32 ≤ g.1.toNat) {F : VReg → BitVec 64}
    (hF : ldPostFile s base gs s.vregs = some F) (rest : List Instr) (s' : SailJoltState) :
    (Program.seq (ldPostRows r gs ++ rest)).Run s s' ↔
      (∀ g ∈ gs, (loadDword? s (base + g.2.1)).isSome) ∧
        (Program.seq rest).Run { s with vregs := F } s' := by
  induction gs generalizing s with
  | nil =>
    simp only [ldPostFile, Option.some.injEq] at hF
    subst hF
    simp only [ldPostRows, List.flatMap_nil, List.nil_append, List.not_mem_nil, false_implies,
      implies_true, true_and]
  | cons g gs ih =>
    obtain ⟨d, off, post⟩ := g
    have hd : 32 ≤ d.toNat := hgs _ List.mem_cons_self
    have hgs' : ∀ q ∈ gs, 32 ≤ q.1.toNat := fun q hq => hgs q (List.mem_cons_of_mem _ hq)
    simp only [ldPostFile, Option.bind_eq_some_iff] at hF
    obtain ⟨f₁, hf₁, hF⟩ := hF
    have hF' : ldPostFile { s with vregs := f₁ } base gs ({ s with vregs := f₁ } : SailJoltState).vregs
        = some F := by simpa using hF
    have hih := ih (s := { s with vregs := f₁ }) (XReads.vregs _ hr) hgs' hF'
    simp only [loadDword?_vregs] at hih
    rw [show ldPostRows r ((d, off, post) :: gs) =
        .LD .normal (.vreg d) (.xreg r) off :: (post ++ ldPostRows r gs) from rfl,
      List.cons_append, List.append_assoc, run_ld_iff hd hr, List.forall_mem_cons]
    constructor
    · rintro ⟨v, hv, hrun⟩
      rw [hv, Option.getD_some] at hf₁
      rw [run_append_of_regRun (s := { s with vregs := setV s.vregs d v }) hf₁] at hrun
      obtain ⟨hall, hrest⟩ := hih.1 hrun
      exact ⟨⟨by simp [hv], hall⟩, hrest⟩
    · rintro ⟨⟨h0, hall⟩, hrun⟩
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 h0
      rw [hv, Option.getD_some] at hf₁
      refine ⟨v, hv, ?_⟩
      rw [run_append_of_regRun (s := { s with vregs := setV s.vregs d v }) hf₁]
      exact hih.2 ⟨hall, hrun⟩

/-! ## Register rows followed by stores -/

/-- For each `(pre, x)` in `gs`, the register rows `pre` and then the row `SD r, x, off + 8k`,
for the `k`-th entry.
Example: `sdPreRows x10 0 [([OR vr48 vr49 vr48], vr48)]` computes `vr48` and stores it at
`x10`. -/
def sdPreRows (r : regidx) (off : Nat) : List (List Instr × VReg) → List Instr
  | [] => []
  | (pre, x) :: gs => pre ++ .SD (.xreg r) (.vreg x) (BitVec.ofNat 64 off) :: sdPreRows r (off + 8) gs

/-- The register file after the register rows of `sdPreRows r off gs` from `f`, and the
doublewords that its stores write, in order. It is `none` when a register row has no register
semantics.
Example: `sdPreFile [([], vr48)] f = some (f, [f vr48])`. -/
def sdPreFile : List (List Instr × VReg) → (VReg → BitVec 64) →
    Option ((VReg → BitVec 64) × List (BitVec 64))
  | [], f => some (f, [])
  | g :: gs, f =>
    (regRun g.1 f).bind fun f₁ => (sdPreFile gs f₁).map fun p => (p.1, f₁ g.2 :: p.2)

/-- **A block of stores with register rows.** Let base register `r` read `C`, with the stores
in RAM and no address wrapping, and let the register rows evaluate to `F` and the stored
doublewords be `vs`. A run of `sdPreRows r off gs ++ rest` from `s` is a run of `rest` from `s`
with register file `F` and `vs` written to consecutive doublewords from `C + off`, and it exists
only when every target doubleword is aligned and writable.
Example: with `x10` reading `0x8001_0000`, a run of `[OR vr48 vr49 vr48; SD vr48, 0(x10); rest]`
is a run of `rest` with `vr49 ||| vr48` in `vr48` and at `0x8001_0000`. -/
theorem run_sdPreRows_iff {r : regidx} {C : BitVec 64} (hC : RAM_START_ADDRESS ≤ C.toNat)
    (off : Nat) (gs : List (List Instr × VReg)) (s : SailJoltState) (hr : XReads s r C)
    (hw : C.toNat + off + 8 * gs.length ≤ 2 ^ 64) {F : VReg → BitVec 64} {vs : List (BitVec 64)}
    (hF : sdPreFile gs s.vregs = some (F, vs)) (rest : List Instr) (s' : SailJoltState) :
    (Program.seq (sdPreRows r off gs ++ rest)).Run s s' ↔
      (∀ k < gs.length, DwordWritable s.jolt_device (C.toNat + off + 8 * k)) ∧
        (Program.seq rest).Run
          { s with vregs := F,
                   sail := { s.sail with mem := writeDwords s.sail.mem (C.toNat + off) vs } } s' := by
  induction gs generalizing off s F vs with
  | nil =>
    simp only [sdPreFile, Option.some.injEq, Prod.mk.injEq] at hF
    obtain ⟨rfl, rfl⟩ := hF
    simp only [sdPreRows, List.nil_append, List.length_nil, Nat.not_lt_zero, false_implies,
      implies_true, true_and, writeDwords]
  | cons g gs ih =>
    obtain ⟨pre, x⟩ := g
    simp only [List.length_cons] at hw
    simp only [sdPreFile, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hF
    obtain ⟨f₁, hf₁, ⟨F', vs'⟩, hF', he⟩ := hF
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    let s₂ : SailJoltState := { s with vregs := f₁, sail := { s.sail with
      mem := writeDwords s.sail.mem (C.toNat + off) [f₁ x] } }
    have hr₂ : XReads s₂ r C := XReads.of_regs (s := s) rfl hr
    have hih := ih (off + 8) s₂ hr₂ (by omega) hF'
    rw [show C.toNat + (off + 8) = C.toNat + off + 8 by omega] at hih
    rw [sdPreRows, List.append_assoc, List.cons_append, run_append_of_regRun hf₁,
      show ∀ l : List Instr, Instr.SD (.xreg r) (.vreg x) (BitVec.ofNat 64 off) :: l =
        sdRows r off [x] ++ l from fun _ => rfl,
      run_sdRows_iff hC off [x] _ (XReads.vregs f₁ hr) (by simp only [List.length_singleton]; omega)]
    simp only [List.length_cons, List.length_nil, Nat.zero_add, List.map_cons, List.map_nil]
    constructor
    · rintro ⟨h0, hrun⟩
      obtain ⟨hall, hrest⟩ := hih.1 hrun
      refine ⟨fun k hk => ?_, hrest⟩
      cases k with
      | zero => exact h0 0 (by omega)
      | succ k =>
        have h := hall k (by omega)
        rwa [show C.toNat + off + 8 * (k + 1) = C.toNat + off + 8 + 8 * k by omega]
    · rintro ⟨hall, hrest⟩
      refine ⟨fun k hk => ?_, hih.2 ⟨fun k hk => ?_, hrest⟩⟩
      · obtain rfl : k = 0 := by omega
        exact hall 0 (by omega)
      · have h := hall (k + 1) (by omega)
        rwa [show C.toNat + off + 8 * (k + 1) = C.toNat + off + 8 + 8 * k by omega] at h

/-! ## Blocks indexed by `List.range` -/

/-- Steps that keep register `r` keep it through a fold over `List.range n`.
Example: if no step writes `vr40`, the fold leaves `vr40` as it was. -/
theorem foldl_range_frame (step : Nat → (VReg → BitVec 64) → VReg → BitVec 64) (n : Nat)
    (F : VReg → BitVec 64) (r : VReg) (h : ∀ k < n, ∀ f, step k f r = f r) :
    (List.range n).foldl (fun f k => step k f) F r = F r := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, h n (by omega),
      ih (fun k hk => h k (by omega))]

/-- If no step after step `i` writes register `r`, the fold over `List.range n` leaves in `r`
what step `i` put there.
Example: step 2 of 4 sets `vr60` and step 3 does not write it, so the fold ends with step 2's
value. -/
theorem foldl_range_apply (step : Nat → (VReg → BitVec 64) → VReg → BitVec 64) (n i : Nat)
    (hi : i < n) (F : VReg → BitVec 64) (r : VReg)
    (h : ∀ k, i < k → k < n → ∀ f, step k f r = f r) :
    (List.range n).foldl (fun f k => step k f) F r =
      step i ((List.range i).foldl (fun f k => step k f) F) r := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · rw [h n hi (by omega), ih hi (fun k h1 h2 => h k h1 (by omega))]
    · rfl

/-- `sdPreFile` of a concatenation runs the first part, then the second, and joins the stored
doublewords.
Example: `sdPreFile (gs ++ []) f = sdPreFile gs f`. -/
theorem sdPreFile_append (gs₁ gs₂ : List (List Instr × VReg)) (f : VReg → BitVec 64) :
    sdPreFile (gs₁ ++ gs₂) f =
      (sdPreFile gs₁ f).bind fun p => (sdPreFile gs₂ p.1).map fun q => (q.1, p.2 ++ q.2) := by
  induction gs₁ generalizing f with
  | nil =>
    simp only [List.nil_append, sdPreFile, Option.bind_some, List.nil_append]
    cases sdPreFile gs₂ f <;> rfl
  | cons g gs ih =>
    simp only [List.cons_append, sdPreFile]
    cases regRun g.1 f with
    | none => rfl
    | some f₁ =>
      simp only [Option.bind_some, ih]
      cases sdPreFile gs f₁ with
      | none => rfl
      | some p =>
        simp only [Option.bind_some, Option.map_some]
        cases sdPreFile gs₂ p.1 <;> rfl

/-- **Loads indexed by `List.range`.** If the register rows of load `i` take the file with the
loaded doubleword to `step i f`, the loads of `(List.range n).map g` evaluate to the fold of the
steps.
Example: for `n = 1`, `ldPostFile s base [g 0] F = some (step 0 F)`. -/
theorem ldPostFile_range (s : SailJoltState) (base : BitVec 64) (n : Nat)
    (g : Nat → VReg × BitVec 64 × List Instr)
    (step : Nat → (VReg → BitVec 64) → VReg → BitVec 64)
    (h : ∀ i < n, ∀ f, regRun (g i).2.2 (setV f (g i).1 ((loadDword? s (base + (g i).2.1)).getD 0)) =
      some (step i f)) (F : VReg → BitVec 64) :
    ldPostFile s base ((List.range n).map g) F =
      some ((List.range n).foldl (fun f i => step i f) F) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.map_append, ldPostFile_append, ih (fun i hi => h i (by omega)),
      Option.bind_some, List.foldl_append, List.map_cons, List.map_nil]
    simp only [ldPostFile, h n (by omega), Option.bind_some, List.foldl_cons, List.foldl_nil]

/-- **Stores indexed by `List.range`.** If the register rows before store `i` take `f` to
`step i f`, the block of `(List.range n).map g` evaluates to the fold of the steps, and store
`i` writes register `(g i).2` as step `i` leaves it.
Example: for `n = 1`, `sdPreFile [g 0] F = some (step 0 F, [step 0 F (g 0).2])`. -/
theorem sdPreFile_range (n : Nat) (g : Nat → List Instr × VReg)
    (step : Nat → (VReg → BitVec 64) → VReg → BitVec 64)
    (h : ∀ i < n, ∀ f, regRun (g i).1 f = some (step i f)) (F : VReg → BitVec 64) :
    sdPreFile ((List.range n).map g) F =
      some ((List.range n).foldl (fun f i => step i f) F,
        (List.range n).map fun i => step i ((List.range i).foldl (fun f k => step k f) F) (g i).2) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.map_append, sdPreFile_append, ih (fun i hi => h i (by omega)),
      Option.bind_some]
    simp only [List.map_cons, List.map_nil, sdPreFile, h n (by omega), Option.bind_some,
      Option.map_some, List.foldl_append, List.foldl_cons, List.foldl_nil, List.map_append]

/-! ## Resets -/

/-- **Resets.** The rows `ADDI vr(48 + k), x0, 0`, one for each `k` in `ks`, set those
registers to zero and keep the others.
Example: for `ks = [0, 1]` they zero `vr48` and `vr49`. -/
theorem regRun_resets (ks : List Nat) (hks : ∀ k ∈ ks, 48 + k < 128) (G : VReg → BitVec 64) :
    regRun (ks.map fun k =>
        .ADDI (.vreg (BitVec.ofNat 7 (48 + k))) (.xreg (regidx.Regidx 0)) 0) G =
      some (fun r => if 48 ≤ r.toNat ∧ r.toNat - 48 ∈ ks then 0 else G r) := by
  induction ks generalizing G with
  | nil => simp [regRun]
  | cons k ks ih =>
    have hk : 48 + k < 128 := hks k List.mem_cons_self
    have hd : (BitVec.ofNat 7 (48 + k)).toNat = 48 + k := by
      show (48 + k) % 128 = 48 + k; omega
    rw [List.map_cons, regRun_cons_of rfl (by rw [hd]; omega),
      ih (fun j hj => hks j (List.mem_cons_of_mem _ hj))]
    congr 1
    funext r
    simp only [setV, List.mem_cons]
    by_cases h1 : 48 ≤ r.toNat ∧ r.toNat - 48 ∈ ks
    · simp only [h1, and_self, or_true, ↓reduceIte]
    · by_cases h2 : r = BitVec.ofNat 7 (48 + k)
      · subst h2
        simp [hd]
      · have h3 : ¬ (48 ≤ r.toNat ∧ (r.toNat - 48 = k ∨ r.toNat - 48 ∈ ks)) := by
          rintro ⟨h4, h5 | h5⟩
          · apply h2
            apply BitVec.eq_of_toNat_eq
            rw [hd]
            omega
          · exact h1 ⟨h4, h5⟩
        simp only [h1, h2, h3, ↓reduceIte]

end JoltISA.Inlines
