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

Both are parametric in the register lists, so BLAKE2, SHA-256 and Keccak can use them.
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

end JoltISA.Inlines
