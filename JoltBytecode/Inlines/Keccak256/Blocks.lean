import JoltBytecode.Inlines.Keccak256.Permutation
import JoltBytecode.Inlines.AdviceStores

/-!
# The blocks of the Keccak rows other than the rounds

* Loads: `stateOf_ldFile` says the loads put the 25 lanes at `A` (`stateAt`) into `vr48..72`.
* Absorption (`KECCAK256_ABSORB_PERMUTE` only): `run_absorbRows_iff` runs the 34 rows, and
  `stateOf_absorbF` says they XOR the 17 lanes of the block at `B` (`blockAt`) into lanes 0 to 16
  (`absorbLanes`). `absorbBlock_blockBytes` says that `absorbLanes` is EthLib's
  `Internal.absorbBlock 136` of the block's 136 bytes (`blockBytes`).
* Stores: `laneRegs_map` says the stores write the lanes of `stateOf`.
* Resets: `regRun_resetRows` says the 37 resets give `poolReset`.
-/

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail LeanRV64D
  LeanRV64D.Functions

set_option autoImplicit false

noncomputable section

namespace JoltISA.Inlines.Keccak256

open JoltSpec.Keccak JoltSpec.Keccak.Internal JoltSpec.Base

/-! ## Lanes in memory -/

/-- The doubleword at `A + 8i` of `s`; a failed load counts as `0`.
Example: `loadLane s A 1` is the doubleword at `A + 8`. -/
def loadLane (s : SailJoltState) (A : BitVec 64) (i : Nat) : BitVec 64 :=
  (loadDword? s (A + BitVec.ofNat 64 (8 * i))).getD 0

/-- What the loads read does not depend on the registers. -/
@[simp] theorem loadLane_vregs (s : SailJoltState) (g : VReg → BitVec 64) (A : BitVec 64)
    (i : Nat) : loadLane { s with vregs := g } A i = loadLane s A i := by
  simp only [loadLane, loadDword?_vregs]

/-- The state whose lane `i` (lane `(x, y)` with `i = x + 5y`) is `g i`.
Example: `(ofLanes g).a7 = .ofBitVec (g 7)`. -/
def ofLanes (g : Nat → BitVec 64) : State :=
  ⟨.ofBitVec (g 0), .ofBitVec (g 1), .ofBitVec (g 2), .ofBitVec (g 3), .ofBitVec (g 4),
    .ofBitVec (g 5), .ofBitVec (g 6), .ofBitVec (g 7), .ofBitVec (g 8), .ofBitVec (g 9),
    .ofBitVec (g 10), .ofBitVec (g 11), .ofBitVec (g 12), .ofBitVec (g 13), .ofBitVec (g 14),
    .ofBitVec (g 15), .ofBitVec (g 16), .ofBitVec (g 17), .ofBitVec (g 18), .ofBitVec (g 19),
    .ofBitVec (g 20), .ofBitVec (g 21), .ofBitVec (g 22), .ofBitVec (g 23), .ofBitVec (g 24)⟩

/-- The 25 lanes of a state as doublewords, lane 0 first.
Example: `(wordsOf S)[7]? = some S.a7.toBitVec`. -/
def wordsOf (S : State) : List (BitVec 64) :=
  [S.a0.toBitVec, S.a1.toBitVec, S.a2.toBitVec, S.a3.toBitVec, S.a4.toBitVec,
    S.a5.toBitVec, S.a6.toBitVec, S.a7.toBitVec, S.a8.toBitVec, S.a9.toBitVec,
    S.a10.toBitVec, S.a11.toBitVec, S.a12.toBitVec, S.a13.toBitVec, S.a14.toBitVec,
    S.a15.toBitVec, S.a16.toBitVec, S.a17.toBitVec, S.a18.toBitVec, S.a19.toBitVec,
    S.a20.toBitVec, S.a21.toBitVec, S.a22.toBitVec, S.a23.toBitVec, S.a24.toBitVec]

/-- `ofLanes` reads `g` only below 25. -/
theorem ofLanes_congr {g g' : Nat → BitVec 64} (h : ∀ i < 25, g i = g' i) :
    ofLanes g = ofLanes g' := by
  simp only [ofLanes,
    h 0 (by omega), h 1 (by omega), h 2 (by omega), h 3 (by omega), h 4 (by omega),
    h 5 (by omega), h 6 (by omega), h 7 (by omega), h 8 (by omega), h 9 (by omega),
    h 10 (by omega), h 11 (by omega), h 12 (by omega), h 13 (by omega), h 14 (by omega),
    h 15 (by omega), h 16 (by omega), h 17 (by omega), h 18 (by omega), h 19 (by omega),
    h 20 (by omega), h 21 (by omega), h 22 (by omega), h 23 (by omega), h 24 (by omega)]

/-- A state is the state of its words. -/
theorem ofLanes_wordsOf (S : State) : ofLanes (fun i => (wordsOf S).getD i 0) = S := by
  cases S
  rfl

/-- The state of the 25 lanes at `A` in `s`.
Example: its lane 1 is the doubleword at `A + 8`. -/
abbrev stateAt (s : SailJoltState) (A : BitVec 64) : State := ofLanes (loadLane s A)

/-- The 17 lanes of the block at `B` in `s`.
Example: its second element is the doubleword at `B + 8`. -/
def blockAt (s : SailJoltState) (B : BitVec 64) : List (BitVec 64) :=
  (List.range 17).map (loadLane s B)

/-- Registers in the pool are not registers outside it. -/
theorem ne_of_pool {r d : VReg} (hr : ¬ InPool r) (hd : InPool d) : r ≠ d := by
  rintro rfl
  exact hr hd

/-- Registers `vr48..84` are in the pool.
Example: `InPool (vr 60)`. -/
theorem vr_pool (n : Nat) (h1 : 48 ≤ n) (h2 : n < 85) : InPool (vr n) := by
  unfold InPool
  rw [BitVec.toNat_ofNat]
  omega

/-- The lanes of the register record are registers `vr48..72`. -/
theorem stateOf_regsOf (g : VReg → BitVec 64) :
    stateOf (regsOf g) = ofLanes (fun i => g (vr (48 + i))) := rfl

/-! ## Loads -/

/-- The 25 lane loads write virtual registers, not architectural ones.
Example: the first load writes `vr48`, and `48 ≥ 32`. -/
theorem laneLds_ge : ∀ p ∈ laneLds, 32 ≤ p.1.toNat := by decide

/-- The 25 loads succeed exactly when the 25 lanes at `A` load. -/
theorem forall_laneLds_iff (s : SailJoltState) (A : BitVec 64) :
    (∀ p ∈ laneLds, (loadDword? s (A + p.2)).isSome) ↔
      ∀ i < 25, (loadDword? s (A + BitVec.ofNat 64 (8 * i))).isSome := by
  simp only [laneLds, List.forall_mem_map, List.mem_range]

/-- **The loads.** After the loads, the lanes of the register file are the state at `A`. -/
theorem stateOf_ldFile (s : SailJoltState) (A : BitVec 64) (f : VReg → BitVec 64) :
    stateOf (regsOf (ldFile s A laneLds f)) = stateAt s A := by
  rw [stateOf_regsOf]
  apply ofLanes_congr
  intro i hi
  apply ldFile_apply_of_mem s A laneLds f (by decide)
  simp only [laneLds, List.mem_map, List.mem_range]
  exact ⟨i, hi, rfl⟩

/-- The loads change no register outside the pool. -/
theorem ldFile_out (s : SailJoltState) (A : BitVec 64) (f : VReg → BitVec 64) (r : VReg)
    (hr : ¬ InPool r) : ldFile s A laneLds f r = f r := by
  apply ldFile_apply_of_forall_ne
  intro p hp
  simp only [laneLds, List.mem_map, List.mem_range] at hp
  obtain ⟨i, hi, rfl⟩ := hp
  exact (ne_of_pool hr (vr_pool _ (by omega) (by omega))).symm

/-! ## Absorption -/

/-- The register file after absorbing block lane `i`: the lane is loaded into `vr84` and XORed
into lane `i`. -/
def absorbStep (s : SailJoltState) (B : BitVec 64) (f : VReg → BitVec 64) (i : Nat) :
    VReg → BitVec 64 :=
  Op.eval (setV f (vr scratch) (loadLane s B i)) (.xor (48 + i) (48 + i) scratch)

/-- The absorption step reads memory only, so the registers of `s` do not matter.
Example: `absorbStep { s with vregs := 0 } B = absorbStep s B`. -/
@[simp] theorem absorbStep_vregs (s : SailJoltState) (g : VReg → BitVec 64) (B : BitVec 64) :
    absorbStep { s with vregs := g } B = absorbStep s B := by
  funext f i
  simp only [absorbStep, loadLane_vregs]

/-- The register file after the 34 absorption rows. -/
def absorbF (s : SailJoltState) (B : BitVec 64) (f : VReg → BitVec 64) : VReg → BitVec 64 :=
  (List.range 17).foldl (absorbStep s B) f

private theorem run_absorb_list {rs2 : regidx} {B : BitVec 64} (is : List Nat)
    (his : ∀ i ∈ is, i < 25) {s : SailJoltState} (hr : XReads s rs2 B) (rest : List Instr)
    (s' : SailJoltState) :
    (Program.seq (is.flatMap (absorbLaneRows rs2) ++ rest)).Run s s' ↔
      (∀ i ∈ is, (loadDword? s (B + BitVec.ofNat 64 (8 * i))).isSome) ∧
        (Program.seq rest).Run { s with vregs := is.foldl (absorbStep s B) s.vregs } s' := by
  induction is generalizing s with
  | nil =>
    simp only [List.flatMap_nil, List.nil_append, List.not_mem_nil, false_implies, implies_true,
      true_and, List.foldl_nil]
  | cons i is ih =>
    have hi : i < 25 := his i List.mem_cons_self
    have hok : (Op.xor (48 + i) (48 + i) scratch).ok = true := by
      simp only [Op.ok, poolNum, scratch, Bool.and_eq_true, decide_eq_true_eq]
      omega
    rw [List.flatMap_cons, List.append_assoc, absorbLaneRows, List.cons_append,
      run_ld_iff (by decide) hr]
    have key : ∀ v : BitVec 64,
        (Program.seq ([Op.xor (48 + i) (48 + i) scratch].map Op.toInstr ++
            (is.flatMap (absorbLaneRows rs2) ++ rest))).Run
          { s with vregs := setV s.vregs (vr scratch) v } s' ↔
          (∀ j ∈ is, (loadDword? s (B + BitVec.ofNat 64 (8 * j))).isSome) ∧
            (Program.seq rest).Run { s with vregs := (is.foldl (absorbStep s B)
              (Op.eval (setV s.vregs (vr scratch) v) (.xor (48 + i) (48 + i) scratch))) } s' := by
      intro v
      rw [run_ops_append _ (by simp only [List.all_cons, hok, List.all_nil, Bool.and_self]),
        ih (fun j hj => his j (List.mem_cons_of_mem _ hj)) (XReads.vregs _ hr)]
      simp only [loadDword?_vregs, absorbStep_vregs, List.foldl_cons, List.foldl_nil]
    simp only [List.singleton_append, List.map_cons, List.map_nil] at key
    simp only [List.cons_append, List.nil_append] at key ⊢
    simp only [key, List.forall_mem_cons, List.foldl_cons]
    constructor
    · rintro ⟨v, hv, hall, hrun⟩
      refine ⟨⟨by simp [hv], hall⟩, ?_⟩
      simpa only [absorbStep, loadLane, hv, Option.getD_some] using hrun
    · rintro ⟨⟨h0, hall⟩, hrun⟩
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 h0
      refine ⟨v, hv, hall, ?_⟩
      simpa only [absorbStep, loadLane, hv, Option.getD_some] using hrun

/-- **The absorption rows.** If `rs2` reads `B`, a run of `absorbRows rs2 ++ rest` is a run of
`rest` from the absorbed register file, and it exists only when the 17 block lanes load. -/
theorem run_absorbRows_iff {rs2 : regidx} {B : BitVec 64} {s : SailJoltState}
    (hr : XReads s rs2 B) (rest : List Instr) (s' : SailJoltState) :
    (Program.seq (absorbRows rs2 ++ rest)).Run s s' ↔
      (∀ j < 17, (loadDword? s (B + BitVec.ofNat 64 (8 * j))).isSome) ∧
        (Program.seq rest).Run { s with vregs := absorbF s B s.vregs } s' := by
  rw [absorbRows, run_absorb_list _ (fun i hi => by simp only [List.mem_range] at hi; omega) hr]
  simp only [List.mem_range, absorbF]

/-- The block lanes XORed into lanes 0 to 16 of `S`; lanes 17 to 24 are kept.
Example: `(absorbLanes S w).a3 = S.a3 ^^^ .ofBitVec (w.getD 3 0)`. -/
def absorbLanes (S : State) (w : List (BitVec 64)) : State :=
  { S with
    a0 := S.a0 ^^^ .ofBitVec (w.getD 0 0), a1 := S.a1 ^^^ .ofBitVec (w.getD 1 0),
    a2 := S.a2 ^^^ .ofBitVec (w.getD 2 0), a3 := S.a3 ^^^ .ofBitVec (w.getD 3 0),
    a4 := S.a4 ^^^ .ofBitVec (w.getD 4 0), a5 := S.a5 ^^^ .ofBitVec (w.getD 5 0),
    a6 := S.a6 ^^^ .ofBitVec (w.getD 6 0), a7 := S.a7 ^^^ .ofBitVec (w.getD 7 0),
    a8 := S.a8 ^^^ .ofBitVec (w.getD 8 0), a9 := S.a9 ^^^ .ofBitVec (w.getD 9 0),
    a10 := S.a10 ^^^ .ofBitVec (w.getD 10 0), a11 := S.a11 ^^^ .ofBitVec (w.getD 11 0),
    a12 := S.a12 ^^^ .ofBitVec (w.getD 12 0), a13 := S.a13 ^^^ .ofBitVec (w.getD 13 0),
    a14 := S.a14 ^^^ .ofBitVec (w.getD 14 0), a15 := S.a15 ^^^ .ofBitVec (w.getD 15 0),
    a16 := S.a16 ^^^ .ofBitVec (w.getD 16 0) }

/-- **The absorption.** After the absorption rows, the lanes are the loaded lanes with the block
XORed in. -/
theorem stateOf_absorbF (s : SailJoltState) (B : BitVec 64) (f : VReg → BitVec 64) :
    stateOf (regsOf (absorbF s B f)) = absorbLanes (stateOf (regsOf f)) (blockAt s B) := rfl

private theorem foldl_absorbStep_out (s : SailJoltState) (B : BitVec 64) (is : List Nat)
    (his : ∀ i ∈ is, i < 25) (f : VReg → BitVec 64) (r : VReg) (hr : ¬ InPool r) :
    is.foldl (absorbStep s B) f r = f r := by
  induction is generalizing f with
  | nil => rfl
  | cons i is ih =>
    have hi : i < 25 := his i List.mem_cons_self
    rw [List.foldl_cons, ih (fun j hj => his j (List.mem_cons_of_mem _ hj))]
    have h1 := ne_of_pool hr (vr_pool (48 + i) (by omega) (by omega))
    have h2 := ne_of_pool hr (vr_pool scratch (by decide) (by decide))
    simp only [absorbStep, Op.eval, Op.dst, setV, h1, h2, ↓reduceIte]

/-- The absorption changes no register outside the pool. -/
theorem absorbF_out (s : SailJoltState) (B : BitVec 64) (f : VReg → BitVec 64) (r : VReg)
    (hr : ¬ InPool r) : absorbF s B f r = f r :=
  foldl_absorbStep_out s B _ (fun i hi => by simp only [List.mem_range] at hi; omega) f r hr

/-! ## Stores -/

/-- The stored registers are the words of the lanes. -/
theorem laneRegs_map (f : VReg → BitVec 64) : laneRegs.map f = wordsOf (stateOf (regsOf f)) :=
  rfl

/-- The stores write 25 registers, one per lane.
Example: the first is `vr48` (lane 0), the last `vr72` (lane 24). -/
theorem laneRegs_length : laneRegs.length = 25 := rfl

/-! ## Resets -/

/-- The register file `f` with the pool registers `vr48..84` reset to zero.
Example: `poolReset f vr60 = 0` and `poolReset f vr40 = f vr40`. -/
def poolReset (f : VReg → BitVec 64) : VReg → BitVec 64 :=
  fun r => if InPool r then 0 else f r

private theorem regRun_resets (ks : List Nat) (hks : ∀ k ∈ ks, 48 + k < 128)
    (G : VReg → BitVec 64) :
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

/-- The 37 reset rows evaluate to `poolReset`.
Example: afterwards `vr48 = 0` and `vr40` is unchanged. -/
theorem regRun_resetRows (G : VReg → BitVec 64) : regRun resetRows G = some (poolReset G) := by
  rw [resetRows, regRun_resets _ (fun k hk => by simp only [List.mem_range] at hk; omega)]
  congr 1
  funext r
  have := r.isLt
  simp only [poolReset, InPool, List.mem_range]
  congr 1
  apply propext
  omega

/-- Register files that agree outside the pool agree after `poolReset`.
Example: `poolReset (setV f vr50 7) = poolReset f`. -/
theorem poolReset_congr {f g : VReg → BitVec 64} (h : ∀ r, ¬ InPool r → f r = g r) :
    poolReset f = poolReset g := by
  funext r
  simp only [poolReset]
  split
  · rfl
  · exact h r ‹_›

/-! ## The block as bytes -/

/-- The bytes of the lanes, eight per lane, each lane least significant byte first, as EthLib
reads a block; 17 lanes give a 136-byte block.
Example: the first byte of `blockBytes [0x0102]` is `0x02`. -/
def blockBytes (w : List (BitVec 64)) : ByteArray :=
  ⟨(w.flatMap fun x => bytesOfLane (UInt64.ofBitVec x)).toArray⟩

/-- The 8 bytes of a lane, read back least significant first, give the lane. -/
theorem laneOfBytes (v : UInt64) :
    (v.toUInt8.toUInt64 ||| (v >>> 8).toUInt8.toUInt64 <<< 8 |||
      (v >>> 16).toUInt8.toUInt64 <<< 16 ||| (v >>> 24).toUInt8.toUInt64 <<< 24 |||
      (v >>> 32).toUInt8.toUInt64 <<< 32 ||| (v >>> 40).toUInt8.toUInt64 <<< 40 |||
      (v >>> 48).toUInt8.toUInt64 <<< 48 ||| (v >>> 56).toUInt8.toUInt64 <<< 56) = v := by
  apply UInt64.toBitVec_inj.1
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have e8 : ((8 : UInt64).toBitVec % 64).toNat = 8 := rfl
  have e16 : ((16 : UInt64).toBitVec % 64).toNat = 16 := rfl
  have e24 : ((24 : UInt64).toBitVec % 64).toNat = 24 := rfl
  have e32 : ((32 : UInt64).toBitVec % 64).toNat = 32 := rfl
  have e40 : ((40 : UInt64).toBitVec % 64).toNat = 40 := rfl
  have e48 : ((48 : UInt64).toBitVec % 64).toNat = 48 := rfl
  have e56 : ((56 : UInt64).toBitVec % 64).toNat = 56 := rfl
  simp only [UInt64.toBitVec_or, UInt64.toBitVec_shiftLeft, UInt64.toBitVec_shiftRight,
    UInt8.toBitVec_toUInt64, UInt64.toBitVec_toUInt8, BitVec.getLsbD_or,
    BitVec.shiftLeft_eq', BitVec.ushiftRight_eq', e8, e16, e24, e32, e40, e48, e56,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
  interval_cases i <;> simp

/-- Element `8i + k` of a list of 8-element lists, flattened, is element `k` of list `i`. -/
theorem getElem?_flatMap_eight {α β : Type} (l : List α) (f : α → List β)
    (hf : ∀ a, (f a).length = 8) (i k : Nat) (hk : k < 8) :
    (l.flatMap f)[8 * i + k]? = l[i]?.bind fun a => (f a)[k]? := by
  induction l generalizing i with
  | nil => simp
  | cons a l ih =>
    rw [List.flatMap_cons]
    cases i with
    | zero =>
      rw [List.getElem?_append_left (by rw [hf]; omega)]
      simp
    | succ i =>
      rw [List.getElem?_append_right (by rw [hf]; omega), hf,
        show 8 * (i + 1) + k - 8 = 8 * i + k by omega, ih]
      simp

/-- EthLib's `byteAt` of a byte list is its `j`-th element, or `0` past the end.
Example: `byteAt ⟨#[7, 8]⟩ 1 = 8` and `byteAt ⟨#[7, 8]⟩ 5 = 0`. -/
theorem byteAt_toArray (l : List UInt8) (j : Nat) : byteAt ⟨l.toArray⟩ j = l[j]?.getD 0 := by
  unfold byteAt
  split
  · rename_i h
    simp only [ByteArray.size, List.size_toArray] at h
    simp [List.getElem?_eq_getElem h]
    rfl
  · rename_i h
    simp only [ByteArray.size, List.size_toArray, not_lt] at h
    simp [List.getElem?_eq_none h]

/-- Lane `i` of the block bytes is block lane `i`. -/
theorem laneAt_blockBytes (w : List (BitVec 64)) (i : Nat) (hi : i < w.length) :
    laneAt (blockBytes w) (8 * i) = UInt64.ofBitVec w[i] := by
  have hb : ∀ k < 8, byteAt (blockBytes w) (8 * i + k) =
      ((bytesOfLane (UInt64.ofBitVec w[i]))[k]?).getD 0 := by
    intro k hk
    rw [blockBytes, byteAt_toArray, getElem?_flatMap_eight _ _ (fun _ => rfl) i k hk,
      List.getElem?_eq_getElem hi]
    rfl
  have h0 := hb 0 (by omega)
  rw [Nat.add_zero] at h0
  rw [laneAt, h0, hb 1 (by omega), hb 2 (by omega), hb 3 (by omega), hb 4 (by omega),
    hb 5 (by omega), hb 6 (by omega), hb 7 (by omega)]
  simp only [bytesOfLane, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
  exact laneOfBytes _

/-- **The block in bytes.** XORing the 136 bytes of 17 block lanes into `S`, as EthLib's
`absorbBlock` does, is `absorbLanes`. -/
theorem absorbBlock_blockBytes (S : State) (w : List (BitVec 64)) (hw : w.length = 17) :
    absorbBlock 136 S (blockBytes w) 0 = absorbLanes S w := by
  have h : ∀ j < 17, blockLane 136 (blockBytes w) 0 j = UInt64.ofBitVec (w.getD j 0) := by
    intro j hj
    have hj' : 8 * j < 136 := by omega
    simp only [blockLane, hj', ↓reduceIte, Nat.zero_add]
    rw [laneAt_blockBytes w j (by omega), List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by omega), Option.getD_some]
  simp only [absorbBlock, absorbLanes,
    h 0 (by omega), h 1 (by omega), h 2 (by omega), h 3 (by omega), h 4 (by omega),
    h 5 (by omega), h 6 (by omega), h 7 (by omega), h 8 (by omega), h 9 (by omega),
    h 10 (by omega), h 11 (by omega), h 12 (by omega), h 13 (by omega), h 14 (by omega),
    h 15 (by omega), h 16 (by omega)]

end JoltISA.Inlines.Keccak256
