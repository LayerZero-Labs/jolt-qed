import JoltBytecode.Inlines.Keccak256.Rows
import JoltBytecode.Inlines.Keccak256.Spec
import JoltBytecode.Inlines.Blake2b.Compress

/-!
# The rounds of the Keccak rows compute Keccak-f[1600]

The 24 rounds of `KECCAK256` and `KECCAK256_ABSORB_PERMUTE` are the same 3,000 register rows
(`Keccak256.roundsRows`). This module proves that they compute EthLib's `keccakF` on the 25
lanes in `vr48..72`.

* `run_ops_append`: a run of the rows of a list of `Op` followed by `rest` is a run of `rest`
  from the register file that `Op.eval` computes. It covers `ANDN`, `VirtualROTRI` and
  `VirtualXORROTL1`, which the generic `regRun` does not.
* `Regs`: the 37 pool registers as a record, so that one block of a round checks against the
  specification by `rfl` (`theta_ops`, `rhoPi_ops`, `chi_ops`). Checked as one piece, a whole
  round takes 12 seconds; the three blocks take 4.2, 0.9 and 2.5 seconds.
* `stateOf_roundsOps`: the 24 rounds compute `keccakF`.
* `foldl_eval_out`: the rounds change no register outside the pool `vr48..84`.
-/

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail LeanRV64D
  LeanRV64D.Functions

set_option autoImplicit false

noncomputable section

namespace JoltISA.Inlines.Keccak256

open JoltSpec.Keccak

/-! ## The values of the rows -/

/-- The rotation mask factors as `2^(64-k) * (2^k - 1)`. -/
theorem rotlMask_eq (k : Nat) (h : k < 64) : rotlMask k = 2 ^ (64 - k) * (2 ^ k - 1) := by
  unfold rotlMask
  rw [Nat.mul_sub, Nat.mul_one, ← Nat.pow_add, Nat.sub_add_cancel h.le]

/-- The mask for a left rotation by `k` has `64 - k` trailing zeros, the right rotation.
Example: `ctz (rotlMask 1) = 63`. -/
theorem ctz_rotlMask (k : Nat) (h0 : 0 < k) (h : k < 64) : ctz (rotlMask k) = 64 - k := by
  have hm : 0 < 2 ^ k - 1 := by
    have : 2 ≤ 2 ^ k := le_trans (show (2 : Nat) ≤ 2 ^ 1 by norm_num) (Nat.pow_le_pow_right (by omega) h0)
    omega
  rw [rotlMask_eq k h, ctz_mul_pow2 _ hm, ctz_of_odd (pow2_sub_one_odd h0)]
  rfl

/-- EthLib's `rotl` by `0 < k < 64`, as bit vectors. -/
theorem toBitVec_rotl (x : BitVec 64) (k : Nat) (h0 : 0 < k) (h : k < 64) :
    (JoltSpec.Keccak.rotl (UInt64.ofBitVec x) (UInt64.ofNat k)).toBitVec =
      x <<< k ||| x >>> (64 - k) := by
  simp only [JoltSpec.Keccak.rotl, UInt64.toBitVec_or, UInt64.toBitVec_shiftLeft,
    UInt64.toBitVec_shiftRight, UInt64.toBitVec_sub, UInt64.toBitVec_ofNat]
  have hk : (UInt64.ofNat k).toBitVec.toNat = k := by
    show (BitVec.ofNat 64 k).toNat = k
    rw [BitVec.toNat_ofNat]; omega
  have h64 : (64 : BitVec 64).toNat = 64 := rfl
  have h1 : ((UInt64.ofNat k).toBitVec % 64).toNat = k := by
    rw [BitVec.toNat_umod, hk, h64]; omega
  have h2 : ((64#64 - (UInt64.ofNat k).toBitVec) % 64).toNat = 64 - k := by
    rw [BitVec.toNat_umod, BitVec.toNat_sub, hk, BitVec.toNat_ofNat, h64]; omega
  rw [BitVec.shiftLeft_eq', BitVec.ushiftRight_eq', h1, h2]

/-- `VirtualROTRI` with `rotlMask k` is EthLib's `rotl` by `k`.
Example: with `k = 1` it rotates `0x8000000000000000` to `1`. -/
theorem rotri_rotlMask (x : BitVec 64) (k : Nat) (h0 : 0 < k) (h : k < 64) :
    jolt_virtual_rotri_value x (rotlMask k) =
      (JoltSpec.Keccak.rotl (UInt64.ofBitVec x) (UInt64.ofNat k)).toBitVec := by
  rw [toBitVec_rotl x k h0 h, jolt_virtual_rotri_value, ctz_rotlMask k h0 h,
    rotater_eq_rotateRight _ _ (by omega), BitVec.rotateRight_def, Nat.mod_eq_of_lt (by omega),
    show 64 - (64 - k) = k by omega, BitVec.or_comm]

/-- `VirtualXORROTL1` is `x ^ rotl y 1` with EthLib's `rotl`. -/
theorem xorrotl1_eq (x y : BitVec 64) :
    jolt_virtual_xorrotl1_value x y = x ^^^ (JoltSpec.Keccak.rotl (UInt64.ofBitVec y) 1).toBitVec := by
  rw [show (1 : UInt64) = UInt64.ofNat 1 from rfl, toBitVec_rotl y 1 (by omega) (by omega),
    jolt_virtual_xorrotl1_value]
  congr 1

/-! ## Ops on register files -/

/-- The destination of an op.
Example: `(Op.xor 73 48 53).dst = 73`. -/
def Op.dst : Op → Nat
  | .xor d _ _ | .xorRotl1 d _ _ | .rotl d _ _ | .andn d _ _ | .xori d _ _ => d

/-- The value an op writes, given register number `n` reads `r n`. Rotations use EthLib's
`rotl`, and `andn` is written `~b & a`, the operand order of EthLib's `chi`.
Example: `(Op.xor 73 48 53).val r = r 48 ^^^ r 53`. -/
def Op.val : Op → (Nat → BitVec 64) → BitVec 64
  | .xor _ a b, r => r a ^^^ r b
  | .xorRotl1 _ a b, r => r a ^^^ (JoltSpec.Keccak.rotl (UInt64.ofBitVec (r b)) 1).toBitVec
  | .rotl _ a k, r => (JoltSpec.Keccak.rotl (UInt64.ofBitVec (r a)) (UInt64.ofNat k)).toBitVec
  | .andn _ a b, r => ~~~(r b) &&& r a
  | .xori _ a imm, r => r a ^^^ imm

/-- The register file after an op.
Example: `Op.eval f (Op.xor 73 48 53) vr73 = f vr48 ^^^ f vr53`. -/
def Op.eval (f : VReg → BitVec 64) (o : Op) : VReg → BitVec 64 :=
  setV f (vr o.dst) (o.val fun n => f (vr n))

/-- A register number in the pool `vr48..84`. -/
abbrev poolNum (n : Nat) : Bool := decide (48 ≤ n ∧ n < 85)

/-- An op that the proofs cover: its registers lie in the pool and a rotation is by `0 < k < 64`.
Every op of a round passes (`roundsOps_ok`).
Example: `(Op.rotl 81 49 1).ok = true`, and `(Op.rotl 81 49 0).ok = false`. -/
def Op.ok : Op → Bool
  | .xor d a b | .xorRotl1 d a b | .andn d a b => poolNum d && poolNum a && poolNum b
  | .rotl d a k => poolNum d && poolNum a && decide (0 < k ∧ k < 64)
  | .xori d a _ => poolNum d && poolNum a

theorem Op.dst_pool (o : Op) (ho : o.ok = true) : 48 ≤ o.dst ∧ o.dst < 85 := by
  cases o <;> simp_all [Op.ok, Op.dst]

/-- The row of an op retires and sets its destination to `Op.val`. -/
theorem execInstr_toInstr (o : Op) (ho : o.ok = true) (s : SailJoltState) :
    (execInstr o.toInstr).run s = .ok RETIRE_SUCCESS { s with vregs := o.eval s.vregs } := by
  have hd := o.dst_pool ho
  have hd' : (vr o.dst).toNat = o.dst := by
    rw [BitVec.toNat_ofNat]; omega
  have hw : WritableVReg (vr o.dst) := by
    unfold WritableVReg; omega
  cases o with
  | xor d a b =>
    exact execInstr_of_regRow (i := (Op.xor d a b).toInstr) (d := vr d)
      (g := fun f => jolt_xor_value (f (vr a)) (f (vr b))) rfl (Nat.le_of_not_lt hw) s
  | xori d a imm =>
    exact execInstr_of_regRow (i := (Op.xori d a imm).toInstr) (d := vr d)
      (g := fun f => jolt_xor_value (f (vr a)) imm) rfl (Nat.le_of_not_lt hw) s
  | xorRotl1 d a b =>
    have hv : (Op.xorRotl1 d a b).eval s.vregs =
        setV s.vregs (vr d) (jolt_virtual_xorrotl1_value (s.vregs (vr a)) (s.vregs (vr b))) := by
      rw [xorrotl1_eq]; rfl
    rw [hv]
    simp only [Op.toInstr, execInstr, EStateM.run, readSrc_vreg, readVReg_run, writeDst_vreg,
      bind, EStateM.bind]
    exact writeVReg_retire_run_of_writable _ _ s hw
  | andn d a b =>
    have hv : (Op.andn d a b).eval s.vregs =
        setV s.vregs (vr d) (jolt_andn_value (s.vregs (vr a)) (s.vregs (vr b))) := by
      simp only [Op.eval, Op.val, Op.dst, jolt_andn_value]
      rw [BitVec.and_comm]
    rw [hv]
    simp only [Op.toInstr, execInstr, EStateM.run, readSrc_vreg, readVReg_run, writeDst_vreg,
      bind, EStateM.bind]
    exact writeVReg_retire_run_of_writable _ _ s hw
  | rotl d a k =>
    have hk : 0 < k ∧ k < 64 := by simp_all [Op.ok]
    have hv : (Op.rotl d a k).eval s.vregs =
        setV s.vregs (vr d) (jolt_virtual_rotri_value (s.vregs (vr a)) (rotlMask k)) := by
      rw [rotri_rotlMask _ _ hk.1 hk.2]; rfl
    rw [hv]
    simp only [Op.toInstr, execInstr, EStateM.run, readSrc_vreg, readVReg_run, writeDst_vreg,
      bind, EStateM.bind]
    exact writeVReg_retire_run_of_writable _ _ s hw

/-- **Op rows run as evaluated.** A run of the rows of `ops` followed by `rest` is a run of
`rest` from the register file after `ops`. Nothing else in the state changes.
Example: a run of `[XOR vr73, vr48, vr53] ++ rest` is a run of `rest` with
`vr73 = vr48 ^ vr53`. -/
theorem run_ops_append (ops : List Op) (h : ops.all Op.ok = true) (rest : List Instr)
    (s s' : SailJoltState) :
    (Program.seq (ops.map Op.toInstr ++ rest)).Run s s' ↔
      (Program.seq rest).Run { s with vregs := ops.foldl Op.eval s.vregs } s' := by
  induction ops generalizing s with
  | nil => rfl
  | cons o ops ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    rw [List.map_cons, List.cons_append, seq_cons, run_instr_iff (execInstr_toInstr o h.1 s),
      ih h.2]
    rfl

/-- The pool `vr48..84` of the Keccak rows.
Example: `InPool vr84` holds and `InPool vr85` does not. -/
def InPool (r : VReg) : Prop := 48 ≤ r.toNat ∧ r.toNat < 85

instance (r : VReg) : Decidable (InPool r) := inferInstanceAs (Decidable (_ ∧ _))

/-- Ops change no register outside the pool. -/
theorem foldl_eval_out (ops : List Op) (h : ops.all Op.ok = true) (f : VReg → BitVec 64)
    (r : VReg) (hr : ¬ InPool r) : ops.foldl Op.eval f r = f r := by
  induction ops generalizing f with
  | nil => rfl
  | cons o ops ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    rw [List.foldl_cons, ih h.2]
    have hd := o.dst_pool h.1
    have hne : r ≠ vr o.dst := by
      intro he
      apply hr
      rw [he, InPool, BitVec.toNat_ofNat]
      omega
    simp only [Op.eval, setV, hne, ↓reduceIte]

/-! ## The pool as a record -/

/-- The 37 pool registers: lanes `a0..a24` (`vr48..72`), `C` (`vr73..77`), `D[0..2]`
(`vr78..80`), the rho-pi temporary, the two chi temporaries and the scratch register. -/
structure Regs where
  (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 c0 c1 c2 c3 c4 d0 d1 d2 pt t3 t4 sc : BitVec 64)

/-- Register number `n` of the record; `0` outside `48..84`. -/
def Regs.get (R : Regs) : Nat → BitVec 64
  | 48 => R.a0
  | 49 => R.a1
  | 50 => R.a2
  | 51 => R.a3
  | 52 => R.a4
  | 53 => R.a5
  | 54 => R.a6
  | 55 => R.a7
  | 56 => R.a8
  | 57 => R.a9
  | 58 => R.a10
  | 59 => R.a11
  | 60 => R.a12
  | 61 => R.a13
  | 62 => R.a14
  | 63 => R.a15
  | 64 => R.a16
  | 65 => R.a17
  | 66 => R.a18
  | 67 => R.a19
  | 68 => R.a20
  | 69 => R.a21
  | 70 => R.a22
  | 71 => R.a23
  | 72 => R.a24
  | 73 => R.c0
  | 74 => R.c1
  | 75 => R.c2
  | 76 => R.c3
  | 77 => R.c4
  | 78 => R.d0
  | 79 => R.d1
  | 80 => R.d2
  | 81 => R.pt
  | 82 => R.t3
  | 83 => R.t4
  | 84 => R.sc
  | _ => 0

/-- The record with register number `n` set to `v`. -/
def Regs.set (R : Regs) (n : Nat) (v : BitVec 64) : Regs :=
  match n with
  | 48 => { R with a0 := v }
  | 49 => { R with a1 := v }
  | 50 => { R with a2 := v }
  | 51 => { R with a3 := v }
  | 52 => { R with a4 := v }
  | 53 => { R with a5 := v }
  | 54 => { R with a6 := v }
  | 55 => { R with a7 := v }
  | 56 => { R with a8 := v }
  | 57 => { R with a9 := v }
  | 58 => { R with a10 := v }
  | 59 => { R with a11 := v }
  | 60 => { R with a12 := v }
  | 61 => { R with a13 := v }
  | 62 => { R with a14 := v }
  | 63 => { R with a15 := v }
  | 64 => { R with a16 := v }
  | 65 => { R with a17 := v }
  | 66 => { R with a18 := v }
  | 67 => { R with a19 := v }
  | 68 => { R with a20 := v }
  | 69 => { R with a21 := v }
  | 70 => { R with a22 := v }
  | 71 => { R with a23 := v }
  | 72 => { R with a24 := v }
  | 73 => { R with c0 := v }
  | 74 => { R with c1 := v }
  | 75 => { R with c2 := v }
  | 76 => { R with c3 := v }
  | 77 => { R with c4 := v }
  | 78 => { R with d0 := v }
  | 79 => { R with d1 := v }
  | 80 => { R with d2 := v }
  | 81 => { R with pt := v }
  | 82 => { R with t3 := v }
  | 83 => { R with t4 := v }
  | 84 => { R with sc := v }
  | _ => R

/-- The pool registers of a register file. -/
def regsOf (f : VReg → BitVec 64) : Regs :=
  ⟨f (vr 48), f (vr 49), f (vr 50), f (vr 51), f (vr 52), f (vr 53), f (vr 54), f (vr 55), f (vr 56), f (vr 57), f (vr 58), f (vr 59), f (vr 60), f (vr 61), f (vr 62), f (vr 63), f (vr 64), f (vr 65), f (vr 66), f (vr 67), f (vr 68), f (vr 69), f (vr 70), f (vr 71), f (vr 72), f (vr 73), f (vr 74), f (vr 75), f (vr 76), f (vr 77), f (vr 78), f (vr 79), f (vr 80), f (vr 81), f (vr 82), f (vr 83), f (vr 84)⟩

/-- The 25 lanes of the record as an EthLib state. -/
def stateOf (R : Regs) : State :=
  ⟨.ofBitVec R.a0, .ofBitVec R.a1, .ofBitVec R.a2, .ofBitVec R.a3, .ofBitVec R.a4, .ofBitVec R.a5, .ofBitVec R.a6, .ofBitVec R.a7, .ofBitVec R.a8, .ofBitVec R.a9, .ofBitVec R.a10, .ofBitVec R.a11, .ofBitVec R.a12, .ofBitVec R.a13, .ofBitVec R.a14, .ofBitVec R.a15, .ofBitVec R.a16, .ofBitVec R.a17, .ofBitVec R.a18, .ofBitVec R.a19, .ofBitVec R.a20, .ofBitVec R.a21, .ofBitVec R.a22, .ofBitVec R.a23, .ofBitVec R.a24⟩

/-- An op on the record. -/
def Op.evalR (R : Regs) (o : Op) : Regs := R.set o.dst (o.val R.get)

theorem get_regsOf (f : VReg → BitVec 64) (n : Nat) (h1 : 48 ≤ n) (h2 : n < 85) :
    (regsOf f).get n = f (vr n) := by
  interval_cases n <;> rfl

theorem regsOf_setV (f : VReg → BitVec 64) (d : Nat) (v : BitVec 64) (h1 : 48 ≤ d)
    (h2 : d < 85) : regsOf (setV f (vr d) v) = (regsOf f).set d v := by
  interval_cases d <;> rfl

theorem Op.val_congr (o : Op) (ho : o.ok = true) (r r' : Nat → BitVec 64)
    (h : ∀ n, 48 ≤ n → n < 85 → r n = r' n) : o.val r = o.val r' := by
  cases o with
  | xor d a b | xorRotl1 d a b | andn d a b =>
    simp only [Op.ok, poolNum, Bool.and_eq_true, decide_eq_true_eq] at ho
    simp only [Op.val]
    rw [h a (by omega) (by omega), h b (by omega) (by omega)]
  | rotl d a k | xori d a k =>
    simp only [Op.ok, poolNum, Bool.and_eq_true, decide_eq_true_eq] at ho
    simp only [Op.val]
    rw [h a (by omega) (by omega)]

theorem regsOf_eval (o : Op) (ho : o.ok = true) (f : VReg → BitVec 64) :
    regsOf (Op.eval f o) = Op.evalR (regsOf f) o := by
  have hd := o.dst_pool ho
  rw [Op.eval, Op.evalR, regsOf_setV _ _ _ hd.1 hd.2]
  congr 1
  exact Op.val_congr o ho _ _ fun n h1 h2 => (get_regsOf f n h1 h2).symm

/-- On the pool, evaluating ops on a register file is evaluating them on the record. -/
theorem regsOf_foldl (ops : List Op) (h : ops.all Op.ok = true) (f : VReg → BitVec 64) :
    regsOf (ops.foldl Op.eval f) = ops.foldl Op.evalR (regsOf f) := by
  induction ops generalizing f with
  | nil => rfl
  | cons o ops ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    rw [List.foldl_cons, List.foldl_cons, ih h.2, regsOf_eval o h.1]

/-! ## One round -/

private theorem rotl_zero (v : UInt64) : JoltSpec.Keccak.rotl v 0 = v := by
  apply UInt64.toBitVec_inj.1
  simp [JoltSpec.Keccak.rotl]

/-- EthLib's `rho` rotates lane 0 by zero, which the rows skip. -/
private theorem rho_a0 (B : State) :
    JoltSpec.Keccak.rho B = { JoltSpec.Keccak.rho B with a0 := B.a0 } := by
  unfold JoltSpec.Keccak.rho
  rw [rotl_zero]

/-- The state between rho-pi and chi: lane `(0, 2)` is in the rho-pi temporary `vr81`. -/
def piState (R : Regs) : State := { stateOf R with a10 := .ofBitVec R.pt }

/-- The 50 theta rows compute `theta`. -/
theorem theta_ops (R : Regs) : stateOf (thetaOps.foldl Op.evalR R) = theta (stateOf R) := by
  cases R
  rfl

/-- The 24 rho-pi rows compute `pi ∘ rho`, with lane `(0, 2)` in `vr81`. -/
theorem rhoPi_ops (R : Regs) :
    piState (rhoPiOps.foldl Op.evalR R) = pi (JoltSpec.Keccak.rho (stateOf R)) := by
  rw [rho_a0]
  cases R
  rfl

/-- The 50 chi rows compute `chi`. -/
theorem chi_ops (R : Regs) : stateOf (chiOps.foldl Op.evalR R) = chi (piState R) := by
  cases R
  rfl

/-- The iota row computes `iota`. -/
theorem iota_op (ir : Fin ROUNDS) (R : Regs) :
    stateOf (Op.evalR R (Op.xori (lane 0 0) (lane 0 0) (RC[ir]).toBitVec)) = iota ir (stateOf R) := by
  cases R
  rfl

/-- **One round.** The 125 rows of round `ir` compute EthLib's `round ir`. -/
theorem stateOf_roundOps (ir : Fin ROUNDS) (R : Regs) :
    stateOf ((roundOps (RC[ir]).toBitVec).foldl Op.evalR R) = round ir (stateOf R) := by
  rw [roundOps, bodyOps, List.foldl_append, List.foldl_append, List.foldl_append, List.foldl_cons,
    List.foldl_nil, iota_op, chi_ops, rhoPi_ops, theta_ops]
  rfl

/-! ## The 24 rounds -/

/-- The builder's round constants are EthLib's `RC`. -/
theorem roundOpsAt_eq (i : Nat) (h : i < ROUNDS) :
    roundOpsAt i = roundOps (RC[(⟨i, h⟩ : Fin ROUNDS)]).toBitVec := by
  have h' : i < 24 := h
  simp only [roundOpsAt, h', ↓reduceIte]
  congr 1
  interval_cases i <;> rfl

/-- The ops of the 24 rounds.
Example: `roundsOps.length = 3000`. -/
def roundsOps : List Op := (List.range 24).flatMap roundOpsAt

/-- The rows of the 24 rounds are the rows of `roundsOps`. -/
theorem roundsRows_eq : roundsRows = roundsOps.map Op.toInstr := by
  rw [roundsRows, roundsOps, List.map_flatMap]
  rfl

private theorem bodyOps_ok : bodyOps.all Op.ok = true := by decide

/-- Every op of the rounds passes `Op.ok`. -/
theorem roundsOps_ok : roundsOps.all Op.ok = true := by
  rw [roundsOps, List.all_flatMap, List.all_eq_true]
  intro i _
  rw [roundOpsAt]
  split
  · rw [roundOps, List.all_append, bodyOps_ok]
    rfl
  · rfl

private theorem stateOf_rangeOps (n i : Nat) (hn : i + n = 24) (R : Regs) :
    stateOf (((List.range' i n).flatMap roundOpsAt).foldl Op.evalR R) =
      keccakF.roundsFrom i (stateOf R) := by
  induction n generalizing i R with
  | zero =>
    have hi : ¬ i < ROUNDS := by show ¬ i < 24; omega
    conv_rhs => rw [keccakF.roundsFrom]
    simp only [hi, ↓reduceDIte]
    rfl
  | succ n ih =>
    have hi : i < ROUNDS := by show i < 24; omega
    conv_rhs => rw [keccakF.roundsFrom]
    simp only [hi, ↓reduceDIte]
    rw [List.range'_succ, List.flatMap_cons, List.foldl_append, ih (i + 1) (by omega),
      roundOpsAt_eq i hi, stateOf_roundOps]

/-- **The 24 rounds compute Keccak-f[1600].** -/
theorem stateOf_roundsOps (R : Regs) :
    stateOf (roundsOps.foldl Op.evalR R) = keccakF (stateOf R) := by
  rw [roundsOps, List.range_eq_range', stateOf_rangeOps 24 0 rfl]
  rfl

/-- **The rounds on a register file.** The lanes after the rounds are `keccakF` of the lanes
before. -/
theorem stateOf_rounds (f : VReg → BitVec 64) :
    stateOf (regsOf (roundsOps.foldl Op.eval f)) = keccakF (stateOf (regsOf f)) := by
  rw [regsOf_foldl _ roundsOps_ok, stateOf_roundsOps]

end JoltISA.Inlines.Keccak256
