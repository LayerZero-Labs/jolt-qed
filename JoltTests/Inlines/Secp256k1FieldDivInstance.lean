import JoltBytecode.Inlines.Secp256k1.FieldDiv
import JoltTests.Inlines.Secp256k1FieldMulInstance

/-!
# secp256k1 `DIV`: known-answer instances, and the case where the result overwrites the dividend

Section 5.4 of `docs/inline-precompiles.md` asks for each `rows_sound` theorem to be applied to a
concrete input. This module reuses the machine state of `Secp256k1FieldMulInstance`: the
dividend `a` at `0x8001_0000` (through `x10`), the divisor `b` at `0x8001_0020` (through
`x11`), and the output buffer at `0x8002_0000` (through `x12`).

* `secp256k1Divq_kat`, `secp256k1Divr_kat`: with `a = 1` and `b = 2`, Jolt's advice is
  `c = (q + 1) / 2` and `w = 1`; the rows run with it, the run meets `FieldDivSpec` (through the
  inline's `rows_sound` theorem), and the output buffer then holds `(q + 1) / 2`.

The second part is requirement R3 of the design document. Before Jolt commit `db9679295` the
`DIV` rows stored each limb of the result `c` right after taking it as advice, before the checks
reload the dividend from `rs1`. When `rs3 = rs1`, the reloads read `c` back.

* `oldDivRows` transcribes those earlier rows.
* `oldDivq_accepts_wrong_result`: with `rs1 = rs3 = x10`, `a = 1`, `b = 1` and the advice
  `c = 2`, `w = 0`, the earlier rows run to the end and leave `2` at `x10`, although
  `1 / 1 = 1`.
* `secp256k1Divq_rejects_wrong_result`: from the same state, no run of the current rows, for
  any advice, leaves `2` at `x10`.

This module is a test: nothing in the headline import closure imports it.
-/

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail LeanRV64D
  LeanRV64D.Functions JoltISA JoltISA.Inlines JoltISA.Inlines.Secp256k1
  JoltISA.Inlines.Generated JoltTests.Secp256k1FieldMulInstance

set_option autoImplicit false

noncomputable section

namespace JoltTests.Secp256k1FieldDivInstance

/-! ## Jolt's advice for `1 / 2` -/

/-- The only solution of `c·2 = w·q + 1` with `c < q` is `w = 1`, `c = (q + 1) / 2`.
Example: for `q = 7`, `c = 4` and `w = 1`, since `4·2 = 7 + 1`. -/
theorem half_unique {q c w : Nat} (h : c * 2 = w * q + 1) (hc : c < q) :
    w = 1 ∧ c = (q + 1) / 2 := by
  have hw : w < 2 := by
    by_contra hw
    have : 2 * q ≤ w * q := Nat.mul_le_mul_right q (by omega)
    omega
  interval_cases w <;> omega

/-- The limbs of `1`: the dividend of both instances, and both operands of the `rs3 = rs1`
example below.
Example: `divA = #v[1, 0, 0, 0]`. -/
def divA : Limbs := natToLimbs 1

/-- The divisor of both instances, `2`.
Example: `divB = #v[2, 0, 0, 0]`. -/
def divB : Limbs := natToLimbs 2

/-- The value of `divA` is `1`.
Example: `limbsToNat #v[1, 0, 0, 0] = 1`. -/
theorem limbsToNat_divA : limbsToNat divA = 1 := by
  rw [divA, limbsToNat_natToLimbs]

/-- The value of `divB` is `2`.
Example: `limbsToNat #v[2, 0, 0, 0] = 2`. -/
theorem limbsToNat_divB : limbsToNat divB = 2 := by
  rw [divB, limbsToNat_natToLimbs]

/-- For an odd modulus `q`, Jolt's division advice for `1 / 2` is `c = (q + 1) / 2`, `w = 1`.
Example: for `q = p`, `c = (p + 1) / 2`, whose low limb is `0xffffffff7ffffe18`. -/
theorem divisionAdvice_half {q : Nat} (hq1 : 1 < q) (hq : q ≤ 2 ^ 256)
    (hcop : Nat.Coprime 2 q) :
    mulqDivisionAdvice q divA divB = some (natToLimbs ((q + 1) / 2), natToLimbs 1) := by
  obtain ⟨c, w, hcw, rel, hc⟩ := mulqDivisionAdvice_spec hq1 hq (a := divA) (b := divB)
    (by rw [limbsToNat_divA]; exact hq1) (by rw [limbsToNat_divB]; exact hcop)
  rw [limbsToNat_divA, limbsToNat_divB] at rel
  obtain ⟨hw, hc2⟩ := half_unique rel hc
  have ec : c = natToLimbs ((q + 1) / 2) := limbs_eq_of_limbsToNat_eq (by
    rw [hc2, limbsToNat_natToLimbs, Nat.mod_eq_of_lt (by omega)])
  have ew : w = natToLimbs 1 := limbs_eq_of_limbsToNat_eq (by
    rw [hw, limbsToNat_natToLimbs])
  rw [hcw, ec, ew]

/-- A run from the instance state that meets the specification and leaves a canonical result
stores `(q + 1) / 2`, the only canonical quotient of `1` by `2`.
Example: for `DIVQ`, the buffer at `0x8002_0000` holds `(p + 1) / 2`. -/
theorem div_kat_result {q : Nat} {s' : SailJoltState}
    (spec : FieldDivSpec q (regidx.Regidx 10) (regidx.Regidx 11) (regidx.Regidx 12)
      (katState divA divB) s')
    (can : FieldMulCanonical q (regidx.Regidx 12) (katState divA divB) s') (i : Nat)
    (hi : i < 4) :
    loadDword? s' (katOut + BitVec.ofNat 64 (8 * i)) =
      (natToLimbs ((q + 1) / 2)).toList[i]? := by
  obtain ⟨a', b', w, c, ha', hb', ⟨rel, -, hc256⟩, -, hload⟩ := spec
  obtain ⟨c', hc', hload'⟩ := can
  rw [kat_x10, kat_limbs_a] at ha'
  rw [kat_x11, kat_limbs_b] at hb'
  cases Option.some.inj ha'
  cases Option.some.inj hb'
  have ec : c = c' := Vector.ext fun j hj => by
    have e := (hload j hj).symm.trans (hload' j hj)
    simpa [Vector.getElem?_toList, hj] using e
  subst ec
  rw [limbsToNat_divA, limbsToNat_divB] at rel
  obtain ⟨-, hc2⟩ := half_unique rel hc'
  have e : c = natToLimbs ((q + 1) / 2) := limbs_eq_of_limbsToNat_eq (by
    rw [limbsToNat_natToLimbs, ← hc2, Nat.mod_eq_of_lt hc256])
  rw [← e, ← hload i hi, kat_out]

/-! ## The two instances -/

/-- Jolt's advice for `DIVQ` with `a = 1`, `b = 2`: `c = (p + 1) / 2` and `w = 1`, interleaved.
Example: the first advice word is `0xffffffff7ffffe18`, the second `1`. -/
theorem divq_advice :
    joltAdvice .divq divA divB =
      some (divisionWords (natToLimbs ((p + 1) / 2)) (natToLimbs 1)) := by
  show (fun cw => divisionWords cw.1 cw.2) <$> mulqDivisionAdvice p divA divB = _
  rw [divisionAdvice_half (by decide) (by decide) (by decide)]
  rfl

/-- Jolt's advice for `DIVR` with `a = 1`, `b = 2`: `c = (n + 1) / 2` and `w = 1`, interleaved.
Example: the first advice word is `0xdfe92f46681b20a1`, the second `1`. -/
theorem divr_advice :
    joltAdvice .divr divA divB =
      some (divisionWords (natToLimbs ((n + 1) / 2)) (natToLimbs 1)) := by
  show (fun cw => divisionWords cw.1 cw.2) <$> mulqDivisionAdvice n divA divB = _
  rw [divisionAdvice_half (by decide) (by decide) (by decide)]
  rfl

/-- **The `DIVQ` instance.** From the instance state with `a = 1` and `b = 2`, the
`SECP256K1_DIVQ` rows (with `rs1 = x10`, `rs2 = x11`, `rs3 = x12`) run with Jolt's advice
`c = (p + 1) / 2`, `w = 1`; by `secp256k1Divq_rows_sound` the run meets `FieldDivSpec`; and the
output buffer then holds `(p + 1) / 2`.
Example: the doubleword at `0x8002_0000` ends as `0xffffffff7ffffe18`. -/
theorem secp256k1Divq_kat :
    joltAdvice .divq divA divB =
      some (divisionWords (natToLimbs ((p + 1) / 2)) (natToLimbs 1)) ∧
    ∃ s', (secp256k1DivqRowsAuto (regidx.Regidx 10) (regidx.Regidx 11) (regidx.Regidx 12)
        (fun i => (divisionWords (natToLimbs ((p + 1) / 2)) (natToLimbs 1)).getD i 0)).Run
        (katState divA divB) s' ∧
      FieldDivSpec p (regidx.Regidx 10) (regidx.Regidx 11) (regidx.Regidx 12)
        (katState divA divB) s' ∧
      ∀ i, i < 4 → loadDword? s' (katOut + BitVec.ofNat 64 (8 * i)) =
        (natToLimbs ((p + 1) / 2)).toList[i]? := by
  obtain ⟨ws, hws, s', run, -, can⟩ := secp256k1Divq_rows_jolt_advice_complete
    (kat_pre .div divA divB) (by rw [kat_x10]; exact kat_limbs_a _ _)
    (by rw [kat_x11]; exact kat_limbs_b _ _) (by rw [limbsToNat_divA]; decide)
    (by rw [limbsToNat_divB]; decide)
  rw [divq_advice] at hws
  cases Option.some.inj hws
  have spec := secp256k1Divq_rows_sound (kat_pre .div divA divB).toFieldMulBuffer run
  exact ⟨divq_advice, s', run, spec, div_kat_result spec can⟩

/-- **The `DIVR` instance.** As `secp256k1Divq_kat`, modulo `n`: the output buffer holds
`(n + 1) / 2`.
Example: the doubleword at `0x8002_0000` ends as `0xdfe92f46681b20a1`. -/
theorem secp256k1Divr_kat :
    joltAdvice .divr divA divB =
      some (divisionWords (natToLimbs ((n + 1) / 2)) (natToLimbs 1)) ∧
    ∃ s', (secp256k1DivrRowsAuto (regidx.Regidx 10) (regidx.Regidx 11) (regidx.Regidx 12)
        (fun i => (divisionWords (natToLimbs ((n + 1) / 2)) (natToLimbs 1)).getD i 0)).Run
        (katState divA divB) s' ∧
      FieldDivSpec n (regidx.Regidx 10) (regidx.Regidx 11) (regidx.Regidx 12)
        (katState divA divB) s' ∧
      ∀ i, i < 4 → loadDword? s' (katOut + BitVec.ofNat 64 (8 * i)) =
        (natToLimbs ((n + 1) / 2)).toList[i]? := by
  obtain ⟨ws, hws, s', run, -, can⟩ := secp256k1Divr_rows_jolt_advice_complete
    (kat_pre .div divA divB) (by rw [kat_x10]; exact kat_limbs_a _ _)
    (by rw [kat_x11]; exact kat_limbs_b _ _) (by rw [limbsToNat_divA]; decide)
    (by rw [limbsToNat_divB]; decide)
  rw [divr_advice] at hws
  cases Option.some.inj hws
  have spec := secp256k1Divr_rows_sound (kat_pre .div divA divB).toFieldMulBuffer run
  exact ⟨divr_advice, s', run, spec, div_kat_result spec can⟩

/-! ## The rows before Jolt commit `db9679295` -/

/-- One round of the earlier `DIV` prologue: load divisor limb `i`, take result limb `i` as
advice and store it at once, then take quotient limb `i` as advice.
Example: round 1 for `DIVQ` with `rs2 = x11`, `rs3 = x10` is `LD vr53, 8(x11);
VirtualAdvice vr49; SD vr49, 8(x10); VirtualAdvice vr57`. -/
def oldRound (L : MulRegs) (rs2 rs3 : regidx) (advice : Nat → BitVec 64) (i : Nat) :
    List Instr :=
  [ldRow (L.b i) rs2 (8 * i), .VirtualAdvice (.vreg (L.a i)) (advice (2 * i)) 0,
    sdRow rs3 (L.a i) (8 * i), .VirtualAdvice (.vreg (L.w i)) (advice (2 * i + 1)) 0]

/-- The `DIV` rows as Jolt emitted them before commit `db9679295`: the four prologue rounds of
`oldRound`, the constant rows, the checks, and the resets, with no stores after the checks.
`MulqBuilder::inline_sequence` at `db9679295^` (`jolt-inlines/secp256k1/src/sequence_builder.rs`)
emits these rows; the commit moved the four stores after the checks, which gives `mulRows .div`.
Example: for `DIVQ` with `rs3 = x10`, the third row is `SD vr48, 0(x10)`, before the first
reload `LD vr61, 0(x10)` of the dividend. -/
def oldDivRows (scalar : Bool) (L : MulRegs) (rs1 rs2 rs3 : regidx)
    (advice : Nat → BitVec 64) : List Instr :=
  ([0, 1, 2, 3].flatMap (oldRound L rs2 rs3 advice)) ++ constRows scalar L ++
    divCheckRows scalar L rs1 rs3 ++ resetRows L.pool

/-- The earlier rows, split into the four prologue rounds and the rest.
Example: for `DIVQ` the first block is `oldRound mulqRegs rs2 rs3 advice 0`. -/
theorem oldDivRows_eq (scalar : Bool) (L : MulRegs) (rs1 rs2 rs3 : regidx)
    (advice : Nat → BitVec 64) :
    oldDivRows scalar L rs1 rs2 rs3 advice =
      oldRound L rs2 rs3 advice 0 ++ (oldRound L rs2 rs3 advice 1 ++
        (oldRound L rs2 rs3 advice 2 ++ (oldRound L rs2 rs3 advice 3 ++
          (constRows scalar L ++ (divCheckRows scalar L rs1 rs3 ++ resetRows L.pool))))) := by
  simp only [oldDivRows, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.append_assoc]

/-- A round of the earlier prologue runs when the divisor limb loads and the store is allowed;
it sets the divisor, result and quotient registers and stores the result limb.
Example: round 0 for `DIVQ` from the instance state loads `1` into `vr52` and stores advice
word `0` at `0x8001_0000`. -/
theorem run_oldRound {L : MulRegs} {i : Nat} {rs2 rs3 : regidx} {advice : Nat → BitVec 64}
    (hb : 32 ≤ (L.b i).toNat) (ha : 32 ≤ (L.a i).toNat) (hw : 32 ≤ (L.w i).toNat)
    {s₀ t : SailJoltState} (ht : t.sail.regs = s₀.sail.regs) {B2 B3 : BitVec 64}
    (h2 : XReads s₀ rs2 B2) (h3 : XReads s₀ rs3 B3)
    (hram : RAM_START_ADDRESS ≤ (B3 + BitVec.ofNat 64 (8 * i)).toNat) {y : BitVec 64}
    (hy : loadDword? t (B2 + BitVec.ofNat 64 (8 * i)) = some y)
    (hwr : DwordWritable t.jolt_device (B3 + BitVec.ofNat 64 (8 * i)).toNat) {ea : Nat}
    (hea : (B3 + BitVec.ofNat 64 (8 * i)).toNat = ea) (f : JoltISA.VReg → BitVec 64)
    (rest : List Instr) (s' : SailJoltState)
    (hrest : (Program.seq rest).Run
      { memWrite t ea (advice (2 * i)) with
        vregs := setV (setV (setV f (L.b i) y) (L.a i) (advice (2 * i))) (L.w i)
          (advice (2 * i + 1)) } s') :
    (Program.seq (oldRound L rs2 rs3 advice i ++ rest)).Run { t with vregs := f } s' := by
  subst hea
  simp only [oldRound, ldRow, sdRow, List.cons_append, List.nil_append]
  rw [run_ld_vregs_iff hb (XReads.of_regs ht.symm h2)]
  refine ⟨y, hy, ?_⟩
  rw [run_va_vregs_iff ha, run_sd_vregs_iff h3 ht hram, run_va_vregs_iff hw, setV_same]
  exact ⟨hwr, hrest⟩

/-- A store elsewhere leaves a RAM doubleword load unchanged.
Example: storing at `0x8001_0000` leaves the load from `0x8001_0020`. -/
theorem loadDword?_memWrite_of_disjoint {t : SailJoltState} {a : BitVec 64} {ea : Nat}
    (v : BitVec 64) (hram : RAM_START_ADDRESS ≤ a.toNat)
    (hw : DwordWritable t.jolt_device a.toNat) (h : ea + 8 ≤ a.toNat ∨ a.toNat + 8 ≤ ea) :
    loadDword? (memWrite t ea v) a = loadDword? t a := by
  have hok := effective_address_ok_read_of_write hram hw.2
  rw [loadDword?_ram (s := memWrite t ea v) hw.1 hram hok, loadDword?_ram hw.1 hram hok]
  exact congrArg some (ram_doubleword_write_ne _ _ _ _ h)

/-! ## The earlier rows accept a wrong result when `rs3 = rs1` -/

/-- Advice that claims `1 / 1 = 2`: result `c = 2` and quotient `w = 0`, interleaved.
Example: `badAdvice 0 = 2` and `badAdvice i = 0` for every other `i`. -/
def badAdvice : Nat → BitVec 64 := fun i => (divisionWords (natToLimbs 2) (natToLimbs 0)).getD i 0

/-- **The earlier rows accept `1 / 1 = 2` when the result overwrites the dividend.** From the
instance state with `a = 1` at `x10` and `b = 1` at `x11`, the rows of `oldDivRows` for `DIVQ`
with `rs1 = rs3 = x10` run to the end with the advice `c = 2`, `w = 0`, and leave `2` at `x10`.
Each check reloads the dividend from `x10` after the prologue stored `c` there, so it compares
`c·1 + 0·p'` with `c` itself.
Example: the doubleword at `0x8001_0000` ends as `2`. -/
theorem oldDivq_accepts_wrong_result :
    ∃ s', (Program.seq (oldDivRows false mulqRegs (regidx.Regidx 10) (regidx.Regidx 11)
        (regidx.Regidx 10) badAdvice)).Run (katState divA divA) s' ∧
      ∀ i, i < 4 → loadDword? s' (katIn + BitVec.ofNat 64 (8 * i)) =
        (natToLimbs 2).toList[i]? := by
  have hv : mulqRegs.Valid .div false := divqRegs_valid
  have h10 := kat_reads_x10 divA divA
  have h11 := kat_reads_x11 divA divA
  have hin : RAM_START_ADDRESS ≤ katIn.toNat := by decide
  have av : ∀ k, k < 8 → badAdvice k = if k = 0 then 2 else 0 := by
    intro k hk
    interval_cases k <;> decide
  -- Addresses and permissions.
  have haddr : ∀ k, k < 4 → (katIn + BitVec.ofNat 64 (8 * k)).toNat = katIn.toNat + 8 * k :=
    fun k hk => out_addr (by decide) hk
  have hwr : ∀ k, k < 8 → DwordWritable katDevice (katIn.toNat + 8 * k) := fun k hk =>
    kat_writable _ (by omega) (by simp [katIn, katOut]; omega) (by simp [katIn])
  have hram : ∀ k, k < 4 → RAM_START_ADDRESS ≤ (katIn + BitVec.ofNat 64 (8 * k)).toNat :=
    fun k hk => by rw [haddr k hk]; omega
  have hwk : ∀ (t : SailJoltState), t.jolt_device = katDevice → ∀ k, k < 4 →
      DwordWritable t.jolt_device (katIn + BitVec.ofNat 64 (8 * k)).toNat :=
    fun t ht k hk => by rw [ht, haddr k hk]; exact hwr k (by omega)
  -- The divisor loads, before and after stores to the dividend.
  have baddr : ∀ k, k < 4 →
      (katIn + 32 + BitVec.ofNat 64 (8 * k)).toNat = katIn.toNat + 8 * (k + 4) := by
    intro k hk
    interval_cases k <;> decide
  have bload : ∀ k (hk : k < 4),
      loadDword? (katState divA divA) (katIn + 32 + BitVec.ofNat 64 (8 * k)) = some divA[k] := by
    intro k hk
    rw [show katIn + 32 + BitVec.ofNat 64 (8 * k) = katIn + BitVec.ofNat 64 (8 * (k + 4)) by
        interval_cases k <;> decide,
      kat_load divA divA (k + 4) (by omega), List.getElem?_append_right (by simp)]
    simp [hk]
  have keep : ∀ (t : SailJoltState), t.jolt_device = katDevice → ∀ j, j < 4 →
      ∀ (v : BitVec 64) k, k < 4 →
      loadDword? (memWrite t (katIn.toNat + 8 * j) v) (katIn + 32 + BitVec.ofNat 64 (8 * k)) =
        loadDword? t (katIn + 32 + BitVec.ofNat 64 (8 * k)) := by
    intro t ht j hj v k hk
    apply loadDword?_memWrite_of_disjoint v (by rw [baddr k hk]; omega)
      (by rw [ht, baddr k hk]; exact hwr (k + 4) (by omega))
    rw [baddr k hk]
    omega
  -- The states after each store of the prologue.
  let s0 := katState divA divA
  let t1 := memWrite s0 (katIn.toNat + 8 * 0) (badAdvice (2 * 0))
  let t2 := memWrite t1 (katIn.toNat + 8 * 1) (badAdvice (2 * 1))
  let t3 := memWrite t2 (katIn.toNat + 8 * 2) (badAdvice (2 * 2))
  let t4 := memWrite t3 (katIn.toNat + 8 * 3) (badAdvice (2 * 3))
  have r1 : t1.sail.regs = s0.sail.regs := memWrite_regs rfl _ _
  have r2 : t2.sail.regs = s0.sail.regs := memWrite_regs r1 _ _
  have r3 : t3.sail.regs = s0.sail.regs := memWrite_regs r2 _ _
  have r4 : t4.sail.regs = s0.sail.regs := memWrite_regs r3 _ _
  have bl1 : loadDword? t1 (katIn + 32 + BitVec.ofNat 64 (8 * 1)) = some divA[1] := by
    rw [keep _ rfl 0 (by decide) _ 1 (by decide), bload 1 (by decide)]
  have bl2 : loadDword? t2 (katIn + 32 + BitVec.ofNat 64 (8 * 2)) = some divA[2] := by
    rw [keep _ rfl 1 (by decide) _ 2 (by decide), keep _ rfl 0 (by decide) _ 2 (by decide),
      bload 2 (by decide)]
  have bl3 : loadDword? t3 (katIn + 32 + BitVec.ofNat 64 (8 * 3)) = some divA[3] := by
    rw [keep _ rfl 2 (by decide) _ 3 (by decide), keep _ rfl 1 (by decide) _ 3 (by decide),
      keep _ rfl 0 (by decide) _ 3 (by decide), bload 3 (by decide)]
  -- The dividend region after the prologue holds the advised result.
  let ws : List (BitVec 64) :=
    [badAdvice (2 * 0), badAdvice (2 * 1), badAdvice (2 * 2), badAdvice (2 * 3)]
  have hm : t4.sail.mem = writeDwords s0.sail.mem katIn.toNat ws :=
    congrArg (fun t => t.sail.mem) (memWrite_four s0 katIn.toNat _ _ _ _)
  have l : ∀ k (hk : k < 4), loadDword? t4 (katIn + BitVec.ofNat 64 (8 * k)) = ws[k]? :=
    fun k hk => loadDword?_of_mem_writeDwords (t := t4) hm hin (by simp [ws]; decide)
      (fun j hj => hwr j (by simp [ws] at hj; omega)) (by simpa [ws] using hk)
  -- The register file after the prologue and the constant rows, and the checks.
  obtain ⟨fa, fb, fw, fp, fp2⟩ := pre_vals_div hv divA badAdvice s0.vregs
  generalize hF : writeAll s0.vregs (preWrites .div false mulqRegs divA divA badAdvice) = F
    at fa fb fw fp fp2
  have hct := colTotal_eq (op := .div) (fun h => absurd h (by decide)) fp fp2
  have hA : limbVal mulqRegs.a F = 2 := by
    simp only [limbVal, fa 0 (by decide), fa 1 (by decide), fa 2 (by decide),
      fa 3 (by decide), av _ (by decide : 2 * 0 < 8), av _ (by decide : 2 * 1 < 8),
      av _ (by decide : 2 * 2 < 8), av _ (by decide : 2 * 3 < 8)]
    decide
  have hW : limbVal mulqRegs.w F = 0 := by
    simp only [limbVal, fw 0 (by decide), fw 1 (by decide), fw 2 (by decide),
      fw 3 (by decide), av _ (by decide : 2 * 0 + 1 < 8), av _ (by decide : 2 * 1 + 1 < 8),
      av _ (by decide : 2 * 2 + 1 < 8), av _ (by decide : 2 * 3 + 1 < 8)]
    decide
  have hB : limbVal mulqRegs.b F = 1 := by
    rw [fb, divA, limbsToNat_natToLimbs]
  rw [hA, hB, hW] at hct
  obtain ⟨R0, R1, R2, R3, R4, R5, R6, C, G, heq, -, hiff⟩ :=
    run_checks_div_iff (rs3 := regidx.Regidx 10) hv (s := t4) (XReads.of_regs r4.symm h10) F
  rw [hct] at heq
  have e0 : R0 = 2 := BitVec.eq_of_toNat_eq (by simp; omega)
  have e1 : R1 = 0 := BitVec.eq_of_toNat_eq (by simp; omega)
  have e2 : R2 = 0 := BitVec.eq_of_toNat_eq (by simp; omega)
  have e3 : R3 = 0 := BitVec.eq_of_toNat_eq (by simp; omega)
  have e4 : R4 = 0 := BitVec.eq_of_toNat_eq (by simp; omega)
  have e5 : R5 = 0 := BitVec.eq_of_toNat_eq (by simp; omega)
  have e6 : R6 = 0 := BitVec.eq_of_toNat_eq (by simp; omega)
  have eC : C = 0 := BitVec.eq_of_toNat_eq (by simp; omega)
  have eHn : (jolt_mulhu_value (F (mulqRegs.a 3)) (F (mulqRegs.b 3))).toNat = 0 := by omega
  have eH : jolt_mulhu_value (F (mulqRegs.a 3)) (F (mulqRegs.b 3)) = 0 :=
    BitVec.eq_of_toNat_eq (by rw [eHn]; rfl)
  have fw' : ∀ k, k < 4 → F (mulqRegs.w k) = 0 := fun k hk => by
    rw [fw k hk, av _ (by omega)]
    simp
  have hpool : ∀ r ∈ mulqRegs.pool, 32 ≤ r.toNat := by
    intro r hr
    simp only [MulRegs.pool, List.mem_map, List.mem_range] at hr
    obtain ⟨i, hi, rfl⟩ := hr
    exact hv.pool i hi
  obtain ⟨V, hV, -⟩ := resetRows_spec mulqRegs.pool hpool G
  have checks := (hiff (resetRows mulqRegs.pool) { t4 with vregs := V }).2
    ⟨(readLimbs?_eq_some_iff _ _ _).2
        ⟨(congrArg (loadDword? t4) (by decide : katIn = katIn + BitVec.ofNat 64 (8 * 0))).trans
            ((l 0 (by decide)).trans (by rw [e0, e1, e2, e3]; decide)),
          (l 1 (by decide)).trans (by rw [e0, e1, e2, e3]; decide),
          (l 2 (by decide)).trans (by rw [e0, e1, e2, e3]; decide),
          (l 3 (by decide)).trans (by rw [e0, e1, e2, e3]; decide)⟩,
      by rw [e4, fw' 0 (by decide)], by rw [e5, fw' 1 (by decide)],
      by rw [e6, fw' 2 (by decide)], by rw [eC, eH, fw' 3 (by decide)]; rfl,
      by rw [eC, eH]; decide, (run_regs_end_iff hV t4 _).2 rfl⟩
  refine ⟨{ t4 with vregs := V }, ?_, fun i hi => ?_⟩
  · rw [oldDivRows_eq]
    change (Program.seq _).Run { s0 with vregs := s0.vregs } _
    refine run_oldRound (i := 0) (by decide) (by decide) (by decide) (s₀ := s0) rfl h11 h10
      (hram 0 (by decide)) (bload 0 (by decide)) (hwk s0 rfl 0 (by decide))
      (haddr 0 (by decide)) _ _ _ ?_
    refine run_oldRound (i := 1) (by decide) (by decide) (by decide) (s₀ := s0) r1 h11 h10
      (hram 1 (by decide)) bl1 (hwk t1 rfl 1 (by decide)) (haddr 1 (by decide)) _ _ _ ?_
    refine run_oldRound (i := 2) (by decide) (by decide) (by decide) (s₀ := s0) r2 h11 h10
      (hram 2 (by decide)) bl2 (hwk t2 rfl 2 (by decide)) (haddr 2 (by decide)) _ _ _ ?_
    refine run_oldRound (i := 3) (by decide) (by decide) (by decide) (s₀ := s0) r3 h11 h10
      (hram 3 (by decide)) bl3 (hwk t3 rfl 3 (by decide)) (haddr 3 (by decide)) _ _ _ ?_
    rw [run_constRows_iff hv]
    rw [← hF] at checks
    exact checks
  · rw [loadDword?_vregs, l i hi]
    interval_cases i <;> decide

/-- **The current rows reject it.** From the same state, with `rs1 = rs3 = x10`, no run of the
`SECP256K1_DIVQ` rows, for any advice, leaves `2` at `x10`: by `secp256k1Divq_rows_sound` the
stored `c` satisfies `c·1 = w·p + 1` for the dividend `1` read before the call, and `2` does
not.
Example: the advice `c = 2`, `w = 0` of `oldDivq_accepts_wrong_result` fails the dividend
check. -/
theorem secp256k1Divq_rejects_wrong_result {advice : Nat → BitVec 64} {s' : SailJoltState}
    (run : (secp256k1DivqRowsAuto (regidx.Regidx 10) (regidx.Regidx 11) (regidx.Regidx 10)
      advice).Run (katState divA divA) s') :
    ¬ ∀ i, i < 4 → loadDword? s' (katIn + BitVec.ofNat 64 (8 * i)) =
        (natToLimbs 2).toList[i]? := by
  intro hbad
  have hout : fieldOut (regidx.Regidx 10) (katState divA divA) = katIn :=
    (XReads.eq_sourceValue (kat_reads_x10 divA divA)).symm
  have buf : FieldMulBuffer (regidx.Regidx 10) (katState divA divA) :=
    ⟨by rw [hout]; decide, by rw [hout]; decide⟩
  obtain ⟨a', b', w, c, ha', hb', ⟨rel, -, -⟩, -, hload⟩ := secp256k1Divq_rows_sound buf run
  rw [kat_x10, kat_limbs_a] at ha'
  rw [kat_x11, kat_limbs_b] at hb'
  cases Option.some.inj ha'
  cases Option.some.inj hb'
  rw [hout] at hload
  have ec : c = natToLimbs 2 := Vector.ext fun j hj => by
    have e := (hload j hj).symm.trans (hbad j hj)
    simpa [Vector.getElem?_toList, hj] using e
  have h1 : limbsToNat divA = 1 := by rw [divA, limbsToNat_natToLimbs]
  have h2 : limbsToNat c = 2 := by rw [ec, limbsToNat_natToLimbs]
  rw [h1, h2] at rel
  have hp : 1 < p := by decide
  rcases Nat.eq_zero_or_pos (limbsToNat w) with hw | hw
  · rw [hw] at rel
    omega
  · have := Nat.le_mul_of_pos_left p hw
    omega

end JoltTests.Secp256k1FieldDivInstance
