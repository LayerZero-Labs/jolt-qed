import JoltBytecode.Inlines.Secp256k1.FieldMul
import JoltBytecode.Inlines.Secp256k1.Prime

/-!
# secp256k1 `DIV`: soundness and completeness of the rows

The inlines `SECP256K1_DIVQ` and `SECP256K1_DIVR` divide modulo the base-field prime `p` (`Q`)
or the group order `n` (`R`). The rows load the divisor `b` from `rs2` and take eight advice
words: the result `c` and the quotient `w`, interleaved. With `p' = 2^256 - q`, the columns
compute `c·b + w·p'`; columns 0 to 3 are compared with the dividend `a`, which each column
reloads from `rs1`, and columns 4 to 7 with `w`. So `c·b + w·p' = a + 2^256·w`, that is
`c·b = w·q + a` (`DivRel`). Only after every check do the rows store `c` at `rs3`.

That order matters when `rs3 = rs1`. Before Jolt commit `db9679295` the rows stored each limb of
`c` right after taking it as advice, so the dividend reloads read `c` back, and with `b = 1`,
`w = 0` every `c` passed. `divRows_sound` reads `a` from the state before the call, so it holds
for every choice of registers, aliased or not. `JoltTests.Inlines.Secp256k1FieldDivInstance`
shows the earlier rows admitting a wrong result under `rs3 = rs1` and the current rows rejecting
it.

* `divRows_sound`: every run of the rows from a state whose output buffer lies in RAM reads
  `a` and `b`, stores four words `c` with `DivRel q a b w c` for some `w`, and changes nothing
  else (`FieldDivSpec`).
* `divRows_jolt_advice_complete`: with Jolt's advice, from a state where the operands and the
  buffer can be read and written (`FieldMulPre`), for a dividend below `q` and a divisor
  nonzero modulo `q`, the rows run, and the stored result is below `q` (`FieldMulCanonical`).
* `secp256k1Divq_rows_sound` … `secp256k1Divr_rows_jolt_advice_complete`: the two theorems
  for each of the two generated row sequences.

Completeness assumes only `b % q ≠ 0`. Because `p` and `n` are prime (`p_prime`, `n_prime` in
`Prime.lean`), such a divisor is coprime to `q` and has an inverse modulo `q`.
-/

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail LeanRV64D
  LeanRV64D.Functions JoltISA JoltISA.Inlines JoltISA.Inlines.Generated

set_option autoImplicit false

namespace JoltISA.Inlines.Secp256k1

/-! ## Limbs -/

/-- Four limbs are determined by their value.
Example: only `#v[1, 0, 0, 0]` has value `1`. -/
theorem limbs_eq_of_limbsToNat_eq {x y : Limbs} (h : limbsToNat x = limbsToNat y) : x = y := by
  have x0 := x[0].isLt
  have x1 := x[1].isLt
  have x2 := x[2].isLt
  have x3 := x[3].isLt
  have y0 := y[0].isLt
  have y1 := y[1].isLt
  have y2 := y[2].isLt
  have y3 := y[3].isLt
  simp only [limbsToNat] at h
  refine Vector.ext fun i hi => BitVec.eq_of_toNat_eq ?_
  interval_cases i <;> omega

/-! ## The prologue -/

/-- **The prologue of `DIV`.** From register file `f`, the divisor loads, advice rows and
constant rows run exactly when the divisor can be read, and they write `preWrites` (which for
division ignores its first operand; we pass the divisor twice).
Example: `DIVQ` with `x11` pointing at readable RAM: `vr52..vr55` get the divisor limbs,
`vr48..vr51` advice words `0, 2, 4, 6`, and `vr56..vr59` advice words `1, 3, 5, 7`. -/
theorem run_prologue_div_iff {scalar : Bool} {L : MulRegs} (hv : L.Valid .div scalar)
    {rs1 rs2 : regidx} {advice : Nat → BitVec 64} {s : SailJoltState} {B2 : BitVec 64}
    (h2 : XReads s rs2 B2) (f : VReg → BitVec 64) (rest : List Instr) (s' : SailJoltState) :
    (Program.seq (prologueRows .div L rs1 rs2 advice ++ constRows scalar L ++ rest)).Run
        { s with vregs := f } s' ↔
      ∃ y : Limbs, readLimbs? s B2 = some y ∧
        (Program.seq rest).Run
          { s with vregs := writeAll f (preWrites .div scalar L y y advice) } s' := by
  have g := hv.pre_ge
  rw [List.append_assoc]
  simp only [prologueRows, ldRow, List.flatMap_cons, List.flatMap_nil,
    List.cons_append, List.nil_append, List.append_nil, Nat.reduceMul, Nat.reduceAdd,
    run_ld_vregs_iff (g (L.b 0) (by simp [preRegs])) h2,
    run_ld_vregs_iff (g (L.b 1) (by simp [preRegs])) h2,
    run_ld_vregs_iff (g (L.b 2) (by simp [preRegs])) h2,
    run_ld_vregs_iff (g (L.b 3) (by simp [preRegs])) h2,
    run_va_vregs_iff (g (L.a 0) (by simp [preRegs])),
    run_va_vregs_iff (g (L.a 1) (by simp [preRegs])),
    run_va_vregs_iff (g (L.a 2) (by simp [preRegs])),
    run_va_vregs_iff (g (L.a 3) (by simp [preRegs])),
    run_va_vregs_iff (g (L.w 0) (by simp [preRegs])),
    run_va_vregs_iff (g (L.w 1) (by simp [preRegs])),
    run_va_vregs_iff (g (L.w 2) (by simp [preRegs])),
    run_va_vregs_iff (g (L.w 3) (by simp [preRegs])),
    run_constRows_iff hv]
  constructor
  · rintro ⟨y0, hy0, y1, hy1, y2, hy2, y3, hy3, hrun⟩
    exact ⟨#v[y0, y1, y2, y3],
      (readLimbs?_eq_some_iff _ _ _).2 ⟨by simpa using hy0, by simpa using hy1,
        by simpa using hy2, by simpa using hy3⟩, hrun⟩
  · rintro ⟨y, hy, hrun⟩
    obtain ⟨hy0, hy1, hy2, hy3⟩ := (readLimbs?_eq_some_iff _ _ _).1 hy
    exact ⟨y[0], by simpa using hy0, y[1], hy1, y[2], hy2, y[3], hy3, hrun⟩

/-- After the prologue of `DIV`, the result registers `a` hold the even advice words, the
divisor registers `b` the divisor, the quotient registers `w` the odd advice words, and `p`
(and `p2`) hold `p'`.
Example: for `DIVQ`, `vr49` holds advice word `2` and `vr57` advice word `3`. -/
theorem pre_vals_div {scalar : Bool} {L : MulRegs} (hv : L.Valid .div scalar) (y : Limbs)
    (advice : Nat → BitVec 64) (f : VReg → BitVec 64) :
    (∀ i, i < 4 → writeAll f (preWrites .div scalar L y y advice) (L.a i) = advice (2 * i)) ∧
    limbVal L.b (writeAll f (preWrites .div scalar L y y advice)) = limbsToNat y ∧
    (∀ i, i < 4 →
      writeAll f (preWrites .div scalar L y y advice) (L.w i) = advice (2 * i + 1)) ∧
    writeAll f (preWrites .div scalar L y y advice) L.p =
      (if scalar then pPrimeScalar0 else pPrimeBase) ∧
    (scalar = true → writeAll f (preWrites .div scalar L y y advice) L.p2 = pPrimeScalar1) := by
  have key : ∀ d v, (d, v) ∈ preWrites .div scalar L y y advice →
      writeAll f (preWrites .div scalar L y y advice) d = v := fun d v h =>
    writeAll_of_mem f (by rw [preWrites_fst]; exact hv.pre_nodup) h
  have b : ∀ i (hi : i < 4), writeAll f (preWrites .div scalar L y y advice) (L.b i) = y[i] := by
    intro i hi
    interval_cases i <;> exact key _ _ (by simp [preWrites])
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    interval_cases i <;> exact key _ _ (by simp [preWrites])
  · simp only [limbVal, limbsToNat, b 0 (by decide), b 1 (by decide), b 2 (by decide),
      b 3 (by decide)]
  · intro i hi
    interval_cases i <;> exact key _ _ (by simp [preWrites])
  · cases scalar <;> exact key _ _ (by simp [preWrites])
  · rintro rfl
    exact key _ _ (by simp [preWrites])

/-! ## The checks -/

/-- The rows of a division after the prologue and before the stores: the columns, each of
columns 0 to 3 compared with a dividend limb reloaded from `rs1`, columns 4 to 6 compared with
the quotient, and the top column.
Example: for `DIVQ` they start with `MUL vr62, vr48, vr52`. -/
def divCheckRows (scalar : Bool) (L : MulRegs) (rs1 rs3 : regidx) : List Instr :=
  col0Rows .div L rs1 rs3 ++
    ((List.range' 1 6).flatMap fun k => colKRows .div scalar L rs1 rs3 k) ++ finalRows L

/-- For `DIV`, the rows after the prologue are the checks, the stores and the resets.
Example: for `DIVQ`, the four stores `SD vr48, 0(rs3)` … `SD vr51, 24(rs3)` come right after
the final `VirtualAssertLTE`. -/
theorem tailRows_div (scalar : Bool) (L : MulRegs) (rs1 rs3 : regidx) :
    tailRows .div scalar L rs1 rs3 =
      divCheckRows scalar L rs1 rs3 ++ (storeRows L rs3 ++ resetRows L.pool) := by
  simp [tailRows, divCheckRows, List.append_assoc]

/-- For `DIV`, the output of columns 0 to 3 is a reload of a dividend limb and a comparison.
Example: column 2 ends with `LD aux, 16(rs1); VirtualAssertEQ r0, aux`. -/
theorem outRows_div_load (L : MulRegs) (rs1 rs3 : regidx) {k : Nat} (hk : k < 4) :
    outRows .div L rs1 rs3 k =
      [ldRow L.aux rs1 (8 * k), .VirtualAssertEQ (.vreg (L.r k)) (.vreg L.aux) 0] := by
  simp [outRows, hk]

/-- A dividend reload and its comparison from `{s with vregs := G}`: the run continues exactly
when the doubleword loads and equals the column register; the reload leaves that value in
`aux`.
Example: `LD vr61, 8(x10); VirtualAssertEQ vr63, vr61` passes when `vr63` holds the doubleword
at `x10 + 8`. -/
theorem run_ld_assert_vregs_iff {aux r : VReg} (haux : 32 ≤ aux.toNat) (hr : r ≠ aux)
    {rs1 : regidx} {s : SailJoltState} {B1 : BitVec 64} (h1 : XReads s rs1 B1) (off : Nat)
    (G : VReg → BitVec 64) (rest : List Instr) (s' : SailJoltState) :
    (Program.seq (ldRow aux rs1 off :: .VirtualAssertEQ (.vreg r) (.vreg aux) 0 :: rest)).Run
        { s with vregs := G } s' ↔
      loadDword? s (B1 + BitVec.ofNat 64 off) = some (G r) ∧
        (Program.seq rest).Run { s with vregs := setV G aux (G r) } s' := by
  rw [ldRow, run_ld_vregs_iff haux h1]
  simp only [run_assertEq_iff, setV_same, setV_ne _ _ hr]
  constructor
  · rintro ⟨v, hv, he, hrun⟩
    subst he
    exact ⟨hv, hrun⟩
  · rintro ⟨hv, hrun⟩
    exact ⟨_, hv, rfl, hrun⟩

/-- **The checks of `DIV`.** From register file `F`, with `rs1` readable at `B1`, the checks
compute column values `R0, …, R6` and a top carry `C` with

`R0 + 2^64·R1 + … + 2^384·R6 + 2^448·(C + hi(a3·b3)) = colTotal F`.

They run exactly when the dividend at `B1` reads as `R0, …, R3`, `R4, R5, R6` equal the
quotient limbs `w0, w1, w2`, and `C + hi(a3·b3)` equals `w3` without overflow; they end in a
register file `G` that agrees with `F` on the operand registers.
Example: for `DIVQ` with `a = 1`, `b = 2` and Jolt's advice `c = (p+1)/2`, `w = 1`, the columns
are `1, 0, 0, 0, 1, 0, 0` and the top column is `0`. -/
theorem run_checks_div_iff {scalar : Bool} {L : MulRegs} (hv : L.Valid .div scalar)
    {rs1 rs3 : regidx} {s : SailJoltState} {B1 : BitVec 64} (h1 : XReads s rs1 B1)
    (F : VReg → BitVec 64) :
    ∃ R0 R1 R2 R3 R4 R5 R6 C : BitVec 64, ∃ G : VReg → BitVec 64,
      R0.toNat + 2 ^ 64 * R1.toNat + 2 ^ 128 * R2.toNat + 2 ^ 192 * R3.toNat +
          2 ^ 256 * R4.toNat + 2 ^ 320 * R5.toNat + 2 ^ 384 * R6.toNat +
          2 ^ 448 * (C.toNat + (jolt_mulhu_value (F (L.a 3)) (F (L.b 3))).toNat) =
        colTotal .div scalar L F ∧
      (∀ r, L.OpFree r → G r = F r) ∧
      ∀ rest s', (Program.seq (divCheckRows scalar L rs1 rs3 ++ rest)).Run
          { s with vregs := F } s' ↔
        readLimbs? s B1 = some #v[R0, R1, R2, R3] ∧
        R4 = F (L.w 0) ∧ R5 = F (L.w 1) ∧ R6 = F (L.w 2) ∧
        C + jolt_mulhu_value (F (L.a 3)) (F (L.b 3)) = F (L.w 3) ∧
        (jolt_mulhu_value (F (L.a 3)) (F (L.b 3))).toNat ≤
          (C + jolt_mulhu_value (F (L.a 3)) (F (L.b 3))).toNat ∧
        (Program.seq rest).Run { s with vregs := G } s' := by
  -- The operand registers are never column registers.
  have oa : ∀ i, i < 4 → L.OpFree (L.a i) := by
    intro i hi
    apply hv.pre_free
    interval_cases i <;> cases scalar <;> simp [preRegs]
  have ow : ∀ i, i < 4 → L.OpFree (L.w i) := by
    intro i hi
    apply hv.pre_free
    interval_cases i <;> cases scalar <;> simp [preRegs]
  have ob : ∀ i, i < 4 → L.OpFree (L.b i) := by
    intro i hi
    apply hv.pre_free
    interval_cases i <;> cases scalar <;> simp [preRegs]
  have c0 : 32 ≤ L.r0.toNat ∧ 32 ≤ L.r1.toNat ∧ 32 ≤ L.aux.toNat ∧ 32 ≤ L.aux2.toNat ∧
      L.r0 ≠ L.r1 ∧ L.aux ≠ L.r0 ∧ L.aux ≠ L.r1 ∧ L.aux2 ≠ L.r0 ∧ L.aux2 ≠ L.r1 ∧
      L.aux ≠ L.aux2 := hv.col0
  have free : ∀ {r}, L.OpFree r → r ≠ L.r0 ∧ r ≠ L.r1 ∧ r ≠ L.aux ∧ r ≠ L.aux2 :=
    fun h => h
  have r0a : L.r0 ≠ L.aux := Ne.symm c0.2.2.2.2.2.1
  have r1a : L.r1 ≠ L.aux := Ne.symm c0.2.2.2.2.2.2.1
  -- Column 0: `MUL r0, a0, b0`, then the term `lo(w0·p)`.
  obtain ⟨g0, hg0, e0', A0⟩ := col0_spec hv F
  -- The reloads write `aux`, which is no operand register.
  have keep : ∀ (g : VReg → BitVec 64) (v : BitVec 64), (∀ r, L.OpFree r → g r = F r) →
      ∀ r, L.OpFree r → setV g L.aux v r = F r := fun g v hg r hr =>
    (setV_ne _ _ (free hr).2.2.1).trans (hg r hr)
  -- Columns 1 to 6; after each of columns 0 to 3, the reload sets `aux`.
  obtain ⟨g1, hg1, e1, A1⟩ := col_step hv (k := 1) (by decide)
    (keep g0 (g0 (L.r 0)) A0)
  obtain ⟨g2, hg2, e2, A2⟩ := col_step hv (k := 2) (by decide)
    (keep g1 (g1 (L.r 1)) A1)
  obtain ⟨g3, hg3, e3, A3⟩ := col_step hv (k := 3) (by decide)
    (keep g2 (g2 (L.r 2)) A2)
  obtain ⟨g4, hg4, e4, A4⟩ := col_step hv (k := 4) (by decide)
    (keep g3 (g3 (L.r 3)) A3)
  obtain ⟨g5, hg5, e5, A5⟩ := col_step hv (k := 5) (by decide) A4
  obtain ⟨g6, hg6, e6, A6⟩ := col_step hv (k := 6) (by decide) A5
  have e1' : (g1 L.r1).toNat + 2 ^ 64 * (g1 L.r0).toNat =
      (setV g0 L.aux (g0 L.r0) L.r1).toNat + colSum .div scalar L F 1 := e1
  have e2' : (g2 L.r0).toNat + 2 ^ 64 * (g2 L.r1).toNat =
      (setV g1 L.aux (g1 L.r1) L.r0).toNat + colSum .div scalar L F 2 := e2
  have e3' : (g3 L.r1).toNat + 2 ^ 64 * (g3 L.r0).toNat =
      (setV g2 L.aux (g2 L.r0) L.r1).toNat + colSum .div scalar L F 3 := e3
  have e4' : (g4 L.r0).toNat + 2 ^ 64 * (g4 L.r1).toNat =
      (setV g3 L.aux (g3 L.r1) L.r0).toNat + colSum .div scalar L F 4 := e4
  have e5' : (g5 L.r1).toNat + 2 ^ 64 * (g5 L.r0).toNat =
      (g4 L.r1).toNat + colSum .div scalar L F 5 := e5
  have e6' : (g6 L.r0).toNat + 2 ^ 64 * (g6 L.r1).toNat =
      (g5 L.r0).toNat + colSum .div scalar L F 6 := e6
  rw [setV_ne _ _ r1a] at e1' e3'
  rw [setV_ne _ _ r0a] at e2' e4'
  -- The top column.
  have hH : jolt_mulhu_value (g6 (L.a 3)) (g6 (L.b 3)) =
      jolt_mulhu_value (F (L.a 3)) (F (L.b 3)) := by
    rw [A6 _ (oa 3 (by decide)), A6 _ (ob 3 (by decide))]
  refine ⟨g0 L.r0, g1 L.r1, g2 L.r0, g3 L.r1, g4 L.r0, g5 L.r1, g6 L.r0, g6 L.r1,
    setV (setV g6 L.aux (jolt_mulhu_value (g6 (L.a 3)) (g6 (L.b 3)))) L.r1
      (setV g6 L.aux (jolt_mulhu_value (g6 (L.a 3)) (g6 (L.b 3))) L.r1 +
        setV g6 L.aux (jolt_mulhu_value (g6 (L.a 3)) (g6 (L.b 3))) L.aux), ?_,
    fun r hr => ?_, fun rest s' => ?_⟩
  · unfold colTotal
    omega
  · rw [setV_ne _ _ (free hr).2.1, setV_ne _ _ (free hr).2.2.1, A6 r hr]
  -- The run, row group by row group.
  simp only [divCheckRows, col0Rows, colKRows, List.range', List.flatMap_cons, List.flatMap_nil,
    List.append_assoc, List.cons_append, List.nil_append, List.append_nil,
    outRows_div_load L rs1 rs3 (show 0 < 4 by decide),
    outRows_div_load L rs1 rs3 (show 1 < 4 by decide),
    outRows_div_load L rs1 rs3 (show 2 < 4 by decide),
    outRows_div_load L rs1 rs3 (show 3 < 4 by decide),
    outRows_assert .div L rs1 rs3 (show ¬ 4 < 4 by decide),
    outRows_assert .div L rs1 rs3 (show ¬ 5 < 4 by decide),
    outRows_assert .div L rs1 rs3 (show ¬ 6 < 4 by decide),
    finalRows, Nat.reduceAdd, Nat.reduceSub]
  rw [run_regRow_vregs_iff (i := .MUL (.vreg L.r0) (.vreg (L.a 0)) (.vreg (L.b 0))) rfl c0.1,
    run_regs_vregs_iff hg0, run_ld_assert_vregs_iff (r := L.r 0) c0.2.2.1 r0a h1,
    run_regs_vregs_iff hg1, run_ld_assert_vregs_iff (r := L.r 1) c0.2.2.1 r1a h1,
    run_regs_vregs_iff hg2, run_ld_assert_vregs_iff (r := L.r 2) c0.2.2.1 r0a h1,
    run_regs_vregs_iff hg3, run_ld_assert_vregs_iff (r := L.r 3) c0.2.2.1 r1a h1,
    run_regs_vregs_iff hg4, run_assertEq_iff,
    run_regs_vregs_iff hg5, run_assertEq_iff,
    run_regs_vregs_iff hg6, run_assertEq_iff,
    run_regRow_vregs_iff (i := .MULHU (.vreg L.aux) (.vreg (L.a 3)) (.vreg (L.b 3))) rfl c0.2.2.1,
    run_regRow_vregs_iff (i := .ADD (.vreg L.r1) (.vreg L.r1) (.vreg L.aux)) rfl c0.2.1,
    run_assertEq_iff, run_assertLTE_iff]
  have r0e : L.r 0 = L.r0 := rfl
  have r1e : L.r 1 = L.r1 := rfl
  have r2e : L.r 2 = L.r0 := rfl
  have r3e : L.r 3 = L.r1 := rfl
  have r4e : L.r 4 = L.r0 := rfl
  have r5e : L.r 5 = L.r1 := rfl
  have r6e : L.r 6 = L.r0 := rfl
  have fw3 := free (ow 3 (by decide))
  have nar1 : L.aux ≠ L.r1 := c0.2.2.2.2.2.2.1
  simp only [r0e, r1e, r2e, r3e, r4e, r5e, r6e, setV_same, setV_ne _ _ (Ne.symm nar1),
    setV_ne _ _ nar1, setV_ne _ _ fw3.2.1, setV_ne _ _ fw3.2.2.1, hH,
    A4 _ (ow 0 (by decide)), A5 _ (ow 1 (by decide)), A6 _ (ow 2 (by decide)),
    A6 _ (ow 3 (by decide))]
  constructor
  · rintro ⟨l0, l1, l2, l3, rest⟩
    exact ⟨(readLimbs?_eq_some_iff _ _ _).2 ⟨by simpa using l0, by simpa using l1,
      by simpa using l2, by simpa using l3⟩, rest⟩
  · rintro ⟨hr, rest⟩
    obtain ⟨l0, l1, l2, l3⟩ := (readLimbs?_eq_some_iff _ _ _).1 hr
    exact ⟨by simpa using l0, by simpa using l1, by simpa using l2, by simpa using l3, rest⟩

/-- A run of the checks reads `rs1`: the first dividend reload reads it.
Example: `DIVQ` with `rs1 = x10`. -/
theorem checks_reads1 {scalar : Bool} {L : MulRegs} (hv : L.Valid .div scalar)
    {rs1 rs3 : regidx} {rest : List Instr} {s s' : SailJoltState} {F : VReg → BitVec 64}
    (h : (Program.seq (divCheckRows scalar L rs1 rs3 ++ rest)).Run { s with vregs := F } s') :
    XReads s rs1 (sourceValue (.xreg rs1) s) := by
  obtain ⟨g0, hg0, -⟩ := col0_spec hv F
  simp only [divCheckRows, col0Rows, List.cons_append, List.append_assoc,
    outRows_div_load L rs1 rs3 (show 0 < 4 by decide), ldRow] at h
  rw [run_regRow_vregs_iff (i := .MUL (.vreg L.r0) (.vreg (L.a 0)) (.vreg (L.b 0))) rfl
    (hv.col0.1 : 32 ≤ L.r0.toNat), run_regs_vregs_iff hg0] at h
  exact XReads.of_run_ld (s := { s with vregs := g0 }) h

/-! ## The stores -/

/-- **The stores of `DIV`.** From register file `G`, with the output buffer `out` in RAM, the
four stores of the result registers and the resets run exactly when the four output
doublewords are writable; the run stores the result registers at `out`.
Example: for `DIVQ` with `out = 0x8002_0000`, `vr48..vr51` go to `0x8002_0000..0x8002_0020`. -/
theorem run_store_div_iff {L : MulRegs} (hpool : ∀ r ∈ L.pool, 32 ≤ r.toNat) {rs3 : regidx}
    {s : SailJoltState} {out : BitVec 64} (h3 : XReads s rs3 out)
    (hram : RAM_START_ADDRESS ≤ out.toNat) (hwrap : out.toNat + 32 ≤ 2 ^ 64)
    (G : VReg → BitVec 64) :
    ∃ V : VReg → BitVec 64, ∀ s',
      (Program.seq (storeRows L rs3 ++ resetRows L.pool)).Run { s with vregs := G } s' ↔
        (∀ k < 4, DwordWritable s.jolt_device (out.toNat + 8 * k)) ∧
        s' = { s with vregs := V,
                      sail := { s.sail with
                        mem := writeDwords s.sail.mem out.toNat
                          [G (L.a 0), G (L.a 1), G (L.a 2), G (L.a 3)] } } := by
  obtain ⟨V, hV, -⟩ := resetRows_spec L.pool hpool G
  refine ⟨V, fun s' => ?_⟩
  have hb : ∀ k, k < 4 → RAM_START_ADDRESS ≤ (out + BitVec.ofNat 64 (8 * k)).toNat :=
    fun k hk => by rw [out_addr hwrap hk]; omega
  simp only [storeRows, sdRow, List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  rw [run_sd_vregs_iff h3 rfl (hb 0 (by decide)),
    run_sd_vregs_iff h3 (memWrite_regs rfl _ _) (hb 1 (by decide)),
    run_sd_vregs_iff h3 (memWrite_regs (memWrite_regs rfl _ _) _ _) (hb 2 (by decide)),
    run_sd_vregs_iff h3 (memWrite_regs (memWrite_regs (memWrite_regs rfl _ _) _ _) _ _)
      (hb 3 (by decide)),
    run_regs_end_iff hV]
  simp only [memWrite_jolt_device]
  rw [out_addr hwrap (k := 0) (by decide), out_addr hwrap (k := 1) (by decide),
    out_addr hwrap (k := 2) (by decide), out_addr hwrap (k := 3) (by decide), memWrite_four]
  constructor
  · rintro ⟨w0, w1, w2, w3, rest⟩
    refine ⟨fun k hk => ?_, rest⟩
    interval_cases k
    · simpa using w0
    · exact w1
    · exact w2
    · exact w3
  · rintro ⟨hw, rest⟩
    exact ⟨by simpa using hw 0 (by decide), hw 1 (by decide), hw 2 (by decide),
      hw 3 (by decide), rest⟩

/-! ## The specification -/

/-- The value-level result of a call of `DIV` modulo `q`: the dividend `a` (at `rs1`) and the
divisor `b` (at `rs2`), both read from the state before the call, and some `w` and `c` with
`c·b = w·q + a`, both below `2^256`. The call stores `c` at the output buffer, changes only
virtual registers otherwise, and `c` reads back. The buffer may alias an operand.
Example: for `DIVQ` with `a = b = 1`, both `c = 1`, `w = 0` and `c = p + 1`, `w = 1` satisfy
it; the rows do not check `c < p`. -/
def FieldDivSpec (q : Nat) (rs1 rs2 rs3 : regidx) (s s' : SailJoltState) : Prop :=
  ∃ a b w c : Limbs,
    readLimbs? s (sourceValue (.xreg rs1) s) = some a ∧
    readLimbs? s (sourceValue (.xreg rs2) s) = some b ∧
    DivRel q (limbsToNat a) (limbsToNat b) (limbsToNat w) (limbsToNat c) ∧
    (∃ V : VReg → BitVec 64,
      s' = { s with vregs := V,
                    sail := { s.sail with
                      mem := writeDwords s.sail.mem (fieldOut rs3 s).toNat c.toList } }) ∧
    ∀ i < 4, loadDword? s' (fieldOut rs3 s + BitVec.ofNat 64 (8 * i)) = c.toList[i]?

/-- **Soundness of the `DIV` rows.** Every run of the rows, for every advice, from a state
whose output buffer lies in RAM, meets `FieldDivSpec` for the modulus of the layout. This holds
when `rs3` equals `rs1`: the dividend in the specification is read before the call.
Example: for `DIVQ` with `a = 1` at `x10 = 0x8001_0000` and `b = 2` at `x11 = 0x8001_0020`,
every run, for any advice, stores `c = (p+1)/2`: it is the only `c < 2^256` with
`2c = w·p + 1` for some `w < 2^256`. -/
theorem divRows_sound {scalar : Bool} {L : MulRegs} (hv : L.Valid .div scalar)
    {rs1 rs2 rs3 : regidx} {advice : Nat → BitVec 64} {s s' : SailJoltState}
    (buf : FieldMulBuffer rs3 s)
    (run : (Program.seq (mulRows .div scalar L rs1 rs2 rs3 advice)).Run s s') :
    FieldDivSpec (if scalar then n else p) rs1 rs2 rs3 s s' := by
  rw [mulRows_eq_append, tailRows_div] at run
  -- The prologue: read the divisor.
  have h2 : XReads s rs2 (sourceValue (.xreg rs2) s) := by
    have h := run
    simp only [prologueRows, List.flatMap_cons, ldRow, List.cons_append] at h
    exact XReads.of_run_ld h
  change (Program.seq _).Run { s with vregs := s.vregs } s' at run
  obtain ⟨y, hy, tail⟩ := (run_prologue_div_iff hv h2 _ _ _).1 run
  -- The checks.
  have h1 := checks_reads1 hv tail
  obtain ⟨R0, R1, R2, R3, R4, R5, R6, C, G, heq, hG, hiff⟩ :=
    run_checks_div_iff (rs3 := rs3) hv h1 (writeAll s.vregs (preWrites .div scalar L y y advice))
  obtain ⟨hx, e4, e5, e6, e7, hle, rest⟩ := (hiff _ s').1 tail
  -- The stores.
  have h3 : XReads s rs3 (fieldOut rs3 s) := by
    have h := rest
    simp only [storeRows, List.map_cons, sdRow, List.cons_append] at h
    exact XReads.of_run_sd (s := { s with vregs := G }) h
  have hpool : ∀ r ∈ L.pool, 32 ≤ r.toNat := by
    intro r hr
    simp only [MulRegs.pool, List.mem_map, List.mem_range] at hr
    obtain ⟨i, hi, rfl⟩ := hr
    exact hv.pool i hi
  obtain ⟨V, hst⟩ := run_store_div_iff hpool h3 buf.ram buf.no_wrap G
  obtain ⟨hw, rfl⟩ := (hst s').1 rest
  -- The arithmetic.
  have oa : ∀ i, i < 4 → L.OpFree (L.a i) := by
    intro i hi
    apply hv.pre_free
    interval_cases i <;> cases scalar <;> simp [preRegs]
  obtain ⟨-, fb, -, fp, fp2⟩ := pre_vals_div hv y advice s.vregs
  have hct := colTotal_eq (op := .div) (fun h => absurd h (by decide)) fp fp2
  set F := writeAll s.vregs (preWrites .div scalar L y y advice)
  set H := jolt_mulhu_value (F (L.a 3)) (F (L.b 3))
  have hCH := toNat_add_of_le hle
  rw [e7] at hCH
  rw [hG _ (oa 0 (by decide)), hG _ (oa 1 (by decide)), hG _ (oa 2 (by decide)),
    hG _ (oa 3 (by decide))]
  have hA : limbVal L.a F = limbsToNat #v[F (L.a 0), F (L.a 1), F (L.a 2), F (L.a 3)] := rfl
  have hW : limbVal L.w F = limbsToNat #v[F (L.w 0), F (L.w 1), F (L.w 2), F (L.w 3)] := rfl
  have hc : limbsToNat #v[R0, R1, R2, R3] =
      R0.toNat + 2 ^ 64 * R1.toNat + 2 ^ 128 * R2.toNat + 2 ^ 192 * R3.toNat := rfl
  have hq : (if scalar then n else p) ≤ 2 ^ 256 := by cases scalar <;> decide
  refine ⟨#v[R0, R1, R2, R3], y, #v[F (L.w 0), F (L.w 1), F (L.w 2), F (L.w 3)],
    #v[F (L.a 0), F (L.a 1), F (L.a 2), F (L.a 3)], hx, hy,
    ⟨?_, limbsToNat_lt _, limbsToNat_lt _⟩, ⟨V, rfl⟩, fun i hi => ?_⟩
  · rw [← rows_identity_iff _ _ _ _ _ hq, ← hA, ← fb, ← hW, hc, ← hct, ← heq]
    simp only [limbVal]
    subst e4 e5 e6
    omega
  · let m' := writeDwords s.sail.mem (fieldOut rs3 s).toNat
      (#v[F (L.a 0), F (L.a 1), F (L.a 2), F (L.a 3)] : Limbs).toList
    exact loadDword?_of_mem_writeDwords
      (t := { s with vregs := V, sail := { s.sail with mem := m' } }) rfl buf.ram
      (by simpa using buf.no_wrap)
      (fun j hj => hw j (by simpa using hj)) (by simpa using hi)

/-! ## Completeness with Jolt's advice -/

/-- Jolt's division advice exists for a divisor coprime to the modulus, and it is a canonical
solution: for a dividend `a < q`, the result `c` and quotient `w` satisfy `c·b = w·q + a` and
`c < q`.
Example: for `q = p`, `a = 1`, `b = 2`, the advice is `c = (p+1)/2`, `w = 1`, and
`(p+1)/2 · 2 = 1·p + 1`. -/
theorem mulqDivisionAdvice_spec {q : Nat} (hq1 : 1 < q) (hq : q ≤ 2 ^ 256) {a b : Limbs}
    (ha : limbsToNat a < q) (hcop : Nat.Coprime (limbsToNat b) q) :
    ∃ c w, mulqDivisionAdvice q a b = some (c, w) ∧
      limbsToNat c * limbsToNat b = limbsToNat w * q + limbsToNat a ∧ limbsToNat c < q := by
  have : NeZero q := ⟨by omega⟩
  have hb0 : limbsToNat b % q ≠ 0 := by
    intro h
    have hd : q ∣ Nat.gcd (limbsToNat b) q :=
      Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero h) (dvd_refl q)
    rw [hcop.gcd_eq_one] at hd
    have := Nat.le_of_dvd (by decide) hd
    omega
  set r := ((limbsToNat a : ZMod q) * (limbsToNat b : ZMod q)⁻¹).val with hr
  have hrq : r < q := ZMod.val_lt _
  have hqt : limbsToNat b * r / q < 2 ^ 256 := by
    have hb := limbsToNat_lt b
    have : limbsToNat b * r / q ≤ limbsToNat b :=
      Nat.div_le_of_le_mul (by rw [Nat.mul_comm q]; exact Nat.mul_le_mul_left _ hrq.le)
    omega
  have hinv : fieldInvMul q b a = some r := by
    simp only [fieldInvMul, hb0, ↓reduceIte, ← hr]
  have hadv : mulqDivisionAdvice q a b =
      some (natToLimbs r, natToLimbs (limbsToNat b * r / q)) := by
    simp only [mulqDivisionAdvice, hinv, fieldLimbs?, show r < 2 ^ 256 by omega, hqt,
      ↓reduceIte, Option.bind_eq_bind, Option.bind_some]
    rfl
  -- `b·r ≡ a (mod q)`.
  have hmod : limbsToNat b * r % q = limbsToNat a := by
    have e : ((limbsToNat b * r : ℕ) : ZMod q) = (limbsToNat a : ZMod q) := by
      rw [Nat.cast_mul, hr, ZMod.natCast_zmod_val, mul_left_comm, ZMod.mul_inv_eq_gcd,
        ZMod.val_natCast, ← Nat.gcd_rec, hcop.symm.gcd_eq_one, Nat.cast_one, mul_one]
    have := congrArg ZMod.val e
    rwa [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt ha] at this
  refine ⟨_, _, hadv, ?_, ?_⟩
  · rw [limbsToNat_natToLimbs, limbsToNat_natToLimbs, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt hqt, Nat.mul_comm r, ← hmod, Nat.mul_comm _ q]
    exact (Nat.div_add_mod _ _).symm
  · rw [limbsToNat_natToLimbs, Nat.mod_eq_of_lt (by omega)]
    exact hrq

/-- **Completeness of the `DIV` rows with Jolt's advice.** For a call that meets its
obligations, with a dividend `a < q` and a divisor `b` nonzero modulo `q`, Jolt's division advice
exists, and the rows run with it (result and quotient words interleaved, as
`divisionWords` orders them); the end state meets the specification, and the stored result is
`a·b⁻¹ mod q`, which is below `q`.
Example: for `DIVQ` with `a = 1` at `x10 = 0x8001_0000` and `b = 2` at `x11 = 0x8001_0020`,
the advice words start `0xffffffff7ffffe18, 1` (the low limbs of `c = (p+1)/2` and `w = 1`),
and the rows store `(p+1)/2`. -/
theorem divRows_jolt_advice_complete {scalar : Bool} {L : MulRegs} (hv : L.Valid .div scalar)
    {rs1 rs2 rs3 : regidx} {s : SailJoltState} (pre : FieldMulPre .div rs1 rs2 rs3 s)
    {a b : Limbs} (ha : readLimbs? s (sourceValue (.xreg rs1) s) = some a)
    (hb : readLimbs? s (sourceValue (.xreg rs2) s) = some b)
    (hca : limbsToNat a < (if scalar then n else p))
    (hb0 : limbsToNat b % (if scalar then n else p) ≠ 0) :
    ∃ c w, mulqDivisionAdvice (if scalar then n else p) a b = some (c, w) ∧
      ∃ s', (Program.seq (mulRows .div scalar L rs1 rs2 rs3
          (fun i => (divisionWords c w).getD i 0))).Run s s' ∧
        FieldDivSpec (if scalar then n else p) rs1 rs2 rs3 s s' ∧
        FieldMulCanonical (if scalar then n else p) rs3 s s' := by
  set q := if scalar then n else p with hqdef
  have hq : q ≤ 2 ^ 256 := by rw [hqdef]; cases scalar <;> decide
  have hq1 : 1 < q := by rw [hqdef]; cases scalar <;> decide
  have hqp : q.Prime := by rw [hqdef]; cases scalar; exacts [p_prime, n_prime]
  obtain ⟨c, w, hcw, rel, hcq⟩ :=
    mulqDivisionAdvice_spec hq1 hq hca (coprime_of_mod_ne_zero hqp hb0)
  set advice : Nat → BitVec 64 := fun i => (divisionWords c w).getD i 0
  -- The register file after the prologue.
  obtain ⟨fa, fb, fw, fp, fp2⟩ := pre_vals_div hv b advice s.vregs
  set F := writeAll s.vregs (preWrites .div scalar L b b advice)
  have hA : limbVal L.a F = limbsToNat c := by
    simp only [limbVal, limbsToNat, fa 0 (by decide), fa 1 (by decide), fa 2 (by decide),
      fa 3 (by decide)]
    rfl
  have hW : limbVal L.w F = limbsToNat w := by
    simp only [limbVal, limbsToNat, fw 0 (by decide), fw 1 (by decide), fw 2 (by decide),
      fw 3 (by decide)]
    rfl
  have hct := colTotal_eq (op := .div) (fun h => absurd h (by decide)) fp fp2
  obtain ⟨R0, R1, R2, R3, R4, R5, R6, C, G, heq, hG, hiff⟩ :=
    run_checks_div_iff (rs3 := rs3) hv pre.reads1 F
  set H := jolt_mulhu_value (F (L.a 3)) (F (L.b 3))
  -- The digits of the column sum.
  have hid : limbsToNat c * limbsToNat b + limbsToNat w * pPrime q =
      limbsToNat a + 2 ^ 256 * limbsToNat w :=
    (rows_identity_iff _ _ _ _ _ hq).2 rel
  have hwF : limbsToNat w = (F (L.w 0)).toNat + 2 ^ 64 * (F (L.w 1)).toNat +
      2 ^ 128 * (F (L.w 2)).toNat + 2 ^ 192 * (F (L.w 3)).toNat := by
    rw [← hW]; rfl
  rw [hct, hA, fb, hW, hid, hwF] at heq
  obtain ⟨hlo, d4, d5, d6, d7, hle⟩ := column_digits heq (limbsToNat_lt a)
  have hx : readLimbs? s (sourceValue (.xreg rs1) s) = some #v[R0, R1, R2, R3] := by
    rw [ha, limbs_eq_of_limbsToNat_eq (x := a) (y := #v[R0, R1, R2, R3]) hlo.symm]
  -- The run.
  have hpool : ∀ r ∈ L.pool, 32 ≤ r.toNat := by
    intro r hr
    simp only [MulRegs.pool, List.mem_map, List.mem_range] at hr
    obtain ⟨i, hi, rfl⟩ := hr
    exact hv.pool i hi
  obtain ⟨V, hst⟩ := run_store_div_iff hpool pre.reads3 pre.ram pre.no_wrap G
  set m1 := writeDwords s.sail.mem (fieldOut rs3 s).toNat
    [G (L.a 0), G (L.a 1), G (L.a 2), G (L.a 3)]
  set s1 : SailJoltState := { s with vregs := V, sail := { s.sail with mem := m1 } }
  have rest := (hst s1).2 ⟨pre.writable, rfl⟩
  have checks := (hiff _ s1).2 ⟨hx, d4, d5, d6, d7, hle, rest⟩
  have run : (Program.seq (mulRows .div scalar L rs1 rs2 rs3 advice)).Run s s1 := by
    rw [mulRows_eq_append, tailRows_div]
    exact (run_prologue_div_iff hv (pre.reads2 (by decide)) _ _ _).2 ⟨b, hb, checks⟩
  have oa : ∀ i, i < 4 → L.OpFree (L.a i) := by
    intro i hi
    apply hv.pre_free
    interval_cases i <;> cases scalar <;> simp [preRegs]
  refine ⟨c, w, hcw, s1, run, divRows_sound hv pre.toFieldMulBuffer run,
    #v[G (L.a 0), G (L.a 1), G (L.a 2), G (L.a 3)], ?_, fun i hi => ?_⟩
  · show limbsToNat #v[G (L.a 0), G (L.a 1), G (L.a 2), G (L.a 3)] < q
    rw [hG _ (oa 0 (by decide)), hG _ (oa 1 (by decide)), hG _ (oa 2 (by decide)),
      hG _ (oa 3 (by decide))]
    change limbVal L.a F < q
    rw [hA]
    exact hcq
  · exact loadDword?_of_mem_writeDwords (t := s1) rfl pre.ram (by simpa using pre.no_wrap)
      (fun j hj => pre.writable j (by simpa using hj)) (by simpa using hi)

/-! ## The two layouts -/

/-- The `SECP256K1_DIVQ` layout, which is the `MULQ` layout, meets the conditions of the
proofs for division.
Example: its result, divisor, quotient and constant registers are the distinct pool registers
`vr48..vr60`. -/
theorem divqRegs_valid : mulqRegs.Valid .div false where
  pre_nodup := by decide
  pre_ge := by decide
  pre_free := by decide
  col0 := by decide
  col1 := by decide
  terms := by decide
  square := fun h => absurd h (by decide)
  pool := by decide

/-- The `SECP256K1_DIVR` layout, which is the `MULR` layout, meets the conditions of the
proofs for division.
Example: its result, divisor, quotient and constant registers `vr48..vr61` are distinct and
differ from the column registers `vr62`, `vr63`, `vr64` and `vr127`. -/
theorem divrRegs_valid : mulrRegs.Valid .div true where
  pre_nodup := by decide
  pre_ge := by decide
  pre_free := by decide
  col0 := by decide
  col1 := by decide
  terms := by decide
  square := fun h => absurd h (by decide)
  pool := by decide

/-! ## The two inlines -/

/-- **Soundness of `SECP256K1_DIVQ`.** Every run of the rows, for every advice, from a state
whose output buffer lies in RAM, stores at `rs3` a value `c` with `c·b = w·p + a` for some
`w < 2^256`, where the dividend `a` and the divisor `b` are read at `rs1` and `rs2` before the
call; only virtual registers and the output buffer change. This holds when `rs3 = rs1`.
Example: with `a = 1` at `x10 = 0x8001_0000`, `b = 2` at `x11 = 0x8001_0020` and the buffer at
`x12 = 0x8002_0000`, every run stores some `c ≡ (p+1)/2 (mod p)`. -/
theorem secp256k1Divq_rows_sound {rs1 rs2 rs3 : regidx} {advice : Nat → BitVec 64}
    {s s' : SailJoltState} (buf : FieldMulBuffer rs3 s)
    (run : (secp256k1DivqRowsAuto rs1 rs2 rs3 advice).Run s s') :
    FieldDivSpec p rs1 rs2 rs3 s s' := by
  unfold secp256k1DivqRowsAuto at run
  rw [secp256k1DivqRowsAutoList_eq] at run
  exact divRows_sound divqRegs_valid buf run

/-- **Completeness of `SECP256K1_DIVQ` with Jolt's advice.** For a call that meets its
obligations, with a dividend below `p` and a divisor nonzero modulo `p`, Jolt's advice exists and
the rows run with it; the end state meets the specification, and the stored result is below
`p`.
Example: with `a = 1` at `x10 = 0x8001_0000`, `b = 2` at `x11 = 0x8001_0020` and the buffer at
`x12 = 0x8002_0000`, the rows run with advice `c = (p+1)/2`, `w = 1` and store `(p+1)/2`. -/
theorem secp256k1Divq_rows_jolt_advice_complete {rs1 rs2 rs3 : regidx} {s : SailJoltState}
    (pre : FieldMulPre .div rs1 rs2 rs3 s) {a b : Limbs}
    (ha : readLimbs? s (sourceValue (.xreg rs1) s) = some a)
    (hb : readLimbs? s (sourceValue (.xreg rs2) s) = some b)
    (hca : limbsToNat a < p) (hb0 : limbsToNat b % p ≠ 0) :
    ∃ ws, joltAdvice .divq a b = some ws ∧
      ∃ s', (secp256k1DivqRowsAuto rs1 rs2 rs3 (fun i => ws.getD i 0)).Run s s' ∧
        FieldDivSpec p rs1 rs2 rs3 s s' ∧ FieldMulCanonical p rs3 s s' := by
  obtain ⟨c, w, hcw, s', run, spec, can⟩ :=
    divRows_jolt_advice_complete (L := mulqRegs) divqRegs_valid pre ha hb hca hb0
  refine ⟨divisionWords c w, ?_, s', ?_, spec, can⟩
  · show (fun cw => divisionWords cw.1 cw.2) <$> mulqDivisionAdvice p a b = _
    rw [show mulqDivisionAdvice p a b = some (c, w) from hcw]
    rfl
  · unfold secp256k1DivqRowsAuto
    rw [secp256k1DivqRowsAutoList_eq]
    exact run

/-- **Soundness of `SECP256K1_DIVR`.** As `secp256k1Divq_rows_sound`, modulo `n`: every run
stores some `c` with `c·b = w·n + a`.
Example: with `a = 1` and `b = 2`, every run stores some `c ≡ (n+1)/2 (mod n)`. -/
theorem secp256k1Divr_rows_sound {rs1 rs2 rs3 : regidx} {advice : Nat → BitVec 64}
    {s s' : SailJoltState} (buf : FieldMulBuffer rs3 s)
    (run : (secp256k1DivrRowsAuto rs1 rs2 rs3 advice).Run s s') :
    FieldDivSpec n rs1 rs2 rs3 s s' := by
  unfold secp256k1DivrRowsAuto at run
  rw [secp256k1DivrRowsAutoList_eq] at run
  exact divRows_sound divrRegs_valid buf run

/-- **Completeness of `SECP256K1_DIVR` with Jolt's advice.** As
`secp256k1Divq_rows_jolt_advice_complete`, modulo `n`.
Example: with `a = 1` and `b = 2`, the rows run with advice `c = (n+1)/2`, `w = 1` and store
`(n+1)/2`. -/
theorem secp256k1Divr_rows_jolt_advice_complete {rs1 rs2 rs3 : regidx} {s : SailJoltState}
    (pre : FieldMulPre .div rs1 rs2 rs3 s) {a b : Limbs}
    (ha : readLimbs? s (sourceValue (.xreg rs1) s) = some a)
    (hb : readLimbs? s (sourceValue (.xreg rs2) s) = some b)
    (hca : limbsToNat a < n) (hb0 : limbsToNat b % n ≠ 0) :
    ∃ ws, joltAdvice .divr a b = some ws ∧
      ∃ s', (secp256k1DivrRowsAuto rs1 rs2 rs3 (fun i => ws.getD i 0)).Run s s' ∧
        FieldDivSpec n rs1 rs2 rs3 s s' ∧ FieldMulCanonical n rs3 s s' := by
  obtain ⟨c, w, hcw, s', run, spec, can⟩ :=
    divRows_jolt_advice_complete (L := mulrRegs) divrRegs_valid pre ha hb hca hb0
  refine ⟨divisionWords c w, ?_, s', ?_, spec, can⟩
  · show (fun cw => divisionWords cw.1 cw.2) <$> mulqDivisionAdvice n a b = _
    rw [show mulqDivisionAdvice n a b = some (c, w) from hcw]
    rfl
  · unfold secp256k1DivrRowsAuto
    rw [secp256k1DivrRowsAutoList_eq]
    exact run

end JoltISA.Inlines.Secp256k1
