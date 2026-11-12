import JoltBytecode.Inlines.AdviceStores
import JoltBytecode.Inlines.Secp256k1.GlvBound
import JoltBytecode.Inlines.Generated.Secp256k1GlvrAdv

/-!
# `SECP256K1_GLVR_ADV`: soundness and completeness of the rows

`GLVR_ADV` has 13 rows. For each of six advice words it writes the word to `vr48` and stores
`vr48` to the output buffer at `rs3`; the last row resets `vr48` to zero. No row checks a word,
so the rows admit any six words (section 5.3 of `docs/inline-precompiles.md`).

* `glvrAdv_rows_sound`: every run from a state whose output buffer lies in RAM writes six
  words there, resets `vr48`, and changes nothing else (`GlvrAdvSpec`).
* `glvrAdv_rows_jolt_advice_complete`: with Jolt's advice for the scalar `k` read at `rs1`
  (`glvrAdvice`), the rows run, and the six words read back are `glvrAdvice k`
  (`GlvrAdvCanonical`).
* `glvrAdvice_correct`: those six words are two sign words in `{0, 1}` and two 128-bit
  magnitudes with `±k₁ ± λ·k₂ ≡ k (mod n)`, the identity the SDK checks after the call.

The per-call definitions live here until the generic `InlineCall`, `Pre` and `InlineSpec` of
section 5.4 exist.
-/

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail LeanRV64D
  LeanRV64D.Functions JoltISA.Inlines.Generated

set_option autoImplicit false

noncomputable section

namespace JoltISA.Inlines.Secp256k1

/-! ## Calls -/

/-- The six advice words in row order.
Example: `glvrWords (glvrAdvAdvice (natToLimbs 1)) = [0, 1, 0, 0, 0, 0]`. -/
def glvrWords (advice : Nat → BitVec 64) : List (BitVec 64) :=
  [advice 0, advice 1, advice 2, advice 3, advice 4, advice 5]

/-- The generated rows are the advice-store rows for the six words, then `ADDI vr48, x0, 0`.
Example: row 1 is `SD rs3, vr48, 0` and row 11 is `SD rs3, vr48, 40`. -/
theorem glvrAdvRowsAutoList_eq (rs1 rs2 rs3 : regidx) (advice : Nat → BitVec 64) :
    secp256k1GlvrAdvRowsAutoList rs1 rs2 rs3 advice =
      adviceStoreRows rs3 (BitVec.ofNat 7 48) 0 (glvrWords advice) ++
        [.ADDI (.vreg (BitVec.ofNat 7 48)) (.xreg (regidx.Regidx 0)) 0] := rfl

/-- The output buffer of a `GLVR_ADV` call: the address in `rs3`.
Example: `0x8002_0000` when `x12 = 0x8002_0000` and `rs3 = x12`. -/
abbrev glvrOut (rs3 : regidx) (s : SailJoltState) : BitVec 64 := sourceValue (.xreg rs3) s

/-- Where the output buffer must lie for soundness: in RAM, with its 48 bytes below `2^64`.
Example: a buffer at `0x8002_0000` meets it; one at `0x1000` (below RAM) does not. -/
structure GlvrAdvBuffer (rs3 : regidx) (s : SailJoltState) : Prop where
  ram : RAM_START_ADDRESS ≤ (glvrOut rs3 s).toNat
  no_wrap : (glvrOut rs3 s).toNat + 48 ≤ 2 ^ 64

/-- The caller's obligations for a `GLVR_ADV` call: the buffer conditions, a readable `rs3`,
and six aligned doublewords that Jolt may store to.
Example: `JoltTests.GlvrAdvInstance.kat_pre`, a buffer at `0x8002_0000` on a heap that ends at
`0x8010_0000`. -/
structure GlvrAdvPre (rs3 : regidx) (s : SailJoltState) : Prop extends GlvrAdvBuffer rs3 s where
  reads : XReads s rs3 (glvrOut rs3 s)
  writable : ∀ k < 6, DwordWritable s.jolt_device ((glvrOut rs3 s).toNat + 8 * k)

/-- What a `GLVR_ADV` call may do: store some six words `ws` at the output buffer and reset
`vr48`; nothing else changes, and loading doubleword `i` of the buffer afterwards returns
`ws[i]`.
Example: with `ws = [0, 1, 0, 0, 0, 0]` (Jolt's split of `k = 1`), loading the buffer's second
doubleword returns `1`. -/
def GlvrAdvSpec (rs3 : regidx) (s s' : SailJoltState) : Prop :=
  ∃ ws : List (BitVec 64), ws.length = 6 ∧
    s' = { s with vregs := setV s.vregs (BitVec.ofNat 7 48) 0,
                  sail := { s.sail with
                    mem := writeDwords s.sail.mem (glvrOut rs3 s).toNat ws } } ∧
    ∀ i < 6, loadDword? s' (glvrOut rs3 s + BitVec.ofNat 64 (8 * i)) = ws[i]?

/-! ## Running the rows -/

/-- The state after the rows with advice `advice`.
Example: for `advice = glvrAdvAdvice (natToLimbs 1)`, the buffer holds `[0, 1, 0, 0, 0, 0]`
and `vr48 = 0`. -/
def glvrAdvFinal (rs3 : regidx) (advice : Nat → BitVec 64) (s : SailJoltState) :
    SailJoltState :=
  { s with vregs := setV s.vregs (BitVec.ofNat 7 48) 0,
           sail := { s.sail with
             mem := writeDwords s.sail.mem (glvrOut rs3 s).toNat (glvrWords advice) } }

/-- Given a readable `rs3` and a buffer in RAM, the rows run exactly when the six target
doublewords are writable, and they end in `glvrAdvFinal`.
Example: with the stack ending at `0x8000_1000`, the stack canary is `0x8000_1000..0x8000_1080`.
A buffer at `0x8000_0ff8` has its first doubleword below the canary, which is writable, and its
second at `0x8000_1000`, in the canary, which is not; so the rows have no run. -/
theorem glvrAdv_run_iff {rs1 rs2 rs3 : regidx} {advice : Nat → BitVec 64}
    {s s' : SailJoltState} (buf : GlvrAdvBuffer rs3 s) (hr : XReads s rs3 (glvrOut rs3 s)) :
    (secp256k1GlvrAdvRowsAuto rs1 rs2 rs3 advice).Run s s' ↔
      (∀ k < 6, DwordWritable s.jolt_device ((glvrOut rs3 s).toNat + 8 * k)) ∧
        s' = glvrAdvFinal rs3 advice s := by
  unfold secp256k1GlvrAdvRowsAuto
  rw [glvrAdvRowsAutoList_eq,
    run_adviceStoreRows_iff (by decide) buf.ram 0 _ s hr
      (by simp only [glvrWords, List.length_cons, List.length_nil]; have := buf.no_wrap; omega)]
  have hreg : ∀ f : VReg → BitVec 64,
      regRun [.ADDI (.vreg (BitVec.ofNat 7 48)) (.xreg (regidx.Regidx 0)) 0] f =
        some (setV f (BitVec.ofNat 7 48) (0 + 0)) := fun f => rfl
  rw [← List.append_nil [Instr.ADDI _ _ _], run_append_of_regRun (hreg _), run_nil_iff]
  simp only [Nat.add_zero, afterStores_setV]
  rfl

/-- **Soundness of `GLVR_ADV`.** Every run of the rows, for every advice, from a state whose
output buffer lies in RAM, stores six words at the buffer, resets `vr48`, and changes nothing
else; the six words read back.
Example: with `rs3 = x12 = 0x8002_0000` and a heap ending at `0x8010_0000`, every run stores six
words at `0x8002_0000..0x8002_0030`, sets `vr48` to `0`, and leaves `x10`, `x12` and the rest
of RAM as they were (`JoltTests.GlvrAdvInstance.glvrAdv_kat`). -/
theorem glvrAdv_rows_sound {rs1 rs2 rs3 : regidx} {advice : Nat → BitVec 64}
    {s s' : SailJoltState} (buf : GlvrAdvBuffer rs3 s)
    (run : (secp256k1GlvrAdvRowsAuto rs1 rs2 rs3 advice).Run s s') :
    GlvrAdvSpec rs3 s s' := by
  have hr : XReads s rs3 (glvrOut rs3 s) := by
    have h := run
    unfold secp256k1GlvrAdvRowsAuto at h
    rw [glvrAdvRowsAutoList_eq, glvrWords, adviceStoreRows, List.cons_append, seq_cons,
      run_instr_iff (execInstr_of_regRow rfl (by decide) s)] at h
    exact XReads.of_run_sd (s := { s with vregs := setV s.vregs (BitVec.ofNat 7 48) (advice 0) }) h
  obtain ⟨hall, rfl⟩ := (glvrAdv_run_iff buf hr).1 run
  refine ⟨glvrWords advice, rfl, rfl, fun i hi => ?_⟩
  exact loadDword?_of_mem_writeDwords (t := glvrAdvFinal rs3 advice s) rfl buf.ram
    (by simp only [glvrWords, List.length_cons, List.length_nil]; have := buf.no_wrap; omega)
    (fun j hj => hall j (by simpa [glvrWords] using hj)) (by simpa [glvrWords] using hi)

/-! ## Completeness with Jolt's advice -/

/-- The four little-endian limbs at address `a`, or `none` when a load fails.
Example: if RAM holds the words `1, 2, 3, 4` at `a`, `a + 8`, `a + 16` and `a + 24`, the result
is `some #v[1, 2, 3, 4]`. -/
def readLimbs? (s : SailJoltState) (a : BitVec 64) : Option Limbs := do
  let l0 ← loadDword? s a
  let l1 ← loadDword? s (a + 8)
  let l2 ← loadDword? s (a + 16)
  let l3 ← loadDword? s (a + 24)
  pure #v[l0, l1, l2, l3]

/-- Jolt's advice for the scalar `k` as row advice: `VirtualAdvice` row `i` writes word `i`
of `glvrAdvice k`.
Example: `glvrAdvAdvice (natToLimbs 1) 1 = 1`, and every index from `6` on gives `0`. -/
def glvrAdvAdvice (k : Limbs) (i : Nat) : BitVec 64 :=
  if h : i < 6 then (glvrAdvice k)[i] else 0

/-- The output of Jolt's advice for the scalar `k`: doubleword `i` of the buffer reads word `i`
of `glvrAdvice k`.
Example: for `k = 1`, the buffer reads `[0, 1, 0, 0, 0, 0]`. -/
def GlvrAdvCanonical (k : Limbs) (rs3 : regidx) (s s' : SailJoltState) : Prop :=
  ∀ i (hi : i < 6), loadDword? s' (glvrOut rs3 s + BitVec.ofNat 64 (8 * i)) =
    some (glvrAdvice k)[i]

/-- **Completeness of `GLVR_ADV` with Jolt's advice.** For a call that meets its obligations,
whose scalar at `rs1` has limbs `k`, the rows run with Jolt's advice for `k`; the end state
meets the specification, and the six stored words are `glvrAdvice k`.
Example: for the scalar `k` with limbs `0x0123456789abcdef, 0xfedcba9876543210,
0x0f1e2d3c4b5a6978, 0x1122334455667788` at `x10 = 0x8001_0000` and the buffer at
`x12 = 0x8002_0000`, the rows run and store `[1, 0x2e4cbe1fe695c34d, 0x213c3de8a76e3bd1, 0,
0xb2eae28114375049, 0x08fc4249719076b4]` (`JoltTests.GlvrAdvInstance.glvrAdv_kat`). -/
theorem glvrAdv_rows_jolt_advice_complete {rs1 rs2 rs3 : regidx} {s : SailJoltState}
    {k : Limbs} (pre : GlvrAdvPre rs3 s)
    (_hk : readLimbs? s (sourceValue (.xreg rs1) s) = some k) :
    ∃ s', (secp256k1GlvrAdvRowsAuto rs1 rs2 rs3 (glvrAdvAdvice k)).Run s s' ∧
      GlvrAdvSpec rs3 s s' ∧ GlvrAdvCanonical k rs3 s s' := by
  have run : (secp256k1GlvrAdvRowsAuto rs1 rs2 rs3 (glvrAdvAdvice k)).Run s
      (glvrAdvFinal rs3 (glvrAdvAdvice k) s) :=
    (glvrAdv_run_iff pre.toGlvrAdvBuffer pre.reads).2 ⟨pre.writable, rfl⟩
  have spec := glvrAdv_rows_sound pre.toGlvrAdvBuffer run
  refine ⟨_, run, spec, fun i hi => ?_⟩
  rw [loadDword?_of_mem_writeDwords (t := glvrAdvFinal rs3 (glvrAdvAdvice k) s) rfl pre.ram
    (by simp only [glvrWords, List.length_cons, List.length_nil]; have := pre.no_wrap; omega)
    (fun j hj => pre.writable j (by simpa [glvrWords] using hj)) (by simpa [glvrWords] using hi)]
  interval_cases i <;> rfl

/-- **What Jolt's advice stores.** The six words of `glvrAdvice k` are two sign words in
`{0, 1}` and two 128-bit magnitudes `k₁ = v[1] + 2^64·v[2]` and `k₂ = v[4] + 2^64·v[5]` with
`±k₁ ± λ·k₂ ≡ k (mod n)`, the recombination identity the SDK checks after the call.
Example: `glvrAdvice (natToLimbs 1) = #v[0, 1, 0, 0, 0, 0]`, so `k₁ = 1`, `k₂ = 0`. -/
theorem glvrAdvice_correct (k : Limbs) :
    let v := glvrAdvice k
    (v[0].toNat = 0 ∨ v[0].toNat = 1) ∧ (v[3].toNat = 0 ∨ v[3].toNat = 1) ∧
    v[1].toNat + 2 ^ 64 * v[2].toNat < 2 ^ 128 ∧ v[4].toNat + 2 ^ 64 * v[5].toNat < 2 ^ 128 ∧
    ((if v[0].toNat = 1 then -1 else 1) * ((v[1].toNat + 2 ^ 64 * v[2].toNat : Nat) : Int) +
      (glvLambda : Int) *
        ((if v[3].toNat = 1 then -1 else 1) * ((v[4].toNat + 2 ^ 64 * v[5].toNat : Nat) : Int))
      - (limbsToNat k : Int)) % (n : Int) = 0 := by
  intro v
  have hv : v = decomposeScalarToU64s ((limbsToNat k % n : Nat) : Int) := rfl
  obtain ⟨hs1, hs2, hrec⟩ :=
    decomposeScalarToU64s_correct ((limbsToNat k % n : Nat) : Int) (Int.natCast_nonneg _)
  rw [← hv] at hs1 hs2 hrec
  have b1 := v[1].isLt
  have b2 := v[2].isLt
  have b4 := v[4].isLt
  have b5 := v[5].isLt
  refine ⟨hs1, hs2, by omega, by omega, ?_⟩
  apply Int.emod_eq_zero_of_dvd
  have h1 := Int.dvd_of_emod_eq_zero hrec
  have h2 : (n : Int) ∣ ((limbsToNat k % n : Nat) : Int) - (limbsToNat k : Int) := by
    rw [Int.natCast_mod, Int.emod_def]
    exact ⟨-(limbsToNat k / n : Int), by ring⟩
  have := dvd_add h1 h2
  convert this using 1
  ring

end JoltISA.Inlines.Secp256k1
