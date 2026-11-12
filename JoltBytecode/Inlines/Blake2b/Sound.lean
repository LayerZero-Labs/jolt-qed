import JoltBytecode.Inlines.Blake2b.Blocks
import JoltBytecode.Inlines.Blake2b.Shape
import JoltBytecode.Inlines.FrameInstances

/-!
# `BLAKE2`: soundness, completeness and determinism of the rows

A `BLAKE2` call compresses one 128-byte message block into the state. Register `rs1` holds the
address `A` of the 8-doubleword state `h`, and `rs2` holds the address `B` of the 16-doubleword
message block, followed by the counter at `B + 128` and the final-block flag at `B + 136`. The
rows load all 26 doublewords, run the 12 rounds of `G` on the work vector, store the new state
at `A`, and reset the pool registers `vr48..87`. No row reads advice.

* `blake2_run_iff`: from a state in which `rs1` reads `A` and `rs2` reads `B`, with the state
  buffer in RAM, the rows run exactly when all 26 loads succeed and the 8 stores are allowed,
  and they end in `blake2Final`.
* `blake2_rows_sound`: every run from a state whose state buffer lies in RAM ends in
  `blake2Final`, and the 8 doublewords at `A` read back the computed state (`Blake2Spec`).
* `blake2_rows_sound_compress`: when the flag is 0 or 1, those 8 doublewords are
  `Spec.compress 12` of the loaded state, block, counter and flag.
* `blake2_rows_complete`: under `Blake2Pre` the rows run, and the end state meets `Blake2Spec`.
* `blake2_rows_deterministic`: two runs from the same state end in the same state.
* The same four for the `rd = x0` rows, which are the same rows.

The frame and the pool reset of every run are `FrameInstances.blake2_frame` and
`FrameInstances.blake2_resetsPool`.

The per-call definitions live here until the generic `InlineCall`, `Pre` and `InlineSpec` of
section 5.4 of `docs/inline-precompiles.md` exist.
-/

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail LeanRV64D
  LeanRV64D.Functions JoltISA.Inlines.Generated

set_option autoImplicit false

noncomputable section

namespace JoltISA.Inlines.Blake2b

open JoltSpec.Blake2b

/-! ## Calls -/

/-- The state buffer of a call: the address in `rs1`.
Example: `0x8002_0000` when `x10 = 0x8002_0000` and `rs1 = x10`. -/
abbrev blake2H (rs1 : regidx) (s : SailJoltState) : BitVec 64 := sourceValue (.xreg rs1) s

/-- The message buffer of a call: the address in `rs2`. -/
abbrev blake2M (rs2 : regidx) (s : SailJoltState) : BitVec 64 := sourceValue (.xreg rs2) s

/-- The inputs of a call: what the loads read from the two buffers. -/
abbrev blake2Input (rs1 rs2 : regidx) (s : SailJoltState) : Input :=
  input s (blake2H rs1 s) (blake2M rs2 s)

/-- Where the state buffer must lie for soundness: in RAM, with its 64 bytes below `2^64`.
Example: a buffer at `0x8002_0000` meets it; one at `0x1000` (below RAM) does not. -/
structure Blake2Buffer (rs1 : regidx) (s : SailJoltState) : Prop where
  ram : RAM_START_ADDRESS ≤ (blake2H rs1 s).toNat
  no_wrap : (blake2H rs1 s).toNat + 64 ≤ 2 ^ 64

/-- The caller's obligations for a `BLAKE2` call: the buffer conditions, readable `rs1` and
`rs2`, 26 loadable doublewords, 8 aligned doublewords at `rs1` that Jolt may store to, and a
final-block flag of 0 or 1.
Example: `JoltTests.Blake2Instance.kat_pre`, a state buffer at `0x8002_0000` and a message
buffer at `0x8003_0000`. -/
structure Blake2Pre (rs1 rs2 : regidx) (s : SailJoltState) : Prop
    extends Blake2Buffer rs1 s where
  reads1 : XReads s rs1 (blake2H rs1 s)
  reads2 : XReads s rs2 (blake2M rs2 s)
  readable : Readable s (blake2H rs1 s) (blake2M rs2 s)
  writable : ∀ k < 8, DwordWritable s.jolt_device ((blake2H rs1 s).toNat + 8 * k)
  flag : (blake2Input rs1 rs2 s).flag = 0 ∨ (blake2Input rs1 rs2 s).flag = 1

/-- The state after a call: the computed state stored at `A`, the pool registers reset, and
nothing else changed.
Example: for the all-zero state, block, counter and flag, the doublewords at `A` hold
`rowsOut ⟨0, 0, 0, 0⟩`. -/
def blake2Final (s : SailJoltState) (A : BitVec 64) (x : Input) : SailJoltState :=
  { s with vregs := poolReset s.vregs,
           sail := { s.sail with mem := writeDwords s.sail.mem A.toNat (rowsOut x).toList } }

/-- What a `BLAKE2` call does: all 26 loads succeed, the end state is `blake2Final` for the
loaded inputs, and doubleword `i` at `A` reads back word `i` of the computed state.
Example: with `h`, `m`, the counter and the flag of the RFC 7693 test vector "abc", loading the
first doubleword at `A` afterwards returns `0x0d4d1c983fa580ba`. -/
def Blake2Spec (rs1 rs2 : regidx) (s s' : SailJoltState) : Prop :=
  Readable s (blake2H rs1 s) (blake2M rs2 s) ∧
    s' = blake2Final s (blake2H rs1 s) (blake2Input rs1 rs2 s) ∧
    ∀ i (hi : i < 8), loadDword? s' (blake2H rs1 s + BitVec.ofNat 64 (8 * i)) =
      some (rowsOut (blake2Input rs1 rs2 s))[i]

/-! ## The register file at the end -/

theorem hRegs_map (f : VReg → BitVec 64) : hRegs.map f = (hView f).toList := by
  simp only [hRegs, hView, List.map_ofFn, Vector.toList_ofFn]
  rfl

theorem mView_loadF (s : SailJoltState) (A B : BitVec 64) :
    mView (loadF s A B) = (input s A B).m := by
  apply Vector.ext
  intro j hj
  rw [show (mView (loadF s A B))[j] = (mView (loadF s A B))[(⟨j, hj⟩ : Fin 16)] from rfl,
    getElem_mView, loadF_mReg]
  rfl

theorem hView_loadF (s : SailJoltState) (A B : BitVec 64) :
    hView (loadF s A B) = (input s A B).h := by
  apply Vector.ext
  intro i hi
  rw [show (hView (loadF s A B))[i] = (hView (loadF s A B))[(⟨i, hi⟩ : Fin 8)] from rfl,
    getElem_hView, loadF_hReg]
  rfl

/-- The register file after the register rows. -/
abbrev endF (s : SailJoltState) (A B : BitVec 64) : VReg → BitVec 64 :=
  finalF (mixesF (roundsMixes 12) (initF (loadF s A B)))

/-- The state registers at the end hold the computed state. -/
theorem hView_endF (s : SailJoltState) (A B : BitVec 64) :
    hView (endF s A B) = rowsOut (input s A B) := by
  have hh : (Vector.ofFn fun i => loadF s A B (hReg i)) = (input s A B).h := hView_loadF s A B
  rw [endF, hView_finalF, hView_mixesF, hView_initF, (views_rounds 12 _).1, mView_initF,
    wView_initF, mView_loadF, hh, loadF_t, loadF_flag, hView_loadF]
  rfl

/-- Outside the pool, the register rows change nothing. -/
theorem poolReset_endF (s : SailJoltState) (A B : BitVec 64) :
    poolReset (endF s A B) = poolReset s.vregs :=
  poolReset_congr fun r hr => by
    rw [endF, finalF_out _ _ hr, mixesF_out _ _ _ hr, initF_out _ _ hr, loadF_out _ _ _ _ hr]

/-! ## Running the rows -/

/-- Given `rs1` reading `A` and `rs2` reading `B`, with the state buffer in RAM, the rows run
exactly when all 26 loads succeed and the 8 target doublewords at `A` are writable, and they
end in `blake2Final`.
Example: a message buffer at `0x8003_0004` is not 8-aligned, so its loads fail and the rows have
no run. -/
theorem blake2_run_iff {rs1 rs2 rs3 : regidx} {s s' : SailJoltState} {A B : BitVec 64}
    (hr1 : XReads s rs1 A) (hr2 : XReads s rs2 B) (hA : RAM_START_ADDRESS ≤ A.toNat)
    (hw : A.toNat + 64 ≤ 2 ^ 64) :
    (blake2RowsAuto rs1 rs2 rs3).Run s s' ↔
      Readable s A B ∧ (∀ k < 8, DwordWritable s.jolt_device (A.toNat + 8 * k)) ∧
        s' = blake2Final s A (input s A B) := by
  unfold blake2RowsAuto
  rw [blake2RowsAutoList_eq, loadRows_eq, storeRows_eq]
  simp only [List.append_assoc]
  rw [run_ldRows_iff hr1 hLds hLds_ge, run_ldRows_iff (XReads.vregs _ hr2) mLds mLds_ge]
  simp only [loadDword?_vregs, ldFile_vregs]
  rw [run_append_of_regRun (regRun_initRows _), run_append_of_regRun (regRun_mixes _ _),
    run_append_of_regRun (regRun_finalRows _),
    run_sdRows_iff hA 0 hRegs _ (XReads.vregs _ hr1) (by simp only [hRegs, List.length_ofFn]; omega),
    ← List.append_nil resetRows, run_append_of_regRun (regRun_resetRows _), run_nil_iff,
    ← readable_iff, and_assoc]
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  have he : ∀ k, A.toNat + 0 + 8 * k = A.toNat + 8 * k := fun k => by omega
  have hl : hRegs.length = 8 := rfl
  simp only [he, hl]
  apply and_congr_right
  intro _
  have h1 := poolReset_endF s A B
  have h2 := hView_endF s A B
  simp only [endF] at h1 h2
  simp only [hRegs_map, h2, h1, Nat.add_zero]
  rfl

/-! ## Soundness -/

/-- **Soundness of `BLAKE2`.** Every run of the rows from a state whose state buffer lies in RAM
loads all 26 inputs, stores the computed state at `rs1`, resets `vr48..87`, and changes nothing
else; the 8 stored doublewords read back.
Example: `JoltTests.Blake2Instance.blake2_kat` for the RFC 7693 test vector "abc". -/
theorem blake2_rows_sound {rs1 rs2 rs3 : regidx} {s s' : SailJoltState}
    (buf : Blake2Buffer rs1 s) (run : (blake2RowsAuto rs1 rs2 rs3).Run s s') :
    Blake2Spec rs1 rs2 s s' := by
  have hr1 : XReads s rs1 (blake2H rs1 s) := by
    have h := run
    unfold blake2RowsAuto at h
    exact XReads.of_run_ld h
  have hr2 : XReads s rs2 (blake2M rs2 s) := by
    have h := run
    unfold blake2RowsAuto at h
    rw [blake2RowsAutoList_eq, loadRows_eq] at h
    simp only [List.append_assoc] at h
    rw [run_ldRows_iff hr1 hLds hLds_ge,
      show ldRows rs2 mLds = .LD .normal (.vreg (BitVec.ofNat 7 64)) (.xreg rs2) 0 ::
        ldRows rs2 mLds.tail from rfl, List.cons_append] at h
    exact XReads.of_run_ld (s := { s with vregs := ldFile s (blake2H rs1 s) hLds s.vregs }) h.2
  obtain ⟨hread, hwr, rfl⟩ := (blake2_run_iff hr1 hr2 buf.ram buf.no_wrap).1 run
  refine ⟨hread, rfl, fun i hi => ?_⟩
  have hlen : (rowsOut (blake2Input rs1 rs2 s)).toList.length = 8 := by simp
  rw [loadDword?_of_mem_writeDwords
    (t := blake2Final s (blake2H rs1 s) (blake2Input rs1 rs2 s)) rfl buf.ram
    (by rw [hlen]; exact buf.no_wrap) (fun j hj => hwr j (by rwa [hlen] at hj))
    (by rwa [hlen])]
  simp

/-- **The stored state is `Spec.compress 12`.** When the loaded flag is 0 or 1, every run from
a state whose state buffer lies in RAM stores at `rs1` the BLAKE2b compression of the loaded
state, block and counter, with the flag as the final-block bit.
Example: for the RFC 7693 test vector "abc" (counter 3, flag 1), the first stored doubleword is
`0x0d4d1c983fa580ba`. -/
theorem blake2_rows_sound_compress {rs1 rs2 rs3 : regidx} {s s' : SailJoltState}
    (buf : Blake2Buffer rs1 s) (run : (blake2RowsAuto rs1 rs2 rs3).Run s s')
    (hf : (blake2Input rs1 rs2 s).flag = 0 ∨ (blake2Input rs1 rs2 s).flag = 1) :
    ∀ i (hi : i < 8), loadDword? s' (blake2H rs1 s + BitVec.ofNat 64 (8 * i)) =
      some (Spec.compress 12 (blake2Input rs1 rs2 s).h (blake2Input rs1 rs2 s).m
        ((blake2Input rs1 rs2 s).t.setWidth 128) (decide ((blake2Input rs1 rs2 s).flag = 1)))[i] := by
  intro i hi
  rw [(blake2_rows_sound buf run).2.2 i hi, rowsOut_eq_compress _ hf]

/-! ## Completeness and determinism -/

/-- **Completeness of `BLAKE2`.** For a call that meets its obligations, the rows run, and the
end state meets the specification. The rows take no advice.
Example: `JoltTests.Blake2Instance.blake2_kat`. -/
theorem blake2_rows_complete {rs1 rs2 rs3 : regidx} {s : SailJoltState}
    (pre : Blake2Pre rs1 rs2 s) :
    ∃ s', (blake2RowsAuto rs1 rs2 rs3).Run s s' ∧ Blake2Spec rs1 rs2 s s' := by
  have run : (blake2RowsAuto rs1 rs2 rs3).Run s
      (blake2Final s (blake2H rs1 s) (blake2Input rs1 rs2 s)) :=
    (blake2_run_iff pre.reads1 pre.reads2 pre.ram pre.no_wrap).2
      ⟨pre.readable, pre.writable, rfl⟩
  exact ⟨_, run, blake2_rows_sound pre.toBlake2Buffer run⟩

/-- **Determinism of `BLAKE2`.** Two runs of the rows from the same state, whose state buffer
lies in RAM, end in the same state. -/
theorem blake2_rows_deterministic {rs1 rs2 rs3 : regidx} {s s₁ s₂ : SailJoltState}
    (buf : Blake2Buffer rs1 s) (run₁ : (blake2RowsAuto rs1 rs2 rs3).Run s s₁)
    (run₂ : (blake2RowsAuto rs1 rs2 rs3).Run s s₂) : s₁ = s₂ :=
  (blake2_rows_sound buf run₁).2.1.trans (blake2_rows_sound buf run₂).2.1.symm

/-! ## The `rd = x0` rows -/

/-- The `rd = x0` program is the `rd ≠ x0` program with any `rs3`. -/
theorem blake2RowsAutoRdZero_eq (rs1 rs2 rs3 : regidx) :
    blake2RowsAutoRdZero rs1 rs2 = blake2RowsAuto rs1 rs2 rs3 := by
  unfold blake2RowsAutoRdZero blake2RowsAuto
  rw [blake2RowsAutoRdZeroList_eq rs1 rs2 rs3]

/-- **Soundness of `BLAKE2`, `rd = x0`.** As `blake2_rows_sound`. -/
theorem blake2RdZero_rows_sound {rs1 rs2 : regidx} {s s' : SailJoltState}
    (buf : Blake2Buffer rs1 s) (run : (blake2RowsAutoRdZero rs1 rs2).Run s s') :
    Blake2Spec rs1 rs2 s s' := by
  rw [blake2RowsAutoRdZero_eq rs1 rs2 rs1] at run
  exact blake2_rows_sound buf run

/-- **The stored state is `Spec.compress 12`, `rd = x0`.** As `blake2_rows_sound_compress`. -/
theorem blake2RdZero_rows_sound_compress {rs1 rs2 : regidx} {s s' : SailJoltState}
    (buf : Blake2Buffer rs1 s) (run : (blake2RowsAutoRdZero rs1 rs2).Run s s')
    (hf : (blake2Input rs1 rs2 s).flag = 0 ∨ (blake2Input rs1 rs2 s).flag = 1) :
    ∀ i (hi : i < 8), loadDword? s' (blake2H rs1 s + BitVec.ofNat 64 (8 * i)) =
      some (Spec.compress 12 (blake2Input rs1 rs2 s).h (blake2Input rs1 rs2 s).m
        ((blake2Input rs1 rs2 s).t.setWidth 128) (decide ((blake2Input rs1 rs2 s).flag = 1)))[i] := by
  rw [blake2RowsAutoRdZero_eq rs1 rs2 rs1] at run
  exact blake2_rows_sound_compress buf run hf

/-- **Completeness of `BLAKE2`, `rd = x0`.** As `blake2_rows_complete`. -/
theorem blake2RdZero_rows_complete {rs1 rs2 : regidx} {s : SailJoltState}
    (pre : Blake2Pre rs1 rs2 s) :
    ∃ s', (blake2RowsAutoRdZero rs1 rs2).Run s s' ∧ Blake2Spec rs1 rs2 s s' := by
  rw [blake2RowsAutoRdZero_eq rs1 rs2 rs1]
  exact blake2_rows_complete pre

/-- **Determinism of `BLAKE2`, `rd = x0`.** As `blake2_rows_deterministic`. -/
theorem blake2RdZero_rows_deterministic {rs1 rs2 : regidx} {s s₁ s₂ : SailJoltState}
    (buf : Blake2Buffer rs1 s) (run₁ : (blake2RowsAutoRdZero rs1 rs2).Run s s₁)
    (run₂ : (blake2RowsAutoRdZero rs1 rs2).Run s s₂) : s₁ = s₂ := by
  rw [blake2RowsAutoRdZero_eq rs1 rs2 rs1] at run₁ run₂
  exact blake2_rows_deterministic buf run₁ run₂

end JoltISA.Inlines.Blake2b
