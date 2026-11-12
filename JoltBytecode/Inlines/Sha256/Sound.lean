import JoltBytecode.Inlines.Sha256.Blocks
import JoltBytecode.Inlines.Sha256.Shape
import JoltBytecode.Inlines.FrameInstances

/-!
# `SHA256` and `SHA256_INIT`: soundness, completeness and determinism of the rows

A `SHA256` call compresses one 64-byte block into a SHA-256 state. Register `rs1` holds the
address `A` of the state, eight words in four doublewords, and `rs2` holds the address `B` of
the block, eight doublewords. The rows load the state and the block, run the 64 rounds, add the
old state, store the new state at `A`, and reset the pool registers `vr48..83`.
`SHA256_INIT` does the same from the initial hash value: it does not load the state, and it
resets `vr48..75`. No row reads advice.

* `sha256_run_iff`: from a state in which `rs1` reads `A` and `rs2` reads `B`, with the state
  buffer in RAM, the rows run exactly when all loads succeed and the 4 stores are allowed, and
  they end in `sha256Final`.
* `sha256_rows_sound`: every run from a state whose state buffer lies in RAM ends in
  `sha256Final`, and the 4 doublewords at `A` read back the computed state (`Sha256Spec`).
* `sha256_rows_sound_compression`: doubleword `i` at `A` holds words `2i` (low half) and
  `2i + 1` (high half) of `Spec.compression` of the loaded block and state.
* `sha256_rows_complete`: under `Sha256Pre` the rows run, and the end state meets `Sha256Spec`.
* `sha256_rows_deterministic`: two runs from the same state end in the same state.
* The same for `SHA256_INIT` (`sha256Init_rows_*`, with `Spec.initial` as the state) and for the
  `rd = x0` rows of both, which are the same rows.

The frame and the pool reset of every run are `FrameInstances.sha256_frame`,
`FrameInstances.sha256_resetsPool` and their `Init` and `RdZero` variants.
-/

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail LeanRV64D
  LeanRV64D.Functions JoltISA.Inlines.Generated

set_option autoImplicit false

noncomputable section

namespace JoltISA.Inlines.Sha256

open JoltSpec.Sha256 JoltSpec.Sha256.Spec

/-! ## Calls -/

/-- The state buffer of a call: the address in `rs1`.
Example: `0x8002_0000` when `x10 = 0x8002_0000` and `rs1 = x10`. -/
abbrev sha256H (rs1 : regidx) (s : SailJoltState) : BitVec 64 := sourceValue (.xreg rs1) s

/-- The block buffer of a call: the address in `rs2`. -/
abbrev sha256M (rs2 : regidx) (s : SailJoltState) : BitVec 64 := sourceValue (.xreg rs2) s

/-- The inputs of a call: what the loads read from the two buffers (`b = false` for `SHA256`,
`b = true` for `SHA256_INIT`). -/
abbrev sha256Input (b : Bool) (rs1 rs2 : regidx) (s : SailJoltState) : Input :=
  input b s (sha256H rs1 s) (sha256M rs2 s)

/-- Where the state buffer must lie for soundness: in RAM, with its 32 bytes below `2^64`.
Example: a buffer at `0x8002_0000` meets it; one at `0x1000` (below RAM) does not. -/
structure Sha256Buffer (rs1 : regidx) (s : SailJoltState) : Prop where
  ram : RAM_START_ADDRESS ≤ (sha256H rs1 s).toNat
  no_wrap : (sha256H rs1 s).toNat + 32 ≤ 2 ^ 64

/-- The caller's obligations for a call: the buffer conditions, readable `rs1` and `rs2`,
loadable doublewords (4 at `rs1` for `SHA256`, 8 at `rs2`), and 4 aligned doublewords at `rs1`
that Jolt may store to.
Example: `JoltTests.Sha256Instance.kat_pre`, a state buffer at `0x8002_0000` and a block
buffer at `0x8003_0000`. -/
structure Sha256Pre (b : Bool) (rs1 rs2 : regidx) (s : SailJoltState) : Prop
    extends Sha256Buffer rs1 s where
  reads1 : XReads s rs1 (sha256H rs1 s)
  reads2 : XReads s rs2 (sha256M rs2 s)
  readable : Readable b s (sha256H rs1 s) (sha256M rs2 s)
  writable : ∀ k < 4, DwordWritable s.jolt_device ((sha256H rs1 s).toNat + 8 * k)

/-- The state after a call: the computed state stored at `A`, the pool registers reset, and
nothing else changed. -/
def sha256Final (b : Bool) (s : SailJoltState) (A : BitVec 64) (x : Input) : SailJoltState :=
  { s with vregs := poolReset b s.vregs,
           sail := { s.sail with mem := writeDwords s.sail.mem A.toNat (rowsOut x).toList } }

/-- What a call does: all loads succeed, the end state is `sha256Final` for the loaded inputs,
and doubleword `i` at `A` reads back doubleword `i` of the computed state.
Example: for `SHA256_INIT` on the padded block of "abc", loading the first doubleword at `A`
afterwards returns `0x8f01cfea_ba7816bf`. -/
def Sha256Spec (b : Bool) (rs1 rs2 : regidx) (s s' : SailJoltState) : Prop :=
  Readable b s (sha256H rs1 s) (sha256M rs2 s) ∧
    s' = sha256Final b s (sha256H rs1 s) (sha256Input b rs1 rs2 s) ∧
    ∀ i (hi : i < 4), loadDword? s' (sha256H rs1 s + BitVec.ofNat 64 (8 * i)) =
      some (rowsOut (sha256Input b rs1 rs2 s))[i]

/-- Doubleword `i` of `rowsOut` holds words `2i + 1` (high half) and `2i` (low half) of the
compression. -/
theorem getElem_rowsOut (x : Input) (i : Nat) (hi : i < 4) :
    (rowsOut x)[i] = (compression x.block x.state).get (2 * i + 1) ++
      (compression x.block x.state).get (2 * i) := by
  simp only [rowsOut, Vector.getElem_ofFn]

/-! ## Running the rows -/

/-- The rows as the loads followed by the other blocks. -/
private theorem sha256Rows_eq (b : Bool) (rs1 rs2 : regidx) :
    sha256Rows b rs1 rs2 =
      loadRows b rs1 rs2 ++ ((allRounds b 64 ++ finalRows b) ++ (storeRows rs1 ++ resetRows b)) := by
  simp only [sha256Rows, List.append_assoc]

/-- Given `rs1` reading `A` and `rs2` reading `B`, with the state buffer in RAM, the rows run
exactly when every load succeeds and the 4 target doublewords at `A` are writable, and they end
in `sha256Final`.
Example: a block buffer at `0x8003_0004` is not 8-aligned, so its loads fail and the rows have no
run. -/
theorem sha256_run_iff {b : Bool} {rs1 rs2 : regidx} {s s' : SailJoltState} {A B : BitVec 64}
    (hr1 : XReads s rs1 A) (hr2 : XReads s rs2 B) (hA : RAM_START_ADDRESS ≤ A.toNat)
    (hw : A.toNat + 32 ≤ 2 ^ 64) :
    (Program.seq (sha256Rows b rs1 rs2)).Run s s' ↔
      Readable b s A B ∧ (∀ k < 4, DwordWritable s.jolt_device (A.toNat + 8 * k)) ∧
        s' = sha256Final b s A (input b s A B) := by
  obtain ⟨F, hF, hlo, hout⟩ := regs_spec b s A B
  have hw' : A.toNat + 0 + 8 * ((List.range 4).map stG).length ≤ 2 ^ 64 := by
    simp only [List.length_map, List.length_range]
    omega
  rw [sha256Rows_eq, run_loadRows_iff (fun _ => hr1) hr2,
    run_append_of_regRun (s := { s with vregs := loadF b s A B }) hF, storeRows_eq,
    run_sdPreRows_iff hA 0 _ _ (XReads.vregs _ hr1) hw' (sdPreFile_stG F),
    ← List.append_nil (resetRows b), run_append_of_regRun (regRun_resetRows b _), run_nil_iff]
  apply and_congr_right
  intro _
  simp only [List.length_map, List.length_range, Nat.add_zero]
  apply and_congr_right
  intro _
  have hp : poolReset b (storeFile F) = poolReset b s.vregs :=
    poolReset_congr fun r hr => by
      have := poolSize_ge b
      unfold InPool at hr
      rw [storeFile_out F r (by omega), hout r (by unfold InPool; exact hr)]
  rw [stored_eq (input b s A B) F hlo, hp]
  rfl

/-- `run_append_of_regRun` with the register file named. -/
private theorem run_append_vregs {l : List Instr} {s : SailJoltState} {F f : VReg → BitVec 64}
    (h : regRun l F = some f) (hs : s.vregs = F) (rest : List Instr) (s' : SailJoltState) :
    (Program.seq (l ++ rest)).Run s s' ↔ (Program.seq rest).Run { s with vregs := f } s' :=
  run_append_of_regRun (hs ▸ h) rest s'

/-- A run reads `rs1` and `rs2`. `SHA256` reads `rs1` in its first row; `SHA256_INIT` reads it
first in its first store. -/
theorem reads_of_run {b : Bool} {rs1 rs2 : regidx} {s s' : SailJoltState}
    (run : (Program.seq (sha256Rows b rs1 rs2)).Run s s') :
    XReads s rs1 (sha256H rs1 s) ∧ XReads s rs2 (sha256M rs2 s) := by
  cases b with
  | false =>
    obtain ⟨rest, hrest⟩ : ∃ rest, sha256Rows false rs1 rs2 =
        .LD .normal (.vreg (vr 72)) (.xreg rs1) (BitVec.ofNat 64 (8 * 0)) :: rest := ⟨_, rfl⟩
    have hr1 : XReads s rs1 (sha256H rs1 s) := by
      rw [hrest] at run
      exact XReads.of_run_ld run
    refine ⟨hr1, ?_⟩
    have h := run
    rw [sha256Rows_eq, loadRows] at h
    simp only [Bool.false_eq_true, ↓reduceIte, ivLoadRows_eq, List.append_assoc] at h
    rw [run_ldPostRows_iff hr1 _ ivG_ge (ldPostFile_ivG s _ s.vregs)] at h
    obtain ⟨rest', hrest'⟩ : ∃ rest', msgLoadRows rs2 ++
        (allRounds false 64 ++ (finalRows false ++ (storeRows rs1 ++ resetRows false))) =
        .LD .normal (.vreg (vr 56)) (.xreg rs2) (BitVec.ofNat 64 (8 * 0)) :: rest' := ⟨_, rfl⟩
    have h2 := h.2
    rw [hrest'] at h2
    have h3 := XReads.of_run_ld h2
    exact h3
  | true =>
    obtain ⟨rest, hrest⟩ : ∃ rest, sha256Rows true rs1 rs2 =
        .LD .normal (.vreg (vr 56)) (.xreg rs2) (BitVec.ofNat 64 (8 * 0)) :: rest := ⟨_, rfl⟩
    have hr2 : XReads s rs2 (sha256M rs2 s) := by
      have h := run
      rw [hrest] at h
      exact XReads.of_run_ld h
    refine ⟨?_, hr2⟩
    obtain ⟨F, hF, -, -⟩ := regs_spec true s (sha256H rs1 s) (sha256M rs2 s)
    have h := run
    rw [sha256Rows_eq, run_loadRows_iff (A := sha256H rs1 s) (fun h => absurd h (by decide)) hr2,
      run_append_of_regRun (s := { s with vregs := loadF true s _ _ }) hF, storeRows_eq] at h
    obtain ⟨rest', hrest'⟩ : ∃ rest', sdPreRows rs1 0 ((List.range 4).map stG) ++
        resetRows true = (stG 0).1 ++ (.SD (.xreg rs1) (.vreg (stG 0).2) (BitVec.ofNat 64 0) ::
          rest') := ⟨_, rfl⟩
    have h2 := h.2
    rw [hrest'] at h2
    have h3 := (run_append_vregs (regRun_stG 0 (by decide) F) (by rfl) _ _).1 h2
    have h4 := XReads.of_run_sd h3
    exact h4

/-! ## Soundness, completeness and determinism of `Program.seq (sha256Rows b rs1 rs2)` -/

/-- Soundness of the rows, for both inlines. -/
theorem rows_sound {b : Bool} {rs1 rs2 : regidx} {s s' : SailJoltState}
    (buf : Sha256Buffer rs1 s) (run : (Program.seq (sha256Rows b rs1 rs2)).Run s s') :
    Sha256Spec b rs1 rs2 s s' := by
  obtain ⟨hr1, hr2⟩ := reads_of_run run
  obtain ⟨hread, hwr, rfl⟩ := (sha256_run_iff hr1 hr2 buf.ram buf.no_wrap).1 run
  refine ⟨hread, rfl, fun i hi => ?_⟩
  have hlen : (rowsOut (sha256Input b rs1 rs2 s)).toList.length = 4 := by simp
  rw [loadDword?_of_mem_writeDwords
    (t := sha256Final b s (sha256H rs1 s) (sha256Input b rs1 rs2 s)) rfl buf.ram
    (by rw [hlen]; exact buf.no_wrap) (fun j hj => hwr j (by rwa [hlen] at hj))
    (by rwa [hlen])]
  simp

/-- Completeness of the rows, for both inlines. -/
theorem rows_complete {b : Bool} {rs1 rs2 : regidx} {s : SailJoltState}
    (pre : Sha256Pre b rs1 rs2 s) :
    ∃ s', (Program.seq (sha256Rows b rs1 rs2)).Run s s' ∧ Sha256Spec b rs1 rs2 s s' := by
  have run : (Program.seq (sha256Rows b rs1 rs2)).Run s
      (sha256Final b s (sha256H rs1 s) (sha256Input b rs1 rs2 s)) :=
    (sha256_run_iff pre.reads1 pre.reads2 pre.ram pre.no_wrap).2
      ⟨pre.readable, pre.writable, rfl⟩
  exact ⟨_, run, rows_sound pre.toSha256Buffer run⟩

/-- Determinism of the rows, for both inlines. -/
theorem rows_deterministic {b : Bool} {rs1 rs2 : regidx} {s s₁ s₂ : SailJoltState}
    (buf : Sha256Buffer rs1 s) (run₁ : (Program.seq (sha256Rows b rs1 rs2)).Run s s₁)
    (run₂ : (Program.seq (sha256Rows b rs1 rs2)).Run s s₂) : s₁ = s₂ :=
  (rows_sound buf run₁).2.1.trans (rows_sound buf run₂).2.1.symm

/-! ## The generated programs -/

/-- The generated `SHA256` program runs `sha256Rows false`. -/
theorem sha256RowsAuto_eq (rs1 rs2 rs3 : regidx) :
    sha256RowsAuto rs1 rs2 rs3 = Program.seq (sha256Rows false rs1 rs2) := by
  unfold sha256RowsAuto
  rw [sha256RowsAutoList_eq]

/-- The generated `SHA256`, `rd = x0` program runs `sha256Rows false`. -/
theorem sha256RowsAutoRdZero_eq (rs1 rs2 : regidx) :
    sha256RowsAutoRdZero rs1 rs2 = Program.seq (sha256Rows false rs1 rs2) := by
  unfold sha256RowsAutoRdZero
  rw [sha256RowsAutoRdZeroList_eq rs1 rs2 rs1, sha256RowsAutoList_eq]

/-- The generated `SHA256_INIT` program runs `sha256Rows true`. -/
theorem sha256InitRowsAuto_eq (rs1 rs2 rs3 : regidx) :
    sha256InitRowsAuto rs1 rs2 rs3 = Program.seq (sha256Rows true rs1 rs2) := by
  unfold sha256InitRowsAuto
  rw [sha256InitRowsAutoList_eq]

/-- The generated `SHA256_INIT`, `rd = x0` program runs `sha256Rows true`. -/
theorem sha256InitRowsAutoRdZero_eq (rs1 rs2 : regidx) :
    sha256InitRowsAutoRdZero rs1 rs2 = Program.seq (sha256Rows true rs1 rs2) := by
  unfold sha256InitRowsAutoRdZero
  rw [sha256InitRowsAutoRdZeroList_eq rs1 rs2 rs1, sha256InitRowsAutoList_eq]

/-! ## `SHA256` -/

/-- **Soundness of `SHA256`.** Every run of the rows from a state whose state buffer lies in RAM
loads the state and the block, stores the computed state at `rs1`, resets `vr48..83`, and
changes nothing else; the 4 stored doublewords read back. -/
theorem sha256_rows_sound {rs1 rs2 rs3 : regidx} {s s' : SailJoltState}
    (buf : Sha256Buffer rs1 s) (run : (sha256RowsAuto rs1 rs2 rs3).Run s s') :
    Sha256Spec false rs1 rs2 s s' := by
  rw [sha256RowsAuto_eq] at run
  exact rows_sound buf run

/-- **The stored state is `Spec.compression`.** Every run of `SHA256` from a state whose state
buffer lies in RAM stores at `rs1 + 8i` words `2i` (low half) and `2i + 1` (high half) of the
SHA-256 compression of the loaded block into the loaded state. -/
theorem sha256_rows_sound_compression {rs1 rs2 rs3 : regidx} {s s' : SailJoltState}
    (buf : Sha256Buffer rs1 s) (run : (sha256RowsAuto rs1 rs2 rs3).Run s s') :
    ∀ i < 4, loadDword? s' (sha256H rs1 s + BitVec.ofNat 64 (8 * i)) =
      some ((compression (sha256Input false rs1 rs2 s).block
          (sha256Input false rs1 rs2 s).state).get (2 * i + 1) ++
        (compression (sha256Input false rs1 rs2 s).block
          (sha256Input false rs1 rs2 s).state).get (2 * i)) := by
  intro i hi
  rw [(sha256_rows_sound buf run).2.2 i hi, getElem_rowsOut _ i hi]

/-- **Completeness of `SHA256`.** For a call that meets its obligations, the rows run, and the
end state meets the specification. The rows take no advice. -/
theorem sha256_rows_complete {rs1 rs2 rs3 : regidx} {s : SailJoltState}
    (pre : Sha256Pre false rs1 rs2 s) :
    ∃ s', (sha256RowsAuto rs1 rs2 rs3).Run s s' ∧ Sha256Spec false rs1 rs2 s s' := by
  rw [sha256RowsAuto_eq]
  exact rows_complete pre

/-- **Determinism of `SHA256`.** Two runs of the rows from the same state, whose state buffer
lies in RAM, end in the same state. -/
theorem sha256_rows_deterministic {rs1 rs2 rs3 : regidx} {s s₁ s₂ : SailJoltState}
    (buf : Sha256Buffer rs1 s) (run₁ : (sha256RowsAuto rs1 rs2 rs3).Run s s₁)
    (run₂ : (sha256RowsAuto rs1 rs2 rs3).Run s s₂) : s₁ = s₂ := by
  rw [sha256RowsAuto_eq] at run₁ run₂
  exact rows_deterministic buf run₁ run₂

/-- **Soundness of `SHA256`, `rd = x0`.** As `sha256_rows_sound`. -/
theorem sha256RdZero_rows_sound {rs1 rs2 : regidx} {s s' : SailJoltState}
    (buf : Sha256Buffer rs1 s) (run : (sha256RowsAutoRdZero rs1 rs2).Run s s') :
    Sha256Spec false rs1 rs2 s s' := by
  rw [sha256RowsAutoRdZero_eq] at run
  exact rows_sound buf run

/-- **The stored state is `Spec.compression`, `rd = x0`.** As `sha256_rows_sound_compression`. -/
theorem sha256RdZero_rows_sound_compression {rs1 rs2 : regidx} {s s' : SailJoltState}
    (buf : Sha256Buffer rs1 s) (run : (sha256RowsAutoRdZero rs1 rs2).Run s s') :
    ∀ i < 4, loadDword? s' (sha256H rs1 s + BitVec.ofNat 64 (8 * i)) =
      some ((compression (sha256Input false rs1 rs2 s).block
          (sha256Input false rs1 rs2 s).state).get (2 * i + 1) ++
        (compression (sha256Input false rs1 rs2 s).block
          (sha256Input false rs1 rs2 s).state).get (2 * i)) := by
  rw [sha256RowsAutoRdZero_eq rs1 rs2, ← sha256RowsAuto_eq rs1 rs2 rs1] at run
  exact sha256_rows_sound_compression buf run

/-- **Completeness of `SHA256`, `rd = x0`.** As `sha256_rows_complete`. -/
theorem sha256RdZero_rows_complete {rs1 rs2 : regidx} {s : SailJoltState}
    (pre : Sha256Pre false rs1 rs2 s) :
    ∃ s', (sha256RowsAutoRdZero rs1 rs2).Run s s' ∧ Sha256Spec false rs1 rs2 s s' := by
  rw [sha256RowsAutoRdZero_eq]
  exact rows_complete pre

/-- **Determinism of `SHA256`, `rd = x0`.** As `sha256_rows_deterministic`. -/
theorem sha256RdZero_rows_deterministic {rs1 rs2 : regidx} {s s₁ s₂ : SailJoltState}
    (buf : Sha256Buffer rs1 s) (run₁ : (sha256RowsAutoRdZero rs1 rs2).Run s s₁)
    (run₂ : (sha256RowsAutoRdZero rs1 rs2).Run s s₂) : s₁ = s₂ := by
  rw [sha256RowsAutoRdZero_eq] at run₁ run₂
  exact rows_deterministic buf run₁ run₂

/-! ## `SHA256_INIT` -/

/-- **Soundness of `SHA256_INIT`.** Every run of the rows from a state whose state buffer lies in
RAM loads the block, stores the computed state at `rs1`, resets `vr48..75`, and changes nothing
else; the 4 stored doublewords read back. -/
theorem sha256Init_rows_sound {rs1 rs2 rs3 : regidx} {s s' : SailJoltState}
    (buf : Sha256Buffer rs1 s) (run : (sha256InitRowsAuto rs1 rs2 rs3).Run s s') :
    Sha256Spec true rs1 rs2 s s' := by
  rw [sha256InitRowsAuto_eq] at run
  exact rows_sound buf run

/-- **The stored state is `Spec.compression` from the initial hash value.** Every run of
`SHA256_INIT` from a state whose state buffer lies in RAM stores at `rs1 + 8i` words `2i` (low
half) and `2i + 1` (high half) of the SHA-256 compression of the loaded block into
`Spec.initial`.
Example: `JoltTests.Sha256Instance.sha256Init_kat` for the padded block of "abc". -/
theorem sha256Init_rows_sound_compression {rs1 rs2 rs3 : regidx} {s s' : SailJoltState}
    (buf : Sha256Buffer rs1 s) (run : (sha256InitRowsAuto rs1 rs2 rs3).Run s s') :
    ∀ i < 4, loadDword? s' (sha256H rs1 s + BitVec.ofNat 64 (8 * i)) =
      some ((compression (sha256Input true rs1 rs2 s).block initial).get (2 * i + 1) ++
        (compression (sha256Input true rs1 rs2 s).block initial).get (2 * i)) := by
  intro i hi
  rw [(sha256Init_rows_sound buf run).2.2 i hi, getElem_rowsOut _ i hi]
  rfl

/-- **Completeness of `SHA256_INIT`.** For a call that meets its obligations, the rows run, and
the end state meets the specification. The rows take no advice. -/
theorem sha256Init_rows_complete {rs1 rs2 rs3 : regidx} {s : SailJoltState}
    (pre : Sha256Pre true rs1 rs2 s) :
    ∃ s', (sha256InitRowsAuto rs1 rs2 rs3).Run s s' ∧ Sha256Spec true rs1 rs2 s s' := by
  rw [sha256InitRowsAuto_eq]
  exact rows_complete pre

/-- **Determinism of `SHA256_INIT`.** Two runs of the rows from the same state, whose state
buffer lies in RAM, end in the same state. -/
theorem sha256Init_rows_deterministic {rs1 rs2 rs3 : regidx} {s s₁ s₂ : SailJoltState}
    (buf : Sha256Buffer rs1 s) (run₁ : (sha256InitRowsAuto rs1 rs2 rs3).Run s s₁)
    (run₂ : (sha256InitRowsAuto rs1 rs2 rs3).Run s s₂) : s₁ = s₂ := by
  rw [sha256InitRowsAuto_eq] at run₁ run₂
  exact rows_deterministic buf run₁ run₂

/-- **Soundness of `SHA256_INIT`, `rd = x0`.** As `sha256Init_rows_sound`. -/
theorem sha256InitRdZero_rows_sound {rs1 rs2 : regidx} {s s' : SailJoltState}
    (buf : Sha256Buffer rs1 s) (run : (sha256InitRowsAutoRdZero rs1 rs2).Run s s') :
    Sha256Spec true rs1 rs2 s s' := by
  rw [sha256InitRowsAutoRdZero_eq] at run
  exact rows_sound buf run

/-- **The stored state is `Spec.compression` from the initial hash value, `rd = x0`.** As
`sha256Init_rows_sound_compression`. -/
theorem sha256InitRdZero_rows_sound_compression {rs1 rs2 : regidx} {s s' : SailJoltState}
    (buf : Sha256Buffer rs1 s) (run : (sha256InitRowsAutoRdZero rs1 rs2).Run s s') :
    ∀ i < 4, loadDword? s' (sha256H rs1 s + BitVec.ofNat 64 (8 * i)) =
      some ((compression (sha256Input true rs1 rs2 s).block initial).get (2 * i + 1) ++
        (compression (sha256Input true rs1 rs2 s).block initial).get (2 * i)) := by
  rw [sha256InitRowsAutoRdZero_eq rs1 rs2, ← sha256InitRowsAuto_eq rs1 rs2 rs1] at run
  exact sha256Init_rows_sound_compression buf run

/-- **Completeness of `SHA256_INIT`, `rd = x0`.** As `sha256Init_rows_complete`. -/
theorem sha256InitRdZero_rows_complete {rs1 rs2 : regidx} {s : SailJoltState}
    (pre : Sha256Pre true rs1 rs2 s) :
    ∃ s', (sha256InitRowsAutoRdZero rs1 rs2).Run s s' ∧ Sha256Spec true rs1 rs2 s s' := by
  rw [sha256InitRowsAutoRdZero_eq]
  exact rows_complete pre

/-- **Determinism of `SHA256_INIT`, `rd = x0`.** As `sha256Init_rows_deterministic`. -/
theorem sha256InitRdZero_rows_deterministic {rs1 rs2 : regidx} {s s₁ s₂ : SailJoltState}
    (buf : Sha256Buffer rs1 s) (run₁ : (sha256InitRowsAutoRdZero rs1 rs2).Run s s₁)
    (run₂ : (sha256InitRowsAutoRdZero rs1 rs2).Run s s₂) : s₁ = s₂ := by
  rw [sha256InitRowsAutoRdZero_eq] at run₁ run₂
  exact rows_deterministic buf run₁ run₂

end JoltISA.Inlines.Sha256
