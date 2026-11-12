import JoltBytecode.Inlines.Keccak256.Blocks
import JoltBytecode.Inlines.Keccak256.Shape
import JoltBytecode.Inlines.FrameInstances

/-!
# `KECCAK256` and `KECCAK256_ABSORB_PERMUTE`: soundness, completeness and determinism

Register `rs1` holds the address `A` of the Keccak state: lane `x + 5y` is the doubleword at
`A + 8(x + 5y)`, as in FIPS 202 and EthLib's `Keccak.Internal.laneAt`. `KECCAK256` loads the 25
lanes, applies Keccak-f[1600], stores the 25 lanes back at `A`, and resets the pool registers
`vr48..84`. `KECCAK256_ABSORB_PERMUTE` also reads the 17 lanes (136 bytes) of a block at the
address `B` in `rs2` and XORs them into lanes 0 to 16 before the permutation. No row reads
advice.

* `keccak256_run_iff`, `absorbPermute_run_iff`: from a state in which `rs1` reads `A` (and
  `rs2` reads `B`), with the state buffer in RAM, the rows run exactly when the loads succeed and
  the 25 stores are allowed, and they end in `keccakFinal`.
* `keccak256_rows_sound`, `absorbPermute_rows_sound`: every run from a state whose state buffer
  lies in RAM ends in `keccakFinal`, and the 25 doublewords at `A` read back the computed state
  (`Keccak256Spec`, `AbsorbPermuteSpec`).
* `keccak256_rows_sound_keccakF`: the state stored at `A` is EthLib's `keccakF` of the loaded
  state. `absorbPermute_rows_sound_keccakF`: it is
  `keccakF (Internal.absorbBlock 136 S block 0)`, with `S` the loaded state and `block` the 136
  loaded block bytes.
* `*_rows_complete`: under `Keccak256Pre` (`AbsorbPermutePre`) the rows run, and the end state
  meets the specification.
* `*_rows_deterministic`: two runs from the same state end in the same state.
* The same for the `rd = x0` rows, which are the same rows.

The frame and the pool reset of every run are `FrameInstances.keccak256_frame`,
`FrameInstances.keccak256_resetsPool` and their `RdZero` and `AbsorbPermute` variants.
-/

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail LeanRV64D
  LeanRV64D.Functions JoltISA.Inlines.Generated

set_option autoImplicit false

noncomputable section

namespace JoltISA.Inlines.Keccak256

open JoltSpec.Keccak JoltSpec.Keccak.Internal

/-! ## Calls -/

/-- The state buffer of a call: the address in `rs1`.
Example: `0x8002_0000` when `x10 = 0x8002_0000` and `rs1 = x10`. -/
abbrev keccakA (rs1 : regidx) (s : SailJoltState) : BitVec 64 := sourceValue (.xreg rs1) s

/-- The block buffer of a `KECCAK256_ABSORB_PERMUTE` call: the address in `rs2`. -/
abbrev keccakB (rs2 : regidx) (s : SailJoltState) : BitVec 64 := sourceValue (.xreg rs2) s

/-- The `n` doublewords at `A`, `A + 8`, ... load.
Example: `LanesLoad s A 25` holds when the 200 bytes at `A` are aligned RAM. -/
def LanesLoad (s : SailJoltState) (A : BitVec 64) (n : Nat) : Prop :=
  ∀ i < n, (loadDword? s (A + BitVec.ofNat 64 (8 * i))).isSome

/-- Where the state buffer must lie for soundness: in RAM, with its 200 bytes below `2^64`.
Example: a buffer at `0x8002_0000` meets it; one at `0x1000` (below RAM) does not. -/
structure KeccakBuffer (rs1 : regidx) (s : SailJoltState) : Prop where
  ram : RAM_START_ADDRESS ≤ (keccakA rs1 s).toNat
  no_wrap : (keccakA rs1 s).toNat + 200 ≤ 2 ^ 64

/-- The caller's obligations for a `KECCAK256` call: the buffer conditions, a readable `rs1`,
25 loadable lanes, and 25 aligned doublewords at `rs1` that Jolt may store to.
Example: `JoltTests.KeccakInstance.kat_pre`, the zero state at `0x8002_0000`. -/
structure Keccak256Pre (rs1 : regidx) (s : SailJoltState) : Prop extends KeccakBuffer rs1 s where
  reads1 : XReads s rs1 (keccakA rs1 s)
  readable : LanesLoad s (keccakA rs1 s) 25
  writable : ∀ k < 25, DwordWritable s.jolt_device ((keccakA rs1 s).toNat + 8 * k)

/-- The caller's obligations for a `KECCAK256_ABSORB_PERMUTE` call: those of `KECCAK256`, a
readable `rs2`, and 17 loadable block lanes at `rs2`.
Example: `JoltTests.KeccakInstance.kat_absorb_pre`. -/
structure AbsorbPermutePre (rs1 rs2 : regidx) (s : SailJoltState) : Prop
    extends Keccak256Pre rs1 s where
  reads2 : XReads s rs2 (keccakB rs2 s)
  readable2 : LanesLoad s (keccakB rs2 s) 17

/-- The state after a call that computes `S`: the 25 lanes of `S` stored at `A`, the pool
registers reset, and nothing else changed. -/
def keccakFinal (s : SailJoltState) (A : BitVec 64) (S : State) : SailJoltState :=
  { s with vregs := poolReset s.vregs,
           sail := { s.sail with mem := writeDwords s.sail.mem A.toNat (wordsOf S) } }

/-- What a `KECCAK256` call does: the 25 loads succeed, the end state is `keccakFinal` for
`keccakF` of the loaded state, and doubleword `i` at `A` reads back lane `i` of that state.
Example: for the zero state, the first doubleword at `A` afterwards is `0xf1258f7940e1dde7`. -/
def Keccak256Spec (rs1 : regidx) (s s' : SailJoltState) : Prop :=
  LanesLoad s (keccakA rs1 s) 25 ∧
    s' = keccakFinal s (keccakA rs1 s) (keccakF (stateAt s (keccakA rs1 s))) ∧
    ∀ i < 25, loadDword? s' (keccakA rs1 s + BitVec.ofNat 64 (8 * i)) =
      (wordsOf (keccakF (stateAt s (keccakA rs1 s))))[i]?

/-- The state a `KECCAK256_ABSORB_PERMUTE` call computes: the block at `B` XORed into the state
at `A`, then permuted. -/
abbrev absorbOut (s : SailJoltState) (A B : BitVec 64) : State :=
  keccakF (absorbLanes (stateAt s A) (blockAt s B))

/-- What a `KECCAK256_ABSORB_PERMUTE` call does: the 25 state loads and the 17 block loads
succeed, the end state is `keccakFinal` for `absorbOut`, and doubleword `i` at `A` reads back
lane `i` of that state.
Example: from the zero state and the padded empty message, the first four doublewords at `A`
afterwards are Keccak-256(""). -/
def AbsorbPermuteSpec (rs1 rs2 : regidx) (s s' : SailJoltState) : Prop :=
  LanesLoad s (keccakA rs1 s) 25 ∧ LanesLoad s (keccakB rs2 s) 17 ∧
    s' = keccakFinal s (keccakA rs1 s) (absorbOut s (keccakA rs1 s) (keccakB rs2 s)) ∧
    ∀ i < 25, loadDword? s' (keccakA rs1 s + BitVec.ofNat 64 (8 * i)) =
      (wordsOf (absorbOut s (keccakA rs1 s) (keccakB rs2 s)))[i]?

/-! ## The end state -/

theorem wordsOf_length (S : State) : (wordsOf S).length = 25 := rfl

/-- A call leaves the device as it was. -/
theorem keccakFinal_jolt_device (s : SailJoltState) (A : BitVec 64) (S : State) :
    (keccakFinal s A S).jolt_device = s.jolt_device := by
  dsimp only [keccakFinal]

/-- The 25 stored lanes read back. -/
theorem loadDword?_keccakFinal {s : SailJoltState} {A : BitVec 64}
    (hA : RAM_START_ADDRESS ≤ A.toNat) (hw : A.toNat + 200 ≤ 2 ^ 64)
    (hwr : ∀ k < 25, DwordWritable s.jolt_device (A.toNat + 8 * k)) (S : State) (i : Nat)
    (hi : i < 25) :
    loadDword? (keccakFinal s A S) (A + BitVec.ofNat 64 (8 * i)) = (wordsOf S)[i]? := by
  have hl := wordsOf_length S
  have hm : (keccakFinal s A S).sail.mem = writeDwords s.sail.mem A.toNat (wordsOf S) := rfl
  apply loadDword?_of_mem_writeDwords hm hA
  · rw [hl]
    exact hw
  · intro k hk
    rw [keccakFinal_jolt_device]
    exact hwr k (by omega)
  · omega

/-- The state at `A` after a call that computes `S` is `S`. -/
theorem stateAt_keccakFinal {s : SailJoltState} {A : BitVec 64}
    (hA : RAM_START_ADDRESS ≤ A.toNat) (hw : A.toNat + 200 ≤ 2 ^ 64)
    (hwr : ∀ k < 25, DwordWritable s.jolt_device (A.toNat + 8 * k)) (S : State) :
    stateAt (keccakFinal s A S) A = S := by
  conv_rhs => rw [← ofLanes_wordsOf S]
  apply ofLanes_congr
  intro i hi
  rw [loadLane, loadDword?_keccakFinal hA hw hwr S i hi, List.getD_eq_getElem?_getD]

/-! ## Running the rows -/

/-- The rounds, stores and resets, from a state `t` whose lanes are `S` and whose register file
is `P` after the pool reset. -/
private theorem run_tail_iff {rs1 : regidx} {A : BitVec 64} {t : SailJoltState} {S : State}
    {P : VReg → BitVec 64} (hr1 : XReads t rs1 A) (hA : RAM_START_ADDRESS ≤ A.toNat)
    (hw : A.toNat + 200 ≤ 2 ^ 64) (hS : stateOf (regsOf t.vregs) = S)
    (hP : poolReset t.vregs = P) (s' : SailJoltState) :
    (Program.seq (roundsRows ++ (storeRows rs1 ++ resetRows))).Run t s' ↔
      (∀ k < 25, DwordWritable t.jolt_device (A.toNat + 8 * k)) ∧
        s' = { t with vregs := P,
                      sail := { t.sail with
                        mem := (writeDwords t.sail.mem A.toNat (wordsOf (keccakF S))) } } := by
  have hF : laneRegs.map (roundsOps.foldl Op.eval t.vregs) = wordsOf (keccakF S) := by
    rw [laneRegs_map, stateOf_rounds, hS]
  have hP' : poolReset (roundsOps.foldl Op.eval t.vregs) = P := by
    rw [← hP]
    exact poolReset_congr fun r hr => foldl_eval_out _ roundsOps_ok _ r hr
  rw [roundsRows_eq, run_ops_append _ roundsOps_ok, storeRows,
    run_sdRows_iff hA 0 laneRegs _ (XReads.vregs _ hr1) (by rw [laneRegs_length]; omega),
    ← List.append_nil resetRows, run_append_of_regRun (regRun_resetRows _), run_nil_iff,
    laneRegs_length]
  simp only [Nat.add_zero, hF, hP']

/-- Given `rs1` reading `A`, with the state buffer in RAM, the `KECCAK256` rows run exactly when
the 25 lanes at `A` load and the 25 target doublewords are writable, and they end in
`keccakFinal` for `keccakF` of the loaded state.
Example: a state buffer at `0x8002_0004` is not 8-aligned, so its loads fail and the rows have no
run. -/
theorem keccak256_run_iff {rs1 rs2 rs3 : regidx} {s s' : SailJoltState} {A : BitVec 64}
    (hr1 : XReads s rs1 A) (hA : RAM_START_ADDRESS ≤ A.toNat) (hw : A.toNat + 200 ≤ 2 ^ 64) :
    (keccak256RowsAuto rs1 rs2 rs3).Run s s' ↔
      LanesLoad s A 25 ∧ (∀ k < 25, DwordWritable s.jolt_device (A.toNat + 8 * k)) ∧
        s' = keccakFinal s A (keccakF (stateAt s A)) := by
  unfold keccak256RowsAuto
  rw [keccak256RowsAutoList_eq, loadRows]
  simp only [List.append_assoc]
  rw [run_ldRows_iff hr1 laneLds laneLds_ge, forall_laneLds_iff,
    run_tail_iff (t := { s with vregs := ldFile s A laneLds s.vregs }) hr1 hA hw
      (stateOf_ldFile s A s.vregs)
      (poolReset_congr fun r hr => ldFile_out s A s.vregs r hr)]
  exact Iff.rfl

@[simp] theorem absorbF_vregs (s : SailJoltState) (g : VReg → BitVec 64) (B : BitVec 64) :
    absorbF { s with vregs := g } B = absorbF s B := by
  unfold absorbF
  rw [absorbStep_vregs]

/-- Given `rs1` reading `A` and `rs2` reading `B`, with the state buffer in RAM, the
`KECCAK256_ABSORB_PERMUTE` rows run exactly when the 25 lanes at `A` and the 17 lanes at `B`
load and the 25 target doublewords are writable, and they end in `keccakFinal` for `absorbOut`.
-/
theorem absorbPermute_run_iff {rs1 rs2 rs3 : regidx} {s s' : SailJoltState} {A B : BitVec 64}
    (hr1 : XReads s rs1 A) (hr2 : XReads s rs2 B) (hA : RAM_START_ADDRESS ≤ A.toNat)
    (hw : A.toNat + 200 ≤ 2 ^ 64) :
    (keccak256AbsorbPermuteRowsAuto rs1 rs2 rs3).Run s s' ↔
      LanesLoad s A 25 ∧ LanesLoad s B 17 ∧
        (∀ k < 25, DwordWritable s.jolt_device (A.toNat + 8 * k)) ∧
        s' = keccakFinal s A (absorbOut s A B) := by
  have hS : stateOf (regsOf (absorbF s B (ldFile s A laneLds s.vregs))) =
      absorbLanes (stateAt s A) (blockAt s B) := by
    rw [stateOf_absorbF, stateOf_ldFile]
  have hP : poolReset (absorbF s B (ldFile s A laneLds s.vregs)) = poolReset s.vregs :=
    poolReset_congr fun r hr => by rw [absorbF_out _ _ _ _ hr, ldFile_out _ _ _ _ hr]
  unfold keccak256AbsorbPermuteRowsAuto
  rw [absorbPermuteRowsAutoList_eq, loadRows]
  simp only [List.append_assoc]
  rw [run_ldRows_iff hr1 laneLds laneLds_ge, forall_laneLds_iff,
    run_absorbRows_iff (XReads.vregs _ hr2)]
  simp only [loadDword?_vregs, absorbF_vregs]
  rw [run_tail_iff (t := { s with vregs := absorbF s B (ldFile s A laneLds s.vregs) }) hr1 hA hw
    hS hP]
  exact Iff.rfl

/-! ## Soundness -/


/-- The first row loads from `rs1`. -/
private theorem loadRows_cons (rs1 : regidx) : ∃ rest,
    loadRows rs1 = .LD .normal (.vreg (vr (48 + 0))) (.xreg rs1) (BitVec.ofNat 64 (8 * 0)) ::
      rest :=
  ⟨_, rfl⟩

private theorem reads_of_run {rs1 : regidx} {rest : List Instr} {s s' : SailJoltState}
    (h : (Program.seq (loadRows rs1 ++ rest)).Run s s') : XReads s rs1 (keccakA rs1 s) := by
  obtain ⟨tl, htl⟩ := loadRows_cons rs1
  rw [htl, List.cons_append] at h
  exact XReads.of_run_ld h

private theorem keccak256_reads {rs1 rs2 rs3 : regidx} {s s' : SailJoltState}
    (run : (keccak256RowsAuto rs1 rs2 rs3).Run s s') : XReads s rs1 (keccakA rs1 s) := by
  have h := run
  unfold keccak256RowsAuto at h
  rw [keccak256RowsAutoList_eq] at h
  simp only [List.append_assoc] at h
  exact reads_of_run h

/-- **Soundness of `KECCAK256`.** Every run of the rows from a state whose state buffer lies in
RAM loads the 25 lanes, stores `keccakF` of them at `rs1`, resets `vr48..84`, and changes nothing
else; the 25 stored doublewords read back.
Example: `JoltTests.KeccakInstance.keccak256_kat` for the zero state. -/
theorem keccak256_rows_sound {rs1 rs2 rs3 : regidx} {s s' : SailJoltState}
    (buf : KeccakBuffer rs1 s) (run : (keccak256RowsAuto rs1 rs2 rs3).Run s s') :
    Keccak256Spec rs1 s s' := by
  have hr1 := keccak256_reads run
  obtain ⟨hread, hwr, rfl⟩ := (keccak256_run_iff hr1 buf.ram buf.no_wrap).1 run
  exact ⟨hread, rfl, loadDword?_keccakFinal buf.ram buf.no_wrap hwr _⟩

/-- **The stored state is Keccak-f[1600].** After every run of the `KECCAK256` rows from a state
whose state buffer lies in RAM, the state at `rs1` is EthLib's `keccakF` of the state there
before. -/
theorem keccak256_rows_sound_keccakF {rs1 rs2 rs3 : regidx} {s s' : SailJoltState}
    (buf : KeccakBuffer rs1 s) (run : (keccak256RowsAuto rs1 rs2 rs3).Run s s') :
    stateAt s' (keccakA rs1 s) = keccakF (stateAt s (keccakA rs1 s)) := by
  have hr1 := keccak256_reads run
  obtain ⟨-, hwr, rfl⟩ := (keccak256_run_iff hr1 buf.ram buf.no_wrap).1 run
  exact stateAt_keccakFinal buf.ram buf.no_wrap hwr _

/-- The first absorption row loads from `rs2`. -/
private theorem absorbRows_cons (rs2 : regidx) : ∃ rest,
    absorbRows rs2 = .LD .normal (.vreg (vr scratch)) (.xreg rs2) (BitVec.ofNat 64 (8 * 0)) ::
      rest :=
  ⟨_, rfl⟩

private theorem absorb_reads {rs1 rs2 rs3 : regidx} {s s' : SailJoltState}
    (run : (keccak256AbsorbPermuteRowsAuto rs1 rs2 rs3).Run s s') :
    XReads s rs1 (keccakA rs1 s) ∧ XReads s rs2 (keccakB rs2 s) := by
  have h := run
  unfold keccak256AbsorbPermuteRowsAuto at h
  rw [absorbPermuteRowsAutoList_eq] at h
  simp only [List.append_assoc] at h
  have hr1 := reads_of_run h
  refine ⟨hr1, ?_⟩
  obtain ⟨rest, hrest⟩ := absorbRows_cons rs2
  rw [loadRows] at h
  rw [run_ldRows_iff hr1 laneLds laneLds_ge, hrest, List.cons_append] at h
  exact XReads.of_run_ld (s := { s with vregs := ldFile s (keccakA rs1 s) laneLds s.vregs }) h.2

/-- **Soundness of `KECCAK256_ABSORB_PERMUTE`.** Every run of the rows from a state whose state
buffer lies in RAM loads the 25 state lanes and the 17 block lanes, stores `absorbOut` at `rs1`,
resets `vr48..84`, and changes nothing else; the 25 stored doublewords read back.
Example: `JoltTests.KeccakInstance.absorbPermute_kat` for the padded empty message. -/
theorem absorbPermute_rows_sound {rs1 rs2 rs3 : regidx} {s s' : SailJoltState}
    (buf : KeccakBuffer rs1 s) (run : (keccak256AbsorbPermuteRowsAuto rs1 rs2 rs3).Run s s') :
    AbsorbPermuteSpec rs1 rs2 s s' := by
  obtain ⟨hr1, hr2⟩ := absorb_reads run
  obtain ⟨hread, hread2, hwr, rfl⟩ := (absorbPermute_run_iff hr1 hr2 buf.ram buf.no_wrap).1 run
  exact ⟨hread, hread2, rfl, loadDword?_keccakFinal buf.ram buf.no_wrap hwr _⟩

/-- **The stored state is the EthLib absorb-and-permute.** After every run of the
`KECCAK256_ABSORB_PERMUTE` rows from a state whose state buffer lies in RAM, the state at `rs1`
is `keccakF (Internal.absorbBlock 136 S block 0)`, where `S` is the state there before and
`block` is the 136 bytes at `rs2`, read as 17 little-endian lanes.
Example: from the zero state and the padded empty message, lanes 0 to 3 are Keccak-256(""). -/
theorem absorbPermute_rows_sound_keccakF {rs1 rs2 rs3 : regidx} {s s' : SailJoltState}
    (buf : KeccakBuffer rs1 s) (run : (keccak256AbsorbPermuteRowsAuto rs1 rs2 rs3).Run s s') :
    stateAt s' (keccakA rs1 s) = keccakF (absorbBlock 136 (stateAt s (keccakA rs1 s))
      (blockBytes (blockAt s (keccakB rs2 s))) 0) := by
  obtain ⟨hr1, hr2⟩ := absorb_reads run
  obtain ⟨-, -, hwr, rfl⟩ := (absorbPermute_run_iff hr1 hr2 buf.ram buf.no_wrap).1 run
  rw [stateAt_keccakFinal buf.ram buf.no_wrap hwr, absorbBlock_blockBytes _ _ (by simp [blockAt])]

/-! ## Completeness and determinism -/

/-- **Completeness of `KECCAK256`.** For a call that meets its obligations, the rows run, and the
end state meets the specification. The rows take no advice.
Example: `JoltTests.KeccakInstance.keccak256_kat`. -/
theorem keccak256_rows_complete {rs1 rs2 rs3 : regidx} {s : SailJoltState}
    (pre : Keccak256Pre rs1 s) :
    ∃ s', (keccak256RowsAuto rs1 rs2 rs3).Run s s' ∧ Keccak256Spec rs1 s s' := by
  have run : (keccak256RowsAuto rs1 rs2 rs3).Run s
      (keccakFinal s (keccakA rs1 s) (keccakF (stateAt s (keccakA rs1 s)))) :=
    (keccak256_run_iff pre.reads1 pre.ram pre.no_wrap).2 ⟨pre.readable, pre.writable, rfl⟩
  exact ⟨_, run, keccak256_rows_sound pre.toKeccakBuffer run⟩

/-- **Determinism of `KECCAK256`.** Two runs of the rows from the same state, whose state buffer
lies in RAM, end in the same state. -/
theorem keccak256_rows_deterministic {rs1 rs2 rs3 : regidx} {s s₁ s₂ : SailJoltState}
    (buf : KeccakBuffer rs1 s) (run₁ : (keccak256RowsAuto rs1 rs2 rs3).Run s s₁)
    (run₂ : (keccak256RowsAuto rs1 rs2 rs3).Run s s₂) : s₁ = s₂ :=
  (keccak256_rows_sound buf run₁).2.1.trans (keccak256_rows_sound buf run₂).2.1.symm

/-- **Completeness of `KECCAK256_ABSORB_PERMUTE`.** For a call that meets its obligations, the
rows run, and the end state meets the specification. The rows take no advice.
Example: `JoltTests.KeccakInstance.absorbPermute_kat`. -/
theorem absorbPermute_rows_complete {rs1 rs2 rs3 : regidx} {s : SailJoltState}
    (pre : AbsorbPermutePre rs1 rs2 s) :
    ∃ s', (keccak256AbsorbPermuteRowsAuto rs1 rs2 rs3).Run s s' ∧
      AbsorbPermuteSpec rs1 rs2 s s' := by
  have run : (keccak256AbsorbPermuteRowsAuto rs1 rs2 rs3).Run s
      (keccakFinal s (keccakA rs1 s) (absorbOut s (keccakA rs1 s) (keccakB rs2 s))) :=
    (absorbPermute_run_iff pre.reads1 pre.reads2 pre.ram pre.no_wrap).2
      ⟨pre.readable, pre.readable2, pre.writable, rfl⟩
  exact ⟨_, run, absorbPermute_rows_sound pre.toKeccakBuffer run⟩

/-- **Determinism of `KECCAK256_ABSORB_PERMUTE`.** Two runs of the rows from the same state,
whose state buffer lies in RAM, end in the same state. -/
theorem absorbPermute_rows_deterministic {rs1 rs2 rs3 : regidx} {s s₁ s₂ : SailJoltState}
    (buf : KeccakBuffer rs1 s) (run₁ : (keccak256AbsorbPermuteRowsAuto rs1 rs2 rs3).Run s s₁)
    (run₂ : (keccak256AbsorbPermuteRowsAuto rs1 rs2 rs3).Run s s₂) : s₁ = s₂ :=
  (absorbPermute_rows_sound buf run₁).2.2.1.trans (absorbPermute_rows_sound buf run₂).2.2.1.symm

/-! ## The `rd = x0` rows -/

/-- The `rd = x0` `KECCAK256` program is the `rd ≠ x0` program with any `rs3`. -/
theorem keccak256RowsAutoRdZero_eq (rs1 rs2 rs3 : regidx) :
    keccak256RowsAutoRdZero rs1 rs2 = keccak256RowsAuto rs1 rs2 rs3 := by
  unfold keccak256RowsAutoRdZero keccak256RowsAuto
  rw [keccak256RowsAutoRdZeroList_eq rs1 rs2 rs3]

/-- **Soundness of `KECCAK256`, `rd = x0`.** As `keccak256_rows_sound`. -/
theorem keccak256RdZero_rows_sound {rs1 rs2 : regidx} {s s' : SailJoltState}
    (buf : KeccakBuffer rs1 s) (run : (keccak256RowsAutoRdZero rs1 rs2).Run s s') :
    Keccak256Spec rs1 s s' := by
  rw [keccak256RowsAutoRdZero_eq rs1 rs2 rs1] at run
  exact keccak256_rows_sound buf run

/-- **The stored state is Keccak-f[1600], `rd = x0`.** As `keccak256_rows_sound_keccakF`. -/
theorem keccak256RdZero_rows_sound_keccakF {rs1 rs2 : regidx} {s s' : SailJoltState}
    (buf : KeccakBuffer rs1 s) (run : (keccak256RowsAutoRdZero rs1 rs2).Run s s') :
    stateAt s' (keccakA rs1 s) = keccakF (stateAt s (keccakA rs1 s)) := by
  rw [keccak256RowsAutoRdZero_eq rs1 rs2 rs1] at run
  exact keccak256_rows_sound_keccakF buf run

/-- **Completeness of `KECCAK256`, `rd = x0`.** As `keccak256_rows_complete`. -/
theorem keccak256RdZero_rows_complete {rs1 rs2 : regidx} {s : SailJoltState}
    (pre : Keccak256Pre rs1 s) :
    ∃ s', (keccak256RowsAutoRdZero rs1 rs2).Run s s' ∧ Keccak256Spec rs1 s s' := by
  rw [keccak256RowsAutoRdZero_eq rs1 rs2 rs1]
  exact keccak256_rows_complete pre

/-- **Determinism of `KECCAK256`, `rd = x0`.** As `keccak256_rows_deterministic`. -/
theorem keccak256RdZero_rows_deterministic {rs1 rs2 : regidx} {s s₁ s₂ : SailJoltState}
    (buf : KeccakBuffer rs1 s) (run₁ : (keccak256RowsAutoRdZero rs1 rs2).Run s s₁)
    (run₂ : (keccak256RowsAutoRdZero rs1 rs2).Run s s₂) : s₁ = s₂ := by
  rw [keccak256RowsAutoRdZero_eq rs1 rs2 rs1] at run₁ run₂
  exact keccak256_rows_deterministic buf run₁ run₂

/-- The `rd = x0` `KECCAK256_ABSORB_PERMUTE` program is the `rd ≠ x0` program with any `rs3`. -/
theorem absorbPermuteRowsAutoRdZero_eq (rs1 rs2 rs3 : regidx) :
    keccak256AbsorbPermuteRowsAutoRdZero rs1 rs2 = keccak256AbsorbPermuteRowsAuto rs1 rs2 rs3 := by
  unfold keccak256AbsorbPermuteRowsAutoRdZero keccak256AbsorbPermuteRowsAuto
  rw [absorbPermuteRowsAutoRdZeroList_eq rs1 rs2 rs3]

/-- **Soundness of `KECCAK256_ABSORB_PERMUTE`, `rd = x0`.** As `absorbPermute_rows_sound`. -/
theorem absorbPermuteRdZero_rows_sound {rs1 rs2 : regidx} {s s' : SailJoltState}
    (buf : KeccakBuffer rs1 s)
    (run : (keccak256AbsorbPermuteRowsAutoRdZero rs1 rs2).Run s s') :
    AbsorbPermuteSpec rs1 rs2 s s' := by
  rw [absorbPermuteRowsAutoRdZero_eq rs1 rs2 rs1] at run
  exact absorbPermute_rows_sound buf run

/-- **The stored state is the EthLib absorb-and-permute, `rd = x0`.** As
`absorbPermute_rows_sound_keccakF`. -/
theorem absorbPermuteRdZero_rows_sound_keccakF {rs1 rs2 : regidx} {s s' : SailJoltState}
    (buf : KeccakBuffer rs1 s)
    (run : (keccak256AbsorbPermuteRowsAutoRdZero rs1 rs2).Run s s') :
    stateAt s' (keccakA rs1 s) = keccakF (absorbBlock 136 (stateAt s (keccakA rs1 s))
      (blockBytes (blockAt s (keccakB rs2 s))) 0) := by
  rw [absorbPermuteRowsAutoRdZero_eq rs1 rs2 rs1] at run
  exact absorbPermute_rows_sound_keccakF buf run

/-- **Completeness of `KECCAK256_ABSORB_PERMUTE`, `rd = x0`.** As
`absorbPermute_rows_complete`. -/
theorem absorbPermuteRdZero_rows_complete {rs1 rs2 : regidx} {s : SailJoltState}
    (pre : AbsorbPermutePre rs1 rs2 s) :
    ∃ s', (keccak256AbsorbPermuteRowsAutoRdZero rs1 rs2).Run s s' ∧
      AbsorbPermuteSpec rs1 rs2 s s' := by
  rw [absorbPermuteRowsAutoRdZero_eq rs1 rs2 rs1]
  exact absorbPermute_rows_complete pre

/-- **Determinism of `KECCAK256_ABSORB_PERMUTE`, `rd = x0`.** As
`absorbPermute_rows_deterministic`. -/
theorem absorbPermuteRdZero_rows_deterministic {rs1 rs2 : regidx} {s s₁ s₂ : SailJoltState}
    (buf : KeccakBuffer rs1 s)
    (run₁ : (keccak256AbsorbPermuteRowsAutoRdZero rs1 rs2).Run s s₁)
    (run₂ : (keccak256AbsorbPermuteRowsAutoRdZero rs1 rs2).Run s s₂) : s₁ = s₂ := by
  rw [absorbPermuteRowsAutoRdZero_eq rs1 rs2 rs1] at run₁ run₂
  exact absorbPermute_rows_deterministic buf run₁ run₂

end JoltISA.Inlines.Keccak256
