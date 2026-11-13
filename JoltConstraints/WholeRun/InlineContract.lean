import JoltConstraints.WholeRun.InlineCalls
import JoltBytecode.Inlines.Blake2b.Sound
import JoltBytecode.Inlines.Sha256.Sound
import JoltBytecode.Inlines.Keccak256.Sound

/-!
# The contract of an inline call

This file states one contract for all twelve in-scope inlines and proves it for every run
of a call's rows, whatever advice words Jolt's tracer patched into them.

* `InlineKey.writeSet` is the call's write set (`FrameInstances`): the `rd = x0` write set
  of a hash inline when `rd = x0`, its `rd ≠ x0` write set otherwise.
* `InlineKey.Pre` is the call's precondition: the output buffer of the per-call soundness
  theorem lies in RAM and does not wrap (`Blake2Buffer`, `Sha256Buffer`, `KeccakBuffer`,
  `FieldMulBuffer`, `GlvrAdvBuffer`).
* `InlineKey.Spec` is the call's specification, the conclusion of the per-call soundness
  theorem (`Blake2Spec`, `Sha256Spec`, `Keccak256Spec`, `AbsorbPermuteSpec`,
  `FieldMulSpec`, `FieldDivSpec`, `GlvrAdvSpec`).

`InlineKey.call_contract` says that every run of `patchAdvice values (key.expandRows rs1 rs2 rd)`
keeps the frame of the write set and, under the precondition, meets the specification.
The hash rows have no VirtualAdvice row, so patching leaves them unchanged
(`blake2_noAdvice` and the other `*_noAdvice` lemmas); the secp256k1 rows become the rows with the patched words as
advice (`mulRows_patch`, `glvrAdvRows_patch`), and their soundness theorems hold for every
advice.

The specifications keep the known gaps of the per-call theorems visible: `GlvrAdvSpec` says
only that six words are stored, `FieldMulSpec` and `FieldDivSpec` allow a non-canonical
result, and `FieldDivSpec` holds for any stored result when both operands are zero
(`docs/inline-precompiles.md`, section 5).
-/

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail
  LeanRV64D LeanRV64D.Functions
open JoltISA JoltISA.Inlines JoltISA.Inlines.Secp256k1 JoltISA.Inlines.FrameInstances

set_option autoImplicit false

noncomputable section

namespace WholeRun

/-! ## Hash rows have no VirtualAdvice row -/

/-- An instruction that is not a VirtualAdvice row.
Example: `LD vr80, 0(x10)` passes and `VirtualAdvice vr48 0 0` does not. -/
def noAdviceRow (instruction : Instr) : Bool := instruction.adviceValue?.isNone

private theorem patch_of_all (values : List (BitVec 64)) {rows : List Instr}
    (h : rows.all noAdviceRow = true) : patchAdvice values rows = rows :=
  patchAdvice_of_forall_none values rows fun instruction mem => by
    have := List.all_eq_true.mp h instruction mem
    simpa [noAdviceRow] using this

open Generated in
private theorem blake2_noAdvice (rs1 rs2 rs3 : regidx) :
    (blake2RowsAutoList rs1 rs2 rs3).all noAdviceRow = true := by
  simp only [blake2RowsAutoList, List.all_append, Bool.and_eq_true]
  and_intros <;> rfl

open Generated in
private theorem sha256_noAdvice (rs1 rs2 rs3 : regidx) :
    (sha256RowsAutoList rs1 rs2 rs3).all noAdviceRow = true := by
  simp only [sha256RowsAutoList, List.all_append, Bool.and_eq_true]
  and_intros <;> rfl

open Generated in
private theorem sha256Init_noAdvice (rs1 rs2 rs3 : regidx) :
    (sha256InitRowsAutoList rs1 rs2 rs3).all noAdviceRow = true := by
  simp only [sha256InitRowsAutoList, List.all_append, Bool.and_eq_true]
  and_intros <;> rfl

private theorem keccakRounds_noAdvice : Keccak256.roundsRows.all noAdviceRow = true := by
  refine List.all_eq_true.mpr fun row mem => ?_
  simp only [Keccak256.roundsRows, Keccak256.roundRows, List.mem_flatMap, List.mem_map] at mem
  obtain ⟨_, _, op, _, rfl⟩ := mem
  cases op <;> rfl

open Generated in
private theorem keccak256_noAdvice (rs1 rs2 rs3 : regidx) :
    (keccak256RowsAutoList rs1 rs2 rs3).all noAdviceRow = true := by
  rw [Keccak256.keccak256RowsAutoList_eq]
  simp only [List.all_append, Bool.and_eq_true, keccakRounds_noAdvice]
  and_intros <;> first | rfl | trivial

open Generated in
private theorem absorbPermute_noAdvice (rs1 rs2 rs3 : regidx) :
    (keccak256AbsorbPermuteRowsAutoList rs1 rs2 rs3).all noAdviceRow = true := by
  rw [Keccak256.absorbPermuteRowsAutoList_eq]
  simp only [List.all_append, Bool.and_eq_true, keccakRounds_noAdvice]
  and_intros <;> first | rfl | trivial

/-- **Hash rows ignore advice.** Patching any words into the rows of a hash inline leaves them as
they are: neither the `rd ≠ x0` rows nor the `rd = x0` rows have a VirtualAdvice row.
Example: `patchAdvice [7] (blake2.expandRows x10 x11 x0) = blake2.expandRows x10 x11 x0`. -/
theorem hash_patchAdvice (key : InlineKey) (hash : key.readsRd = false) (rs1 rs2 rd : regidx)
    (values : List (BitVec 64)) :
    patchAdvice values (key.expandRows rs1 rs2 rd) = key.expandRows rs1 rs2 rd := by
  cases key <;> simp only [InlineKey.readsRd, Bool.true_eq_false] at hash <;>
    cases zero : isX0 rd <;>
    simp only [InlineKey.expandRows, InlineKey.rows, InlineKey.rowsRdZero, zero,
      Bool.false_eq_true, ↓reduceIte]
  · exact patch_of_all values (sha256_noAdvice rs1 rs2 rd)
  · exact patch_of_all values
      (Sha256.sha256RowsAutoRdZeroList_eq rs1 rs2 rs1 ▸ sha256_noAdvice rs1 rs2 rs1)
  · exact patch_of_all values (sha256Init_noAdvice rs1 rs2 rd)
  · exact patch_of_all values (Sha256.sha256InitRowsAutoRdZeroList_eq rs1 rs2 rs1 ▸
      sha256Init_noAdvice rs1 rs2 rs1)
  · exact patch_of_all values (keccak256_noAdvice rs1 rs2 rd)
  · exact patch_of_all values (Keccak256.keccak256RowsAutoRdZeroList_eq rs1 rs2 rs1 ▸
      keccak256_noAdvice rs1 rs2 rs1)
  · exact patch_of_all values (absorbPermute_noAdvice rs1 rs2 rd)
  · exact patch_of_all values (Keccak256.absorbPermuteRowsAutoRdZeroList_eq rs1 rs2 rs1 ▸
      absorbPermute_noAdvice rs1 rs2 rs1)
  · exact patch_of_all values (blake2_noAdvice rs1 rs2 rd)
  · exact patch_of_all values (Blake2b.blake2RowsAutoRdZeroList_eq rs1 rs2 rs1 ▸
      blake2_noAdvice rs1 rs2 rs1)

end WholeRun

/-! ## The contract -/

namespace JoltISA.Inlines.InlineKey

open WholeRun

/-- The write set of the call `key rd, rs1, rs2` (`FrameInstances`). A hash inline with
`rd = x0` runs its `rd = x0` rows; a secp256k1 inline never has `rd = x0` (decision D7).
Example: `blake2.writeSet x10 x11 x0 = blake2RdZeroWriteSet x10`. -/
def writeSet : InlineKey → regidx → regidx → regidx → WriteSet
  | .sha256, rs1, _, rd =>
      if isX0 rd then sha256RdZeroWriteSet rs1 else sha256WriteSet rs1
  | .sha256Init, rs1, _, rd =>
      if isX0 rd then sha256InitRdZeroWriteSet rs1 else sha256InitWriteSet rs1
  | .keccak256, rs1, _, rd =>
      if isX0 rd then keccak256RdZeroWriteSet rs1 else keccak256WriteSet rs1
  | .keccak256AbsorbPermute, rs1, _, rd =>
      if isX0 rd then keccak256AbsorbPermuteRdZeroWriteSet rs1
      else keccak256AbsorbPermuteWriteSet rs1
  | .blake2, rs1, _, rd =>
      if isX0 rd then blake2RdZeroWriteSet rs1 else blake2WriteSet rs1
  | .secp256k1Mulq, _, _, rd => secp256k1MulqWriteSet rd
  | .secp256k1Mulr, _, _, rd => secp256k1MulrWriteSet rd
  | .secp256k1Squareq, _, _, rd => secp256k1SquareqWriteSet rd
  | .secp256k1Squarer, _, _, rd => secp256k1SquarerWriteSet rd
  | .secp256k1Divq, _, _, rd => secp256k1DivqWriteSet rd
  | .secp256k1Divr, _, _, rd => secp256k1DivrWriteSet rd
  | .secp256k1GlvrAdv, _, _, rd => secp256k1GlvrAdvWriteSet rd

/-- The precondition of the call `key rd, rs1, rs2` in state `s`: the output buffer lies in
RAM and does not wrap. The hash inlines write the state at the address in `rs1`; the
secp256k1 inlines write the result at the address in `rd`.
Example: `blake2.Pre x10 x11 x0 s` says that the 64 bytes at `x10` lie in RAM. -/
def Pre : InlineKey → regidx → regidx → regidx → SailJoltState → Prop
  | .sha256, rs1, _, _ => Sha256.Sha256Buffer rs1
  | .sha256Init, rs1, _, _ => Sha256.Sha256Buffer rs1
  | .keccak256, rs1, _, _ => Keccak256.KeccakBuffer rs1
  | .keccak256AbsorbPermute, rs1, _, _ => Keccak256.KeccakBuffer rs1
  | .blake2, rs1, _, _ => Blake2b.Blake2Buffer rs1
  | .secp256k1Mulq, _, _, rd => FieldMulBuffer rd
  | .secp256k1Mulr, _, _, rd => FieldMulBuffer rd
  | .secp256k1Squareq, _, _, rd => FieldMulBuffer rd
  | .secp256k1Squarer, _, _, rd => FieldMulBuffer rd
  | .secp256k1Divq, _, _, rd => FieldMulBuffer rd
  | .secp256k1Divr, _, _, rd => FieldMulBuffer rd
  | .secp256k1GlvrAdv, _, _, rd => GlvrAdvBuffer rd

/-- The specification of the call `key rd, rs1, rs2` from state `s` to state `s'`: the
conclusion of the key's per-call soundness theorem.
Example: `blake2.Spec x10 x11 x0 s s'` is `Blake2Spec x10 x11 s s'`: `s'` is `s` with the
BLAKE2b compression of the inputs at `x10` and `x11` stored at `x10`. -/
def Spec : InlineKey → regidx → regidx → regidx → SailJoltState → SailJoltState → Prop
  | .sha256, rs1, rs2, _ => Sha256.Sha256Spec false rs1 rs2
  | .sha256Init, rs1, rs2, _ => Sha256.Sha256Spec true rs1 rs2
  | .keccak256, rs1, _, _ => Keccak256.Keccak256Spec rs1
  | .keccak256AbsorbPermute, rs1, rs2, _ => Keccak256.AbsorbPermuteSpec rs1 rs2
  | .blake2, rs1, rs2, _ => Blake2b.Blake2Spec rs1 rs2
  | .secp256k1Mulq, rs1, rs2, rd => FieldMulSpec p .mul rs1 rs2 rd
  | .secp256k1Mulr, rs1, rs2, rd => FieldMulSpec n .mul rs1 rs2 rd
  | .secp256k1Squareq, rs1, rs2, rd => FieldMulSpec p .square rs1 rs2 rd
  | .secp256k1Squarer, rs1, rs2, rd => FieldMulSpec n .square rs1 rs2 rd
  | .secp256k1Divq, rs1, rs2, rd => FieldDivSpec p rs1 rs2 rd
  | .secp256k1Divr, rs1, rs2, rd => FieldDivSpec n rs1 rs2 rd
  | .secp256k1GlvrAdv, _, _, rd => GlvrAdvSpec rd

/-- **The contract of one inline call.** Let the call `key rd, rs1, rs2` be one that
`SourceInstruction.expand` accepts: `rd ≠ x0` when the key reads `rd`. Every run of the
call's rows, with any advice words patched in, keeps the frame of the call's write set, and
meets the call's specification when the call's precondition holds in the start state.
Example: a run of the `SECP256K1_MULQ` rows with the advice words `[5, 0, 0, 0]` from a
state whose `rd` buffer lies in RAM stores some `c` with `a·b = w·p + c` for the stored
quotient `w`. -/
theorem call_contract (key : InlineKey) (rs1 rs2 rd : regidx)
    (accepted : key.readsRd = true → isX0 rd = false)
    (values : List (BitVec 64)) {s s' : SailJoltState}
    (run : (Program.seq (patchAdvice values (key.expandRows rs1 rs2 rd))).Run s s') :
    Frame (key.writeSet rs1 rs2 rd) s s' ∧ (key.Pre rs1 rs2 rd s → key.Spec rs1 rs2 rd s s') := by
  cases key
  case sha256 =>
    cases zero : isX0 rd
    · simp only [expandRows, rows, zero, Bool.false_eq_true, ↓reduceIte] at run
      rw [patch_of_all values (sha256_noAdvice rs1 rs2 rd)] at run
      simp only [writeSet, Pre, Spec, zero, Bool.false_eq_true, ↓reduceIte]
      exact ⟨sha256_frame rs1 rs2 rd run, fun buf => Sha256.sha256_rows_sound buf run⟩
    · simp only [expandRows, rowsRdZero, zero, ↓reduceIte] at run
      rw [patch_of_all values
        (Sha256.sha256RowsAutoRdZeroList_eq rs1 rs2 rs1 ▸ sha256_noAdvice rs1 rs2 rs1)] at run
      simp only [writeSet, Pre, Spec, zero, ↓reduceIte]
      exact ⟨sha256RdZero_frame rs1 rs2 run, fun buf => Sha256.sha256RdZero_rows_sound buf run⟩
  case sha256Init =>
    cases zero : isX0 rd
    · simp only [expandRows, rows, zero, Bool.false_eq_true, ↓reduceIte] at run
      rw [patch_of_all values (sha256Init_noAdvice rs1 rs2 rd)] at run
      simp only [writeSet, Pre, Spec, zero, Bool.false_eq_true, ↓reduceIte]
      exact ⟨sha256Init_frame rs1 rs2 rd run, fun buf => Sha256.sha256Init_rows_sound buf run⟩
    · simp only [expandRows, rowsRdZero, zero, ↓reduceIte] at run
      rw [patch_of_all values (Sha256.sha256InitRowsAutoRdZeroList_eq rs1 rs2 rs1 ▸
        sha256Init_noAdvice rs1 rs2 rs1)] at run
      simp only [writeSet, Pre, Spec, zero, ↓reduceIte]
      exact ⟨sha256InitRdZero_frame rs1 rs2 run,
        fun buf => Sha256.sha256InitRdZero_rows_sound buf run⟩
  case keccak256 =>
    cases zero : isX0 rd
    · simp only [expandRows, rows, zero, Bool.false_eq_true, ↓reduceIte] at run
      rw [patch_of_all values (keccak256_noAdvice rs1 rs2 rd)] at run
      simp only [writeSet, Pre, Spec, zero, Bool.false_eq_true, ↓reduceIte]
      exact ⟨keccak256_frame rs1 rs2 rd run, fun buf => Keccak256.keccak256_rows_sound buf run⟩
    · simp only [expandRows, rowsRdZero, zero, ↓reduceIte] at run
      rw [patch_of_all values (Keccak256.keccak256RowsAutoRdZeroList_eq rs1 rs2 rs1 ▸
        keccak256_noAdvice rs1 rs2 rs1)] at run
      simp only [writeSet, Pre, Spec, zero, ↓reduceIte]
      exact ⟨keccak256RdZero_frame rs1 rs2 run,
        fun buf => Keccak256.keccak256RdZero_rows_sound buf run⟩
  case keccak256AbsorbPermute =>
    cases zero : isX0 rd
    · simp only [expandRows, rows, zero, Bool.false_eq_true, ↓reduceIte] at run
      rw [patch_of_all values (absorbPermute_noAdvice rs1 rs2 rd)] at run
      simp only [writeSet, Pre, Spec, zero, Bool.false_eq_true, ↓reduceIte]
      exact ⟨keccak256AbsorbPermute_frame rs1 rs2 rd run,
        fun buf => Keccak256.absorbPermute_rows_sound buf run⟩
    · simp only [expandRows, rowsRdZero, zero, ↓reduceIte] at run
      rw [patch_of_all values (Keccak256.absorbPermuteRowsAutoRdZeroList_eq rs1 rs2 rs1 ▸
        absorbPermute_noAdvice rs1 rs2 rs1)] at run
      simp only [writeSet, Pre, Spec, zero, ↓reduceIte]
      exact ⟨keccak256AbsorbPermuteRdZero_frame rs1 rs2 run,
        fun buf => Keccak256.absorbPermuteRdZero_rows_sound buf run⟩
  case blake2 =>
    cases zero : isX0 rd
    · simp only [expandRows, rows, zero, Bool.false_eq_true, ↓reduceIte] at run
      rw [patch_of_all values (blake2_noAdvice rs1 rs2 rd)] at run
      simp only [writeSet, Pre, Spec, zero, Bool.false_eq_true, ↓reduceIte]
      exact ⟨blake2_frame rs1 rs2 rd run, fun buf => Blake2b.blake2_rows_sound buf run⟩
    · simp only [expandRows, rowsRdZero, zero, ↓reduceIte] at run
      rw [patch_of_all values (Blake2b.blake2RowsAutoRdZeroList_eq rs1 rs2 rs1 ▸
        blake2_noAdvice rs1 rs2 rs1)] at run
      simp only [writeSet, Pre, Spec, zero, ↓reduceIte]
      exact ⟨blake2RdZero_frame rs1 rs2 run, fun buf => Blake2b.blake2RdZero_rows_sound buf run⟩
  case secp256k1Mulq =>
    simp only [expandRows, rows, accepted rfl, Bool.false_eq_true, ↓reduceIte] at run
    rw [secp256k1MulqRowsAutoList_eq, mulRows_patch, ← secp256k1MulqRowsAutoList_eq] at run
    exact ⟨secp256k1Mulq_frame _ _ _ _ run, fun buf => secp256k1Mulq_rows_sound buf run⟩
  case secp256k1Mulr =>
    simp only [expandRows, rows, accepted rfl, Bool.false_eq_true, ↓reduceIte] at run
    rw [secp256k1MulrRowsAutoList_eq, mulRows_patch, ← secp256k1MulrRowsAutoList_eq] at run
    exact ⟨secp256k1Mulr_frame _ _ _ _ run, fun buf => secp256k1Mulr_rows_sound buf run⟩
  case secp256k1Squareq =>
    simp only [expandRows, rows, accepted rfl, Bool.false_eq_true, ↓reduceIte] at run
    rw [secp256k1SquareqRowsAutoList_eq, mulRows_patch, ← secp256k1SquareqRowsAutoList_eq] at run
    exact ⟨secp256k1Squareq_frame _ _ _ _ run, fun buf => secp256k1Squareq_rows_sound buf run⟩
  case secp256k1Squarer =>
    simp only [expandRows, rows, accepted rfl, Bool.false_eq_true, ↓reduceIte] at run
    rw [secp256k1SquarerRowsAutoList_eq, mulRows_patch, ← secp256k1SquarerRowsAutoList_eq] at run
    exact ⟨secp256k1Squarer_frame _ _ _ _ run, fun buf => secp256k1Squarer_rows_sound buf run⟩
  case secp256k1Divq =>
    simp only [expandRows, rows, accepted rfl, Bool.false_eq_true, ↓reduceIte] at run
    rw [secp256k1DivqRowsAutoList_eq, mulRows_patch, ← secp256k1DivqRowsAutoList_eq] at run
    exact ⟨secp256k1Divq_frame _ _ _ _ run, fun buf => secp256k1Divq_rows_sound buf run⟩
  case secp256k1Divr =>
    simp only [expandRows, rows, accepted rfl, Bool.false_eq_true, ↓reduceIte] at run
    rw [secp256k1DivrRowsAutoList_eq, mulRows_patch, ← secp256k1DivrRowsAutoList_eq] at run
    exact ⟨secp256k1Divr_frame _ _ _ _ run, fun buf => secp256k1Divr_rows_sound buf run⟩
  case secp256k1GlvrAdv =>
    simp only [expandRows, rows, accepted rfl, Bool.false_eq_true, ↓reduceIte,
      glvrAdvRows_patch] at run
    exact ⟨secp256k1GlvrAdv_frame _ _ _ _ run, fun buf => glvrAdv_rows_sound buf run⟩

end JoltISA.Inlines.InlineKey
