import JoltBytecode.Inlines.Frame
import JoltBytecode.Inlines.Generated.Sha256
import JoltBytecode.Inlines.Generated.Sha256Init
import JoltBytecode.Inlines.Generated.Keccak256
import JoltBytecode.Inlines.Generated.Keccak256AbsorbPermute
import JoltBytecode.Inlines.Generated.Blake2
import JoltBytecode.Inlines.Generated.Secp256k1Mulq
import JoltBytecode.Inlines.Generated.Secp256k1Mulr
import JoltBytecode.Inlines.Generated.Secp256k1Squareq
import JoltBytecode.Inlines.Generated.Secp256k1Squarer
import JoltBytecode.Inlines.Generated.Secp256k1Divq
import JoltBytecode.Inlines.Generated.Secp256k1Divr
import JoltBytecode.Inlines.Generated.Secp256k1GlvrAdv

/-!
# Write sets of the twelve in-scope inlines

For each in-scope inline and each allocation case (`rd ≠ x0` and `rd = x0`) this file
gives the write set, the store slots of the generated rows, the static frame check
`Program.WritesWithin` and the pool-reset check, and the frame corollary.

The write sets are exact: `vregs` lists the pool registers the rows write (always a
contiguous range from `vr48`), `xregs` is empty, and `stores` lists the store rows.
No row writes an instruction temporary `vr40..47` or an architectural register.

The checks run chunk by chunk. Each `_chunkN` lemma checks one generated chunk (about
100 rows) by `rfl`, and `Program.rowsWithin_seq_append`, `Program.storeSlots_seq_append`
and `Program.resetsPoolCheck_seq_append` assemble the chunks. `rfl` works although the
rows take free register parameters: with `xregs = []` the checks never compare two
architectural registers. A single `rfl` or `decide` on a whole program exceeds the
default recursion depth, and checking every chunk inside one declaration exceeds the
default heartbeat budget for the 31- and 32-chunk Keccak programs.
-/

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail LeanRV64D
  LeanRV64D.Functions

set_option autoImplicit false

noncomputable section

namespace JoltISA.Inlines.FrameInstances

open JoltISA.Inlines.Generated

/-- The pool registers `vr48 .. vr(48 + n - 1)`. -/
def poolVRegs (n : Nat) : List VReg := (List.range n).map fun k => BitVec.ofNat 7 (48 + k)

/-! ### `Sha256`, rd ≠ x0 -/

/-- Store slots of `Sha256` (rd ≠ x0). -/
def sha256Stores (rs1 : regidx) : List StoreSlot :=
  [⟨.xreg rs1, 0, .dword⟩, ⟨.xreg rs1, 8, .dword⟩, ⟨.xreg rs1, 16, .dword⟩,
    ⟨.xreg rs1, 24, .dword⟩]

/-- Write set of `Sha256` (rd ≠ x0): pool registers `vr48..vr83`, no
architectural register, 4 store rows. -/
def sha256WriteSet (rs1 : regidx) : WriteSet where
  vregs := poolVRegs 36
  xregs := []
  stores := sha256Stores rs1

/-- Chunk 0 of `Sha256` (rd ≠ x0). -/
theorem sha256_chunk0
    (rs1 rs2 rs3 : regidx) :
    (Program.seq (sha256RowsAutoChunk0 rs1 rs2 rs3)).rowsWithin (sha256WriteSet rs1) = true ∧
      (Program.seq (sha256RowsAutoChunk0 rs1 rs2 rs3)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 1 of `Sha256` (rd ≠ x0). -/
theorem sha256_chunk1
    (rs1 rs2 rs3 : regidx) :
    (Program.seq (sha256RowsAutoChunk1 rs1 rs2 rs3)).rowsWithin (sha256WriteSet rs1) = true ∧
      (Program.seq (sha256RowsAutoChunk1 rs1 rs2 rs3)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 2 of `Sha256` (rd ≠ x0). -/
theorem sha256_chunk2
    (rs1 rs2 rs3 : regidx) :
    (Program.seq (sha256RowsAutoChunk2 rs1 rs2 rs3)).rowsWithin (sha256WriteSet rs1) = true ∧
      (Program.seq (sha256RowsAutoChunk2 rs1 rs2 rs3)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 3 of `Sha256` (rd ≠ x0). -/
theorem sha256_chunk3
    (rs1 rs2 rs3 : regidx) :
    (Program.seq (sha256RowsAutoChunk3 rs1 rs2 rs3)).rowsWithin (sha256WriteSet rs1) = true ∧
      (Program.seq (sha256RowsAutoChunk3 rs1 rs2 rs3)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 4 of `Sha256` (rd ≠ x0). -/
theorem sha256_chunk4
    (rs1 rs2 rs3 : regidx) :
    (Program.seq (sha256RowsAutoChunk4 rs1 rs2 rs3)).rowsWithin (sha256WriteSet rs1) = true ∧
      (Program.seq (sha256RowsAutoChunk4 rs1 rs2 rs3)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 5 of `Sha256` (rd ≠ x0). -/
theorem sha256_chunk5
    (rs1 rs2 rs3 : regidx) :
    (Program.seq (sha256RowsAutoChunk5 rs1 rs2 rs3)).rowsWithin (sha256WriteSet rs1) = true ∧
      (Program.seq (sha256RowsAutoChunk5 rs1 rs2 rs3)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 6 of `Sha256` (rd ≠ x0). -/
theorem sha256_chunk6
    (rs1 rs2 rs3 : regidx) :
    (Program.seq (sha256RowsAutoChunk6 rs1 rs2 rs3)).rowsWithin (sha256WriteSet rs1) = true ∧
      (Program.seq (sha256RowsAutoChunk6 rs1 rs2 rs3)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 7 of `Sha256` (rd ≠ x0). -/
theorem sha256_chunk7
    (rs1 rs2 rs3 : regidx) :
    (Program.seq (sha256RowsAutoChunk7 rs1 rs2 rs3)).rowsWithin (sha256WriteSet rs1) = true ∧
      (Program.seq (sha256RowsAutoChunk7 rs1 rs2 rs3)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 8 of `Sha256` (rd ≠ x0). -/
theorem sha256_chunk8
    (rs1 rs2 rs3 : regidx) :
    (Program.seq (sha256RowsAutoChunk8 rs1 rs2 rs3)).rowsWithin (sha256WriteSet rs1) = true ∧
      (Program.seq (sha256RowsAutoChunk8 rs1 rs2 rs3)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 9 of `Sha256` (rd ≠ x0). -/
theorem sha256_chunk9
    (rs1 rs2 rs3 : regidx) :
    (Program.seq (sha256RowsAutoChunk9 rs1 rs2 rs3)).rowsWithin (sha256WriteSet rs1) = true ∧
      (Program.seq (sha256RowsAutoChunk9 rs1 rs2 rs3)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 10 of `Sha256` (rd ≠ x0). -/
theorem sha256_chunk10
    (rs1 rs2 rs3 : regidx) :
    (Program.seq (sha256RowsAutoChunk10 rs1 rs2 rs3)).rowsWithin (sha256WriteSet rs1) = true ∧
      (Program.seq (sha256RowsAutoChunk10 rs1 rs2 rs3)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 11 of `Sha256` (rd ≠ x0). -/
theorem sha256_chunk11
    (rs1 rs2 rs3 : regidx) :
    (Program.seq (sha256RowsAutoChunk11 rs1 rs2 rs3)).rowsWithin (sha256WriteSet rs1) = true ∧
      (Program.seq (sha256RowsAutoChunk11 rs1 rs2 rs3)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 12 of `Sha256` (rd ≠ x0). -/
theorem sha256_chunk12
    (rs1 rs2 rs3 : regidx) :
    (Program.seq (sha256RowsAutoChunk12 rs1 rs2 rs3)).rowsWithin (sha256WriteSet rs1) = true ∧
      (Program.seq (sha256RowsAutoChunk12 rs1 rs2 rs3)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 13 of `Sha256` (rd ≠ x0). -/
theorem sha256_chunk13
    (rs1 rs2 rs3 : regidx) :
    (Program.seq (sha256RowsAutoChunk13 rs1 rs2 rs3)).rowsWithin (sha256WriteSet rs1) = true ∧
      (Program.seq (sha256RowsAutoChunk13 rs1 rs2 rs3)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 14 of `Sha256` (rd ≠ x0). -/
theorem sha256_chunk14
    (rs1 rs2 rs3 : regidx) :
    (Program.seq (sha256RowsAutoChunk14 rs1 rs2 rs3)).rowsWithin (sha256WriteSet rs1) = true ∧
      (Program.seq (sha256RowsAutoChunk14 rs1 rs2 rs3)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 15 of `Sha256` (rd ≠ x0). -/
theorem sha256_chunk15
    (rs1 rs2 rs3 : regidx) :
    (Program.seq (sha256RowsAutoChunk15 rs1 rs2 rs3)).rowsWithin (sha256WriteSet rs1) = true ∧
      (Program.seq (sha256RowsAutoChunk15 rs1 rs2 rs3)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 16 of `Sha256` (rd ≠ x0). -/
theorem sha256_chunk16
    (rs1 rs2 rs3 : regidx) :
    (Program.seq (sha256RowsAutoChunk16 rs1 rs2 rs3)).rowsWithin (sha256WriteSet rs1) = true ∧
      (Program.seq (sha256RowsAutoChunk16 rs1 rs2 rs3)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 17 of `Sha256` (rd ≠ x0). -/
theorem sha256_chunk17
    (rs1 rs2 rs3 : regidx) :
    (Program.seq (sha256RowsAutoChunk17 rs1 rs2 rs3)).rowsWithin (sha256WriteSet rs1) = true ∧
      (Program.seq (sha256RowsAutoChunk17 rs1 rs2 rs3)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 18 of `Sha256` (rd ≠ x0). -/
theorem sha256_chunk18
    (rs1 rs2 rs3 : regidx) :
    (Program.seq (sha256RowsAutoChunk18 rs1 rs2 rs3)).rowsWithin (sha256WriteSet rs1) = true ∧
      (Program.seq (sha256RowsAutoChunk18 rs1 rs2 rs3)).storeSlots =
        [⟨.xreg rs1, 0, .dword⟩, ⟨.xreg rs1, 8, .dword⟩, ⟨.xreg rs1, 16, .dword⟩, ⟨.xreg rs1, 24, .dword⟩] :=
  ⟨rfl, rfl⟩

theorem sha256_storeSlots
    (rs1 rs2 rs3 : regidx) :
    (sha256RowsAuto rs1 rs2 rs3).storeSlots =
      sha256Stores rs1 := by
  unfold sha256RowsAuto sha256RowsAutoList
  simp only [Program.storeSlots_seq_append,
      (sha256_chunk0 rs1 rs2 rs3).2,
      (sha256_chunk1 rs1 rs2 rs3).2,
      (sha256_chunk2 rs1 rs2 rs3).2,
      (sha256_chunk3 rs1 rs2 rs3).2,
      (sha256_chunk4 rs1 rs2 rs3).2,
      (sha256_chunk5 rs1 rs2 rs3).2,
      (sha256_chunk6 rs1 rs2 rs3).2,
      (sha256_chunk7 rs1 rs2 rs3).2,
      (sha256_chunk8 rs1 rs2 rs3).2,
      (sha256_chunk9 rs1 rs2 rs3).2,
      (sha256_chunk10 rs1 rs2 rs3).2,
      (sha256_chunk11 rs1 rs2 rs3).2,
      (sha256_chunk12 rs1 rs2 rs3).2,
      (sha256_chunk13 rs1 rs2 rs3).2,
      (sha256_chunk14 rs1 rs2 rs3).2,
      (sha256_chunk15 rs1 rs2 rs3).2,
      (sha256_chunk16 rs1 rs2 rs3).2,
      (sha256_chunk17 rs1 rs2 rs3).2,
      (sha256_chunk18 rs1 rs2 rs3).2]
  rfl

theorem sha256_writesWithin
    (rs1 rs2 rs3 : regidx) :
    (sha256RowsAuto rs1 rs2 rs3).WritesWithin
      (sha256WriteSet rs1) :=
  ⟨by
    unfold sha256RowsAuto sha256RowsAutoList
    simp only [Program.rowsWithin_seq_append,
      (sha256_chunk0 rs1 rs2 rs3).1,
      (sha256_chunk1 rs1 rs2 rs3).1,
      (sha256_chunk2 rs1 rs2 rs3).1,
      (sha256_chunk3 rs1 rs2 rs3).1,
      (sha256_chunk4 rs1 rs2 rs3).1,
      (sha256_chunk5 rs1 rs2 rs3).1,
      (sha256_chunk6 rs1 rs2 rs3).1,
      (sha256_chunk7 rs1 rs2 rs3).1,
      (sha256_chunk8 rs1 rs2 rs3).1,
      (sha256_chunk9 rs1 rs2 rs3).1,
      (sha256_chunk10 rs1 rs2 rs3).1,
      (sha256_chunk11 rs1 rs2 rs3).1,
      (sha256_chunk12 rs1 rs2 rs3).1,
      (sha256_chunk13 rs1 rs2 rs3).1,
      (sha256_chunk14 rs1 rs2 rs3).1,
      (sha256_chunk15 rs1 rs2 rs3).1,
      (sha256_chunk16 rs1 rs2 rs3).1,
      (sha256_chunk17 rs1 rs2 rs3).1,
      (sha256_chunk18 rs1 rs2 rs3).1,
      Bool.and_self],
   by rw [sha256_storeSlots]; exact List.Subset.refl _, rfl⟩

/-- The final chunks of `Sha256` (rd ≠ x0), which contain the last write of every
pool register. -/
theorem sha256_tailResets
    (rs1 rs2 rs3 : regidx) :
    (Program.seq (sha256RowsAutoChunk18 rs1 rs2 rs3)).resetsPoolCheck (poolVRegs 36) = true := rfl

theorem sha256_resetsPoolCheck
    (rs1 rs2 rs3 : regidx) :
    (sha256RowsAuto rs1 rs2 rs3).resetsPoolCheck (poolVRegs 36) = true := by
  unfold sha256RowsAuto sha256RowsAutoList
  exact Program.resetsPoolCheck_seq_append _ (sha256_tailResets rs1 rs2 rs3)

theorem sha256_frame
    (rs1 rs2 rs3 : regidx) {s s' : SailJoltState}
    (h : (sha256RowsAuto rs1 rs2 rs3).Run s s') :
    Frame (sha256WriteSet rs1) s s' :=
  frame_of_run (sha256_writesWithin rs1 rs2 rs3) h

/-! ### `Sha256`, rd = x0 -/

/-- Store slots of `Sha256` (rd = x0). -/
def sha256RdZeroStores (rs1 : regidx) : List StoreSlot :=
  [⟨.xreg rs1, 0, .dword⟩, ⟨.xreg rs1, 8, .dword⟩, ⟨.xreg rs1, 16, .dword⟩,
    ⟨.xreg rs1, 24, .dword⟩]

/-- Write set of `Sha256` (rd = x0): pool registers `vr48..vr83`, no
architectural register, 4 store rows. -/
def sha256RdZeroWriteSet (rs1 : regidx) : WriteSet where
  vregs := poolVRegs 36
  xregs := []
  stores := sha256RdZeroStores rs1

/-- Chunk 0 of `Sha256` (rd = x0). -/
theorem sha256RdZero_chunk0
    (rs1 rs2 : regidx) :
    (Program.seq (sha256RowsAutoRdZeroChunk0 rs1 rs2)).rowsWithin (sha256RdZeroWriteSet rs1) = true ∧
      (Program.seq (sha256RowsAutoRdZeroChunk0 rs1 rs2)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 1 of `Sha256` (rd = x0). -/
theorem sha256RdZero_chunk1
    (rs1 rs2 : regidx) :
    (Program.seq (sha256RowsAutoRdZeroChunk1 rs1 rs2)).rowsWithin (sha256RdZeroWriteSet rs1) = true ∧
      (Program.seq (sha256RowsAutoRdZeroChunk1 rs1 rs2)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 2 of `Sha256` (rd = x0). -/
theorem sha256RdZero_chunk2
    (rs1 rs2 : regidx) :
    (Program.seq (sha256RowsAutoRdZeroChunk2 rs1 rs2)).rowsWithin (sha256RdZeroWriteSet rs1) = true ∧
      (Program.seq (sha256RowsAutoRdZeroChunk2 rs1 rs2)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 3 of `Sha256` (rd = x0). -/
theorem sha256RdZero_chunk3
    (rs1 rs2 : regidx) :
    (Program.seq (sha256RowsAutoRdZeroChunk3 rs1 rs2)).rowsWithin (sha256RdZeroWriteSet rs1) = true ∧
      (Program.seq (sha256RowsAutoRdZeroChunk3 rs1 rs2)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 4 of `Sha256` (rd = x0). -/
theorem sha256RdZero_chunk4
    (rs1 rs2 : regidx) :
    (Program.seq (sha256RowsAutoRdZeroChunk4 rs1 rs2)).rowsWithin (sha256RdZeroWriteSet rs1) = true ∧
      (Program.seq (sha256RowsAutoRdZeroChunk4 rs1 rs2)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 5 of `Sha256` (rd = x0). -/
theorem sha256RdZero_chunk5
    (rs1 rs2 : regidx) :
    (Program.seq (sha256RowsAutoRdZeroChunk5 rs1 rs2)).rowsWithin (sha256RdZeroWriteSet rs1) = true ∧
      (Program.seq (sha256RowsAutoRdZeroChunk5 rs1 rs2)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 6 of `Sha256` (rd = x0). -/
theorem sha256RdZero_chunk6
    (rs1 rs2 : regidx) :
    (Program.seq (sha256RowsAutoRdZeroChunk6 rs1 rs2)).rowsWithin (sha256RdZeroWriteSet rs1) = true ∧
      (Program.seq (sha256RowsAutoRdZeroChunk6 rs1 rs2)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 7 of `Sha256` (rd = x0). -/
theorem sha256RdZero_chunk7
    (rs1 rs2 : regidx) :
    (Program.seq (sha256RowsAutoRdZeroChunk7 rs1 rs2)).rowsWithin (sha256RdZeroWriteSet rs1) = true ∧
      (Program.seq (sha256RowsAutoRdZeroChunk7 rs1 rs2)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 8 of `Sha256` (rd = x0). -/
theorem sha256RdZero_chunk8
    (rs1 rs2 : regidx) :
    (Program.seq (sha256RowsAutoRdZeroChunk8 rs1 rs2)).rowsWithin (sha256RdZeroWriteSet rs1) = true ∧
      (Program.seq (sha256RowsAutoRdZeroChunk8 rs1 rs2)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 9 of `Sha256` (rd = x0). -/
theorem sha256RdZero_chunk9
    (rs1 rs2 : regidx) :
    (Program.seq (sha256RowsAutoRdZeroChunk9 rs1 rs2)).rowsWithin (sha256RdZeroWriteSet rs1) = true ∧
      (Program.seq (sha256RowsAutoRdZeroChunk9 rs1 rs2)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 10 of `Sha256` (rd = x0). -/
theorem sha256RdZero_chunk10
    (rs1 rs2 : regidx) :
    (Program.seq (sha256RowsAutoRdZeroChunk10 rs1 rs2)).rowsWithin (sha256RdZeroWriteSet rs1) = true ∧
      (Program.seq (sha256RowsAutoRdZeroChunk10 rs1 rs2)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 11 of `Sha256` (rd = x0). -/
theorem sha256RdZero_chunk11
    (rs1 rs2 : regidx) :
    (Program.seq (sha256RowsAutoRdZeroChunk11 rs1 rs2)).rowsWithin (sha256RdZeroWriteSet rs1) = true ∧
      (Program.seq (sha256RowsAutoRdZeroChunk11 rs1 rs2)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 12 of `Sha256` (rd = x0). -/
theorem sha256RdZero_chunk12
    (rs1 rs2 : regidx) :
    (Program.seq (sha256RowsAutoRdZeroChunk12 rs1 rs2)).rowsWithin (sha256RdZeroWriteSet rs1) = true ∧
      (Program.seq (sha256RowsAutoRdZeroChunk12 rs1 rs2)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 13 of `Sha256` (rd = x0). -/
theorem sha256RdZero_chunk13
    (rs1 rs2 : regidx) :
    (Program.seq (sha256RowsAutoRdZeroChunk13 rs1 rs2)).rowsWithin (sha256RdZeroWriteSet rs1) = true ∧
      (Program.seq (sha256RowsAutoRdZeroChunk13 rs1 rs2)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 14 of `Sha256` (rd = x0). -/
theorem sha256RdZero_chunk14
    (rs1 rs2 : regidx) :
    (Program.seq (sha256RowsAutoRdZeroChunk14 rs1 rs2)).rowsWithin (sha256RdZeroWriteSet rs1) = true ∧
      (Program.seq (sha256RowsAutoRdZeroChunk14 rs1 rs2)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 15 of `Sha256` (rd = x0). -/
theorem sha256RdZero_chunk15
    (rs1 rs2 : regidx) :
    (Program.seq (sha256RowsAutoRdZeroChunk15 rs1 rs2)).rowsWithin (sha256RdZeroWriteSet rs1) = true ∧
      (Program.seq (sha256RowsAutoRdZeroChunk15 rs1 rs2)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 16 of `Sha256` (rd = x0). -/
theorem sha256RdZero_chunk16
    (rs1 rs2 : regidx) :
    (Program.seq (sha256RowsAutoRdZeroChunk16 rs1 rs2)).rowsWithin (sha256RdZeroWriteSet rs1) = true ∧
      (Program.seq (sha256RowsAutoRdZeroChunk16 rs1 rs2)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 17 of `Sha256` (rd = x0). -/
theorem sha256RdZero_chunk17
    (rs1 rs2 : regidx) :
    (Program.seq (sha256RowsAutoRdZeroChunk17 rs1 rs2)).rowsWithin (sha256RdZeroWriteSet rs1) = true ∧
      (Program.seq (sha256RowsAutoRdZeroChunk17 rs1 rs2)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 18 of `Sha256` (rd = x0). -/
theorem sha256RdZero_chunk18
    (rs1 rs2 : regidx) :
    (Program.seq (sha256RowsAutoRdZeroChunk18 rs1 rs2)).rowsWithin (sha256RdZeroWriteSet rs1) = true ∧
      (Program.seq (sha256RowsAutoRdZeroChunk18 rs1 rs2)).storeSlots =
        [⟨.xreg rs1, 0, .dword⟩, ⟨.xreg rs1, 8, .dword⟩, ⟨.xreg rs1, 16, .dword⟩, ⟨.xreg rs1, 24, .dword⟩] :=
  ⟨rfl, rfl⟩

theorem sha256RdZero_storeSlots
    (rs1 rs2 : regidx) :
    (sha256RowsAutoRdZero rs1 rs2).storeSlots =
      sha256RdZeroStores rs1 := by
  unfold sha256RowsAutoRdZero sha256RowsAutoRdZeroList
  simp only [Program.storeSlots_seq_append,
      (sha256RdZero_chunk0 rs1 rs2).2,
      (sha256RdZero_chunk1 rs1 rs2).2,
      (sha256RdZero_chunk2 rs1 rs2).2,
      (sha256RdZero_chunk3 rs1 rs2).2,
      (sha256RdZero_chunk4 rs1 rs2).2,
      (sha256RdZero_chunk5 rs1 rs2).2,
      (sha256RdZero_chunk6 rs1 rs2).2,
      (sha256RdZero_chunk7 rs1 rs2).2,
      (sha256RdZero_chunk8 rs1 rs2).2,
      (sha256RdZero_chunk9 rs1 rs2).2,
      (sha256RdZero_chunk10 rs1 rs2).2,
      (sha256RdZero_chunk11 rs1 rs2).2,
      (sha256RdZero_chunk12 rs1 rs2).2,
      (sha256RdZero_chunk13 rs1 rs2).2,
      (sha256RdZero_chunk14 rs1 rs2).2,
      (sha256RdZero_chunk15 rs1 rs2).2,
      (sha256RdZero_chunk16 rs1 rs2).2,
      (sha256RdZero_chunk17 rs1 rs2).2,
      (sha256RdZero_chunk18 rs1 rs2).2]
  rfl

theorem sha256RdZero_writesWithin
    (rs1 rs2 : regidx) :
    (sha256RowsAutoRdZero rs1 rs2).WritesWithin
      (sha256RdZeroWriteSet rs1) :=
  ⟨by
    unfold sha256RowsAutoRdZero sha256RowsAutoRdZeroList
    simp only [Program.rowsWithin_seq_append,
      (sha256RdZero_chunk0 rs1 rs2).1,
      (sha256RdZero_chunk1 rs1 rs2).1,
      (sha256RdZero_chunk2 rs1 rs2).1,
      (sha256RdZero_chunk3 rs1 rs2).1,
      (sha256RdZero_chunk4 rs1 rs2).1,
      (sha256RdZero_chunk5 rs1 rs2).1,
      (sha256RdZero_chunk6 rs1 rs2).1,
      (sha256RdZero_chunk7 rs1 rs2).1,
      (sha256RdZero_chunk8 rs1 rs2).1,
      (sha256RdZero_chunk9 rs1 rs2).1,
      (sha256RdZero_chunk10 rs1 rs2).1,
      (sha256RdZero_chunk11 rs1 rs2).1,
      (sha256RdZero_chunk12 rs1 rs2).1,
      (sha256RdZero_chunk13 rs1 rs2).1,
      (sha256RdZero_chunk14 rs1 rs2).1,
      (sha256RdZero_chunk15 rs1 rs2).1,
      (sha256RdZero_chunk16 rs1 rs2).1,
      (sha256RdZero_chunk17 rs1 rs2).1,
      (sha256RdZero_chunk18 rs1 rs2).1,
      Bool.and_self],
   by rw [sha256RdZero_storeSlots]; exact List.Subset.refl _, rfl⟩

/-- The final chunks of `Sha256` (rd = x0), which contain the last write of every
pool register. -/
theorem sha256RdZero_tailResets
    (rs1 rs2 : regidx) :
    (Program.seq (sha256RowsAutoRdZeroChunk18 rs1 rs2)).resetsPoolCheck (poolVRegs 36) = true := rfl

theorem sha256RdZero_resetsPoolCheck
    (rs1 rs2 : regidx) :
    (sha256RowsAutoRdZero rs1 rs2).resetsPoolCheck (poolVRegs 36) = true := by
  unfold sha256RowsAutoRdZero sha256RowsAutoRdZeroList
  exact Program.resetsPoolCheck_seq_append _ (sha256RdZero_tailResets rs1 rs2)

theorem sha256RdZero_frame
    (rs1 rs2 : regidx) {s s' : SailJoltState}
    (h : (sha256RowsAutoRdZero rs1 rs2).Run s s') :
    Frame (sha256RdZeroWriteSet rs1) s s' :=
  frame_of_run (sha256RdZero_writesWithin rs1 rs2) h

/-! ### `Sha256Init`, rd ≠ x0 -/

/-- Store slots of `Sha256Init` (rd ≠ x0). -/
def sha256InitStores (rs1 : regidx) : List StoreSlot :=
  [⟨.xreg rs1, 0, .dword⟩, ⟨.xreg rs1, 8, .dword⟩, ⟨.xreg rs1, 16, .dword⟩,
    ⟨.xreg rs1, 24, .dword⟩]

/-- Write set of `Sha256Init` (rd ≠ x0): pool registers `vr48..vr75`, no
architectural register, 4 store rows. -/
def sha256InitWriteSet (rs1 : regidx) : WriteSet where
  vregs := poolVRegs 28
  xregs := []
  stores := sha256InitStores rs1

/-- Chunk 0 of `Sha256Init` (rd ≠ x0). -/
theorem sha256Init_chunk0
    (rs1 rs2 rs3 : regidx) :
    (Program.seq (sha256InitRowsAutoChunk0 rs1 rs2 rs3)).rowsWithin (sha256InitWriteSet rs1) = true ∧
      (Program.seq (sha256InitRowsAutoChunk0 rs1 rs2 rs3)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 1 of `Sha256Init` (rd ≠ x0). -/
theorem sha256Init_chunk1
    (rs1 rs2 rs3 : regidx) :
    (Program.seq (sha256InitRowsAutoChunk1 rs1 rs2 rs3)).rowsWithin (sha256InitWriteSet rs1) = true ∧
      (Program.seq (sha256InitRowsAutoChunk1 rs1 rs2 rs3)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 2 of `Sha256Init` (rd ≠ x0). -/
theorem sha256Init_chunk2
    (rs1 rs2 rs3 : regidx) :
    (Program.seq (sha256InitRowsAutoChunk2 rs1 rs2 rs3)).rowsWithin (sha256InitWriteSet rs1) = true ∧
      (Program.seq (sha256InitRowsAutoChunk2 rs1 rs2 rs3)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 3 of `Sha256Init` (rd ≠ x0). -/
theorem sha256Init_chunk3
    (rs1 rs2 rs3 : regidx) :
    (Program.seq (sha256InitRowsAutoChunk3 rs1 rs2 rs3)).rowsWithin (sha256InitWriteSet rs1) = true ∧
      (Program.seq (sha256InitRowsAutoChunk3 rs1 rs2 rs3)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 4 of `Sha256Init` (rd ≠ x0). -/
theorem sha256Init_chunk4
    (rs1 rs2 rs3 : regidx) :
    (Program.seq (sha256InitRowsAutoChunk4 rs1 rs2 rs3)).rowsWithin (sha256InitWriteSet rs1) = true ∧
      (Program.seq (sha256InitRowsAutoChunk4 rs1 rs2 rs3)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 5 of `Sha256Init` (rd ≠ x0). -/
theorem sha256Init_chunk5
    (rs1 rs2 rs3 : regidx) :
    (Program.seq (sha256InitRowsAutoChunk5 rs1 rs2 rs3)).rowsWithin (sha256InitWriteSet rs1) = true ∧
      (Program.seq (sha256InitRowsAutoChunk5 rs1 rs2 rs3)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 6 of `Sha256Init` (rd ≠ x0). -/
theorem sha256Init_chunk6
    (rs1 rs2 rs3 : regidx) :
    (Program.seq (sha256InitRowsAutoChunk6 rs1 rs2 rs3)).rowsWithin (sha256InitWriteSet rs1) = true ∧
      (Program.seq (sha256InitRowsAutoChunk6 rs1 rs2 rs3)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 7 of `Sha256Init` (rd ≠ x0). -/
theorem sha256Init_chunk7
    (rs1 rs2 rs3 : regidx) :
    (Program.seq (sha256InitRowsAutoChunk7 rs1 rs2 rs3)).rowsWithin (sha256InitWriteSet rs1) = true ∧
      (Program.seq (sha256InitRowsAutoChunk7 rs1 rs2 rs3)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 8 of `Sha256Init` (rd ≠ x0). -/
theorem sha256Init_chunk8
    (rs1 rs2 rs3 : regidx) :
    (Program.seq (sha256InitRowsAutoChunk8 rs1 rs2 rs3)).rowsWithin (sha256InitWriteSet rs1) = true ∧
      (Program.seq (sha256InitRowsAutoChunk8 rs1 rs2 rs3)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 9 of `Sha256Init` (rd ≠ x0). -/
theorem sha256Init_chunk9
    (rs1 rs2 rs3 : regidx) :
    (Program.seq (sha256InitRowsAutoChunk9 rs1 rs2 rs3)).rowsWithin (sha256InitWriteSet rs1) = true ∧
      (Program.seq (sha256InitRowsAutoChunk9 rs1 rs2 rs3)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 10 of `Sha256Init` (rd ≠ x0). -/
theorem sha256Init_chunk10
    (rs1 rs2 rs3 : regidx) :
    (Program.seq (sha256InitRowsAutoChunk10 rs1 rs2 rs3)).rowsWithin (sha256InitWriteSet rs1) = true ∧
      (Program.seq (sha256InitRowsAutoChunk10 rs1 rs2 rs3)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 11 of `Sha256Init` (rd ≠ x0). -/
theorem sha256Init_chunk11
    (rs1 rs2 rs3 : regidx) :
    (Program.seq (sha256InitRowsAutoChunk11 rs1 rs2 rs3)).rowsWithin (sha256InitWriteSet rs1) = true ∧
      (Program.seq (sha256InitRowsAutoChunk11 rs1 rs2 rs3)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 12 of `Sha256Init` (rd ≠ x0). -/
theorem sha256Init_chunk12
    (rs1 rs2 rs3 : regidx) :
    (Program.seq (sha256InitRowsAutoChunk12 rs1 rs2 rs3)).rowsWithin (sha256InitWriteSet rs1) = true ∧
      (Program.seq (sha256InitRowsAutoChunk12 rs1 rs2 rs3)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 13 of `Sha256Init` (rd ≠ x0). -/
theorem sha256Init_chunk13
    (rs1 rs2 rs3 : regidx) :
    (Program.seq (sha256InitRowsAutoChunk13 rs1 rs2 rs3)).rowsWithin (sha256InitWriteSet rs1) = true ∧
      (Program.seq (sha256InitRowsAutoChunk13 rs1 rs2 rs3)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 14 of `Sha256Init` (rd ≠ x0). -/
theorem sha256Init_chunk14
    (rs1 rs2 rs3 : regidx) :
    (Program.seq (sha256InitRowsAutoChunk14 rs1 rs2 rs3)).rowsWithin (sha256InitWriteSet rs1) = true ∧
      (Program.seq (sha256InitRowsAutoChunk14 rs1 rs2 rs3)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 15 of `Sha256Init` (rd ≠ x0). -/
theorem sha256Init_chunk15
    (rs1 rs2 rs3 : regidx) :
    (Program.seq (sha256InitRowsAutoChunk15 rs1 rs2 rs3)).rowsWithin (sha256InitWriteSet rs1) = true ∧
      (Program.seq (sha256InitRowsAutoChunk15 rs1 rs2 rs3)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 16 of `Sha256Init` (rd ≠ x0). -/
theorem sha256Init_chunk16
    (rs1 rs2 rs3 : regidx) :
    (Program.seq (sha256InitRowsAutoChunk16 rs1 rs2 rs3)).rowsWithin (sha256InitWriteSet rs1) = true ∧
      (Program.seq (sha256InitRowsAutoChunk16 rs1 rs2 rs3)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 17 of `Sha256Init` (rd ≠ x0). -/
theorem sha256Init_chunk17
    (rs1 rs2 rs3 : regidx) :
    (Program.seq (sha256InitRowsAutoChunk17 rs1 rs2 rs3)).rowsWithin (sha256InitWriteSet rs1) = true ∧
      (Program.seq (sha256InitRowsAutoChunk17 rs1 rs2 rs3)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 18 of `Sha256Init` (rd ≠ x0). -/
theorem sha256Init_chunk18
    (rs1 rs2 rs3 : regidx) :
    (Program.seq (sha256InitRowsAutoChunk18 rs1 rs2 rs3)).rowsWithin (sha256InitWriteSet rs1) = true ∧
      (Program.seq (sha256InitRowsAutoChunk18 rs1 rs2 rs3)).storeSlots =
        [⟨.xreg rs1, 0, .dword⟩, ⟨.xreg rs1, 8, .dword⟩, ⟨.xreg rs1, 16, .dword⟩, ⟨.xreg rs1, 24, .dword⟩] :=
  ⟨rfl, rfl⟩

theorem sha256Init_storeSlots
    (rs1 rs2 rs3 : regidx) :
    (sha256InitRowsAuto rs1 rs2 rs3).storeSlots =
      sha256InitStores rs1 := by
  unfold sha256InitRowsAuto sha256InitRowsAutoList
  simp only [Program.storeSlots_seq_append,
      (sha256Init_chunk0 rs1 rs2 rs3).2,
      (sha256Init_chunk1 rs1 rs2 rs3).2,
      (sha256Init_chunk2 rs1 rs2 rs3).2,
      (sha256Init_chunk3 rs1 rs2 rs3).2,
      (sha256Init_chunk4 rs1 rs2 rs3).2,
      (sha256Init_chunk5 rs1 rs2 rs3).2,
      (sha256Init_chunk6 rs1 rs2 rs3).2,
      (sha256Init_chunk7 rs1 rs2 rs3).2,
      (sha256Init_chunk8 rs1 rs2 rs3).2,
      (sha256Init_chunk9 rs1 rs2 rs3).2,
      (sha256Init_chunk10 rs1 rs2 rs3).2,
      (sha256Init_chunk11 rs1 rs2 rs3).2,
      (sha256Init_chunk12 rs1 rs2 rs3).2,
      (sha256Init_chunk13 rs1 rs2 rs3).2,
      (sha256Init_chunk14 rs1 rs2 rs3).2,
      (sha256Init_chunk15 rs1 rs2 rs3).2,
      (sha256Init_chunk16 rs1 rs2 rs3).2,
      (sha256Init_chunk17 rs1 rs2 rs3).2,
      (sha256Init_chunk18 rs1 rs2 rs3).2]
  rfl

theorem sha256Init_writesWithin
    (rs1 rs2 rs3 : regidx) :
    (sha256InitRowsAuto rs1 rs2 rs3).WritesWithin
      (sha256InitWriteSet rs1) :=
  ⟨by
    unfold sha256InitRowsAuto sha256InitRowsAutoList
    simp only [Program.rowsWithin_seq_append,
      (sha256Init_chunk0 rs1 rs2 rs3).1,
      (sha256Init_chunk1 rs1 rs2 rs3).1,
      (sha256Init_chunk2 rs1 rs2 rs3).1,
      (sha256Init_chunk3 rs1 rs2 rs3).1,
      (sha256Init_chunk4 rs1 rs2 rs3).1,
      (sha256Init_chunk5 rs1 rs2 rs3).1,
      (sha256Init_chunk6 rs1 rs2 rs3).1,
      (sha256Init_chunk7 rs1 rs2 rs3).1,
      (sha256Init_chunk8 rs1 rs2 rs3).1,
      (sha256Init_chunk9 rs1 rs2 rs3).1,
      (sha256Init_chunk10 rs1 rs2 rs3).1,
      (sha256Init_chunk11 rs1 rs2 rs3).1,
      (sha256Init_chunk12 rs1 rs2 rs3).1,
      (sha256Init_chunk13 rs1 rs2 rs3).1,
      (sha256Init_chunk14 rs1 rs2 rs3).1,
      (sha256Init_chunk15 rs1 rs2 rs3).1,
      (sha256Init_chunk16 rs1 rs2 rs3).1,
      (sha256Init_chunk17 rs1 rs2 rs3).1,
      (sha256Init_chunk18 rs1 rs2 rs3).1,
      Bool.and_self],
   by rw [sha256Init_storeSlots]; exact List.Subset.refl _, rfl⟩

/-- The final chunks of `Sha256Init` (rd ≠ x0), which contain the last write of every
pool register. -/
theorem sha256Init_tailResets
    (rs1 rs2 rs3 : regidx) :
    (Program.seq (sha256InitRowsAutoChunk18 rs1 rs2 rs3)).resetsPoolCheck (poolVRegs 28) = true := rfl

theorem sha256Init_resetsPoolCheck
    (rs1 rs2 rs3 : regidx) :
    (sha256InitRowsAuto rs1 rs2 rs3).resetsPoolCheck (poolVRegs 28) = true := by
  unfold sha256InitRowsAuto sha256InitRowsAutoList
  exact Program.resetsPoolCheck_seq_append _ (sha256Init_tailResets rs1 rs2 rs3)

theorem sha256Init_frame
    (rs1 rs2 rs3 : regidx) {s s' : SailJoltState}
    (h : (sha256InitRowsAuto rs1 rs2 rs3).Run s s') :
    Frame (sha256InitWriteSet rs1) s s' :=
  frame_of_run (sha256Init_writesWithin rs1 rs2 rs3) h

/-! ### `Sha256Init`, rd = x0 -/

/-- Store slots of `Sha256Init` (rd = x0). -/
def sha256InitRdZeroStores (rs1 : regidx) : List StoreSlot :=
  [⟨.xreg rs1, 0, .dword⟩, ⟨.xreg rs1, 8, .dword⟩, ⟨.xreg rs1, 16, .dword⟩,
    ⟨.xreg rs1, 24, .dword⟩]

/-- Write set of `Sha256Init` (rd = x0): pool registers `vr48..vr75`, no
architectural register, 4 store rows. -/
def sha256InitRdZeroWriteSet (rs1 : regidx) : WriteSet where
  vregs := poolVRegs 28
  xregs := []
  stores := sha256InitRdZeroStores rs1

/-- Chunk 0 of `Sha256Init` (rd = x0). -/
theorem sha256InitRdZero_chunk0
    (rs1 rs2 : regidx) :
    (Program.seq (sha256InitRowsAutoRdZeroChunk0 rs1 rs2)).rowsWithin (sha256InitRdZeroWriteSet rs1) = true ∧
      (Program.seq (sha256InitRowsAutoRdZeroChunk0 rs1 rs2)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 1 of `Sha256Init` (rd = x0). -/
theorem sha256InitRdZero_chunk1
    (rs1 rs2 : regidx) :
    (Program.seq (sha256InitRowsAutoRdZeroChunk1 rs1 rs2)).rowsWithin (sha256InitRdZeroWriteSet rs1) = true ∧
      (Program.seq (sha256InitRowsAutoRdZeroChunk1 rs1 rs2)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 2 of `Sha256Init` (rd = x0). -/
theorem sha256InitRdZero_chunk2
    (rs1 rs2 : regidx) :
    (Program.seq (sha256InitRowsAutoRdZeroChunk2 rs1 rs2)).rowsWithin (sha256InitRdZeroWriteSet rs1) = true ∧
      (Program.seq (sha256InitRowsAutoRdZeroChunk2 rs1 rs2)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 3 of `Sha256Init` (rd = x0). -/
theorem sha256InitRdZero_chunk3
    (rs1 rs2 : regidx) :
    (Program.seq (sha256InitRowsAutoRdZeroChunk3 rs1 rs2)).rowsWithin (sha256InitRdZeroWriteSet rs1) = true ∧
      (Program.seq (sha256InitRowsAutoRdZeroChunk3 rs1 rs2)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 4 of `Sha256Init` (rd = x0). -/
theorem sha256InitRdZero_chunk4
    (rs1 rs2 : regidx) :
    (Program.seq (sha256InitRowsAutoRdZeroChunk4 rs1 rs2)).rowsWithin (sha256InitRdZeroWriteSet rs1) = true ∧
      (Program.seq (sha256InitRowsAutoRdZeroChunk4 rs1 rs2)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 5 of `Sha256Init` (rd = x0). -/
theorem sha256InitRdZero_chunk5
    (rs1 rs2 : regidx) :
    (Program.seq (sha256InitRowsAutoRdZeroChunk5 rs1 rs2)).rowsWithin (sha256InitRdZeroWriteSet rs1) = true ∧
      (Program.seq (sha256InitRowsAutoRdZeroChunk5 rs1 rs2)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 6 of `Sha256Init` (rd = x0). -/
theorem sha256InitRdZero_chunk6
    (rs1 rs2 : regidx) :
    (Program.seq (sha256InitRowsAutoRdZeroChunk6 rs1 rs2)).rowsWithin (sha256InitRdZeroWriteSet rs1) = true ∧
      (Program.seq (sha256InitRowsAutoRdZeroChunk6 rs1 rs2)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 7 of `Sha256Init` (rd = x0). -/
theorem sha256InitRdZero_chunk7
    (rs1 rs2 : regidx) :
    (Program.seq (sha256InitRowsAutoRdZeroChunk7 rs1 rs2)).rowsWithin (sha256InitRdZeroWriteSet rs1) = true ∧
      (Program.seq (sha256InitRowsAutoRdZeroChunk7 rs1 rs2)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 8 of `Sha256Init` (rd = x0). -/
theorem sha256InitRdZero_chunk8
    (rs1 rs2 : regidx) :
    (Program.seq (sha256InitRowsAutoRdZeroChunk8 rs1 rs2)).rowsWithin (sha256InitRdZeroWriteSet rs1) = true ∧
      (Program.seq (sha256InitRowsAutoRdZeroChunk8 rs1 rs2)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 9 of `Sha256Init` (rd = x0). -/
theorem sha256InitRdZero_chunk9
    (rs1 rs2 : regidx) :
    (Program.seq (sha256InitRowsAutoRdZeroChunk9 rs1 rs2)).rowsWithin (sha256InitRdZeroWriteSet rs1) = true ∧
      (Program.seq (sha256InitRowsAutoRdZeroChunk9 rs1 rs2)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 10 of `Sha256Init` (rd = x0). -/
theorem sha256InitRdZero_chunk10
    (rs1 rs2 : regidx) :
    (Program.seq (sha256InitRowsAutoRdZeroChunk10 rs1 rs2)).rowsWithin (sha256InitRdZeroWriteSet rs1) = true ∧
      (Program.seq (sha256InitRowsAutoRdZeroChunk10 rs1 rs2)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 11 of `Sha256Init` (rd = x0). -/
theorem sha256InitRdZero_chunk11
    (rs1 rs2 : regidx) :
    (Program.seq (sha256InitRowsAutoRdZeroChunk11 rs1 rs2)).rowsWithin (sha256InitRdZeroWriteSet rs1) = true ∧
      (Program.seq (sha256InitRowsAutoRdZeroChunk11 rs1 rs2)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 12 of `Sha256Init` (rd = x0). -/
theorem sha256InitRdZero_chunk12
    (rs1 rs2 : regidx) :
    (Program.seq (sha256InitRowsAutoRdZeroChunk12 rs1 rs2)).rowsWithin (sha256InitRdZeroWriteSet rs1) = true ∧
      (Program.seq (sha256InitRowsAutoRdZeroChunk12 rs1 rs2)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 13 of `Sha256Init` (rd = x0). -/
theorem sha256InitRdZero_chunk13
    (rs1 rs2 : regidx) :
    (Program.seq (sha256InitRowsAutoRdZeroChunk13 rs1 rs2)).rowsWithin (sha256InitRdZeroWriteSet rs1) = true ∧
      (Program.seq (sha256InitRowsAutoRdZeroChunk13 rs1 rs2)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 14 of `Sha256Init` (rd = x0). -/
theorem sha256InitRdZero_chunk14
    (rs1 rs2 : regidx) :
    (Program.seq (sha256InitRowsAutoRdZeroChunk14 rs1 rs2)).rowsWithin (sha256InitRdZeroWriteSet rs1) = true ∧
      (Program.seq (sha256InitRowsAutoRdZeroChunk14 rs1 rs2)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 15 of `Sha256Init` (rd = x0). -/
theorem sha256InitRdZero_chunk15
    (rs1 rs2 : regidx) :
    (Program.seq (sha256InitRowsAutoRdZeroChunk15 rs1 rs2)).rowsWithin (sha256InitRdZeroWriteSet rs1) = true ∧
      (Program.seq (sha256InitRowsAutoRdZeroChunk15 rs1 rs2)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 16 of `Sha256Init` (rd = x0). -/
theorem sha256InitRdZero_chunk16
    (rs1 rs2 : regidx) :
    (Program.seq (sha256InitRowsAutoRdZeroChunk16 rs1 rs2)).rowsWithin (sha256InitRdZeroWriteSet rs1) = true ∧
      (Program.seq (sha256InitRowsAutoRdZeroChunk16 rs1 rs2)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 17 of `Sha256Init` (rd = x0). -/
theorem sha256InitRdZero_chunk17
    (rs1 rs2 : regidx) :
    (Program.seq (sha256InitRowsAutoRdZeroChunk17 rs1 rs2)).rowsWithin (sha256InitRdZeroWriteSet rs1) = true ∧
      (Program.seq (sha256InitRowsAutoRdZeroChunk17 rs1 rs2)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 18 of `Sha256Init` (rd = x0). -/
theorem sha256InitRdZero_chunk18
    (rs1 rs2 : regidx) :
    (Program.seq (sha256InitRowsAutoRdZeroChunk18 rs1 rs2)).rowsWithin (sha256InitRdZeroWriteSet rs1) = true ∧
      (Program.seq (sha256InitRowsAutoRdZeroChunk18 rs1 rs2)).storeSlots =
        [⟨.xreg rs1, 0, .dword⟩, ⟨.xreg rs1, 8, .dword⟩, ⟨.xreg rs1, 16, .dword⟩, ⟨.xreg rs1, 24, .dword⟩] :=
  ⟨rfl, rfl⟩

theorem sha256InitRdZero_storeSlots
    (rs1 rs2 : regidx) :
    (sha256InitRowsAutoRdZero rs1 rs2).storeSlots =
      sha256InitRdZeroStores rs1 := by
  unfold sha256InitRowsAutoRdZero sha256InitRowsAutoRdZeroList
  simp only [Program.storeSlots_seq_append,
      (sha256InitRdZero_chunk0 rs1 rs2).2,
      (sha256InitRdZero_chunk1 rs1 rs2).2,
      (sha256InitRdZero_chunk2 rs1 rs2).2,
      (sha256InitRdZero_chunk3 rs1 rs2).2,
      (sha256InitRdZero_chunk4 rs1 rs2).2,
      (sha256InitRdZero_chunk5 rs1 rs2).2,
      (sha256InitRdZero_chunk6 rs1 rs2).2,
      (sha256InitRdZero_chunk7 rs1 rs2).2,
      (sha256InitRdZero_chunk8 rs1 rs2).2,
      (sha256InitRdZero_chunk9 rs1 rs2).2,
      (sha256InitRdZero_chunk10 rs1 rs2).2,
      (sha256InitRdZero_chunk11 rs1 rs2).2,
      (sha256InitRdZero_chunk12 rs1 rs2).2,
      (sha256InitRdZero_chunk13 rs1 rs2).2,
      (sha256InitRdZero_chunk14 rs1 rs2).2,
      (sha256InitRdZero_chunk15 rs1 rs2).2,
      (sha256InitRdZero_chunk16 rs1 rs2).2,
      (sha256InitRdZero_chunk17 rs1 rs2).2,
      (sha256InitRdZero_chunk18 rs1 rs2).2]
  rfl

theorem sha256InitRdZero_writesWithin
    (rs1 rs2 : regidx) :
    (sha256InitRowsAutoRdZero rs1 rs2).WritesWithin
      (sha256InitRdZeroWriteSet rs1) :=
  ⟨by
    unfold sha256InitRowsAutoRdZero sha256InitRowsAutoRdZeroList
    simp only [Program.rowsWithin_seq_append,
      (sha256InitRdZero_chunk0 rs1 rs2).1,
      (sha256InitRdZero_chunk1 rs1 rs2).1,
      (sha256InitRdZero_chunk2 rs1 rs2).1,
      (sha256InitRdZero_chunk3 rs1 rs2).1,
      (sha256InitRdZero_chunk4 rs1 rs2).1,
      (sha256InitRdZero_chunk5 rs1 rs2).1,
      (sha256InitRdZero_chunk6 rs1 rs2).1,
      (sha256InitRdZero_chunk7 rs1 rs2).1,
      (sha256InitRdZero_chunk8 rs1 rs2).1,
      (sha256InitRdZero_chunk9 rs1 rs2).1,
      (sha256InitRdZero_chunk10 rs1 rs2).1,
      (sha256InitRdZero_chunk11 rs1 rs2).1,
      (sha256InitRdZero_chunk12 rs1 rs2).1,
      (sha256InitRdZero_chunk13 rs1 rs2).1,
      (sha256InitRdZero_chunk14 rs1 rs2).1,
      (sha256InitRdZero_chunk15 rs1 rs2).1,
      (sha256InitRdZero_chunk16 rs1 rs2).1,
      (sha256InitRdZero_chunk17 rs1 rs2).1,
      (sha256InitRdZero_chunk18 rs1 rs2).1,
      Bool.and_self],
   by rw [sha256InitRdZero_storeSlots]; exact List.Subset.refl _, rfl⟩

/-- The final chunks of `Sha256Init` (rd = x0), which contain the last write of every
pool register. -/
theorem sha256InitRdZero_tailResets
    (rs1 rs2 : regidx) :
    (Program.seq (sha256InitRowsAutoRdZeroChunk18 rs1 rs2)).resetsPoolCheck (poolVRegs 28) = true := rfl

theorem sha256InitRdZero_resetsPoolCheck
    (rs1 rs2 : regidx) :
    (sha256InitRowsAutoRdZero rs1 rs2).resetsPoolCheck (poolVRegs 28) = true := by
  unfold sha256InitRowsAutoRdZero sha256InitRowsAutoRdZeroList
  exact Program.resetsPoolCheck_seq_append _ (sha256InitRdZero_tailResets rs1 rs2)

theorem sha256InitRdZero_frame
    (rs1 rs2 : regidx) {s s' : SailJoltState}
    (h : (sha256InitRowsAutoRdZero rs1 rs2).Run s s') :
    Frame (sha256InitRdZeroWriteSet rs1) s s' :=
  frame_of_run (sha256InitRdZero_writesWithin rs1 rs2) h

/-! ### `Keccak256`, rd ≠ x0 -/

/-- Store slots of `Keccak256` (rd ≠ x0). -/
def keccak256Stores (rs1 : regidx) : List StoreSlot :=
  [⟨.xreg rs1, 0, .dword⟩, ⟨.xreg rs1, 8, .dword⟩, ⟨.xreg rs1, 16, .dword⟩,
    ⟨.xreg rs1, 24, .dword⟩, ⟨.xreg rs1, 32, .dword⟩, ⟨.xreg rs1, 40, .dword⟩,
    ⟨.xreg rs1, 48, .dword⟩, ⟨.xreg rs1, 56, .dword⟩, ⟨.xreg rs1, 64, .dword⟩,
    ⟨.xreg rs1, 72, .dword⟩, ⟨.xreg rs1, 80, .dword⟩, ⟨.xreg rs1, 88, .dword⟩,
    ⟨.xreg rs1, 96, .dword⟩, ⟨.xreg rs1, 104, .dword⟩, ⟨.xreg rs1, 112, .dword⟩,
    ⟨.xreg rs1, 120, .dword⟩, ⟨.xreg rs1, 128, .dword⟩, ⟨.xreg rs1, 136, .dword⟩,
    ⟨.xreg rs1, 144, .dword⟩, ⟨.xreg rs1, 152, .dword⟩, ⟨.xreg rs1, 160, .dword⟩,
    ⟨.xreg rs1, 168, .dword⟩, ⟨.xreg rs1, 176, .dword⟩, ⟨.xreg rs1, 184, .dword⟩,
    ⟨.xreg rs1, 192, .dword⟩]

/-- Write set of `Keccak256` (rd ≠ x0): pool registers `vr48..vr84`, no
architectural register, 25 store rows. -/
def keccak256WriteSet (rs1 : regidx) : WriteSet where
  vregs := poolVRegs 37
  xregs := []
  stores := keccak256Stores rs1

/-- Chunk 0 of `Keccak256` (rd ≠ x0). -/
theorem keccak256_chunk0
    (rs1 rs2 rs3 : regidx) :
    (Program.seq (keccak256RowsAutoChunk0 rs1 rs2 rs3)).rowsWithin (keccak256WriteSet rs1) = true ∧
      (Program.seq (keccak256RowsAutoChunk0 rs1 rs2 rs3)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 1 of `Keccak256` (rd ≠ x0). -/
theorem keccak256_chunk1
    (rs1 rs2 rs3 : regidx) :
    (Program.seq (keccak256RowsAutoChunk1 rs1 rs2 rs3)).rowsWithin (keccak256WriteSet rs1) = true ∧
      (Program.seq (keccak256RowsAutoChunk1 rs1 rs2 rs3)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 2 of `Keccak256` (rd ≠ x0). -/
theorem keccak256_chunk2
    (rs1 rs2 rs3 : regidx) :
    (Program.seq (keccak256RowsAutoChunk2 rs1 rs2 rs3)).rowsWithin (keccak256WriteSet rs1) = true ∧
      (Program.seq (keccak256RowsAutoChunk2 rs1 rs2 rs3)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 3 of `Keccak256` (rd ≠ x0). -/
theorem keccak256_chunk3
    (rs1 rs2 rs3 : regidx) :
    (Program.seq (keccak256RowsAutoChunk3 rs1 rs2 rs3)).rowsWithin (keccak256WriteSet rs1) = true ∧
      (Program.seq (keccak256RowsAutoChunk3 rs1 rs2 rs3)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 4 of `Keccak256` (rd ≠ x0). -/
theorem keccak256_chunk4
    (rs1 rs2 rs3 : regidx) :
    (Program.seq (keccak256RowsAutoChunk4 rs1 rs2 rs3)).rowsWithin (keccak256WriteSet rs1) = true ∧
      (Program.seq (keccak256RowsAutoChunk4 rs1 rs2 rs3)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 5 of `Keccak256` (rd ≠ x0). -/
theorem keccak256_chunk5
    (rs1 rs2 rs3 : regidx) :
    (Program.seq (keccak256RowsAutoChunk5 rs1 rs2 rs3)).rowsWithin (keccak256WriteSet rs1) = true ∧
      (Program.seq (keccak256RowsAutoChunk5 rs1 rs2 rs3)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 6 of `Keccak256` (rd ≠ x0). -/
theorem keccak256_chunk6
    (rs1 rs2 rs3 : regidx) :
    (Program.seq (keccak256RowsAutoChunk6 rs1 rs2 rs3)).rowsWithin (keccak256WriteSet rs1) = true ∧
      (Program.seq (keccak256RowsAutoChunk6 rs1 rs2 rs3)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 7 of `Keccak256` (rd ≠ x0). -/
theorem keccak256_chunk7
    (rs1 rs2 rs3 : regidx) :
    (Program.seq (keccak256RowsAutoChunk7 rs1 rs2 rs3)).rowsWithin (keccak256WriteSet rs1) = true ∧
      (Program.seq (keccak256RowsAutoChunk7 rs1 rs2 rs3)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 8 of `Keccak256` (rd ≠ x0). -/
theorem keccak256_chunk8
    (rs1 rs2 rs3 : regidx) :
    (Program.seq (keccak256RowsAutoChunk8 rs1 rs2 rs3)).rowsWithin (keccak256WriteSet rs1) = true ∧
      (Program.seq (keccak256RowsAutoChunk8 rs1 rs2 rs3)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 9 of `Keccak256` (rd ≠ x0). -/
theorem keccak256_chunk9
    (rs1 rs2 rs3 : regidx) :
    (Program.seq (keccak256RowsAutoChunk9 rs1 rs2 rs3)).rowsWithin (keccak256WriteSet rs1) = true ∧
      (Program.seq (keccak256RowsAutoChunk9 rs1 rs2 rs3)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 10 of `Keccak256` (rd ≠ x0). -/
theorem keccak256_chunk10
    (rs1 rs2 rs3 : regidx) :
    (Program.seq (keccak256RowsAutoChunk10 rs1 rs2 rs3)).rowsWithin (keccak256WriteSet rs1) = true ∧
      (Program.seq (keccak256RowsAutoChunk10 rs1 rs2 rs3)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 11 of `Keccak256` (rd ≠ x0). -/
theorem keccak256_chunk11
    (rs1 rs2 rs3 : regidx) :
    (Program.seq (keccak256RowsAutoChunk11 rs1 rs2 rs3)).rowsWithin (keccak256WriteSet rs1) = true ∧
      (Program.seq (keccak256RowsAutoChunk11 rs1 rs2 rs3)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 12 of `Keccak256` (rd ≠ x0). -/
theorem keccak256_chunk12
    (rs1 rs2 rs3 : regidx) :
    (Program.seq (keccak256RowsAutoChunk12 rs1 rs2 rs3)).rowsWithin (keccak256WriteSet rs1) = true ∧
      (Program.seq (keccak256RowsAutoChunk12 rs1 rs2 rs3)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 13 of `Keccak256` (rd ≠ x0). -/
theorem keccak256_chunk13
    (rs1 rs2 rs3 : regidx) :
    (Program.seq (keccak256RowsAutoChunk13 rs1 rs2 rs3)).rowsWithin (keccak256WriteSet rs1) = true ∧
      (Program.seq (keccak256RowsAutoChunk13 rs1 rs2 rs3)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 14 of `Keccak256` (rd ≠ x0). -/
theorem keccak256_chunk14
    (rs1 rs2 rs3 : regidx) :
    (Program.seq (keccak256RowsAutoChunk14 rs1 rs2 rs3)).rowsWithin (keccak256WriteSet rs1) = true ∧
      (Program.seq (keccak256RowsAutoChunk14 rs1 rs2 rs3)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 15 of `Keccak256` (rd ≠ x0). -/
theorem keccak256_chunk15
    (rs1 rs2 rs3 : regidx) :
    (Program.seq (keccak256RowsAutoChunk15 rs1 rs2 rs3)).rowsWithin (keccak256WriteSet rs1) = true ∧
      (Program.seq (keccak256RowsAutoChunk15 rs1 rs2 rs3)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 16 of `Keccak256` (rd ≠ x0). -/
theorem keccak256_chunk16
    (rs1 rs2 rs3 : regidx) :
    (Program.seq (keccak256RowsAutoChunk16 rs1 rs2 rs3)).rowsWithin (keccak256WriteSet rs1) = true ∧
      (Program.seq (keccak256RowsAutoChunk16 rs1 rs2 rs3)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 17 of `Keccak256` (rd ≠ x0). -/
theorem keccak256_chunk17
    (rs1 rs2 rs3 : regidx) :
    (Program.seq (keccak256RowsAutoChunk17 rs1 rs2 rs3)).rowsWithin (keccak256WriteSet rs1) = true ∧
      (Program.seq (keccak256RowsAutoChunk17 rs1 rs2 rs3)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 18 of `Keccak256` (rd ≠ x0). -/
theorem keccak256_chunk18
    (rs1 rs2 rs3 : regidx) :
    (Program.seq (keccak256RowsAutoChunk18 rs1 rs2 rs3)).rowsWithin (keccak256WriteSet rs1) = true ∧
      (Program.seq (keccak256RowsAutoChunk18 rs1 rs2 rs3)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 19 of `Keccak256` (rd ≠ x0). -/
theorem keccak256_chunk19
    (rs1 rs2 rs3 : regidx) :
    (Program.seq (keccak256RowsAutoChunk19 rs1 rs2 rs3)).rowsWithin (keccak256WriteSet rs1) = true ∧
      (Program.seq (keccak256RowsAutoChunk19 rs1 rs2 rs3)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 20 of `Keccak256` (rd ≠ x0). -/
theorem keccak256_chunk20
    (rs1 rs2 rs3 : regidx) :
    (Program.seq (keccak256RowsAutoChunk20 rs1 rs2 rs3)).rowsWithin (keccak256WriteSet rs1) = true ∧
      (Program.seq (keccak256RowsAutoChunk20 rs1 rs2 rs3)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 21 of `Keccak256` (rd ≠ x0). -/
theorem keccak256_chunk21
    (rs1 rs2 rs3 : regidx) :
    (Program.seq (keccak256RowsAutoChunk21 rs1 rs2 rs3)).rowsWithin (keccak256WriteSet rs1) = true ∧
      (Program.seq (keccak256RowsAutoChunk21 rs1 rs2 rs3)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 22 of `Keccak256` (rd ≠ x0). -/
theorem keccak256_chunk22
    (rs1 rs2 rs3 : regidx) :
    (Program.seq (keccak256RowsAutoChunk22 rs1 rs2 rs3)).rowsWithin (keccak256WriteSet rs1) = true ∧
      (Program.seq (keccak256RowsAutoChunk22 rs1 rs2 rs3)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 23 of `Keccak256` (rd ≠ x0). -/
theorem keccak256_chunk23
    (rs1 rs2 rs3 : regidx) :
    (Program.seq (keccak256RowsAutoChunk23 rs1 rs2 rs3)).rowsWithin (keccak256WriteSet rs1) = true ∧
      (Program.seq (keccak256RowsAutoChunk23 rs1 rs2 rs3)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 24 of `Keccak256` (rd ≠ x0). -/
theorem keccak256_chunk24
    (rs1 rs2 rs3 : regidx) :
    (Program.seq (keccak256RowsAutoChunk24 rs1 rs2 rs3)).rowsWithin (keccak256WriteSet rs1) = true ∧
      (Program.seq (keccak256RowsAutoChunk24 rs1 rs2 rs3)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 25 of `Keccak256` (rd ≠ x0). -/
theorem keccak256_chunk25
    (rs1 rs2 rs3 : regidx) :
    (Program.seq (keccak256RowsAutoChunk25 rs1 rs2 rs3)).rowsWithin (keccak256WriteSet rs1) = true ∧
      (Program.seq (keccak256RowsAutoChunk25 rs1 rs2 rs3)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 26 of `Keccak256` (rd ≠ x0). -/
theorem keccak256_chunk26
    (rs1 rs2 rs3 : regidx) :
    (Program.seq (keccak256RowsAutoChunk26 rs1 rs2 rs3)).rowsWithin (keccak256WriteSet rs1) = true ∧
      (Program.seq (keccak256RowsAutoChunk26 rs1 rs2 rs3)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 27 of `Keccak256` (rd ≠ x0). -/
theorem keccak256_chunk27
    (rs1 rs2 rs3 : regidx) :
    (Program.seq (keccak256RowsAutoChunk27 rs1 rs2 rs3)).rowsWithin (keccak256WriteSet rs1) = true ∧
      (Program.seq (keccak256RowsAutoChunk27 rs1 rs2 rs3)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 28 of `Keccak256` (rd ≠ x0). -/
theorem keccak256_chunk28
    (rs1 rs2 rs3 : regidx) :
    (Program.seq (keccak256RowsAutoChunk28 rs1 rs2 rs3)).rowsWithin (keccak256WriteSet rs1) = true ∧
      (Program.seq (keccak256RowsAutoChunk28 rs1 rs2 rs3)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 29 of `Keccak256` (rd ≠ x0). -/
theorem keccak256_chunk29
    (rs1 rs2 rs3 : regidx) :
    (Program.seq (keccak256RowsAutoChunk29 rs1 rs2 rs3)).rowsWithin (keccak256WriteSet rs1) = true ∧
      (Program.seq (keccak256RowsAutoChunk29 rs1 rs2 rs3)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 30 of `Keccak256` (rd ≠ x0). -/
theorem keccak256_chunk30
    (rs1 rs2 rs3 : regidx) :
    (Program.seq (keccak256RowsAutoChunk30 rs1 rs2 rs3)).rowsWithin (keccak256WriteSet rs1) = true ∧
      (Program.seq (keccak256RowsAutoChunk30 rs1 rs2 rs3)).storeSlots =
        [⟨.xreg rs1, 0, .dword⟩, ⟨.xreg rs1, 8, .dword⟩, ⟨.xreg rs1, 16, .dword⟩, ⟨.xreg rs1, 24, .dword⟩, ⟨.xreg rs1, 32, .dword⟩, ⟨.xreg rs1, 40, .dword⟩, ⟨.xreg rs1, 48, .dword⟩, ⟨.xreg rs1, 56, .dword⟩, ⟨.xreg rs1, 64, .dword⟩, ⟨.xreg rs1, 72, .dword⟩, ⟨.xreg rs1, 80, .dword⟩, ⟨.xreg rs1, 88, .dword⟩, ⟨.xreg rs1, 96, .dword⟩, ⟨.xreg rs1, 104, .dword⟩, ⟨.xreg rs1, 112, .dword⟩, ⟨.xreg rs1, 120, .dword⟩, ⟨.xreg rs1, 128, .dword⟩, ⟨.xreg rs1, 136, .dword⟩, ⟨.xreg rs1, 144, .dword⟩, ⟨.xreg rs1, 152, .dword⟩, ⟨.xreg rs1, 160, .dword⟩, ⟨.xreg rs1, 168, .dword⟩, ⟨.xreg rs1, 176, .dword⟩, ⟨.xreg rs1, 184, .dword⟩, ⟨.xreg rs1, 192, .dword⟩] :=
  ⟨rfl, rfl⟩

theorem keccak256_storeSlots
    (rs1 rs2 rs3 : regidx) :
    (keccak256RowsAuto rs1 rs2 rs3).storeSlots =
      keccak256Stores rs1 := by
  unfold keccak256RowsAuto keccak256RowsAutoList
  simp only [Program.storeSlots_seq_append,
      (keccak256_chunk0 rs1 rs2 rs3).2,
      (keccak256_chunk1 rs1 rs2 rs3).2,
      (keccak256_chunk2 rs1 rs2 rs3).2,
      (keccak256_chunk3 rs1 rs2 rs3).2,
      (keccak256_chunk4 rs1 rs2 rs3).2,
      (keccak256_chunk5 rs1 rs2 rs3).2,
      (keccak256_chunk6 rs1 rs2 rs3).2,
      (keccak256_chunk7 rs1 rs2 rs3).2,
      (keccak256_chunk8 rs1 rs2 rs3).2,
      (keccak256_chunk9 rs1 rs2 rs3).2,
      (keccak256_chunk10 rs1 rs2 rs3).2,
      (keccak256_chunk11 rs1 rs2 rs3).2,
      (keccak256_chunk12 rs1 rs2 rs3).2,
      (keccak256_chunk13 rs1 rs2 rs3).2,
      (keccak256_chunk14 rs1 rs2 rs3).2,
      (keccak256_chunk15 rs1 rs2 rs3).2,
      (keccak256_chunk16 rs1 rs2 rs3).2,
      (keccak256_chunk17 rs1 rs2 rs3).2,
      (keccak256_chunk18 rs1 rs2 rs3).2,
      (keccak256_chunk19 rs1 rs2 rs3).2,
      (keccak256_chunk20 rs1 rs2 rs3).2,
      (keccak256_chunk21 rs1 rs2 rs3).2,
      (keccak256_chunk22 rs1 rs2 rs3).2,
      (keccak256_chunk23 rs1 rs2 rs3).2,
      (keccak256_chunk24 rs1 rs2 rs3).2,
      (keccak256_chunk25 rs1 rs2 rs3).2,
      (keccak256_chunk26 rs1 rs2 rs3).2,
      (keccak256_chunk27 rs1 rs2 rs3).2,
      (keccak256_chunk28 rs1 rs2 rs3).2,
      (keccak256_chunk29 rs1 rs2 rs3).2,
      (keccak256_chunk30 rs1 rs2 rs3).2]
  rfl

theorem keccak256_writesWithin
    (rs1 rs2 rs3 : regidx) :
    (keccak256RowsAuto rs1 rs2 rs3).WritesWithin
      (keccak256WriteSet rs1) :=
  ⟨by
    unfold keccak256RowsAuto keccak256RowsAutoList
    simp only [Program.rowsWithin_seq_append,
      (keccak256_chunk0 rs1 rs2 rs3).1,
      (keccak256_chunk1 rs1 rs2 rs3).1,
      (keccak256_chunk2 rs1 rs2 rs3).1,
      (keccak256_chunk3 rs1 rs2 rs3).1,
      (keccak256_chunk4 rs1 rs2 rs3).1,
      (keccak256_chunk5 rs1 rs2 rs3).1,
      (keccak256_chunk6 rs1 rs2 rs3).1,
      (keccak256_chunk7 rs1 rs2 rs3).1,
      (keccak256_chunk8 rs1 rs2 rs3).1,
      (keccak256_chunk9 rs1 rs2 rs3).1,
      (keccak256_chunk10 rs1 rs2 rs3).1,
      (keccak256_chunk11 rs1 rs2 rs3).1,
      (keccak256_chunk12 rs1 rs2 rs3).1,
      (keccak256_chunk13 rs1 rs2 rs3).1,
      (keccak256_chunk14 rs1 rs2 rs3).1,
      (keccak256_chunk15 rs1 rs2 rs3).1,
      (keccak256_chunk16 rs1 rs2 rs3).1,
      (keccak256_chunk17 rs1 rs2 rs3).1,
      (keccak256_chunk18 rs1 rs2 rs3).1,
      (keccak256_chunk19 rs1 rs2 rs3).1,
      (keccak256_chunk20 rs1 rs2 rs3).1,
      (keccak256_chunk21 rs1 rs2 rs3).1,
      (keccak256_chunk22 rs1 rs2 rs3).1,
      (keccak256_chunk23 rs1 rs2 rs3).1,
      (keccak256_chunk24 rs1 rs2 rs3).1,
      (keccak256_chunk25 rs1 rs2 rs3).1,
      (keccak256_chunk26 rs1 rs2 rs3).1,
      (keccak256_chunk27 rs1 rs2 rs3).1,
      (keccak256_chunk28 rs1 rs2 rs3).1,
      (keccak256_chunk29 rs1 rs2 rs3).1,
      (keccak256_chunk30 rs1 rs2 rs3).1,
      Bool.and_self],
   by rw [keccak256_storeSlots]; exact List.Subset.refl _, rfl⟩

/-- The final chunks of `Keccak256` (rd ≠ x0), which contain the last write of every
pool register. -/
theorem keccak256_tailResets
    (rs1 rs2 rs3 : regidx) :
    (Program.seq (keccak256RowsAutoChunk30 rs1 rs2 rs3)).resetsPoolCheck (poolVRegs 37) = true := rfl

theorem keccak256_resetsPoolCheck
    (rs1 rs2 rs3 : regidx) :
    (keccak256RowsAuto rs1 rs2 rs3).resetsPoolCheck (poolVRegs 37) = true := by
  unfold keccak256RowsAuto keccak256RowsAutoList
  exact Program.resetsPoolCheck_seq_append _ (keccak256_tailResets rs1 rs2 rs3)

theorem keccak256_frame
    (rs1 rs2 rs3 : regidx) {s s' : SailJoltState}
    (h : (keccak256RowsAuto rs1 rs2 rs3).Run s s') :
    Frame (keccak256WriteSet rs1) s s' :=
  frame_of_run (keccak256_writesWithin rs1 rs2 rs3) h

/-! ### `Keccak256`, rd = x0 -/

/-- Store slots of `Keccak256` (rd = x0). -/
def keccak256RdZeroStores (rs1 : regidx) : List StoreSlot :=
  [⟨.xreg rs1, 0, .dword⟩, ⟨.xreg rs1, 8, .dword⟩, ⟨.xreg rs1, 16, .dword⟩,
    ⟨.xreg rs1, 24, .dword⟩, ⟨.xreg rs1, 32, .dword⟩, ⟨.xreg rs1, 40, .dword⟩,
    ⟨.xreg rs1, 48, .dword⟩, ⟨.xreg rs1, 56, .dword⟩, ⟨.xreg rs1, 64, .dword⟩,
    ⟨.xreg rs1, 72, .dword⟩, ⟨.xreg rs1, 80, .dword⟩, ⟨.xreg rs1, 88, .dword⟩,
    ⟨.xreg rs1, 96, .dword⟩, ⟨.xreg rs1, 104, .dword⟩, ⟨.xreg rs1, 112, .dword⟩,
    ⟨.xreg rs1, 120, .dword⟩, ⟨.xreg rs1, 128, .dword⟩, ⟨.xreg rs1, 136, .dword⟩,
    ⟨.xreg rs1, 144, .dword⟩, ⟨.xreg rs1, 152, .dword⟩, ⟨.xreg rs1, 160, .dword⟩,
    ⟨.xreg rs1, 168, .dword⟩, ⟨.xreg rs1, 176, .dword⟩, ⟨.xreg rs1, 184, .dword⟩,
    ⟨.xreg rs1, 192, .dword⟩]

/-- Write set of `Keccak256` (rd = x0): pool registers `vr48..vr84`, no
architectural register, 25 store rows. -/
def keccak256RdZeroWriteSet (rs1 : regidx) : WriteSet where
  vregs := poolVRegs 37
  xregs := []
  stores := keccak256RdZeroStores rs1

/-- Chunk 0 of `Keccak256` (rd = x0). -/
theorem keccak256RdZero_chunk0
    (rs1 rs2 : regidx) :
    (Program.seq (keccak256RowsAutoRdZeroChunk0 rs1 rs2)).rowsWithin (keccak256RdZeroWriteSet rs1) = true ∧
      (Program.seq (keccak256RowsAutoRdZeroChunk0 rs1 rs2)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 1 of `Keccak256` (rd = x0). -/
theorem keccak256RdZero_chunk1
    (rs1 rs2 : regidx) :
    (Program.seq (keccak256RowsAutoRdZeroChunk1 rs1 rs2)).rowsWithin (keccak256RdZeroWriteSet rs1) = true ∧
      (Program.seq (keccak256RowsAutoRdZeroChunk1 rs1 rs2)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 2 of `Keccak256` (rd = x0). -/
theorem keccak256RdZero_chunk2
    (rs1 rs2 : regidx) :
    (Program.seq (keccak256RowsAutoRdZeroChunk2 rs1 rs2)).rowsWithin (keccak256RdZeroWriteSet rs1) = true ∧
      (Program.seq (keccak256RowsAutoRdZeroChunk2 rs1 rs2)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 3 of `Keccak256` (rd = x0). -/
theorem keccak256RdZero_chunk3
    (rs1 rs2 : regidx) :
    (Program.seq (keccak256RowsAutoRdZeroChunk3 rs1 rs2)).rowsWithin (keccak256RdZeroWriteSet rs1) = true ∧
      (Program.seq (keccak256RowsAutoRdZeroChunk3 rs1 rs2)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 4 of `Keccak256` (rd = x0). -/
theorem keccak256RdZero_chunk4
    (rs1 rs2 : regidx) :
    (Program.seq (keccak256RowsAutoRdZeroChunk4 rs1 rs2)).rowsWithin (keccak256RdZeroWriteSet rs1) = true ∧
      (Program.seq (keccak256RowsAutoRdZeroChunk4 rs1 rs2)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 5 of `Keccak256` (rd = x0). -/
theorem keccak256RdZero_chunk5
    (rs1 rs2 : regidx) :
    (Program.seq (keccak256RowsAutoRdZeroChunk5 rs1 rs2)).rowsWithin (keccak256RdZeroWriteSet rs1) = true ∧
      (Program.seq (keccak256RowsAutoRdZeroChunk5 rs1 rs2)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 6 of `Keccak256` (rd = x0). -/
theorem keccak256RdZero_chunk6
    (rs1 rs2 : regidx) :
    (Program.seq (keccak256RowsAutoRdZeroChunk6 rs1 rs2)).rowsWithin (keccak256RdZeroWriteSet rs1) = true ∧
      (Program.seq (keccak256RowsAutoRdZeroChunk6 rs1 rs2)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 7 of `Keccak256` (rd = x0). -/
theorem keccak256RdZero_chunk7
    (rs1 rs2 : regidx) :
    (Program.seq (keccak256RowsAutoRdZeroChunk7 rs1 rs2)).rowsWithin (keccak256RdZeroWriteSet rs1) = true ∧
      (Program.seq (keccak256RowsAutoRdZeroChunk7 rs1 rs2)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 8 of `Keccak256` (rd = x0). -/
theorem keccak256RdZero_chunk8
    (rs1 rs2 : regidx) :
    (Program.seq (keccak256RowsAutoRdZeroChunk8 rs1 rs2)).rowsWithin (keccak256RdZeroWriteSet rs1) = true ∧
      (Program.seq (keccak256RowsAutoRdZeroChunk8 rs1 rs2)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 9 of `Keccak256` (rd = x0). -/
theorem keccak256RdZero_chunk9
    (rs1 rs2 : regidx) :
    (Program.seq (keccak256RowsAutoRdZeroChunk9 rs1 rs2)).rowsWithin (keccak256RdZeroWriteSet rs1) = true ∧
      (Program.seq (keccak256RowsAutoRdZeroChunk9 rs1 rs2)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 10 of `Keccak256` (rd = x0). -/
theorem keccak256RdZero_chunk10
    (rs1 rs2 : regidx) :
    (Program.seq (keccak256RowsAutoRdZeroChunk10 rs1 rs2)).rowsWithin (keccak256RdZeroWriteSet rs1) = true ∧
      (Program.seq (keccak256RowsAutoRdZeroChunk10 rs1 rs2)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 11 of `Keccak256` (rd = x0). -/
theorem keccak256RdZero_chunk11
    (rs1 rs2 : regidx) :
    (Program.seq (keccak256RowsAutoRdZeroChunk11 rs1 rs2)).rowsWithin (keccak256RdZeroWriteSet rs1) = true ∧
      (Program.seq (keccak256RowsAutoRdZeroChunk11 rs1 rs2)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 12 of `Keccak256` (rd = x0). -/
theorem keccak256RdZero_chunk12
    (rs1 rs2 : regidx) :
    (Program.seq (keccak256RowsAutoRdZeroChunk12 rs1 rs2)).rowsWithin (keccak256RdZeroWriteSet rs1) = true ∧
      (Program.seq (keccak256RowsAutoRdZeroChunk12 rs1 rs2)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 13 of `Keccak256` (rd = x0). -/
theorem keccak256RdZero_chunk13
    (rs1 rs2 : regidx) :
    (Program.seq (keccak256RowsAutoRdZeroChunk13 rs1 rs2)).rowsWithin (keccak256RdZeroWriteSet rs1) = true ∧
      (Program.seq (keccak256RowsAutoRdZeroChunk13 rs1 rs2)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 14 of `Keccak256` (rd = x0). -/
theorem keccak256RdZero_chunk14
    (rs1 rs2 : regidx) :
    (Program.seq (keccak256RowsAutoRdZeroChunk14 rs1 rs2)).rowsWithin (keccak256RdZeroWriteSet rs1) = true ∧
      (Program.seq (keccak256RowsAutoRdZeroChunk14 rs1 rs2)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 15 of `Keccak256` (rd = x0). -/
theorem keccak256RdZero_chunk15
    (rs1 rs2 : regidx) :
    (Program.seq (keccak256RowsAutoRdZeroChunk15 rs1 rs2)).rowsWithin (keccak256RdZeroWriteSet rs1) = true ∧
      (Program.seq (keccak256RowsAutoRdZeroChunk15 rs1 rs2)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 16 of `Keccak256` (rd = x0). -/
theorem keccak256RdZero_chunk16
    (rs1 rs2 : regidx) :
    (Program.seq (keccak256RowsAutoRdZeroChunk16 rs1 rs2)).rowsWithin (keccak256RdZeroWriteSet rs1) = true ∧
      (Program.seq (keccak256RowsAutoRdZeroChunk16 rs1 rs2)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 17 of `Keccak256` (rd = x0). -/
theorem keccak256RdZero_chunk17
    (rs1 rs2 : regidx) :
    (Program.seq (keccak256RowsAutoRdZeroChunk17 rs1 rs2)).rowsWithin (keccak256RdZeroWriteSet rs1) = true ∧
      (Program.seq (keccak256RowsAutoRdZeroChunk17 rs1 rs2)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 18 of `Keccak256` (rd = x0). -/
theorem keccak256RdZero_chunk18
    (rs1 rs2 : regidx) :
    (Program.seq (keccak256RowsAutoRdZeroChunk18 rs1 rs2)).rowsWithin (keccak256RdZeroWriteSet rs1) = true ∧
      (Program.seq (keccak256RowsAutoRdZeroChunk18 rs1 rs2)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 19 of `Keccak256` (rd = x0). -/
theorem keccak256RdZero_chunk19
    (rs1 rs2 : regidx) :
    (Program.seq (keccak256RowsAutoRdZeroChunk19 rs1 rs2)).rowsWithin (keccak256RdZeroWriteSet rs1) = true ∧
      (Program.seq (keccak256RowsAutoRdZeroChunk19 rs1 rs2)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 20 of `Keccak256` (rd = x0). -/
theorem keccak256RdZero_chunk20
    (rs1 rs2 : regidx) :
    (Program.seq (keccak256RowsAutoRdZeroChunk20 rs1 rs2)).rowsWithin (keccak256RdZeroWriteSet rs1) = true ∧
      (Program.seq (keccak256RowsAutoRdZeroChunk20 rs1 rs2)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 21 of `Keccak256` (rd = x0). -/
theorem keccak256RdZero_chunk21
    (rs1 rs2 : regidx) :
    (Program.seq (keccak256RowsAutoRdZeroChunk21 rs1 rs2)).rowsWithin (keccak256RdZeroWriteSet rs1) = true ∧
      (Program.seq (keccak256RowsAutoRdZeroChunk21 rs1 rs2)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 22 of `Keccak256` (rd = x0). -/
theorem keccak256RdZero_chunk22
    (rs1 rs2 : regidx) :
    (Program.seq (keccak256RowsAutoRdZeroChunk22 rs1 rs2)).rowsWithin (keccak256RdZeroWriteSet rs1) = true ∧
      (Program.seq (keccak256RowsAutoRdZeroChunk22 rs1 rs2)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 23 of `Keccak256` (rd = x0). -/
theorem keccak256RdZero_chunk23
    (rs1 rs2 : regidx) :
    (Program.seq (keccak256RowsAutoRdZeroChunk23 rs1 rs2)).rowsWithin (keccak256RdZeroWriteSet rs1) = true ∧
      (Program.seq (keccak256RowsAutoRdZeroChunk23 rs1 rs2)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 24 of `Keccak256` (rd = x0). -/
theorem keccak256RdZero_chunk24
    (rs1 rs2 : regidx) :
    (Program.seq (keccak256RowsAutoRdZeroChunk24 rs1 rs2)).rowsWithin (keccak256RdZeroWriteSet rs1) = true ∧
      (Program.seq (keccak256RowsAutoRdZeroChunk24 rs1 rs2)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 25 of `Keccak256` (rd = x0). -/
theorem keccak256RdZero_chunk25
    (rs1 rs2 : regidx) :
    (Program.seq (keccak256RowsAutoRdZeroChunk25 rs1 rs2)).rowsWithin (keccak256RdZeroWriteSet rs1) = true ∧
      (Program.seq (keccak256RowsAutoRdZeroChunk25 rs1 rs2)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 26 of `Keccak256` (rd = x0). -/
theorem keccak256RdZero_chunk26
    (rs1 rs2 : regidx) :
    (Program.seq (keccak256RowsAutoRdZeroChunk26 rs1 rs2)).rowsWithin (keccak256RdZeroWriteSet rs1) = true ∧
      (Program.seq (keccak256RowsAutoRdZeroChunk26 rs1 rs2)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 27 of `Keccak256` (rd = x0). -/
theorem keccak256RdZero_chunk27
    (rs1 rs2 : regidx) :
    (Program.seq (keccak256RowsAutoRdZeroChunk27 rs1 rs2)).rowsWithin (keccak256RdZeroWriteSet rs1) = true ∧
      (Program.seq (keccak256RowsAutoRdZeroChunk27 rs1 rs2)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 28 of `Keccak256` (rd = x0). -/
theorem keccak256RdZero_chunk28
    (rs1 rs2 : regidx) :
    (Program.seq (keccak256RowsAutoRdZeroChunk28 rs1 rs2)).rowsWithin (keccak256RdZeroWriteSet rs1) = true ∧
      (Program.seq (keccak256RowsAutoRdZeroChunk28 rs1 rs2)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 29 of `Keccak256` (rd = x0). -/
theorem keccak256RdZero_chunk29
    (rs1 rs2 : regidx) :
    (Program.seq (keccak256RowsAutoRdZeroChunk29 rs1 rs2)).rowsWithin (keccak256RdZeroWriteSet rs1) = true ∧
      (Program.seq (keccak256RowsAutoRdZeroChunk29 rs1 rs2)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 30 of `Keccak256` (rd = x0). -/
theorem keccak256RdZero_chunk30
    (rs1 rs2 : regidx) :
    (Program.seq (keccak256RowsAutoRdZeroChunk30 rs1 rs2)).rowsWithin (keccak256RdZeroWriteSet rs1) = true ∧
      (Program.seq (keccak256RowsAutoRdZeroChunk30 rs1 rs2)).storeSlots =
        [⟨.xreg rs1, 0, .dword⟩, ⟨.xreg rs1, 8, .dword⟩, ⟨.xreg rs1, 16, .dword⟩, ⟨.xreg rs1, 24, .dword⟩, ⟨.xreg rs1, 32, .dword⟩, ⟨.xreg rs1, 40, .dword⟩, ⟨.xreg rs1, 48, .dword⟩, ⟨.xreg rs1, 56, .dword⟩, ⟨.xreg rs1, 64, .dword⟩, ⟨.xreg rs1, 72, .dword⟩, ⟨.xreg rs1, 80, .dword⟩, ⟨.xreg rs1, 88, .dword⟩, ⟨.xreg rs1, 96, .dword⟩, ⟨.xreg rs1, 104, .dword⟩, ⟨.xreg rs1, 112, .dword⟩, ⟨.xreg rs1, 120, .dword⟩, ⟨.xreg rs1, 128, .dword⟩, ⟨.xreg rs1, 136, .dword⟩, ⟨.xreg rs1, 144, .dword⟩, ⟨.xreg rs1, 152, .dword⟩, ⟨.xreg rs1, 160, .dword⟩, ⟨.xreg rs1, 168, .dword⟩, ⟨.xreg rs1, 176, .dword⟩, ⟨.xreg rs1, 184, .dword⟩, ⟨.xreg rs1, 192, .dword⟩] :=
  ⟨rfl, rfl⟩

theorem keccak256RdZero_storeSlots
    (rs1 rs2 : regidx) :
    (keccak256RowsAutoRdZero rs1 rs2).storeSlots =
      keccak256RdZeroStores rs1 := by
  unfold keccak256RowsAutoRdZero keccak256RowsAutoRdZeroList
  simp only [Program.storeSlots_seq_append,
      (keccak256RdZero_chunk0 rs1 rs2).2,
      (keccak256RdZero_chunk1 rs1 rs2).2,
      (keccak256RdZero_chunk2 rs1 rs2).2,
      (keccak256RdZero_chunk3 rs1 rs2).2,
      (keccak256RdZero_chunk4 rs1 rs2).2,
      (keccak256RdZero_chunk5 rs1 rs2).2,
      (keccak256RdZero_chunk6 rs1 rs2).2,
      (keccak256RdZero_chunk7 rs1 rs2).2,
      (keccak256RdZero_chunk8 rs1 rs2).2,
      (keccak256RdZero_chunk9 rs1 rs2).2,
      (keccak256RdZero_chunk10 rs1 rs2).2,
      (keccak256RdZero_chunk11 rs1 rs2).2,
      (keccak256RdZero_chunk12 rs1 rs2).2,
      (keccak256RdZero_chunk13 rs1 rs2).2,
      (keccak256RdZero_chunk14 rs1 rs2).2,
      (keccak256RdZero_chunk15 rs1 rs2).2,
      (keccak256RdZero_chunk16 rs1 rs2).2,
      (keccak256RdZero_chunk17 rs1 rs2).2,
      (keccak256RdZero_chunk18 rs1 rs2).2,
      (keccak256RdZero_chunk19 rs1 rs2).2,
      (keccak256RdZero_chunk20 rs1 rs2).2,
      (keccak256RdZero_chunk21 rs1 rs2).2,
      (keccak256RdZero_chunk22 rs1 rs2).2,
      (keccak256RdZero_chunk23 rs1 rs2).2,
      (keccak256RdZero_chunk24 rs1 rs2).2,
      (keccak256RdZero_chunk25 rs1 rs2).2,
      (keccak256RdZero_chunk26 rs1 rs2).2,
      (keccak256RdZero_chunk27 rs1 rs2).2,
      (keccak256RdZero_chunk28 rs1 rs2).2,
      (keccak256RdZero_chunk29 rs1 rs2).2,
      (keccak256RdZero_chunk30 rs1 rs2).2]
  rfl

theorem keccak256RdZero_writesWithin
    (rs1 rs2 : regidx) :
    (keccak256RowsAutoRdZero rs1 rs2).WritesWithin
      (keccak256RdZeroWriteSet rs1) :=
  ⟨by
    unfold keccak256RowsAutoRdZero keccak256RowsAutoRdZeroList
    simp only [Program.rowsWithin_seq_append,
      (keccak256RdZero_chunk0 rs1 rs2).1,
      (keccak256RdZero_chunk1 rs1 rs2).1,
      (keccak256RdZero_chunk2 rs1 rs2).1,
      (keccak256RdZero_chunk3 rs1 rs2).1,
      (keccak256RdZero_chunk4 rs1 rs2).1,
      (keccak256RdZero_chunk5 rs1 rs2).1,
      (keccak256RdZero_chunk6 rs1 rs2).1,
      (keccak256RdZero_chunk7 rs1 rs2).1,
      (keccak256RdZero_chunk8 rs1 rs2).1,
      (keccak256RdZero_chunk9 rs1 rs2).1,
      (keccak256RdZero_chunk10 rs1 rs2).1,
      (keccak256RdZero_chunk11 rs1 rs2).1,
      (keccak256RdZero_chunk12 rs1 rs2).1,
      (keccak256RdZero_chunk13 rs1 rs2).1,
      (keccak256RdZero_chunk14 rs1 rs2).1,
      (keccak256RdZero_chunk15 rs1 rs2).1,
      (keccak256RdZero_chunk16 rs1 rs2).1,
      (keccak256RdZero_chunk17 rs1 rs2).1,
      (keccak256RdZero_chunk18 rs1 rs2).1,
      (keccak256RdZero_chunk19 rs1 rs2).1,
      (keccak256RdZero_chunk20 rs1 rs2).1,
      (keccak256RdZero_chunk21 rs1 rs2).1,
      (keccak256RdZero_chunk22 rs1 rs2).1,
      (keccak256RdZero_chunk23 rs1 rs2).1,
      (keccak256RdZero_chunk24 rs1 rs2).1,
      (keccak256RdZero_chunk25 rs1 rs2).1,
      (keccak256RdZero_chunk26 rs1 rs2).1,
      (keccak256RdZero_chunk27 rs1 rs2).1,
      (keccak256RdZero_chunk28 rs1 rs2).1,
      (keccak256RdZero_chunk29 rs1 rs2).1,
      (keccak256RdZero_chunk30 rs1 rs2).1,
      Bool.and_self],
   by rw [keccak256RdZero_storeSlots]; exact List.Subset.refl _, rfl⟩

/-- The final chunks of `Keccak256` (rd = x0), which contain the last write of every
pool register. -/
theorem keccak256RdZero_tailResets
    (rs1 rs2 : regidx) :
    (Program.seq (keccak256RowsAutoRdZeroChunk30 rs1 rs2)).resetsPoolCheck (poolVRegs 37) = true := rfl

theorem keccak256RdZero_resetsPoolCheck
    (rs1 rs2 : regidx) :
    (keccak256RowsAutoRdZero rs1 rs2).resetsPoolCheck (poolVRegs 37) = true := by
  unfold keccak256RowsAutoRdZero keccak256RowsAutoRdZeroList
  exact Program.resetsPoolCheck_seq_append _ (keccak256RdZero_tailResets rs1 rs2)

theorem keccak256RdZero_frame
    (rs1 rs2 : regidx) {s s' : SailJoltState}
    (h : (keccak256RowsAutoRdZero rs1 rs2).Run s s') :
    Frame (keccak256RdZeroWriteSet rs1) s s' :=
  frame_of_run (keccak256RdZero_writesWithin rs1 rs2) h

/-! ### `Keccak256AbsorbPermute`, rd ≠ x0 -/

/-- Store slots of `Keccak256AbsorbPermute` (rd ≠ x0). -/
def keccak256AbsorbPermuteStores (rs1 : regidx) : List StoreSlot :=
  [⟨.xreg rs1, 0, .dword⟩, ⟨.xreg rs1, 8, .dword⟩, ⟨.xreg rs1, 16, .dword⟩,
    ⟨.xreg rs1, 24, .dword⟩, ⟨.xreg rs1, 32, .dword⟩, ⟨.xreg rs1, 40, .dword⟩,
    ⟨.xreg rs1, 48, .dword⟩, ⟨.xreg rs1, 56, .dword⟩, ⟨.xreg rs1, 64, .dword⟩,
    ⟨.xreg rs1, 72, .dword⟩, ⟨.xreg rs1, 80, .dword⟩, ⟨.xreg rs1, 88, .dword⟩,
    ⟨.xreg rs1, 96, .dword⟩, ⟨.xreg rs1, 104, .dword⟩, ⟨.xreg rs1, 112, .dword⟩,
    ⟨.xreg rs1, 120, .dword⟩, ⟨.xreg rs1, 128, .dword⟩, ⟨.xreg rs1, 136, .dword⟩,
    ⟨.xreg rs1, 144, .dword⟩, ⟨.xreg rs1, 152, .dword⟩, ⟨.xreg rs1, 160, .dword⟩,
    ⟨.xreg rs1, 168, .dword⟩, ⟨.xreg rs1, 176, .dword⟩, ⟨.xreg rs1, 184, .dword⟩,
    ⟨.xreg rs1, 192, .dword⟩]

/-- Write set of `Keccak256AbsorbPermute` (rd ≠ x0): pool registers `vr48..vr84`, no
architectural register, 25 store rows. -/
def keccak256AbsorbPermuteWriteSet (rs1 : regidx) : WriteSet where
  vregs := poolVRegs 37
  xregs := []
  stores := keccak256AbsorbPermuteStores rs1

/-- Chunk 0 of `Keccak256AbsorbPermute` (rd ≠ x0). -/
theorem keccak256AbsorbPermute_chunk0
    (rs1 rs2 rs3 : regidx) :
    (Program.seq (keccak256AbsorbPermuteRowsAutoChunk0 rs1 rs2 rs3)).rowsWithin (keccak256AbsorbPermuteWriteSet rs1) = true ∧
      (Program.seq (keccak256AbsorbPermuteRowsAutoChunk0 rs1 rs2 rs3)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 1 of `Keccak256AbsorbPermute` (rd ≠ x0). -/
theorem keccak256AbsorbPermute_chunk1
    (rs1 rs2 rs3 : regidx) :
    (Program.seq (keccak256AbsorbPermuteRowsAutoChunk1 rs1 rs2 rs3)).rowsWithin (keccak256AbsorbPermuteWriteSet rs1) = true ∧
      (Program.seq (keccak256AbsorbPermuteRowsAutoChunk1 rs1 rs2 rs3)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 2 of `Keccak256AbsorbPermute` (rd ≠ x0). -/
theorem keccak256AbsorbPermute_chunk2
    (rs1 rs2 rs3 : regidx) :
    (Program.seq (keccak256AbsorbPermuteRowsAutoChunk2 rs1 rs2 rs3)).rowsWithin (keccak256AbsorbPermuteWriteSet rs1) = true ∧
      (Program.seq (keccak256AbsorbPermuteRowsAutoChunk2 rs1 rs2 rs3)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 3 of `Keccak256AbsorbPermute` (rd ≠ x0). -/
theorem keccak256AbsorbPermute_chunk3
    (rs1 rs2 rs3 : regidx) :
    (Program.seq (keccak256AbsorbPermuteRowsAutoChunk3 rs1 rs2 rs3)).rowsWithin (keccak256AbsorbPermuteWriteSet rs1) = true ∧
      (Program.seq (keccak256AbsorbPermuteRowsAutoChunk3 rs1 rs2 rs3)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 4 of `Keccak256AbsorbPermute` (rd ≠ x0). -/
theorem keccak256AbsorbPermute_chunk4
    (rs1 rs2 rs3 : regidx) :
    (Program.seq (keccak256AbsorbPermuteRowsAutoChunk4 rs1 rs2 rs3)).rowsWithin (keccak256AbsorbPermuteWriteSet rs1) = true ∧
      (Program.seq (keccak256AbsorbPermuteRowsAutoChunk4 rs1 rs2 rs3)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 5 of `Keccak256AbsorbPermute` (rd ≠ x0). -/
theorem keccak256AbsorbPermute_chunk5
    (rs1 rs2 rs3 : regidx) :
    (Program.seq (keccak256AbsorbPermuteRowsAutoChunk5 rs1 rs2 rs3)).rowsWithin (keccak256AbsorbPermuteWriteSet rs1) = true ∧
      (Program.seq (keccak256AbsorbPermuteRowsAutoChunk5 rs1 rs2 rs3)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 6 of `Keccak256AbsorbPermute` (rd ≠ x0). -/
theorem keccak256AbsorbPermute_chunk6
    (rs1 rs2 rs3 : regidx) :
    (Program.seq (keccak256AbsorbPermuteRowsAutoChunk6 rs1 rs2 rs3)).rowsWithin (keccak256AbsorbPermuteWriteSet rs1) = true ∧
      (Program.seq (keccak256AbsorbPermuteRowsAutoChunk6 rs1 rs2 rs3)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 7 of `Keccak256AbsorbPermute` (rd ≠ x0). -/
theorem keccak256AbsorbPermute_chunk7
    (rs1 rs2 rs3 : regidx) :
    (Program.seq (keccak256AbsorbPermuteRowsAutoChunk7 rs1 rs2 rs3)).rowsWithin (keccak256AbsorbPermuteWriteSet rs1) = true ∧
      (Program.seq (keccak256AbsorbPermuteRowsAutoChunk7 rs1 rs2 rs3)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 8 of `Keccak256AbsorbPermute` (rd ≠ x0). -/
theorem keccak256AbsorbPermute_chunk8
    (rs1 rs2 rs3 : regidx) :
    (Program.seq (keccak256AbsorbPermuteRowsAutoChunk8 rs1 rs2 rs3)).rowsWithin (keccak256AbsorbPermuteWriteSet rs1) = true ∧
      (Program.seq (keccak256AbsorbPermuteRowsAutoChunk8 rs1 rs2 rs3)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 9 of `Keccak256AbsorbPermute` (rd ≠ x0). -/
theorem keccak256AbsorbPermute_chunk9
    (rs1 rs2 rs3 : regidx) :
    (Program.seq (keccak256AbsorbPermuteRowsAutoChunk9 rs1 rs2 rs3)).rowsWithin (keccak256AbsorbPermuteWriteSet rs1) = true ∧
      (Program.seq (keccak256AbsorbPermuteRowsAutoChunk9 rs1 rs2 rs3)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 10 of `Keccak256AbsorbPermute` (rd ≠ x0). -/
theorem keccak256AbsorbPermute_chunk10
    (rs1 rs2 rs3 : regidx) :
    (Program.seq (keccak256AbsorbPermuteRowsAutoChunk10 rs1 rs2 rs3)).rowsWithin (keccak256AbsorbPermuteWriteSet rs1) = true ∧
      (Program.seq (keccak256AbsorbPermuteRowsAutoChunk10 rs1 rs2 rs3)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 11 of `Keccak256AbsorbPermute` (rd ≠ x0). -/
theorem keccak256AbsorbPermute_chunk11
    (rs1 rs2 rs3 : regidx) :
    (Program.seq (keccak256AbsorbPermuteRowsAutoChunk11 rs1 rs2 rs3)).rowsWithin (keccak256AbsorbPermuteWriteSet rs1) = true ∧
      (Program.seq (keccak256AbsorbPermuteRowsAutoChunk11 rs1 rs2 rs3)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 12 of `Keccak256AbsorbPermute` (rd ≠ x0). -/
theorem keccak256AbsorbPermute_chunk12
    (rs1 rs2 rs3 : regidx) :
    (Program.seq (keccak256AbsorbPermuteRowsAutoChunk12 rs1 rs2 rs3)).rowsWithin (keccak256AbsorbPermuteWriteSet rs1) = true ∧
      (Program.seq (keccak256AbsorbPermuteRowsAutoChunk12 rs1 rs2 rs3)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 13 of `Keccak256AbsorbPermute` (rd ≠ x0). -/
theorem keccak256AbsorbPermute_chunk13
    (rs1 rs2 rs3 : regidx) :
    (Program.seq (keccak256AbsorbPermuteRowsAutoChunk13 rs1 rs2 rs3)).rowsWithin (keccak256AbsorbPermuteWriteSet rs1) = true ∧
      (Program.seq (keccak256AbsorbPermuteRowsAutoChunk13 rs1 rs2 rs3)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 14 of `Keccak256AbsorbPermute` (rd ≠ x0). -/
theorem keccak256AbsorbPermute_chunk14
    (rs1 rs2 rs3 : regidx) :
    (Program.seq (keccak256AbsorbPermuteRowsAutoChunk14 rs1 rs2 rs3)).rowsWithin (keccak256AbsorbPermuteWriteSet rs1) = true ∧
      (Program.seq (keccak256AbsorbPermuteRowsAutoChunk14 rs1 rs2 rs3)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 15 of `Keccak256AbsorbPermute` (rd ≠ x0). -/
theorem keccak256AbsorbPermute_chunk15
    (rs1 rs2 rs3 : regidx) :
    (Program.seq (keccak256AbsorbPermuteRowsAutoChunk15 rs1 rs2 rs3)).rowsWithin (keccak256AbsorbPermuteWriteSet rs1) = true ∧
      (Program.seq (keccak256AbsorbPermuteRowsAutoChunk15 rs1 rs2 rs3)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 16 of `Keccak256AbsorbPermute` (rd ≠ x0). -/
theorem keccak256AbsorbPermute_chunk16
    (rs1 rs2 rs3 : regidx) :
    (Program.seq (keccak256AbsorbPermuteRowsAutoChunk16 rs1 rs2 rs3)).rowsWithin (keccak256AbsorbPermuteWriteSet rs1) = true ∧
      (Program.seq (keccak256AbsorbPermuteRowsAutoChunk16 rs1 rs2 rs3)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 17 of `Keccak256AbsorbPermute` (rd ≠ x0). -/
theorem keccak256AbsorbPermute_chunk17
    (rs1 rs2 rs3 : regidx) :
    (Program.seq (keccak256AbsorbPermuteRowsAutoChunk17 rs1 rs2 rs3)).rowsWithin (keccak256AbsorbPermuteWriteSet rs1) = true ∧
      (Program.seq (keccak256AbsorbPermuteRowsAutoChunk17 rs1 rs2 rs3)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 18 of `Keccak256AbsorbPermute` (rd ≠ x0). -/
theorem keccak256AbsorbPermute_chunk18
    (rs1 rs2 rs3 : regidx) :
    (Program.seq (keccak256AbsorbPermuteRowsAutoChunk18 rs1 rs2 rs3)).rowsWithin (keccak256AbsorbPermuteWriteSet rs1) = true ∧
      (Program.seq (keccak256AbsorbPermuteRowsAutoChunk18 rs1 rs2 rs3)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 19 of `Keccak256AbsorbPermute` (rd ≠ x0). -/
theorem keccak256AbsorbPermute_chunk19
    (rs1 rs2 rs3 : regidx) :
    (Program.seq (keccak256AbsorbPermuteRowsAutoChunk19 rs1 rs2 rs3)).rowsWithin (keccak256AbsorbPermuteWriteSet rs1) = true ∧
      (Program.seq (keccak256AbsorbPermuteRowsAutoChunk19 rs1 rs2 rs3)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 20 of `Keccak256AbsorbPermute` (rd ≠ x0). -/
theorem keccak256AbsorbPermute_chunk20
    (rs1 rs2 rs3 : regidx) :
    (Program.seq (keccak256AbsorbPermuteRowsAutoChunk20 rs1 rs2 rs3)).rowsWithin (keccak256AbsorbPermuteWriteSet rs1) = true ∧
      (Program.seq (keccak256AbsorbPermuteRowsAutoChunk20 rs1 rs2 rs3)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 21 of `Keccak256AbsorbPermute` (rd ≠ x0). -/
theorem keccak256AbsorbPermute_chunk21
    (rs1 rs2 rs3 : regidx) :
    (Program.seq (keccak256AbsorbPermuteRowsAutoChunk21 rs1 rs2 rs3)).rowsWithin (keccak256AbsorbPermuteWriteSet rs1) = true ∧
      (Program.seq (keccak256AbsorbPermuteRowsAutoChunk21 rs1 rs2 rs3)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 22 of `Keccak256AbsorbPermute` (rd ≠ x0). -/
theorem keccak256AbsorbPermute_chunk22
    (rs1 rs2 rs3 : regidx) :
    (Program.seq (keccak256AbsorbPermuteRowsAutoChunk22 rs1 rs2 rs3)).rowsWithin (keccak256AbsorbPermuteWriteSet rs1) = true ∧
      (Program.seq (keccak256AbsorbPermuteRowsAutoChunk22 rs1 rs2 rs3)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 23 of `Keccak256AbsorbPermute` (rd ≠ x0). -/
theorem keccak256AbsorbPermute_chunk23
    (rs1 rs2 rs3 : regidx) :
    (Program.seq (keccak256AbsorbPermuteRowsAutoChunk23 rs1 rs2 rs3)).rowsWithin (keccak256AbsorbPermuteWriteSet rs1) = true ∧
      (Program.seq (keccak256AbsorbPermuteRowsAutoChunk23 rs1 rs2 rs3)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 24 of `Keccak256AbsorbPermute` (rd ≠ x0). -/
theorem keccak256AbsorbPermute_chunk24
    (rs1 rs2 rs3 : regidx) :
    (Program.seq (keccak256AbsorbPermuteRowsAutoChunk24 rs1 rs2 rs3)).rowsWithin (keccak256AbsorbPermuteWriteSet rs1) = true ∧
      (Program.seq (keccak256AbsorbPermuteRowsAutoChunk24 rs1 rs2 rs3)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 25 of `Keccak256AbsorbPermute` (rd ≠ x0). -/
theorem keccak256AbsorbPermute_chunk25
    (rs1 rs2 rs3 : regidx) :
    (Program.seq (keccak256AbsorbPermuteRowsAutoChunk25 rs1 rs2 rs3)).rowsWithin (keccak256AbsorbPermuteWriteSet rs1) = true ∧
      (Program.seq (keccak256AbsorbPermuteRowsAutoChunk25 rs1 rs2 rs3)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 26 of `Keccak256AbsorbPermute` (rd ≠ x0). -/
theorem keccak256AbsorbPermute_chunk26
    (rs1 rs2 rs3 : regidx) :
    (Program.seq (keccak256AbsorbPermuteRowsAutoChunk26 rs1 rs2 rs3)).rowsWithin (keccak256AbsorbPermuteWriteSet rs1) = true ∧
      (Program.seq (keccak256AbsorbPermuteRowsAutoChunk26 rs1 rs2 rs3)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 27 of `Keccak256AbsorbPermute` (rd ≠ x0). -/
theorem keccak256AbsorbPermute_chunk27
    (rs1 rs2 rs3 : regidx) :
    (Program.seq (keccak256AbsorbPermuteRowsAutoChunk27 rs1 rs2 rs3)).rowsWithin (keccak256AbsorbPermuteWriteSet rs1) = true ∧
      (Program.seq (keccak256AbsorbPermuteRowsAutoChunk27 rs1 rs2 rs3)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 28 of `Keccak256AbsorbPermute` (rd ≠ x0). -/
theorem keccak256AbsorbPermute_chunk28
    (rs1 rs2 rs3 : regidx) :
    (Program.seq (keccak256AbsorbPermuteRowsAutoChunk28 rs1 rs2 rs3)).rowsWithin (keccak256AbsorbPermuteWriteSet rs1) = true ∧
      (Program.seq (keccak256AbsorbPermuteRowsAutoChunk28 rs1 rs2 rs3)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 29 of `Keccak256AbsorbPermute` (rd ≠ x0). -/
theorem keccak256AbsorbPermute_chunk29
    (rs1 rs2 rs3 : regidx) :
    (Program.seq (keccak256AbsorbPermuteRowsAutoChunk29 rs1 rs2 rs3)).rowsWithin (keccak256AbsorbPermuteWriteSet rs1) = true ∧
      (Program.seq (keccak256AbsorbPermuteRowsAutoChunk29 rs1 rs2 rs3)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 30 of `Keccak256AbsorbPermute` (rd ≠ x0). -/
theorem keccak256AbsorbPermute_chunk30
    (rs1 rs2 rs3 : regidx) :
    (Program.seq (keccak256AbsorbPermuteRowsAutoChunk30 rs1 rs2 rs3)).rowsWithin (keccak256AbsorbPermuteWriteSet rs1) = true ∧
      (Program.seq (keccak256AbsorbPermuteRowsAutoChunk30 rs1 rs2 rs3)).storeSlots =
        [⟨.xreg rs1, 0, .dword⟩, ⟨.xreg rs1, 8, .dword⟩, ⟨.xreg rs1, 16, .dword⟩, ⟨.xreg rs1, 24, .dword⟩, ⟨.xreg rs1, 32, .dword⟩, ⟨.xreg rs1, 40, .dword⟩, ⟨.xreg rs1, 48, .dword⟩, ⟨.xreg rs1, 56, .dword⟩, ⟨.xreg rs1, 64, .dword⟩, ⟨.xreg rs1, 72, .dword⟩, ⟨.xreg rs1, 80, .dword⟩, ⟨.xreg rs1, 88, .dword⟩, ⟨.xreg rs1, 96, .dword⟩, ⟨.xreg rs1, 104, .dword⟩, ⟨.xreg rs1, 112, .dword⟩, ⟨.xreg rs1, 120, .dword⟩, ⟨.xreg rs1, 128, .dword⟩, ⟨.xreg rs1, 136, .dword⟩, ⟨.xreg rs1, 144, .dword⟩, ⟨.xreg rs1, 152, .dword⟩, ⟨.xreg rs1, 160, .dword⟩, ⟨.xreg rs1, 168, .dword⟩, ⟨.xreg rs1, 176, .dword⟩, ⟨.xreg rs1, 184, .dword⟩, ⟨.xreg rs1, 192, .dword⟩] :=
  ⟨rfl, rfl⟩

/-- Chunk 31 of `Keccak256AbsorbPermute` (rd ≠ x0). -/
theorem keccak256AbsorbPermute_chunk31
    (rs1 rs2 rs3 : regidx) :
    (Program.seq (keccak256AbsorbPermuteRowsAutoChunk31 rs1 rs2 rs3)).rowsWithin (keccak256AbsorbPermuteWriteSet rs1) = true ∧
      (Program.seq (keccak256AbsorbPermuteRowsAutoChunk31 rs1 rs2 rs3)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

theorem keccak256AbsorbPermute_storeSlots
    (rs1 rs2 rs3 : regidx) :
    (keccak256AbsorbPermuteRowsAuto rs1 rs2 rs3).storeSlots =
      keccak256AbsorbPermuteStores rs1 := by
  unfold keccak256AbsorbPermuteRowsAuto keccak256AbsorbPermuteRowsAutoList
  simp only [Program.storeSlots_seq_append,
      (keccak256AbsorbPermute_chunk0 rs1 rs2 rs3).2,
      (keccak256AbsorbPermute_chunk1 rs1 rs2 rs3).2,
      (keccak256AbsorbPermute_chunk2 rs1 rs2 rs3).2,
      (keccak256AbsorbPermute_chunk3 rs1 rs2 rs3).2,
      (keccak256AbsorbPermute_chunk4 rs1 rs2 rs3).2,
      (keccak256AbsorbPermute_chunk5 rs1 rs2 rs3).2,
      (keccak256AbsorbPermute_chunk6 rs1 rs2 rs3).2,
      (keccak256AbsorbPermute_chunk7 rs1 rs2 rs3).2,
      (keccak256AbsorbPermute_chunk8 rs1 rs2 rs3).2,
      (keccak256AbsorbPermute_chunk9 rs1 rs2 rs3).2,
      (keccak256AbsorbPermute_chunk10 rs1 rs2 rs3).2,
      (keccak256AbsorbPermute_chunk11 rs1 rs2 rs3).2,
      (keccak256AbsorbPermute_chunk12 rs1 rs2 rs3).2,
      (keccak256AbsorbPermute_chunk13 rs1 rs2 rs3).2,
      (keccak256AbsorbPermute_chunk14 rs1 rs2 rs3).2,
      (keccak256AbsorbPermute_chunk15 rs1 rs2 rs3).2,
      (keccak256AbsorbPermute_chunk16 rs1 rs2 rs3).2,
      (keccak256AbsorbPermute_chunk17 rs1 rs2 rs3).2,
      (keccak256AbsorbPermute_chunk18 rs1 rs2 rs3).2,
      (keccak256AbsorbPermute_chunk19 rs1 rs2 rs3).2,
      (keccak256AbsorbPermute_chunk20 rs1 rs2 rs3).2,
      (keccak256AbsorbPermute_chunk21 rs1 rs2 rs3).2,
      (keccak256AbsorbPermute_chunk22 rs1 rs2 rs3).2,
      (keccak256AbsorbPermute_chunk23 rs1 rs2 rs3).2,
      (keccak256AbsorbPermute_chunk24 rs1 rs2 rs3).2,
      (keccak256AbsorbPermute_chunk25 rs1 rs2 rs3).2,
      (keccak256AbsorbPermute_chunk26 rs1 rs2 rs3).2,
      (keccak256AbsorbPermute_chunk27 rs1 rs2 rs3).2,
      (keccak256AbsorbPermute_chunk28 rs1 rs2 rs3).2,
      (keccak256AbsorbPermute_chunk29 rs1 rs2 rs3).2,
      (keccak256AbsorbPermute_chunk30 rs1 rs2 rs3).2,
      (keccak256AbsorbPermute_chunk31 rs1 rs2 rs3).2]
  rfl

theorem keccak256AbsorbPermute_writesWithin
    (rs1 rs2 rs3 : regidx) :
    (keccak256AbsorbPermuteRowsAuto rs1 rs2 rs3).WritesWithin
      (keccak256AbsorbPermuteWriteSet rs1) :=
  ⟨by
    unfold keccak256AbsorbPermuteRowsAuto keccak256AbsorbPermuteRowsAutoList
    simp only [Program.rowsWithin_seq_append,
      (keccak256AbsorbPermute_chunk0 rs1 rs2 rs3).1,
      (keccak256AbsorbPermute_chunk1 rs1 rs2 rs3).1,
      (keccak256AbsorbPermute_chunk2 rs1 rs2 rs3).1,
      (keccak256AbsorbPermute_chunk3 rs1 rs2 rs3).1,
      (keccak256AbsorbPermute_chunk4 rs1 rs2 rs3).1,
      (keccak256AbsorbPermute_chunk5 rs1 rs2 rs3).1,
      (keccak256AbsorbPermute_chunk6 rs1 rs2 rs3).1,
      (keccak256AbsorbPermute_chunk7 rs1 rs2 rs3).1,
      (keccak256AbsorbPermute_chunk8 rs1 rs2 rs3).1,
      (keccak256AbsorbPermute_chunk9 rs1 rs2 rs3).1,
      (keccak256AbsorbPermute_chunk10 rs1 rs2 rs3).1,
      (keccak256AbsorbPermute_chunk11 rs1 rs2 rs3).1,
      (keccak256AbsorbPermute_chunk12 rs1 rs2 rs3).1,
      (keccak256AbsorbPermute_chunk13 rs1 rs2 rs3).1,
      (keccak256AbsorbPermute_chunk14 rs1 rs2 rs3).1,
      (keccak256AbsorbPermute_chunk15 rs1 rs2 rs3).1,
      (keccak256AbsorbPermute_chunk16 rs1 rs2 rs3).1,
      (keccak256AbsorbPermute_chunk17 rs1 rs2 rs3).1,
      (keccak256AbsorbPermute_chunk18 rs1 rs2 rs3).1,
      (keccak256AbsorbPermute_chunk19 rs1 rs2 rs3).1,
      (keccak256AbsorbPermute_chunk20 rs1 rs2 rs3).1,
      (keccak256AbsorbPermute_chunk21 rs1 rs2 rs3).1,
      (keccak256AbsorbPermute_chunk22 rs1 rs2 rs3).1,
      (keccak256AbsorbPermute_chunk23 rs1 rs2 rs3).1,
      (keccak256AbsorbPermute_chunk24 rs1 rs2 rs3).1,
      (keccak256AbsorbPermute_chunk25 rs1 rs2 rs3).1,
      (keccak256AbsorbPermute_chunk26 rs1 rs2 rs3).1,
      (keccak256AbsorbPermute_chunk27 rs1 rs2 rs3).1,
      (keccak256AbsorbPermute_chunk28 rs1 rs2 rs3).1,
      (keccak256AbsorbPermute_chunk29 rs1 rs2 rs3).1,
      (keccak256AbsorbPermute_chunk30 rs1 rs2 rs3).1,
      (keccak256AbsorbPermute_chunk31 rs1 rs2 rs3).1,
      Bool.and_self],
   by rw [keccak256AbsorbPermute_storeSlots]; exact List.Subset.refl _, rfl⟩

/-- The final chunks of `Keccak256AbsorbPermute` (rd ≠ x0), which contain the last write of every
pool register. -/
theorem keccak256AbsorbPermute_tailResets
    (rs1 rs2 rs3 : regidx) :
    (Program.seq (keccak256AbsorbPermuteRowsAutoChunk30 rs1 rs2 rs3 ++
      keccak256AbsorbPermuteRowsAutoChunk31 rs1 rs2 rs3)).resetsPoolCheck (poolVRegs 37) = true := rfl

theorem keccak256AbsorbPermute_resetsPoolCheck
    (rs1 rs2 rs3 : regidx) :
    (keccak256AbsorbPermuteRowsAuto rs1 rs2 rs3).resetsPoolCheck (poolVRegs 37) = true := by
  unfold keccak256AbsorbPermuteRowsAuto keccak256AbsorbPermuteRowsAutoList
  exact Program.resetsPoolCheck_seq_append_append _ (keccak256AbsorbPermute_tailResets rs1 rs2 rs3)

theorem keccak256AbsorbPermute_frame
    (rs1 rs2 rs3 : regidx) {s s' : SailJoltState}
    (h : (keccak256AbsorbPermuteRowsAuto rs1 rs2 rs3).Run s s') :
    Frame (keccak256AbsorbPermuteWriteSet rs1) s s' :=
  frame_of_run (keccak256AbsorbPermute_writesWithin rs1 rs2 rs3) h

/-! ### `Keccak256AbsorbPermute`, rd = x0 -/

/-- Store slots of `Keccak256AbsorbPermute` (rd = x0). -/
def keccak256AbsorbPermuteRdZeroStores (rs1 : regidx) : List StoreSlot :=
  [⟨.xreg rs1, 0, .dword⟩, ⟨.xreg rs1, 8, .dword⟩, ⟨.xreg rs1, 16, .dword⟩,
    ⟨.xreg rs1, 24, .dword⟩, ⟨.xreg rs1, 32, .dword⟩, ⟨.xreg rs1, 40, .dword⟩,
    ⟨.xreg rs1, 48, .dword⟩, ⟨.xreg rs1, 56, .dword⟩, ⟨.xreg rs1, 64, .dword⟩,
    ⟨.xreg rs1, 72, .dword⟩, ⟨.xreg rs1, 80, .dword⟩, ⟨.xreg rs1, 88, .dword⟩,
    ⟨.xreg rs1, 96, .dword⟩, ⟨.xreg rs1, 104, .dword⟩, ⟨.xreg rs1, 112, .dword⟩,
    ⟨.xreg rs1, 120, .dword⟩, ⟨.xreg rs1, 128, .dword⟩, ⟨.xreg rs1, 136, .dword⟩,
    ⟨.xreg rs1, 144, .dword⟩, ⟨.xreg rs1, 152, .dword⟩, ⟨.xreg rs1, 160, .dword⟩,
    ⟨.xreg rs1, 168, .dword⟩, ⟨.xreg rs1, 176, .dword⟩, ⟨.xreg rs1, 184, .dword⟩,
    ⟨.xreg rs1, 192, .dword⟩]

/-- Write set of `Keccak256AbsorbPermute` (rd = x0): pool registers `vr48..vr84`, no
architectural register, 25 store rows. -/
def keccak256AbsorbPermuteRdZeroWriteSet (rs1 : regidx) : WriteSet where
  vregs := poolVRegs 37
  xregs := []
  stores := keccak256AbsorbPermuteRdZeroStores rs1

/-- Chunk 0 of `Keccak256AbsorbPermute` (rd = x0). -/
theorem keccak256AbsorbPermuteRdZero_chunk0
    (rs1 rs2 : regidx) :
    (Program.seq (keccak256AbsorbPermuteRowsAutoRdZeroChunk0 rs1 rs2)).rowsWithin (keccak256AbsorbPermuteRdZeroWriteSet rs1) = true ∧
      (Program.seq (keccak256AbsorbPermuteRowsAutoRdZeroChunk0 rs1 rs2)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 1 of `Keccak256AbsorbPermute` (rd = x0). -/
theorem keccak256AbsorbPermuteRdZero_chunk1
    (rs1 rs2 : regidx) :
    (Program.seq (keccak256AbsorbPermuteRowsAutoRdZeroChunk1 rs1 rs2)).rowsWithin (keccak256AbsorbPermuteRdZeroWriteSet rs1) = true ∧
      (Program.seq (keccak256AbsorbPermuteRowsAutoRdZeroChunk1 rs1 rs2)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 2 of `Keccak256AbsorbPermute` (rd = x0). -/
theorem keccak256AbsorbPermuteRdZero_chunk2
    (rs1 rs2 : regidx) :
    (Program.seq (keccak256AbsorbPermuteRowsAutoRdZeroChunk2 rs1 rs2)).rowsWithin (keccak256AbsorbPermuteRdZeroWriteSet rs1) = true ∧
      (Program.seq (keccak256AbsorbPermuteRowsAutoRdZeroChunk2 rs1 rs2)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 3 of `Keccak256AbsorbPermute` (rd = x0). -/
theorem keccak256AbsorbPermuteRdZero_chunk3
    (rs1 rs2 : regidx) :
    (Program.seq (keccak256AbsorbPermuteRowsAutoRdZeroChunk3 rs1 rs2)).rowsWithin (keccak256AbsorbPermuteRdZeroWriteSet rs1) = true ∧
      (Program.seq (keccak256AbsorbPermuteRowsAutoRdZeroChunk3 rs1 rs2)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 4 of `Keccak256AbsorbPermute` (rd = x0). -/
theorem keccak256AbsorbPermuteRdZero_chunk4
    (rs1 rs2 : regidx) :
    (Program.seq (keccak256AbsorbPermuteRowsAutoRdZeroChunk4 rs1 rs2)).rowsWithin (keccak256AbsorbPermuteRdZeroWriteSet rs1) = true ∧
      (Program.seq (keccak256AbsorbPermuteRowsAutoRdZeroChunk4 rs1 rs2)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 5 of `Keccak256AbsorbPermute` (rd = x0). -/
theorem keccak256AbsorbPermuteRdZero_chunk5
    (rs1 rs2 : regidx) :
    (Program.seq (keccak256AbsorbPermuteRowsAutoRdZeroChunk5 rs1 rs2)).rowsWithin (keccak256AbsorbPermuteRdZeroWriteSet rs1) = true ∧
      (Program.seq (keccak256AbsorbPermuteRowsAutoRdZeroChunk5 rs1 rs2)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 6 of `Keccak256AbsorbPermute` (rd = x0). -/
theorem keccak256AbsorbPermuteRdZero_chunk6
    (rs1 rs2 : regidx) :
    (Program.seq (keccak256AbsorbPermuteRowsAutoRdZeroChunk6 rs1 rs2)).rowsWithin (keccak256AbsorbPermuteRdZeroWriteSet rs1) = true ∧
      (Program.seq (keccak256AbsorbPermuteRowsAutoRdZeroChunk6 rs1 rs2)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 7 of `Keccak256AbsorbPermute` (rd = x0). -/
theorem keccak256AbsorbPermuteRdZero_chunk7
    (rs1 rs2 : regidx) :
    (Program.seq (keccak256AbsorbPermuteRowsAutoRdZeroChunk7 rs1 rs2)).rowsWithin (keccak256AbsorbPermuteRdZeroWriteSet rs1) = true ∧
      (Program.seq (keccak256AbsorbPermuteRowsAutoRdZeroChunk7 rs1 rs2)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 8 of `Keccak256AbsorbPermute` (rd = x0). -/
theorem keccak256AbsorbPermuteRdZero_chunk8
    (rs1 rs2 : regidx) :
    (Program.seq (keccak256AbsorbPermuteRowsAutoRdZeroChunk8 rs1 rs2)).rowsWithin (keccak256AbsorbPermuteRdZeroWriteSet rs1) = true ∧
      (Program.seq (keccak256AbsorbPermuteRowsAutoRdZeroChunk8 rs1 rs2)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 9 of `Keccak256AbsorbPermute` (rd = x0). -/
theorem keccak256AbsorbPermuteRdZero_chunk9
    (rs1 rs2 : regidx) :
    (Program.seq (keccak256AbsorbPermuteRowsAutoRdZeroChunk9 rs1 rs2)).rowsWithin (keccak256AbsorbPermuteRdZeroWriteSet rs1) = true ∧
      (Program.seq (keccak256AbsorbPermuteRowsAutoRdZeroChunk9 rs1 rs2)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 10 of `Keccak256AbsorbPermute` (rd = x0). -/
theorem keccak256AbsorbPermuteRdZero_chunk10
    (rs1 rs2 : regidx) :
    (Program.seq (keccak256AbsorbPermuteRowsAutoRdZeroChunk10 rs1 rs2)).rowsWithin (keccak256AbsorbPermuteRdZeroWriteSet rs1) = true ∧
      (Program.seq (keccak256AbsorbPermuteRowsAutoRdZeroChunk10 rs1 rs2)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 11 of `Keccak256AbsorbPermute` (rd = x0). -/
theorem keccak256AbsorbPermuteRdZero_chunk11
    (rs1 rs2 : regidx) :
    (Program.seq (keccak256AbsorbPermuteRowsAutoRdZeroChunk11 rs1 rs2)).rowsWithin (keccak256AbsorbPermuteRdZeroWriteSet rs1) = true ∧
      (Program.seq (keccak256AbsorbPermuteRowsAutoRdZeroChunk11 rs1 rs2)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 12 of `Keccak256AbsorbPermute` (rd = x0). -/
theorem keccak256AbsorbPermuteRdZero_chunk12
    (rs1 rs2 : regidx) :
    (Program.seq (keccak256AbsorbPermuteRowsAutoRdZeroChunk12 rs1 rs2)).rowsWithin (keccak256AbsorbPermuteRdZeroWriteSet rs1) = true ∧
      (Program.seq (keccak256AbsorbPermuteRowsAutoRdZeroChunk12 rs1 rs2)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 13 of `Keccak256AbsorbPermute` (rd = x0). -/
theorem keccak256AbsorbPermuteRdZero_chunk13
    (rs1 rs2 : regidx) :
    (Program.seq (keccak256AbsorbPermuteRowsAutoRdZeroChunk13 rs1 rs2)).rowsWithin (keccak256AbsorbPermuteRdZeroWriteSet rs1) = true ∧
      (Program.seq (keccak256AbsorbPermuteRowsAutoRdZeroChunk13 rs1 rs2)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 14 of `Keccak256AbsorbPermute` (rd = x0). -/
theorem keccak256AbsorbPermuteRdZero_chunk14
    (rs1 rs2 : regidx) :
    (Program.seq (keccak256AbsorbPermuteRowsAutoRdZeroChunk14 rs1 rs2)).rowsWithin (keccak256AbsorbPermuteRdZeroWriteSet rs1) = true ∧
      (Program.seq (keccak256AbsorbPermuteRowsAutoRdZeroChunk14 rs1 rs2)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 15 of `Keccak256AbsorbPermute` (rd = x0). -/
theorem keccak256AbsorbPermuteRdZero_chunk15
    (rs1 rs2 : regidx) :
    (Program.seq (keccak256AbsorbPermuteRowsAutoRdZeroChunk15 rs1 rs2)).rowsWithin (keccak256AbsorbPermuteRdZeroWriteSet rs1) = true ∧
      (Program.seq (keccak256AbsorbPermuteRowsAutoRdZeroChunk15 rs1 rs2)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 16 of `Keccak256AbsorbPermute` (rd = x0). -/
theorem keccak256AbsorbPermuteRdZero_chunk16
    (rs1 rs2 : regidx) :
    (Program.seq (keccak256AbsorbPermuteRowsAutoRdZeroChunk16 rs1 rs2)).rowsWithin (keccak256AbsorbPermuteRdZeroWriteSet rs1) = true ∧
      (Program.seq (keccak256AbsorbPermuteRowsAutoRdZeroChunk16 rs1 rs2)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 17 of `Keccak256AbsorbPermute` (rd = x0). -/
theorem keccak256AbsorbPermuteRdZero_chunk17
    (rs1 rs2 : regidx) :
    (Program.seq (keccak256AbsorbPermuteRowsAutoRdZeroChunk17 rs1 rs2)).rowsWithin (keccak256AbsorbPermuteRdZeroWriteSet rs1) = true ∧
      (Program.seq (keccak256AbsorbPermuteRowsAutoRdZeroChunk17 rs1 rs2)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 18 of `Keccak256AbsorbPermute` (rd = x0). -/
theorem keccak256AbsorbPermuteRdZero_chunk18
    (rs1 rs2 : regidx) :
    (Program.seq (keccak256AbsorbPermuteRowsAutoRdZeroChunk18 rs1 rs2)).rowsWithin (keccak256AbsorbPermuteRdZeroWriteSet rs1) = true ∧
      (Program.seq (keccak256AbsorbPermuteRowsAutoRdZeroChunk18 rs1 rs2)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 19 of `Keccak256AbsorbPermute` (rd = x0). -/
theorem keccak256AbsorbPermuteRdZero_chunk19
    (rs1 rs2 : regidx) :
    (Program.seq (keccak256AbsorbPermuteRowsAutoRdZeroChunk19 rs1 rs2)).rowsWithin (keccak256AbsorbPermuteRdZeroWriteSet rs1) = true ∧
      (Program.seq (keccak256AbsorbPermuteRowsAutoRdZeroChunk19 rs1 rs2)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 20 of `Keccak256AbsorbPermute` (rd = x0). -/
theorem keccak256AbsorbPermuteRdZero_chunk20
    (rs1 rs2 : regidx) :
    (Program.seq (keccak256AbsorbPermuteRowsAutoRdZeroChunk20 rs1 rs2)).rowsWithin (keccak256AbsorbPermuteRdZeroWriteSet rs1) = true ∧
      (Program.seq (keccak256AbsorbPermuteRowsAutoRdZeroChunk20 rs1 rs2)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 21 of `Keccak256AbsorbPermute` (rd = x0). -/
theorem keccak256AbsorbPermuteRdZero_chunk21
    (rs1 rs2 : regidx) :
    (Program.seq (keccak256AbsorbPermuteRowsAutoRdZeroChunk21 rs1 rs2)).rowsWithin (keccak256AbsorbPermuteRdZeroWriteSet rs1) = true ∧
      (Program.seq (keccak256AbsorbPermuteRowsAutoRdZeroChunk21 rs1 rs2)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 22 of `Keccak256AbsorbPermute` (rd = x0). -/
theorem keccak256AbsorbPermuteRdZero_chunk22
    (rs1 rs2 : regidx) :
    (Program.seq (keccak256AbsorbPermuteRowsAutoRdZeroChunk22 rs1 rs2)).rowsWithin (keccak256AbsorbPermuteRdZeroWriteSet rs1) = true ∧
      (Program.seq (keccak256AbsorbPermuteRowsAutoRdZeroChunk22 rs1 rs2)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 23 of `Keccak256AbsorbPermute` (rd = x0). -/
theorem keccak256AbsorbPermuteRdZero_chunk23
    (rs1 rs2 : regidx) :
    (Program.seq (keccak256AbsorbPermuteRowsAutoRdZeroChunk23 rs1 rs2)).rowsWithin (keccak256AbsorbPermuteRdZeroWriteSet rs1) = true ∧
      (Program.seq (keccak256AbsorbPermuteRowsAutoRdZeroChunk23 rs1 rs2)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 24 of `Keccak256AbsorbPermute` (rd = x0). -/
theorem keccak256AbsorbPermuteRdZero_chunk24
    (rs1 rs2 : regidx) :
    (Program.seq (keccak256AbsorbPermuteRowsAutoRdZeroChunk24 rs1 rs2)).rowsWithin (keccak256AbsorbPermuteRdZeroWriteSet rs1) = true ∧
      (Program.seq (keccak256AbsorbPermuteRowsAutoRdZeroChunk24 rs1 rs2)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 25 of `Keccak256AbsorbPermute` (rd = x0). -/
theorem keccak256AbsorbPermuteRdZero_chunk25
    (rs1 rs2 : regidx) :
    (Program.seq (keccak256AbsorbPermuteRowsAutoRdZeroChunk25 rs1 rs2)).rowsWithin (keccak256AbsorbPermuteRdZeroWriteSet rs1) = true ∧
      (Program.seq (keccak256AbsorbPermuteRowsAutoRdZeroChunk25 rs1 rs2)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 26 of `Keccak256AbsorbPermute` (rd = x0). -/
theorem keccak256AbsorbPermuteRdZero_chunk26
    (rs1 rs2 : regidx) :
    (Program.seq (keccak256AbsorbPermuteRowsAutoRdZeroChunk26 rs1 rs2)).rowsWithin (keccak256AbsorbPermuteRdZeroWriteSet rs1) = true ∧
      (Program.seq (keccak256AbsorbPermuteRowsAutoRdZeroChunk26 rs1 rs2)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 27 of `Keccak256AbsorbPermute` (rd = x0). -/
theorem keccak256AbsorbPermuteRdZero_chunk27
    (rs1 rs2 : regidx) :
    (Program.seq (keccak256AbsorbPermuteRowsAutoRdZeroChunk27 rs1 rs2)).rowsWithin (keccak256AbsorbPermuteRdZeroWriteSet rs1) = true ∧
      (Program.seq (keccak256AbsorbPermuteRowsAutoRdZeroChunk27 rs1 rs2)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 28 of `Keccak256AbsorbPermute` (rd = x0). -/
theorem keccak256AbsorbPermuteRdZero_chunk28
    (rs1 rs2 : regidx) :
    (Program.seq (keccak256AbsorbPermuteRowsAutoRdZeroChunk28 rs1 rs2)).rowsWithin (keccak256AbsorbPermuteRdZeroWriteSet rs1) = true ∧
      (Program.seq (keccak256AbsorbPermuteRowsAutoRdZeroChunk28 rs1 rs2)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 29 of `Keccak256AbsorbPermute` (rd = x0). -/
theorem keccak256AbsorbPermuteRdZero_chunk29
    (rs1 rs2 : regidx) :
    (Program.seq (keccak256AbsorbPermuteRowsAutoRdZeroChunk29 rs1 rs2)).rowsWithin (keccak256AbsorbPermuteRdZeroWriteSet rs1) = true ∧
      (Program.seq (keccak256AbsorbPermuteRowsAutoRdZeroChunk29 rs1 rs2)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 30 of `Keccak256AbsorbPermute` (rd = x0). -/
theorem keccak256AbsorbPermuteRdZero_chunk30
    (rs1 rs2 : regidx) :
    (Program.seq (keccak256AbsorbPermuteRowsAutoRdZeroChunk30 rs1 rs2)).rowsWithin (keccak256AbsorbPermuteRdZeroWriteSet rs1) = true ∧
      (Program.seq (keccak256AbsorbPermuteRowsAutoRdZeroChunk30 rs1 rs2)).storeSlots =
        [⟨.xreg rs1, 0, .dword⟩, ⟨.xreg rs1, 8, .dword⟩, ⟨.xreg rs1, 16, .dword⟩, ⟨.xreg rs1, 24, .dword⟩, ⟨.xreg rs1, 32, .dword⟩, ⟨.xreg rs1, 40, .dword⟩, ⟨.xreg rs1, 48, .dword⟩, ⟨.xreg rs1, 56, .dword⟩, ⟨.xreg rs1, 64, .dword⟩, ⟨.xreg rs1, 72, .dword⟩, ⟨.xreg rs1, 80, .dword⟩, ⟨.xreg rs1, 88, .dword⟩, ⟨.xreg rs1, 96, .dword⟩, ⟨.xreg rs1, 104, .dword⟩, ⟨.xreg rs1, 112, .dword⟩, ⟨.xreg rs1, 120, .dword⟩, ⟨.xreg rs1, 128, .dword⟩, ⟨.xreg rs1, 136, .dword⟩, ⟨.xreg rs1, 144, .dword⟩, ⟨.xreg rs1, 152, .dword⟩, ⟨.xreg rs1, 160, .dword⟩, ⟨.xreg rs1, 168, .dword⟩, ⟨.xreg rs1, 176, .dword⟩, ⟨.xreg rs1, 184, .dword⟩, ⟨.xreg rs1, 192, .dword⟩] :=
  ⟨rfl, rfl⟩

/-- Chunk 31 of `Keccak256AbsorbPermute` (rd = x0). -/
theorem keccak256AbsorbPermuteRdZero_chunk31
    (rs1 rs2 : regidx) :
    (Program.seq (keccak256AbsorbPermuteRowsAutoRdZeroChunk31 rs1 rs2)).rowsWithin (keccak256AbsorbPermuteRdZeroWriteSet rs1) = true ∧
      (Program.seq (keccak256AbsorbPermuteRowsAutoRdZeroChunk31 rs1 rs2)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

theorem keccak256AbsorbPermuteRdZero_storeSlots
    (rs1 rs2 : regidx) :
    (keccak256AbsorbPermuteRowsAutoRdZero rs1 rs2).storeSlots =
      keccak256AbsorbPermuteRdZeroStores rs1 := by
  unfold keccak256AbsorbPermuteRowsAutoRdZero keccak256AbsorbPermuteRowsAutoRdZeroList
  simp only [Program.storeSlots_seq_append,
      (keccak256AbsorbPermuteRdZero_chunk0 rs1 rs2).2,
      (keccak256AbsorbPermuteRdZero_chunk1 rs1 rs2).2,
      (keccak256AbsorbPermuteRdZero_chunk2 rs1 rs2).2,
      (keccak256AbsorbPermuteRdZero_chunk3 rs1 rs2).2,
      (keccak256AbsorbPermuteRdZero_chunk4 rs1 rs2).2,
      (keccak256AbsorbPermuteRdZero_chunk5 rs1 rs2).2,
      (keccak256AbsorbPermuteRdZero_chunk6 rs1 rs2).2,
      (keccak256AbsorbPermuteRdZero_chunk7 rs1 rs2).2,
      (keccak256AbsorbPermuteRdZero_chunk8 rs1 rs2).2,
      (keccak256AbsorbPermuteRdZero_chunk9 rs1 rs2).2,
      (keccak256AbsorbPermuteRdZero_chunk10 rs1 rs2).2,
      (keccak256AbsorbPermuteRdZero_chunk11 rs1 rs2).2,
      (keccak256AbsorbPermuteRdZero_chunk12 rs1 rs2).2,
      (keccak256AbsorbPermuteRdZero_chunk13 rs1 rs2).2,
      (keccak256AbsorbPermuteRdZero_chunk14 rs1 rs2).2,
      (keccak256AbsorbPermuteRdZero_chunk15 rs1 rs2).2,
      (keccak256AbsorbPermuteRdZero_chunk16 rs1 rs2).2,
      (keccak256AbsorbPermuteRdZero_chunk17 rs1 rs2).2,
      (keccak256AbsorbPermuteRdZero_chunk18 rs1 rs2).2,
      (keccak256AbsorbPermuteRdZero_chunk19 rs1 rs2).2,
      (keccak256AbsorbPermuteRdZero_chunk20 rs1 rs2).2,
      (keccak256AbsorbPermuteRdZero_chunk21 rs1 rs2).2,
      (keccak256AbsorbPermuteRdZero_chunk22 rs1 rs2).2,
      (keccak256AbsorbPermuteRdZero_chunk23 rs1 rs2).2,
      (keccak256AbsorbPermuteRdZero_chunk24 rs1 rs2).2,
      (keccak256AbsorbPermuteRdZero_chunk25 rs1 rs2).2,
      (keccak256AbsorbPermuteRdZero_chunk26 rs1 rs2).2,
      (keccak256AbsorbPermuteRdZero_chunk27 rs1 rs2).2,
      (keccak256AbsorbPermuteRdZero_chunk28 rs1 rs2).2,
      (keccak256AbsorbPermuteRdZero_chunk29 rs1 rs2).2,
      (keccak256AbsorbPermuteRdZero_chunk30 rs1 rs2).2,
      (keccak256AbsorbPermuteRdZero_chunk31 rs1 rs2).2]
  rfl

theorem keccak256AbsorbPermuteRdZero_writesWithin
    (rs1 rs2 : regidx) :
    (keccak256AbsorbPermuteRowsAutoRdZero rs1 rs2).WritesWithin
      (keccak256AbsorbPermuteRdZeroWriteSet rs1) :=
  ⟨by
    unfold keccak256AbsorbPermuteRowsAutoRdZero keccak256AbsorbPermuteRowsAutoRdZeroList
    simp only [Program.rowsWithin_seq_append,
      (keccak256AbsorbPermuteRdZero_chunk0 rs1 rs2).1,
      (keccak256AbsorbPermuteRdZero_chunk1 rs1 rs2).1,
      (keccak256AbsorbPermuteRdZero_chunk2 rs1 rs2).1,
      (keccak256AbsorbPermuteRdZero_chunk3 rs1 rs2).1,
      (keccak256AbsorbPermuteRdZero_chunk4 rs1 rs2).1,
      (keccak256AbsorbPermuteRdZero_chunk5 rs1 rs2).1,
      (keccak256AbsorbPermuteRdZero_chunk6 rs1 rs2).1,
      (keccak256AbsorbPermuteRdZero_chunk7 rs1 rs2).1,
      (keccak256AbsorbPermuteRdZero_chunk8 rs1 rs2).1,
      (keccak256AbsorbPermuteRdZero_chunk9 rs1 rs2).1,
      (keccak256AbsorbPermuteRdZero_chunk10 rs1 rs2).1,
      (keccak256AbsorbPermuteRdZero_chunk11 rs1 rs2).1,
      (keccak256AbsorbPermuteRdZero_chunk12 rs1 rs2).1,
      (keccak256AbsorbPermuteRdZero_chunk13 rs1 rs2).1,
      (keccak256AbsorbPermuteRdZero_chunk14 rs1 rs2).1,
      (keccak256AbsorbPermuteRdZero_chunk15 rs1 rs2).1,
      (keccak256AbsorbPermuteRdZero_chunk16 rs1 rs2).1,
      (keccak256AbsorbPermuteRdZero_chunk17 rs1 rs2).1,
      (keccak256AbsorbPermuteRdZero_chunk18 rs1 rs2).1,
      (keccak256AbsorbPermuteRdZero_chunk19 rs1 rs2).1,
      (keccak256AbsorbPermuteRdZero_chunk20 rs1 rs2).1,
      (keccak256AbsorbPermuteRdZero_chunk21 rs1 rs2).1,
      (keccak256AbsorbPermuteRdZero_chunk22 rs1 rs2).1,
      (keccak256AbsorbPermuteRdZero_chunk23 rs1 rs2).1,
      (keccak256AbsorbPermuteRdZero_chunk24 rs1 rs2).1,
      (keccak256AbsorbPermuteRdZero_chunk25 rs1 rs2).1,
      (keccak256AbsorbPermuteRdZero_chunk26 rs1 rs2).1,
      (keccak256AbsorbPermuteRdZero_chunk27 rs1 rs2).1,
      (keccak256AbsorbPermuteRdZero_chunk28 rs1 rs2).1,
      (keccak256AbsorbPermuteRdZero_chunk29 rs1 rs2).1,
      (keccak256AbsorbPermuteRdZero_chunk30 rs1 rs2).1,
      (keccak256AbsorbPermuteRdZero_chunk31 rs1 rs2).1,
      Bool.and_self],
   by rw [keccak256AbsorbPermuteRdZero_storeSlots]; exact List.Subset.refl _, rfl⟩

/-- The final chunks of `Keccak256AbsorbPermute` (rd = x0), which contain the last write of every
pool register. -/
theorem keccak256AbsorbPermuteRdZero_tailResets
    (rs1 rs2 : regidx) :
    (Program.seq (keccak256AbsorbPermuteRowsAutoRdZeroChunk30 rs1 rs2 ++
      keccak256AbsorbPermuteRowsAutoRdZeroChunk31 rs1 rs2)).resetsPoolCheck (poolVRegs 37) = true := rfl

theorem keccak256AbsorbPermuteRdZero_resetsPoolCheck
    (rs1 rs2 : regidx) :
    (keccak256AbsorbPermuteRowsAutoRdZero rs1 rs2).resetsPoolCheck (poolVRegs 37) = true := by
  unfold keccak256AbsorbPermuteRowsAutoRdZero keccak256AbsorbPermuteRowsAutoRdZeroList
  exact Program.resetsPoolCheck_seq_append_append _ (keccak256AbsorbPermuteRdZero_tailResets rs1 rs2)

theorem keccak256AbsorbPermuteRdZero_frame
    (rs1 rs2 : regidx) {s s' : SailJoltState}
    (h : (keccak256AbsorbPermuteRowsAutoRdZero rs1 rs2).Run s s') :
    Frame (keccak256AbsorbPermuteRdZeroWriteSet rs1) s s' :=
  frame_of_run (keccak256AbsorbPermuteRdZero_writesWithin rs1 rs2) h

/-! ### `Blake2`, rd ≠ x0 -/

/-- Store slots of `Blake2` (rd ≠ x0). -/
def blake2Stores (rs1 : regidx) : List StoreSlot :=
  [⟨.xreg rs1, 0, .dword⟩, ⟨.xreg rs1, 8, .dword⟩, ⟨.xreg rs1, 16, .dword⟩,
    ⟨.xreg rs1, 24, .dword⟩, ⟨.xreg rs1, 32, .dword⟩, ⟨.xreg rs1, 40, .dword⟩,
    ⟨.xreg rs1, 48, .dword⟩, ⟨.xreg rs1, 56, .dword⟩]

/-- Write set of `Blake2` (rd ≠ x0): pool registers `vr48..vr87`, no
architectural register, 8 store rows. -/
def blake2WriteSet (rs1 : regidx) : WriteSet where
  vregs := poolVRegs 40
  xregs := []
  stores := blake2Stores rs1

/-- Chunk 0 of `Blake2` (rd ≠ x0). -/
theorem blake2_chunk0
    (rs1 rs2 rs3 : regidx) :
    (Program.seq (blake2RowsAutoChunk0 rs1 rs2 rs3)).rowsWithin (blake2WriteSet rs1) = true ∧
      (Program.seq (blake2RowsAutoChunk0 rs1 rs2 rs3)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 1 of `Blake2` (rd ≠ x0). -/
theorem blake2_chunk1
    (rs1 rs2 rs3 : regidx) :
    (Program.seq (blake2RowsAutoChunk1 rs1 rs2 rs3)).rowsWithin (blake2WriteSet rs1) = true ∧
      (Program.seq (blake2RowsAutoChunk1 rs1 rs2 rs3)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 2 of `Blake2` (rd ≠ x0). -/
theorem blake2_chunk2
    (rs1 rs2 rs3 : regidx) :
    (Program.seq (blake2RowsAutoChunk2 rs1 rs2 rs3)).rowsWithin (blake2WriteSet rs1) = true ∧
      (Program.seq (blake2RowsAutoChunk2 rs1 rs2 rs3)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 3 of `Blake2` (rd ≠ x0). -/
theorem blake2_chunk3
    (rs1 rs2 rs3 : regidx) :
    (Program.seq (blake2RowsAutoChunk3 rs1 rs2 rs3)).rowsWithin (blake2WriteSet rs1) = true ∧
      (Program.seq (blake2RowsAutoChunk3 rs1 rs2 rs3)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 4 of `Blake2` (rd ≠ x0). -/
theorem blake2_chunk4
    (rs1 rs2 rs3 : regidx) :
    (Program.seq (blake2RowsAutoChunk4 rs1 rs2 rs3)).rowsWithin (blake2WriteSet rs1) = true ∧
      (Program.seq (blake2RowsAutoChunk4 rs1 rs2 rs3)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 5 of `Blake2` (rd ≠ x0). -/
theorem blake2_chunk5
    (rs1 rs2 rs3 : regidx) :
    (Program.seq (blake2RowsAutoChunk5 rs1 rs2 rs3)).rowsWithin (blake2WriteSet rs1) = true ∧
      (Program.seq (blake2RowsAutoChunk5 rs1 rs2 rs3)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 6 of `Blake2` (rd ≠ x0). -/
theorem blake2_chunk6
    (rs1 rs2 rs3 : regidx) :
    (Program.seq (blake2RowsAutoChunk6 rs1 rs2 rs3)).rowsWithin (blake2WriteSet rs1) = true ∧
      (Program.seq (blake2RowsAutoChunk6 rs1 rs2 rs3)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 7 of `Blake2` (rd ≠ x0). -/
theorem blake2_chunk7
    (rs1 rs2 rs3 : regidx) :
    (Program.seq (blake2RowsAutoChunk7 rs1 rs2 rs3)).rowsWithin (blake2WriteSet rs1) = true ∧
      (Program.seq (blake2RowsAutoChunk7 rs1 rs2 rs3)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 8 of `Blake2` (rd ≠ x0). -/
theorem blake2_chunk8
    (rs1 rs2 rs3 : regidx) :
    (Program.seq (blake2RowsAutoChunk8 rs1 rs2 rs3)).rowsWithin (blake2WriteSet rs1) = true ∧
      (Program.seq (blake2RowsAutoChunk8 rs1 rs2 rs3)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 9 of `Blake2` (rd ≠ x0). -/
theorem blake2_chunk9
    (rs1 rs2 rs3 : regidx) :
    (Program.seq (blake2RowsAutoChunk9 rs1 rs2 rs3)).rowsWithin (blake2WriteSet rs1) = true ∧
      (Program.seq (blake2RowsAutoChunk9 rs1 rs2 rs3)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 10 of `Blake2` (rd ≠ x0). -/
theorem blake2_chunk10
    (rs1 rs2 rs3 : regidx) :
    (Program.seq (blake2RowsAutoChunk10 rs1 rs2 rs3)).rowsWithin (blake2WriteSet rs1) = true ∧
      (Program.seq (blake2RowsAutoChunk10 rs1 rs2 rs3)).storeSlots =
        [⟨.xreg rs1, 0, .dword⟩, ⟨.xreg rs1, 8, .dword⟩, ⟨.xreg rs1, 16, .dword⟩, ⟨.xreg rs1, 24, .dword⟩, ⟨.xreg rs1, 32, .dword⟩, ⟨.xreg rs1, 40, .dword⟩, ⟨.xreg rs1, 48, .dword⟩, ⟨.xreg rs1, 56, .dword⟩] :=
  ⟨rfl, rfl⟩

theorem blake2_storeSlots
    (rs1 rs2 rs3 : regidx) :
    (blake2RowsAuto rs1 rs2 rs3).storeSlots =
      blake2Stores rs1 := by
  unfold blake2RowsAuto blake2RowsAutoList
  simp only [Program.storeSlots_seq_append,
      (blake2_chunk0 rs1 rs2 rs3).2,
      (blake2_chunk1 rs1 rs2 rs3).2,
      (blake2_chunk2 rs1 rs2 rs3).2,
      (blake2_chunk3 rs1 rs2 rs3).2,
      (blake2_chunk4 rs1 rs2 rs3).2,
      (blake2_chunk5 rs1 rs2 rs3).2,
      (blake2_chunk6 rs1 rs2 rs3).2,
      (blake2_chunk7 rs1 rs2 rs3).2,
      (blake2_chunk8 rs1 rs2 rs3).2,
      (blake2_chunk9 rs1 rs2 rs3).2,
      (blake2_chunk10 rs1 rs2 rs3).2]
  rfl

theorem blake2_writesWithin
    (rs1 rs2 rs3 : regidx) :
    (blake2RowsAuto rs1 rs2 rs3).WritesWithin
      (blake2WriteSet rs1) :=
  ⟨by
    unfold blake2RowsAuto blake2RowsAutoList
    simp only [Program.rowsWithin_seq_append,
      (blake2_chunk0 rs1 rs2 rs3).1,
      (blake2_chunk1 rs1 rs2 rs3).1,
      (blake2_chunk2 rs1 rs2 rs3).1,
      (blake2_chunk3 rs1 rs2 rs3).1,
      (blake2_chunk4 rs1 rs2 rs3).1,
      (blake2_chunk5 rs1 rs2 rs3).1,
      (blake2_chunk6 rs1 rs2 rs3).1,
      (blake2_chunk7 rs1 rs2 rs3).1,
      (blake2_chunk8 rs1 rs2 rs3).1,
      (blake2_chunk9 rs1 rs2 rs3).1,
      (blake2_chunk10 rs1 rs2 rs3).1,
      Bool.and_self],
   by rw [blake2_storeSlots]; exact List.Subset.refl _, rfl⟩

/-- The final chunks of `Blake2` (rd ≠ x0), which contain the last write of every
pool register. -/
theorem blake2_tailResets
    (rs1 rs2 rs3 : regidx) :
    (Program.seq (blake2RowsAutoChunk10 rs1 rs2 rs3)).resetsPoolCheck (poolVRegs 40) = true := rfl

theorem blake2_resetsPoolCheck
    (rs1 rs2 rs3 : regidx) :
    (blake2RowsAuto rs1 rs2 rs3).resetsPoolCheck (poolVRegs 40) = true := by
  unfold blake2RowsAuto blake2RowsAutoList
  exact Program.resetsPoolCheck_seq_append _ (blake2_tailResets rs1 rs2 rs3)

theorem blake2_frame
    (rs1 rs2 rs3 : regidx) {s s' : SailJoltState}
    (h : (blake2RowsAuto rs1 rs2 rs3).Run s s') :
    Frame (blake2WriteSet rs1) s s' :=
  frame_of_run (blake2_writesWithin rs1 rs2 rs3) h

/-! ### `Blake2`, rd = x0 -/

/-- Store slots of `Blake2` (rd = x0). -/
def blake2RdZeroStores (rs1 : regidx) : List StoreSlot :=
  [⟨.xreg rs1, 0, .dword⟩, ⟨.xreg rs1, 8, .dword⟩, ⟨.xreg rs1, 16, .dword⟩,
    ⟨.xreg rs1, 24, .dword⟩, ⟨.xreg rs1, 32, .dword⟩, ⟨.xreg rs1, 40, .dword⟩,
    ⟨.xreg rs1, 48, .dword⟩, ⟨.xreg rs1, 56, .dword⟩]

/-- Write set of `Blake2` (rd = x0): pool registers `vr48..vr87`, no
architectural register, 8 store rows. -/
def blake2RdZeroWriteSet (rs1 : regidx) : WriteSet where
  vregs := poolVRegs 40
  xregs := []
  stores := blake2RdZeroStores rs1

/-- Chunk 0 of `Blake2` (rd = x0). -/
theorem blake2RdZero_chunk0
    (rs1 rs2 : regidx) :
    (Program.seq (blake2RowsAutoRdZeroChunk0 rs1 rs2)).rowsWithin (blake2RdZeroWriteSet rs1) = true ∧
      (Program.seq (blake2RowsAutoRdZeroChunk0 rs1 rs2)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 1 of `Blake2` (rd = x0). -/
theorem blake2RdZero_chunk1
    (rs1 rs2 : regidx) :
    (Program.seq (blake2RowsAutoRdZeroChunk1 rs1 rs2)).rowsWithin (blake2RdZeroWriteSet rs1) = true ∧
      (Program.seq (blake2RowsAutoRdZeroChunk1 rs1 rs2)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 2 of `Blake2` (rd = x0). -/
theorem blake2RdZero_chunk2
    (rs1 rs2 : regidx) :
    (Program.seq (blake2RowsAutoRdZeroChunk2 rs1 rs2)).rowsWithin (blake2RdZeroWriteSet rs1) = true ∧
      (Program.seq (blake2RowsAutoRdZeroChunk2 rs1 rs2)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 3 of `Blake2` (rd = x0). -/
theorem blake2RdZero_chunk3
    (rs1 rs2 : regidx) :
    (Program.seq (blake2RowsAutoRdZeroChunk3 rs1 rs2)).rowsWithin (blake2RdZeroWriteSet rs1) = true ∧
      (Program.seq (blake2RowsAutoRdZeroChunk3 rs1 rs2)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 4 of `Blake2` (rd = x0). -/
theorem blake2RdZero_chunk4
    (rs1 rs2 : regidx) :
    (Program.seq (blake2RowsAutoRdZeroChunk4 rs1 rs2)).rowsWithin (blake2RdZeroWriteSet rs1) = true ∧
      (Program.seq (blake2RowsAutoRdZeroChunk4 rs1 rs2)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 5 of `Blake2` (rd = x0). -/
theorem blake2RdZero_chunk5
    (rs1 rs2 : regidx) :
    (Program.seq (blake2RowsAutoRdZeroChunk5 rs1 rs2)).rowsWithin (blake2RdZeroWriteSet rs1) = true ∧
      (Program.seq (blake2RowsAutoRdZeroChunk5 rs1 rs2)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 6 of `Blake2` (rd = x0). -/
theorem blake2RdZero_chunk6
    (rs1 rs2 : regidx) :
    (Program.seq (blake2RowsAutoRdZeroChunk6 rs1 rs2)).rowsWithin (blake2RdZeroWriteSet rs1) = true ∧
      (Program.seq (blake2RowsAutoRdZeroChunk6 rs1 rs2)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 7 of `Blake2` (rd = x0). -/
theorem blake2RdZero_chunk7
    (rs1 rs2 : regidx) :
    (Program.seq (blake2RowsAutoRdZeroChunk7 rs1 rs2)).rowsWithin (blake2RdZeroWriteSet rs1) = true ∧
      (Program.seq (blake2RowsAutoRdZeroChunk7 rs1 rs2)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 8 of `Blake2` (rd = x0). -/
theorem blake2RdZero_chunk8
    (rs1 rs2 : regidx) :
    (Program.seq (blake2RowsAutoRdZeroChunk8 rs1 rs2)).rowsWithin (blake2RdZeroWriteSet rs1) = true ∧
      (Program.seq (blake2RowsAutoRdZeroChunk8 rs1 rs2)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 9 of `Blake2` (rd = x0). -/
theorem blake2RdZero_chunk9
    (rs1 rs2 : regidx) :
    (Program.seq (blake2RowsAutoRdZeroChunk9 rs1 rs2)).rowsWithin (blake2RdZeroWriteSet rs1) = true ∧
      (Program.seq (blake2RowsAutoRdZeroChunk9 rs1 rs2)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 10 of `Blake2` (rd = x0). -/
theorem blake2RdZero_chunk10
    (rs1 rs2 : regidx) :
    (Program.seq (blake2RowsAutoRdZeroChunk10 rs1 rs2)).rowsWithin (blake2RdZeroWriteSet rs1) = true ∧
      (Program.seq (blake2RowsAutoRdZeroChunk10 rs1 rs2)).storeSlots =
        [⟨.xreg rs1, 0, .dword⟩, ⟨.xreg rs1, 8, .dword⟩, ⟨.xreg rs1, 16, .dword⟩, ⟨.xreg rs1, 24, .dword⟩, ⟨.xreg rs1, 32, .dword⟩, ⟨.xreg rs1, 40, .dword⟩, ⟨.xreg rs1, 48, .dword⟩, ⟨.xreg rs1, 56, .dword⟩] :=
  ⟨rfl, rfl⟩

theorem blake2RdZero_storeSlots
    (rs1 rs2 : regidx) :
    (blake2RowsAutoRdZero rs1 rs2).storeSlots =
      blake2RdZeroStores rs1 := by
  unfold blake2RowsAutoRdZero blake2RowsAutoRdZeroList
  simp only [Program.storeSlots_seq_append,
      (blake2RdZero_chunk0 rs1 rs2).2,
      (blake2RdZero_chunk1 rs1 rs2).2,
      (blake2RdZero_chunk2 rs1 rs2).2,
      (blake2RdZero_chunk3 rs1 rs2).2,
      (blake2RdZero_chunk4 rs1 rs2).2,
      (blake2RdZero_chunk5 rs1 rs2).2,
      (blake2RdZero_chunk6 rs1 rs2).2,
      (blake2RdZero_chunk7 rs1 rs2).2,
      (blake2RdZero_chunk8 rs1 rs2).2,
      (blake2RdZero_chunk9 rs1 rs2).2,
      (blake2RdZero_chunk10 rs1 rs2).2]
  rfl

theorem blake2RdZero_writesWithin
    (rs1 rs2 : regidx) :
    (blake2RowsAutoRdZero rs1 rs2).WritesWithin
      (blake2RdZeroWriteSet rs1) :=
  ⟨by
    unfold blake2RowsAutoRdZero blake2RowsAutoRdZeroList
    simp only [Program.rowsWithin_seq_append,
      (blake2RdZero_chunk0 rs1 rs2).1,
      (blake2RdZero_chunk1 rs1 rs2).1,
      (blake2RdZero_chunk2 rs1 rs2).1,
      (blake2RdZero_chunk3 rs1 rs2).1,
      (blake2RdZero_chunk4 rs1 rs2).1,
      (blake2RdZero_chunk5 rs1 rs2).1,
      (blake2RdZero_chunk6 rs1 rs2).1,
      (blake2RdZero_chunk7 rs1 rs2).1,
      (blake2RdZero_chunk8 rs1 rs2).1,
      (blake2RdZero_chunk9 rs1 rs2).1,
      (blake2RdZero_chunk10 rs1 rs2).1,
      Bool.and_self],
   by rw [blake2RdZero_storeSlots]; exact List.Subset.refl _, rfl⟩

/-- The final chunks of `Blake2` (rd = x0), which contain the last write of every
pool register. -/
theorem blake2RdZero_tailResets
    (rs1 rs2 : regidx) :
    (Program.seq (blake2RowsAutoRdZeroChunk10 rs1 rs2)).resetsPoolCheck (poolVRegs 40) = true := rfl

theorem blake2RdZero_resetsPoolCheck
    (rs1 rs2 : regidx) :
    (blake2RowsAutoRdZero rs1 rs2).resetsPoolCheck (poolVRegs 40) = true := by
  unfold blake2RowsAutoRdZero blake2RowsAutoRdZeroList
  exact Program.resetsPoolCheck_seq_append _ (blake2RdZero_tailResets rs1 rs2)

theorem blake2RdZero_frame
    (rs1 rs2 : regidx) {s s' : SailJoltState}
    (h : (blake2RowsAutoRdZero rs1 rs2).Run s s') :
    Frame (blake2RdZeroWriteSet rs1) s s' :=
  frame_of_run (blake2RdZero_writesWithin rs1 rs2) h

/-! ### `Secp256k1Mulq`, rd ≠ x0 -/

/-- Store slots of `Secp256k1Mulq` (rd ≠ x0). -/
def secp256k1MulqStores (rs3 : regidx) : List StoreSlot :=
  [⟨.xreg rs3, 0, .dword⟩, ⟨.xreg rs3, 8, .dword⟩, ⟨.xreg rs3, 16, .dword⟩,
    ⟨.xreg rs3, 24, .dword⟩]

/-- Write set of `Secp256k1Mulq` (rd ≠ x0): pool registers `vr48..vr63`, no
architectural register, 4 store rows. -/
def secp256k1MulqWriteSet (rs3 : regidx) : WriteSet where
  vregs := poolVRegs 16
  xregs := []
  stores := secp256k1MulqStores rs3

/-- Chunk 0 of `Secp256k1Mulq` (rd ≠ x0). -/
theorem secp256k1Mulq_chunk0
    (rs1 rs2 rs3 : regidx) (advice : Nat → BitVec 64) :
    (Program.seq (secp256k1MulqRowsAutoChunk0 rs1 rs2 rs3 advice)).rowsWithin (secp256k1MulqWriteSet rs3) = true ∧
      (Program.seq (secp256k1MulqRowsAutoChunk0 rs1 rs2 rs3 advice)).storeSlots =
        [⟨.xreg rs3, 0, .dword⟩, ⟨.xreg rs3, 8, .dword⟩, ⟨.xreg rs3, 16, .dword⟩] :=
  ⟨rfl, rfl⟩

/-- Chunk 1 of `Secp256k1Mulq` (rd ≠ x0). -/
theorem secp256k1Mulq_chunk1
    (rs1 rs2 rs3 : regidx) (advice : Nat → BitVec 64) :
    (Program.seq (secp256k1MulqRowsAutoChunk1 rs1 rs2 rs3 advice)).rowsWithin (secp256k1MulqWriteSet rs3) = true ∧
      (Program.seq (secp256k1MulqRowsAutoChunk1 rs1 rs2 rs3 advice)).storeSlots =
        [⟨.xreg rs3, 24, .dword⟩] :=
  ⟨rfl, rfl⟩

theorem secp256k1Mulq_storeSlots
    (rs1 rs2 rs3 : regidx) (advice : Nat → BitVec 64) :
    (secp256k1MulqRowsAuto rs1 rs2 rs3 advice).storeSlots =
      secp256k1MulqStores rs3 := by
  unfold secp256k1MulqRowsAuto secp256k1MulqRowsAutoList
  simp only [Program.storeSlots_seq_append,
      (secp256k1Mulq_chunk0 rs1 rs2 rs3 advice).2,
      (secp256k1Mulq_chunk1 rs1 rs2 rs3 advice).2]
  rfl

theorem secp256k1Mulq_writesWithin
    (rs1 rs2 rs3 : regidx) (advice : Nat → BitVec 64) :
    (secp256k1MulqRowsAuto rs1 rs2 rs3 advice).WritesWithin
      (secp256k1MulqWriteSet rs3) :=
  ⟨by
    unfold secp256k1MulqRowsAuto secp256k1MulqRowsAutoList
    simp only [Program.rowsWithin_seq_append,
      (secp256k1Mulq_chunk0 rs1 rs2 rs3 advice).1,
      (secp256k1Mulq_chunk1 rs1 rs2 rs3 advice).1,
      Bool.and_self],
   by rw [secp256k1Mulq_storeSlots]; exact List.Subset.refl _, rfl⟩

/-- The final chunks of `Secp256k1Mulq` (rd ≠ x0), which contain the last write of every
pool register. -/
theorem secp256k1Mulq_tailResets
    (rs1 rs2 rs3 : regidx) (advice : Nat → BitVec 64) :
    (Program.seq (secp256k1MulqRowsAutoChunk1 rs1 rs2 rs3 advice)).resetsPoolCheck (poolVRegs 16) = true := rfl

theorem secp256k1Mulq_resetsPoolCheck
    (rs1 rs2 rs3 : regidx) (advice : Nat → BitVec 64) :
    (secp256k1MulqRowsAuto rs1 rs2 rs3 advice).resetsPoolCheck (poolVRegs 16) = true := by
  unfold secp256k1MulqRowsAuto secp256k1MulqRowsAutoList
  exact Program.resetsPoolCheck_seq_append _ (secp256k1Mulq_tailResets rs1 rs2 rs3 advice)

theorem secp256k1Mulq_frame
    (rs1 rs2 rs3 : regidx) (advice : Nat → BitVec 64) {s s' : SailJoltState}
    (h : (secp256k1MulqRowsAuto rs1 rs2 rs3 advice).Run s s') :
    Frame (secp256k1MulqWriteSet rs3) s s' :=
  frame_of_run (secp256k1Mulq_writesWithin rs1 rs2 rs3 advice) h

/-! ### `Secp256k1Mulq`, rd = x0 -/

/-- Store slots of `Secp256k1Mulq` (rd = x0).
The store rows address memory through `vr40`, which no row writes, so the footprint
is `s.vregs 40 + 8k`: the value `vr40` holds when the inline starts. -/
def secp256k1MulqRdZeroStores : List StoreSlot :=
  [⟨.vreg 40, 0, .dword⟩, ⟨.vreg 40, 8, .dword⟩, ⟨.vreg 40, 16, .dword⟩,
    ⟨.vreg 40, 24, .dword⟩]

/-- Write set of `Secp256k1Mulq` (rd = x0): pool registers `vr48..vr63`, no
architectural register, 4 store rows. -/
def secp256k1MulqRdZeroWriteSet : WriteSet where
  vregs := poolVRegs 16
  xregs := []
  stores := secp256k1MulqRdZeroStores

/-- Chunk 0 of `Secp256k1Mulq` (rd = x0). -/
theorem secp256k1MulqRdZero_chunk0
    (rs1 rs2 : regidx) (advice : Nat → BitVec 64) :
    (Program.seq (secp256k1MulqRowsAutoRdZeroChunk0 rs1 rs2 advice)).rowsWithin (secp256k1MulqRdZeroWriteSet) = true ∧
      (Program.seq (secp256k1MulqRowsAutoRdZeroChunk0 rs1 rs2 advice)).storeSlots =
        [⟨.vreg 40, 0, .dword⟩, ⟨.vreg 40, 8, .dword⟩, ⟨.vreg 40, 16, .dword⟩] :=
  ⟨rfl, rfl⟩

/-- Chunk 1 of `Secp256k1Mulq` (rd = x0). -/
theorem secp256k1MulqRdZero_chunk1
    (rs1 rs2 : regidx) (advice : Nat → BitVec 64) :
    (Program.seq (secp256k1MulqRowsAutoRdZeroChunk1 rs1 rs2 advice)).rowsWithin (secp256k1MulqRdZeroWriteSet) = true ∧
      (Program.seq (secp256k1MulqRowsAutoRdZeroChunk1 rs1 rs2 advice)).storeSlots =
        [⟨.vreg 40, 24, .dword⟩] :=
  ⟨rfl, rfl⟩

theorem secp256k1MulqRdZero_storeSlots
    (rs1 rs2 : regidx) (advice : Nat → BitVec 64) :
    (secp256k1MulqRowsAutoRdZero rs1 rs2 advice).storeSlots =
      secp256k1MulqRdZeroStores := by
  unfold secp256k1MulqRowsAutoRdZero secp256k1MulqRowsAutoRdZeroList
  simp only [Program.storeSlots_seq_append,
      (secp256k1MulqRdZero_chunk0 rs1 rs2 advice).2,
      (secp256k1MulqRdZero_chunk1 rs1 rs2 advice).2]
  rfl

theorem secp256k1MulqRdZero_writesWithin
    (rs1 rs2 : regidx) (advice : Nat → BitVec 64) :
    (secp256k1MulqRowsAutoRdZero rs1 rs2 advice).WritesWithin
      (secp256k1MulqRdZeroWriteSet) :=
  ⟨by
    unfold secp256k1MulqRowsAutoRdZero secp256k1MulqRowsAutoRdZeroList
    simp only [Program.rowsWithin_seq_append,
      (secp256k1MulqRdZero_chunk0 rs1 rs2 advice).1,
      (secp256k1MulqRdZero_chunk1 rs1 rs2 advice).1,
      Bool.and_self],
   by rw [secp256k1MulqRdZero_storeSlots]; exact List.Subset.refl _, rfl⟩

/-- The final chunks of `Secp256k1Mulq` (rd = x0), which contain the last write of every
pool register. -/
theorem secp256k1MulqRdZero_tailResets
    (rs1 rs2 : regidx) (advice : Nat → BitVec 64) :
    (Program.seq (secp256k1MulqRowsAutoRdZeroChunk1 rs1 rs2 advice)).resetsPoolCheck (poolVRegs 16) = true := rfl

theorem secp256k1MulqRdZero_resetsPoolCheck
    (rs1 rs2 : regidx) (advice : Nat → BitVec 64) :
    (secp256k1MulqRowsAutoRdZero rs1 rs2 advice).resetsPoolCheck (poolVRegs 16) = true := by
  unfold secp256k1MulqRowsAutoRdZero secp256k1MulqRowsAutoRdZeroList
  exact Program.resetsPoolCheck_seq_append _ (secp256k1MulqRdZero_tailResets rs1 rs2 advice)

theorem secp256k1MulqRdZero_frame
    (rs1 rs2 : regidx) (advice : Nat → BitVec 64) {s s' : SailJoltState}
    (h : (secp256k1MulqRowsAutoRdZero rs1 rs2 advice).Run s s') :
    Frame (secp256k1MulqRdZeroWriteSet) s s' :=
  frame_of_run (secp256k1MulqRdZero_writesWithin rs1 rs2 advice) h

/-! ### `Secp256k1Mulr`, rd ≠ x0 -/

/-- Store slots of `Secp256k1Mulr` (rd ≠ x0). -/
def secp256k1MulrStores (rs3 : regidx) : List StoreSlot :=
  [⟨.xreg rs3, 0, .dword⟩, ⟨.xreg rs3, 8, .dword⟩, ⟨.xreg rs3, 16, .dword⟩,
    ⟨.xreg rs3, 24, .dword⟩]

/-- Write set of `Secp256k1Mulr` (rd ≠ x0): pool registers `vr48..vr64`, no
architectural register, 4 store rows. -/
def secp256k1MulrWriteSet (rs3 : regidx) : WriteSet where
  vregs := poolVRegs 17
  xregs := []
  stores := secp256k1MulrStores rs3

/-- Chunk 0 of `Secp256k1Mulr` (rd ≠ x0). -/
theorem secp256k1Mulr_chunk0
    (rs1 rs2 rs3 : regidx) (advice : Nat → BitVec 64) :
    (Program.seq (secp256k1MulrRowsAutoChunk0 rs1 rs2 rs3 advice)).rowsWithin (secp256k1MulrWriteSet rs3) = true ∧
      (Program.seq (secp256k1MulrRowsAutoChunk0 rs1 rs2 rs3 advice)).storeSlots =
        [⟨.xreg rs3, 0, .dword⟩, ⟨.xreg rs3, 8, .dword⟩, ⟨.xreg rs3, 16, .dword⟩] :=
  ⟨rfl, rfl⟩

/-- Chunk 1 of `Secp256k1Mulr` (rd ≠ x0). -/
theorem secp256k1Mulr_chunk1
    (rs1 rs2 rs3 : regidx) (advice : Nat → BitVec 64) :
    (Program.seq (secp256k1MulrRowsAutoChunk1 rs1 rs2 rs3 advice)).rowsWithin (secp256k1MulrWriteSet rs3) = true ∧
      (Program.seq (secp256k1MulrRowsAutoChunk1 rs1 rs2 rs3 advice)).storeSlots =
        [⟨.xreg rs3, 24, .dword⟩] :=
  ⟨rfl, rfl⟩

/-- Chunk 2 of `Secp256k1Mulr` (rd ≠ x0). -/
theorem secp256k1Mulr_chunk2
    (rs1 rs2 rs3 : regidx) (advice : Nat → BitVec 64) :
    (Program.seq (secp256k1MulrRowsAutoChunk2 rs1 rs2 rs3 advice)).rowsWithin (secp256k1MulrWriteSet rs3) = true ∧
      (Program.seq (secp256k1MulrRowsAutoChunk2 rs1 rs2 rs3 advice)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

theorem secp256k1Mulr_storeSlots
    (rs1 rs2 rs3 : regidx) (advice : Nat → BitVec 64) :
    (secp256k1MulrRowsAuto rs1 rs2 rs3 advice).storeSlots =
      secp256k1MulrStores rs3 := by
  unfold secp256k1MulrRowsAuto secp256k1MulrRowsAutoList
  simp only [Program.storeSlots_seq_append,
      (secp256k1Mulr_chunk0 rs1 rs2 rs3 advice).2,
      (secp256k1Mulr_chunk1 rs1 rs2 rs3 advice).2,
      (secp256k1Mulr_chunk2 rs1 rs2 rs3 advice).2]
  rfl

theorem secp256k1Mulr_writesWithin
    (rs1 rs2 rs3 : regidx) (advice : Nat → BitVec 64) :
    (secp256k1MulrRowsAuto rs1 rs2 rs3 advice).WritesWithin
      (secp256k1MulrWriteSet rs3) :=
  ⟨by
    unfold secp256k1MulrRowsAuto secp256k1MulrRowsAutoList
    simp only [Program.rowsWithin_seq_append,
      (secp256k1Mulr_chunk0 rs1 rs2 rs3 advice).1,
      (secp256k1Mulr_chunk1 rs1 rs2 rs3 advice).1,
      (secp256k1Mulr_chunk2 rs1 rs2 rs3 advice).1,
      Bool.and_self],
   by rw [secp256k1Mulr_storeSlots]; exact List.Subset.refl _, rfl⟩

/-- The final chunks of `Secp256k1Mulr` (rd ≠ x0), which contain the last write of every
pool register. -/
theorem secp256k1Mulr_tailResets
    (rs1 rs2 rs3 : regidx) (advice : Nat → BitVec 64) :
    (Program.seq (secp256k1MulrRowsAutoChunk2 rs1 rs2 rs3 advice)).resetsPoolCheck (poolVRegs 17) = true := rfl

theorem secp256k1Mulr_resetsPoolCheck
    (rs1 rs2 rs3 : regidx) (advice : Nat → BitVec 64) :
    (secp256k1MulrRowsAuto rs1 rs2 rs3 advice).resetsPoolCheck (poolVRegs 17) = true := by
  unfold secp256k1MulrRowsAuto secp256k1MulrRowsAutoList
  exact Program.resetsPoolCheck_seq_append _ (secp256k1Mulr_tailResets rs1 rs2 rs3 advice)

theorem secp256k1Mulr_frame
    (rs1 rs2 rs3 : regidx) (advice : Nat → BitVec 64) {s s' : SailJoltState}
    (h : (secp256k1MulrRowsAuto rs1 rs2 rs3 advice).Run s s') :
    Frame (secp256k1MulrWriteSet rs3) s s' :=
  frame_of_run (secp256k1Mulr_writesWithin rs1 rs2 rs3 advice) h

/-! ### `Secp256k1Mulr`, rd = x0 -/

/-- Store slots of `Secp256k1Mulr` (rd = x0).
The store rows address memory through `vr40`, which no row writes, so the footprint
is `s.vregs 40 + 8k`: the value `vr40` holds when the inline starts. -/
def secp256k1MulrRdZeroStores : List StoreSlot :=
  [⟨.vreg 40, 0, .dword⟩, ⟨.vreg 40, 8, .dword⟩, ⟨.vreg 40, 16, .dword⟩,
    ⟨.vreg 40, 24, .dword⟩]

/-- Write set of `Secp256k1Mulr` (rd = x0): pool registers `vr48..vr64`, no
architectural register, 4 store rows. -/
def secp256k1MulrRdZeroWriteSet : WriteSet where
  vregs := poolVRegs 17
  xregs := []
  stores := secp256k1MulrRdZeroStores

/-- Chunk 0 of `Secp256k1Mulr` (rd = x0). -/
theorem secp256k1MulrRdZero_chunk0
    (rs1 rs2 : regidx) (advice : Nat → BitVec 64) :
    (Program.seq (secp256k1MulrRowsAutoRdZeroChunk0 rs1 rs2 advice)).rowsWithin (secp256k1MulrRdZeroWriteSet) = true ∧
      (Program.seq (secp256k1MulrRowsAutoRdZeroChunk0 rs1 rs2 advice)).storeSlots =
        [⟨.vreg 40, 0, .dword⟩, ⟨.vreg 40, 8, .dword⟩, ⟨.vreg 40, 16, .dword⟩] :=
  ⟨rfl, rfl⟩

/-- Chunk 1 of `Secp256k1Mulr` (rd = x0). -/
theorem secp256k1MulrRdZero_chunk1
    (rs1 rs2 : regidx) (advice : Nat → BitVec 64) :
    (Program.seq (secp256k1MulrRowsAutoRdZeroChunk1 rs1 rs2 advice)).rowsWithin (secp256k1MulrRdZeroWriteSet) = true ∧
      (Program.seq (secp256k1MulrRowsAutoRdZeroChunk1 rs1 rs2 advice)).storeSlots =
        [⟨.vreg 40, 24, .dword⟩] :=
  ⟨rfl, rfl⟩

/-- Chunk 2 of `Secp256k1Mulr` (rd = x0). -/
theorem secp256k1MulrRdZero_chunk2
    (rs1 rs2 : regidx) (advice : Nat → BitVec 64) :
    (Program.seq (secp256k1MulrRowsAutoRdZeroChunk2 rs1 rs2 advice)).rowsWithin (secp256k1MulrRdZeroWriteSet) = true ∧
      (Program.seq (secp256k1MulrRowsAutoRdZeroChunk2 rs1 rs2 advice)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

theorem secp256k1MulrRdZero_storeSlots
    (rs1 rs2 : regidx) (advice : Nat → BitVec 64) :
    (secp256k1MulrRowsAutoRdZero rs1 rs2 advice).storeSlots =
      secp256k1MulrRdZeroStores := by
  unfold secp256k1MulrRowsAutoRdZero secp256k1MulrRowsAutoRdZeroList
  simp only [Program.storeSlots_seq_append,
      (secp256k1MulrRdZero_chunk0 rs1 rs2 advice).2,
      (secp256k1MulrRdZero_chunk1 rs1 rs2 advice).2,
      (secp256k1MulrRdZero_chunk2 rs1 rs2 advice).2]
  rfl

theorem secp256k1MulrRdZero_writesWithin
    (rs1 rs2 : regidx) (advice : Nat → BitVec 64) :
    (secp256k1MulrRowsAutoRdZero rs1 rs2 advice).WritesWithin
      (secp256k1MulrRdZeroWriteSet) :=
  ⟨by
    unfold secp256k1MulrRowsAutoRdZero secp256k1MulrRowsAutoRdZeroList
    simp only [Program.rowsWithin_seq_append,
      (secp256k1MulrRdZero_chunk0 rs1 rs2 advice).1,
      (secp256k1MulrRdZero_chunk1 rs1 rs2 advice).1,
      (secp256k1MulrRdZero_chunk2 rs1 rs2 advice).1,
      Bool.and_self],
   by rw [secp256k1MulrRdZero_storeSlots]; exact List.Subset.refl _, rfl⟩

/-- The final chunks of `Secp256k1Mulr` (rd = x0), which contain the last write of every
pool register. -/
theorem secp256k1MulrRdZero_tailResets
    (rs1 rs2 : regidx) (advice : Nat → BitVec 64) :
    (Program.seq (secp256k1MulrRowsAutoRdZeroChunk2 rs1 rs2 advice)).resetsPoolCheck (poolVRegs 17) = true := rfl

theorem secp256k1MulrRdZero_resetsPoolCheck
    (rs1 rs2 : regidx) (advice : Nat → BitVec 64) :
    (secp256k1MulrRowsAutoRdZero rs1 rs2 advice).resetsPoolCheck (poolVRegs 17) = true := by
  unfold secp256k1MulrRowsAutoRdZero secp256k1MulrRowsAutoRdZeroList
  exact Program.resetsPoolCheck_seq_append _ (secp256k1MulrRdZero_tailResets rs1 rs2 advice)

theorem secp256k1MulrRdZero_frame
    (rs1 rs2 : regidx) (advice : Nat → BitVec 64) {s s' : SailJoltState}
    (h : (secp256k1MulrRowsAutoRdZero rs1 rs2 advice).Run s s') :
    Frame (secp256k1MulrRdZeroWriteSet) s s' :=
  frame_of_run (secp256k1MulrRdZero_writesWithin rs1 rs2 advice) h

/-! ### `Secp256k1Squareq`, rd ≠ x0 -/

/-- Store slots of `Secp256k1Squareq` (rd ≠ x0). -/
def secp256k1SquareqStores (rs3 : regidx) : List StoreSlot :=
  [⟨.xreg rs3, 0, .dword⟩, ⟨.xreg rs3, 8, .dword⟩, ⟨.xreg rs3, 16, .dword⟩,
    ⟨.xreg rs3, 24, .dword⟩]

/-- Write set of `Secp256k1Squareq` (rd ≠ x0): pool registers `vr48..vr60`, no
architectural register, 4 store rows. -/
def secp256k1SquareqWriteSet (rs3 : regidx) : WriteSet where
  vregs := poolVRegs 13
  xregs := []
  stores := secp256k1SquareqStores rs3

/-- Chunk 0 of `Secp256k1Squareq` (rd ≠ x0). -/
theorem secp256k1Squareq_chunk0
    (rs1 rs2 rs3 : regidx) (advice : Nat → BitVec 64) :
    (Program.seq (secp256k1SquareqRowsAutoChunk0 rs1 rs2 rs3 advice)).rowsWithin (secp256k1SquareqWriteSet rs3) = true ∧
      (Program.seq (secp256k1SquareqRowsAutoChunk0 rs1 rs2 rs3 advice)).storeSlots =
        [⟨.xreg rs3, 0, .dword⟩, ⟨.xreg rs3, 8, .dword⟩, ⟨.xreg rs3, 16, .dword⟩, ⟨.xreg rs3, 24, .dword⟩] :=
  ⟨rfl, rfl⟩

/-- Chunk 1 of `Secp256k1Squareq` (rd ≠ x0). -/
theorem secp256k1Squareq_chunk1
    (rs1 rs2 rs3 : regidx) (advice : Nat → BitVec 64) :
    (Program.seq (secp256k1SquareqRowsAutoChunk1 rs1 rs2 rs3 advice)).rowsWithin (secp256k1SquareqWriteSet rs3) = true ∧
      (Program.seq (secp256k1SquareqRowsAutoChunk1 rs1 rs2 rs3 advice)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

theorem secp256k1Squareq_storeSlots
    (rs1 rs2 rs3 : regidx) (advice : Nat → BitVec 64) :
    (secp256k1SquareqRowsAuto rs1 rs2 rs3 advice).storeSlots =
      secp256k1SquareqStores rs3 := by
  unfold secp256k1SquareqRowsAuto secp256k1SquareqRowsAutoList
  simp only [Program.storeSlots_seq_append,
      (secp256k1Squareq_chunk0 rs1 rs2 rs3 advice).2,
      (secp256k1Squareq_chunk1 rs1 rs2 rs3 advice).2]
  rfl

theorem secp256k1Squareq_writesWithin
    (rs1 rs2 rs3 : regidx) (advice : Nat → BitVec 64) :
    (secp256k1SquareqRowsAuto rs1 rs2 rs3 advice).WritesWithin
      (secp256k1SquareqWriteSet rs3) :=
  ⟨by
    unfold secp256k1SquareqRowsAuto secp256k1SquareqRowsAutoList
    simp only [Program.rowsWithin_seq_append,
      (secp256k1Squareq_chunk0 rs1 rs2 rs3 advice).1,
      (secp256k1Squareq_chunk1 rs1 rs2 rs3 advice).1,
      Bool.and_self],
   by rw [secp256k1Squareq_storeSlots]; exact List.Subset.refl _, rfl⟩

/-- The final chunks of `Secp256k1Squareq` (rd ≠ x0), which contain the last write of every
pool register. -/
theorem secp256k1Squareq_tailResets
    (rs1 rs2 rs3 : regidx) (advice : Nat → BitVec 64) :
    (Program.seq (secp256k1SquareqRowsAutoChunk1 rs1 rs2 rs3 advice)).resetsPoolCheck (poolVRegs 13) = true := rfl

theorem secp256k1Squareq_resetsPoolCheck
    (rs1 rs2 rs3 : regidx) (advice : Nat → BitVec 64) :
    (secp256k1SquareqRowsAuto rs1 rs2 rs3 advice).resetsPoolCheck (poolVRegs 13) = true := by
  unfold secp256k1SquareqRowsAuto secp256k1SquareqRowsAutoList
  exact Program.resetsPoolCheck_seq_append _ (secp256k1Squareq_tailResets rs1 rs2 rs3 advice)

theorem secp256k1Squareq_frame
    (rs1 rs2 rs3 : regidx) (advice : Nat → BitVec 64) {s s' : SailJoltState}
    (h : (secp256k1SquareqRowsAuto rs1 rs2 rs3 advice).Run s s') :
    Frame (secp256k1SquareqWriteSet rs3) s s' :=
  frame_of_run (secp256k1Squareq_writesWithin rs1 rs2 rs3 advice) h

/-! ### `Secp256k1Squareq`, rd = x0 -/

/-- Store slots of `Secp256k1Squareq` (rd = x0).
The store rows address memory through `vr40`, which no row writes, so the footprint
is `s.vregs 40 + 8k`: the value `vr40` holds when the inline starts. -/
def secp256k1SquareqRdZeroStores : List StoreSlot :=
  [⟨.vreg 40, 0, .dword⟩, ⟨.vreg 40, 8, .dword⟩, ⟨.vreg 40, 16, .dword⟩,
    ⟨.vreg 40, 24, .dword⟩]

/-- Write set of `Secp256k1Squareq` (rd = x0): pool registers `vr48..vr60`, no
architectural register, 4 store rows. -/
def secp256k1SquareqRdZeroWriteSet : WriteSet where
  vregs := poolVRegs 13
  xregs := []
  stores := secp256k1SquareqRdZeroStores

/-- Chunk 0 of `Secp256k1Squareq` (rd = x0). -/
theorem secp256k1SquareqRdZero_chunk0
    (rs1 rs2 : regidx) (advice : Nat → BitVec 64) :
    (Program.seq (secp256k1SquareqRowsAutoRdZeroChunk0 rs1 rs2 advice)).rowsWithin (secp256k1SquareqRdZeroWriteSet) = true ∧
      (Program.seq (secp256k1SquareqRowsAutoRdZeroChunk0 rs1 rs2 advice)).storeSlots =
        [⟨.vreg 40, 0, .dword⟩, ⟨.vreg 40, 8, .dword⟩, ⟨.vreg 40, 16, .dword⟩, ⟨.vreg 40, 24, .dword⟩] :=
  ⟨rfl, rfl⟩

/-- Chunk 1 of `Secp256k1Squareq` (rd = x0). -/
theorem secp256k1SquareqRdZero_chunk1
    (rs1 rs2 : regidx) (advice : Nat → BitVec 64) :
    (Program.seq (secp256k1SquareqRowsAutoRdZeroChunk1 rs1 rs2 advice)).rowsWithin (secp256k1SquareqRdZeroWriteSet) = true ∧
      (Program.seq (secp256k1SquareqRowsAutoRdZeroChunk1 rs1 rs2 advice)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

theorem secp256k1SquareqRdZero_storeSlots
    (rs1 rs2 : regidx) (advice : Nat → BitVec 64) :
    (secp256k1SquareqRowsAutoRdZero rs1 rs2 advice).storeSlots =
      secp256k1SquareqRdZeroStores := by
  unfold secp256k1SquareqRowsAutoRdZero secp256k1SquareqRowsAutoRdZeroList
  simp only [Program.storeSlots_seq_append,
      (secp256k1SquareqRdZero_chunk0 rs1 rs2 advice).2,
      (secp256k1SquareqRdZero_chunk1 rs1 rs2 advice).2]
  rfl

theorem secp256k1SquareqRdZero_writesWithin
    (rs1 rs2 : regidx) (advice : Nat → BitVec 64) :
    (secp256k1SquareqRowsAutoRdZero rs1 rs2 advice).WritesWithin
      (secp256k1SquareqRdZeroWriteSet) :=
  ⟨by
    unfold secp256k1SquareqRowsAutoRdZero secp256k1SquareqRowsAutoRdZeroList
    simp only [Program.rowsWithin_seq_append,
      (secp256k1SquareqRdZero_chunk0 rs1 rs2 advice).1,
      (secp256k1SquareqRdZero_chunk1 rs1 rs2 advice).1,
      Bool.and_self],
   by rw [secp256k1SquareqRdZero_storeSlots]; exact List.Subset.refl _, rfl⟩

/-- The final chunks of `Secp256k1Squareq` (rd = x0), which contain the last write of every
pool register. -/
theorem secp256k1SquareqRdZero_tailResets
    (rs1 rs2 : regidx) (advice : Nat → BitVec 64) :
    (Program.seq (secp256k1SquareqRowsAutoRdZeroChunk1 rs1 rs2 advice)).resetsPoolCheck (poolVRegs 13) = true := rfl

theorem secp256k1SquareqRdZero_resetsPoolCheck
    (rs1 rs2 : regidx) (advice : Nat → BitVec 64) :
    (secp256k1SquareqRowsAutoRdZero rs1 rs2 advice).resetsPoolCheck (poolVRegs 13) = true := by
  unfold secp256k1SquareqRowsAutoRdZero secp256k1SquareqRowsAutoRdZeroList
  exact Program.resetsPoolCheck_seq_append _ (secp256k1SquareqRdZero_tailResets rs1 rs2 advice)

theorem secp256k1SquareqRdZero_frame
    (rs1 rs2 : regidx) (advice : Nat → BitVec 64) {s s' : SailJoltState}
    (h : (secp256k1SquareqRowsAutoRdZero rs1 rs2 advice).Run s s') :
    Frame (secp256k1SquareqRdZeroWriteSet) s s' :=
  frame_of_run (secp256k1SquareqRdZero_writesWithin rs1 rs2 advice) h

/-! ### `Secp256k1Squarer`, rd ≠ x0 -/

/-- Store slots of `Secp256k1Squarer` (rd ≠ x0). -/
def secp256k1SquarerStores (rs3 : regidx) : List StoreSlot :=
  [⟨.xreg rs3, 0, .dword⟩, ⟨.xreg rs3, 8, .dword⟩, ⟨.xreg rs3, 16, .dword⟩,
    ⟨.xreg rs3, 24, .dword⟩]

/-- Write set of `Secp256k1Squarer` (rd ≠ x0): pool registers `vr48..vr61`, no
architectural register, 4 store rows. -/
def secp256k1SquarerWriteSet (rs3 : regidx) : WriteSet where
  vregs := poolVRegs 14
  xregs := []
  stores := secp256k1SquarerStores rs3

/-- Chunk 0 of `Secp256k1Squarer` (rd ≠ x0). -/
theorem secp256k1Squarer_chunk0
    (rs1 rs2 rs3 : regidx) (advice : Nat → BitVec 64) :
    (Program.seq (secp256k1SquarerRowsAutoChunk0 rs1 rs2 rs3 advice)).rowsWithin (secp256k1SquarerWriteSet rs3) = true ∧
      (Program.seq (secp256k1SquarerRowsAutoChunk0 rs1 rs2 rs3 advice)).storeSlots =
        [⟨.xreg rs3, 0, .dword⟩, ⟨.xreg rs3, 8, .dword⟩, ⟨.xreg rs3, 16, .dword⟩] :=
  ⟨rfl, rfl⟩

/-- Chunk 1 of `Secp256k1Squarer` (rd ≠ x0). -/
theorem secp256k1Squarer_chunk1
    (rs1 rs2 rs3 : regidx) (advice : Nat → BitVec 64) :
    (Program.seq (secp256k1SquarerRowsAutoChunk1 rs1 rs2 rs3 advice)).rowsWithin (secp256k1SquarerWriteSet rs3) = true ∧
      (Program.seq (secp256k1SquarerRowsAutoChunk1 rs1 rs2 rs3 advice)).storeSlots =
        [⟨.xreg rs3, 24, .dword⟩] :=
  ⟨rfl, rfl⟩

/-- Chunk 2 of `Secp256k1Squarer` (rd ≠ x0). -/
theorem secp256k1Squarer_chunk2
    (rs1 rs2 rs3 : regidx) (advice : Nat → BitVec 64) :
    (Program.seq (secp256k1SquarerRowsAutoChunk2 rs1 rs2 rs3 advice)).rowsWithin (secp256k1SquarerWriteSet rs3) = true ∧
      (Program.seq (secp256k1SquarerRowsAutoChunk2 rs1 rs2 rs3 advice)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

theorem secp256k1Squarer_storeSlots
    (rs1 rs2 rs3 : regidx) (advice : Nat → BitVec 64) :
    (secp256k1SquarerRowsAuto rs1 rs2 rs3 advice).storeSlots =
      secp256k1SquarerStores rs3 := by
  unfold secp256k1SquarerRowsAuto secp256k1SquarerRowsAutoList
  simp only [Program.storeSlots_seq_append,
      (secp256k1Squarer_chunk0 rs1 rs2 rs3 advice).2,
      (secp256k1Squarer_chunk1 rs1 rs2 rs3 advice).2,
      (secp256k1Squarer_chunk2 rs1 rs2 rs3 advice).2]
  rfl

theorem secp256k1Squarer_writesWithin
    (rs1 rs2 rs3 : regidx) (advice : Nat → BitVec 64) :
    (secp256k1SquarerRowsAuto rs1 rs2 rs3 advice).WritesWithin
      (secp256k1SquarerWriteSet rs3) :=
  ⟨by
    unfold secp256k1SquarerRowsAuto secp256k1SquarerRowsAutoList
    simp only [Program.rowsWithin_seq_append,
      (secp256k1Squarer_chunk0 rs1 rs2 rs3 advice).1,
      (secp256k1Squarer_chunk1 rs1 rs2 rs3 advice).1,
      (secp256k1Squarer_chunk2 rs1 rs2 rs3 advice).1,
      Bool.and_self],
   by rw [secp256k1Squarer_storeSlots]; exact List.Subset.refl _, rfl⟩

/-- The final chunks of `Secp256k1Squarer` (rd ≠ x0), which contain the last write of every
pool register. -/
theorem secp256k1Squarer_tailResets
    (rs1 rs2 rs3 : regidx) (advice : Nat → BitVec 64) :
    (Program.seq (secp256k1SquarerRowsAutoChunk1 rs1 rs2 rs3 advice ++
      secp256k1SquarerRowsAutoChunk2 rs1 rs2 rs3 advice)).resetsPoolCheck (poolVRegs 14) = true := rfl

theorem secp256k1Squarer_resetsPoolCheck
    (rs1 rs2 rs3 : regidx) (advice : Nat → BitVec 64) :
    (secp256k1SquarerRowsAuto rs1 rs2 rs3 advice).resetsPoolCheck (poolVRegs 14) = true := by
  unfold secp256k1SquarerRowsAuto secp256k1SquarerRowsAutoList
  exact Program.resetsPoolCheck_seq_append_append _ (secp256k1Squarer_tailResets rs1 rs2 rs3 advice)

theorem secp256k1Squarer_frame
    (rs1 rs2 rs3 : regidx) (advice : Nat → BitVec 64) {s s' : SailJoltState}
    (h : (secp256k1SquarerRowsAuto rs1 rs2 rs3 advice).Run s s') :
    Frame (secp256k1SquarerWriteSet rs3) s s' :=
  frame_of_run (secp256k1Squarer_writesWithin rs1 rs2 rs3 advice) h

/-! ### `Secp256k1Squarer`, rd = x0 -/

/-- Store slots of `Secp256k1Squarer` (rd = x0).
The store rows address memory through `vr40`, which no row writes, so the footprint
is `s.vregs 40 + 8k`: the value `vr40` holds when the inline starts. -/
def secp256k1SquarerRdZeroStores : List StoreSlot :=
  [⟨.vreg 40, 0, .dword⟩, ⟨.vreg 40, 8, .dword⟩, ⟨.vreg 40, 16, .dword⟩,
    ⟨.vreg 40, 24, .dword⟩]

/-- Write set of `Secp256k1Squarer` (rd = x0): pool registers `vr48..vr61`, no
architectural register, 4 store rows. -/
def secp256k1SquarerRdZeroWriteSet : WriteSet where
  vregs := poolVRegs 14
  xregs := []
  stores := secp256k1SquarerRdZeroStores

/-- Chunk 0 of `Secp256k1Squarer` (rd = x0). -/
theorem secp256k1SquarerRdZero_chunk0
    (rs1 rs2 : regidx) (advice : Nat → BitVec 64) :
    (Program.seq (secp256k1SquarerRowsAutoRdZeroChunk0 rs1 rs2 advice)).rowsWithin (secp256k1SquarerRdZeroWriteSet) = true ∧
      (Program.seq (secp256k1SquarerRowsAutoRdZeroChunk0 rs1 rs2 advice)).storeSlots =
        [⟨.vreg 40, 0, .dword⟩, ⟨.vreg 40, 8, .dword⟩, ⟨.vreg 40, 16, .dword⟩] :=
  ⟨rfl, rfl⟩

/-- Chunk 1 of `Secp256k1Squarer` (rd = x0). -/
theorem secp256k1SquarerRdZero_chunk1
    (rs1 rs2 : regidx) (advice : Nat → BitVec 64) :
    (Program.seq (secp256k1SquarerRowsAutoRdZeroChunk1 rs1 rs2 advice)).rowsWithin (secp256k1SquarerRdZeroWriteSet) = true ∧
      (Program.seq (secp256k1SquarerRowsAutoRdZeroChunk1 rs1 rs2 advice)).storeSlots =
        [⟨.vreg 40, 24, .dword⟩] :=
  ⟨rfl, rfl⟩

/-- Chunk 2 of `Secp256k1Squarer` (rd = x0). -/
theorem secp256k1SquarerRdZero_chunk2
    (rs1 rs2 : regidx) (advice : Nat → BitVec 64) :
    (Program.seq (secp256k1SquarerRowsAutoRdZeroChunk2 rs1 rs2 advice)).rowsWithin (secp256k1SquarerRdZeroWriteSet) = true ∧
      (Program.seq (secp256k1SquarerRowsAutoRdZeroChunk2 rs1 rs2 advice)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

theorem secp256k1SquarerRdZero_storeSlots
    (rs1 rs2 : regidx) (advice : Nat → BitVec 64) :
    (secp256k1SquarerRowsAutoRdZero rs1 rs2 advice).storeSlots =
      secp256k1SquarerRdZeroStores := by
  unfold secp256k1SquarerRowsAutoRdZero secp256k1SquarerRowsAutoRdZeroList
  simp only [Program.storeSlots_seq_append,
      (secp256k1SquarerRdZero_chunk0 rs1 rs2 advice).2,
      (secp256k1SquarerRdZero_chunk1 rs1 rs2 advice).2,
      (secp256k1SquarerRdZero_chunk2 rs1 rs2 advice).2]
  rfl

theorem secp256k1SquarerRdZero_writesWithin
    (rs1 rs2 : regidx) (advice : Nat → BitVec 64) :
    (secp256k1SquarerRowsAutoRdZero rs1 rs2 advice).WritesWithin
      (secp256k1SquarerRdZeroWriteSet) :=
  ⟨by
    unfold secp256k1SquarerRowsAutoRdZero secp256k1SquarerRowsAutoRdZeroList
    simp only [Program.rowsWithin_seq_append,
      (secp256k1SquarerRdZero_chunk0 rs1 rs2 advice).1,
      (secp256k1SquarerRdZero_chunk1 rs1 rs2 advice).1,
      (secp256k1SquarerRdZero_chunk2 rs1 rs2 advice).1,
      Bool.and_self],
   by rw [secp256k1SquarerRdZero_storeSlots]; exact List.Subset.refl _, rfl⟩

/-- The final chunks of `Secp256k1Squarer` (rd = x0), which contain the last write of every
pool register. -/
theorem secp256k1SquarerRdZero_tailResets
    (rs1 rs2 : regidx) (advice : Nat → BitVec 64) :
    (Program.seq (secp256k1SquarerRowsAutoRdZeroChunk1 rs1 rs2 advice ++
      secp256k1SquarerRowsAutoRdZeroChunk2 rs1 rs2 advice)).resetsPoolCheck (poolVRegs 14) = true := rfl

theorem secp256k1SquarerRdZero_resetsPoolCheck
    (rs1 rs2 : regidx) (advice : Nat → BitVec 64) :
    (secp256k1SquarerRowsAutoRdZero rs1 rs2 advice).resetsPoolCheck (poolVRegs 14) = true := by
  unfold secp256k1SquarerRowsAutoRdZero secp256k1SquarerRowsAutoRdZeroList
  exact Program.resetsPoolCheck_seq_append_append _ (secp256k1SquarerRdZero_tailResets rs1 rs2 advice)

theorem secp256k1SquarerRdZero_frame
    (rs1 rs2 : regidx) (advice : Nat → BitVec 64) {s s' : SailJoltState}
    (h : (secp256k1SquarerRowsAutoRdZero rs1 rs2 advice).Run s s') :
    Frame (secp256k1SquarerRdZeroWriteSet) s s' :=
  frame_of_run (secp256k1SquarerRdZero_writesWithin rs1 rs2 advice) h

/-! ### `Secp256k1Divq`, rd ≠ x0 -/

/-- Store slots of `Secp256k1Divq` (rd ≠ x0). -/
def secp256k1DivqStores (rs3 : regidx) : List StoreSlot :=
  [⟨.xreg rs3, 0, .dword⟩, ⟨.xreg rs3, 8, .dword⟩, ⟨.xreg rs3, 16, .dword⟩,
    ⟨.xreg rs3, 24, .dword⟩]

/-- Write set of `Secp256k1Divq` (rd ≠ x0): pool registers `vr48..vr63`, no
architectural register, 4 store rows. -/
def secp256k1DivqWriteSet (rs3 : regidx) : WriteSet where
  vregs := poolVRegs 16
  xregs := []
  stores := secp256k1DivqStores rs3

/-- Chunk 0 of `Secp256k1Divq` (rd ≠ x0). -/
theorem secp256k1Divq_chunk0
    (rs1 rs2 rs3 : regidx) (advice : Nat → BitVec 64) :
    (Program.seq (secp256k1DivqRowsAutoChunk0 rs1 rs2 rs3 advice)).rowsWithin (secp256k1DivqWriteSet rs3) = true ∧
      (Program.seq (secp256k1DivqRowsAutoChunk0 rs1 rs2 rs3 advice)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 1 of `Secp256k1Divq` (rd ≠ x0). -/
theorem secp256k1Divq_chunk1
    (rs1 rs2 rs3 : regidx) (advice : Nat → BitVec 64) :
    (Program.seq (secp256k1DivqRowsAutoChunk1 rs1 rs2 rs3 advice)).rowsWithin (secp256k1DivqWriteSet rs3) = true ∧
      (Program.seq (secp256k1DivqRowsAutoChunk1 rs1 rs2 rs3 advice)).storeSlots =
        [⟨.xreg rs3, 0, .dword⟩, ⟨.xreg rs3, 8, .dword⟩, ⟨.xreg rs3, 16, .dword⟩, ⟨.xreg rs3, 24, .dword⟩] :=
  ⟨rfl, rfl⟩

theorem secp256k1Divq_storeSlots
    (rs1 rs2 rs3 : regidx) (advice : Nat → BitVec 64) :
    (secp256k1DivqRowsAuto rs1 rs2 rs3 advice).storeSlots =
      secp256k1DivqStores rs3 := by
  unfold secp256k1DivqRowsAuto secp256k1DivqRowsAutoList
  simp only [Program.storeSlots_seq_append,
      (secp256k1Divq_chunk0 rs1 rs2 rs3 advice).2,
      (secp256k1Divq_chunk1 rs1 rs2 rs3 advice).2]
  rfl

theorem secp256k1Divq_writesWithin
    (rs1 rs2 rs3 : regidx) (advice : Nat → BitVec 64) :
    (secp256k1DivqRowsAuto rs1 rs2 rs3 advice).WritesWithin
      (secp256k1DivqWriteSet rs3) :=
  ⟨by
    unfold secp256k1DivqRowsAuto secp256k1DivqRowsAutoList
    simp only [Program.rowsWithin_seq_append,
      (secp256k1Divq_chunk0 rs1 rs2 rs3 advice).1,
      (secp256k1Divq_chunk1 rs1 rs2 rs3 advice).1,
      Bool.and_self],
   by rw [secp256k1Divq_storeSlots]; exact List.Subset.refl _, rfl⟩

/-- The final chunks of `Secp256k1Divq` (rd ≠ x0), which contain the last write of every
pool register. -/
theorem secp256k1Divq_tailResets
    (rs1 rs2 rs3 : regidx) (advice : Nat → BitVec 64) :
    (Program.seq (secp256k1DivqRowsAutoChunk1 rs1 rs2 rs3 advice)).resetsPoolCheck (poolVRegs 16) = true := rfl

theorem secp256k1Divq_resetsPoolCheck
    (rs1 rs2 rs3 : regidx) (advice : Nat → BitVec 64) :
    (secp256k1DivqRowsAuto rs1 rs2 rs3 advice).resetsPoolCheck (poolVRegs 16) = true := by
  unfold secp256k1DivqRowsAuto secp256k1DivqRowsAutoList
  exact Program.resetsPoolCheck_seq_append _ (secp256k1Divq_tailResets rs1 rs2 rs3 advice)

theorem secp256k1Divq_frame
    (rs1 rs2 rs3 : regidx) (advice : Nat → BitVec 64) {s s' : SailJoltState}
    (h : (secp256k1DivqRowsAuto rs1 rs2 rs3 advice).Run s s') :
    Frame (secp256k1DivqWriteSet rs3) s s' :=
  frame_of_run (secp256k1Divq_writesWithin rs1 rs2 rs3 advice) h

/-! ### `Secp256k1Divq`, rd = x0 -/

/-- Store slots of `Secp256k1Divq` (rd = x0).
The store rows address memory through `vr40`, which no row writes, so the footprint
is `s.vregs 40 + 8k`: the value `vr40` holds when the inline starts. -/
def secp256k1DivqRdZeroStores : List StoreSlot :=
  [⟨.vreg 40, 0, .dword⟩, ⟨.vreg 40, 8, .dword⟩, ⟨.vreg 40, 16, .dword⟩,
    ⟨.vreg 40, 24, .dword⟩]

/-- Write set of `Secp256k1Divq` (rd = x0): pool registers `vr48..vr63`, no
architectural register, 4 store rows. -/
def secp256k1DivqRdZeroWriteSet : WriteSet where
  vregs := poolVRegs 16
  xregs := []
  stores := secp256k1DivqRdZeroStores

/-- Chunk 0 of `Secp256k1Divq` (rd = x0). -/
theorem secp256k1DivqRdZero_chunk0
    (rs1 rs2 : regidx) (advice : Nat → BitVec 64) :
    (Program.seq (secp256k1DivqRowsAutoRdZeroChunk0 rs1 rs2 advice)).rowsWithin (secp256k1DivqRdZeroWriteSet) = true ∧
      (Program.seq (secp256k1DivqRowsAutoRdZeroChunk0 rs1 rs2 advice)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 1 of `Secp256k1Divq` (rd = x0). -/
theorem secp256k1DivqRdZero_chunk1
    (rs1 rs2 : regidx) (advice : Nat → BitVec 64) :
    (Program.seq (secp256k1DivqRowsAutoRdZeroChunk1 rs1 rs2 advice)).rowsWithin (secp256k1DivqRdZeroWriteSet) = true ∧
      (Program.seq (secp256k1DivqRowsAutoRdZeroChunk1 rs1 rs2 advice)).storeSlots =
        [⟨.vreg 40, 0, .dword⟩, ⟨.vreg 40, 8, .dword⟩, ⟨.vreg 40, 16, .dword⟩, ⟨.vreg 40, 24, .dword⟩] :=
  ⟨rfl, rfl⟩

theorem secp256k1DivqRdZero_storeSlots
    (rs1 rs2 : regidx) (advice : Nat → BitVec 64) :
    (secp256k1DivqRowsAutoRdZero rs1 rs2 advice).storeSlots =
      secp256k1DivqRdZeroStores := by
  unfold secp256k1DivqRowsAutoRdZero secp256k1DivqRowsAutoRdZeroList
  simp only [Program.storeSlots_seq_append,
      (secp256k1DivqRdZero_chunk0 rs1 rs2 advice).2,
      (secp256k1DivqRdZero_chunk1 rs1 rs2 advice).2]
  rfl

theorem secp256k1DivqRdZero_writesWithin
    (rs1 rs2 : regidx) (advice : Nat → BitVec 64) :
    (secp256k1DivqRowsAutoRdZero rs1 rs2 advice).WritesWithin
      (secp256k1DivqRdZeroWriteSet) :=
  ⟨by
    unfold secp256k1DivqRowsAutoRdZero secp256k1DivqRowsAutoRdZeroList
    simp only [Program.rowsWithin_seq_append,
      (secp256k1DivqRdZero_chunk0 rs1 rs2 advice).1,
      (secp256k1DivqRdZero_chunk1 rs1 rs2 advice).1,
      Bool.and_self],
   by rw [secp256k1DivqRdZero_storeSlots]; exact List.Subset.refl _, rfl⟩

/-- The final chunks of `Secp256k1Divq` (rd = x0), which contain the last write of every
pool register. -/
theorem secp256k1DivqRdZero_tailResets
    (rs1 rs2 : regidx) (advice : Nat → BitVec 64) :
    (Program.seq (secp256k1DivqRowsAutoRdZeroChunk1 rs1 rs2 advice)).resetsPoolCheck (poolVRegs 16) = true := rfl

theorem secp256k1DivqRdZero_resetsPoolCheck
    (rs1 rs2 : regidx) (advice : Nat → BitVec 64) :
    (secp256k1DivqRowsAutoRdZero rs1 rs2 advice).resetsPoolCheck (poolVRegs 16) = true := by
  unfold secp256k1DivqRowsAutoRdZero secp256k1DivqRowsAutoRdZeroList
  exact Program.resetsPoolCheck_seq_append _ (secp256k1DivqRdZero_tailResets rs1 rs2 advice)

theorem secp256k1DivqRdZero_frame
    (rs1 rs2 : regidx) (advice : Nat → BitVec 64) {s s' : SailJoltState}
    (h : (secp256k1DivqRowsAutoRdZero rs1 rs2 advice).Run s s') :
    Frame (secp256k1DivqRdZeroWriteSet) s s' :=
  frame_of_run (secp256k1DivqRdZero_writesWithin rs1 rs2 advice) h

/-! ### `Secp256k1Divr`, rd ≠ x0 -/

/-- Store slots of `Secp256k1Divr` (rd ≠ x0). -/
def secp256k1DivrStores (rs3 : regidx) : List StoreSlot :=
  [⟨.xreg rs3, 0, .dword⟩, ⟨.xreg rs3, 8, .dword⟩, ⟨.xreg rs3, 16, .dword⟩,
    ⟨.xreg rs3, 24, .dword⟩]

/-- Write set of `Secp256k1Divr` (rd ≠ x0): pool registers `vr48..vr64`, no
architectural register, 4 store rows. -/
def secp256k1DivrWriteSet (rs3 : regidx) : WriteSet where
  vregs := poolVRegs 17
  xregs := []
  stores := secp256k1DivrStores rs3

/-- Chunk 0 of `Secp256k1Divr` (rd ≠ x0). -/
theorem secp256k1Divr_chunk0
    (rs1 rs2 rs3 : regidx) (advice : Nat → BitVec 64) :
    (Program.seq (secp256k1DivrRowsAutoChunk0 rs1 rs2 rs3 advice)).rowsWithin (secp256k1DivrWriteSet rs3) = true ∧
      (Program.seq (secp256k1DivrRowsAutoChunk0 rs1 rs2 rs3 advice)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 1 of `Secp256k1Divr` (rd ≠ x0). -/
theorem secp256k1Divr_chunk1
    (rs1 rs2 rs3 : regidx) (advice : Nat → BitVec 64) :
    (Program.seq (secp256k1DivrRowsAutoChunk1 rs1 rs2 rs3 advice)).rowsWithin (secp256k1DivrWriteSet rs3) = true ∧
      (Program.seq (secp256k1DivrRowsAutoChunk1 rs1 rs2 rs3 advice)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 2 of `Secp256k1Divr` (rd ≠ x0). -/
theorem secp256k1Divr_chunk2
    (rs1 rs2 rs3 : regidx) (advice : Nat → BitVec 64) :
    (Program.seq (secp256k1DivrRowsAutoChunk2 rs1 rs2 rs3 advice)).rowsWithin (secp256k1DivrWriteSet rs3) = true ∧
      (Program.seq (secp256k1DivrRowsAutoChunk2 rs1 rs2 rs3 advice)).storeSlots =
        [⟨.xreg rs3, 0, .dword⟩, ⟨.xreg rs3, 8, .dword⟩, ⟨.xreg rs3, 16, .dword⟩, ⟨.xreg rs3, 24, .dword⟩] :=
  ⟨rfl, rfl⟩

theorem secp256k1Divr_storeSlots
    (rs1 rs2 rs3 : regidx) (advice : Nat → BitVec 64) :
    (secp256k1DivrRowsAuto rs1 rs2 rs3 advice).storeSlots =
      secp256k1DivrStores rs3 := by
  unfold secp256k1DivrRowsAuto secp256k1DivrRowsAutoList
  simp only [Program.storeSlots_seq_append,
      (secp256k1Divr_chunk0 rs1 rs2 rs3 advice).2,
      (secp256k1Divr_chunk1 rs1 rs2 rs3 advice).2,
      (secp256k1Divr_chunk2 rs1 rs2 rs3 advice).2]
  rfl

theorem secp256k1Divr_writesWithin
    (rs1 rs2 rs3 : regidx) (advice : Nat → BitVec 64) :
    (secp256k1DivrRowsAuto rs1 rs2 rs3 advice).WritesWithin
      (secp256k1DivrWriteSet rs3) :=
  ⟨by
    unfold secp256k1DivrRowsAuto secp256k1DivrRowsAutoList
    simp only [Program.rowsWithin_seq_append,
      (secp256k1Divr_chunk0 rs1 rs2 rs3 advice).1,
      (secp256k1Divr_chunk1 rs1 rs2 rs3 advice).1,
      (secp256k1Divr_chunk2 rs1 rs2 rs3 advice).1,
      Bool.and_self],
   by rw [secp256k1Divr_storeSlots]; exact List.Subset.refl _, rfl⟩

/-- The final chunks of `Secp256k1Divr` (rd ≠ x0), which contain the last write of every
pool register. -/
theorem secp256k1Divr_tailResets
    (rs1 rs2 rs3 : regidx) (advice : Nat → BitVec 64) :
    (Program.seq (secp256k1DivrRowsAutoChunk2 rs1 rs2 rs3 advice)).resetsPoolCheck (poolVRegs 17) = true := rfl

theorem secp256k1Divr_resetsPoolCheck
    (rs1 rs2 rs3 : regidx) (advice : Nat → BitVec 64) :
    (secp256k1DivrRowsAuto rs1 rs2 rs3 advice).resetsPoolCheck (poolVRegs 17) = true := by
  unfold secp256k1DivrRowsAuto secp256k1DivrRowsAutoList
  exact Program.resetsPoolCheck_seq_append _ (secp256k1Divr_tailResets rs1 rs2 rs3 advice)

theorem secp256k1Divr_frame
    (rs1 rs2 rs3 : regidx) (advice : Nat → BitVec 64) {s s' : SailJoltState}
    (h : (secp256k1DivrRowsAuto rs1 rs2 rs3 advice).Run s s') :
    Frame (secp256k1DivrWriteSet rs3) s s' :=
  frame_of_run (secp256k1Divr_writesWithin rs1 rs2 rs3 advice) h

/-! ### `Secp256k1Divr`, rd = x0 -/

/-- Store slots of `Secp256k1Divr` (rd = x0).
The store rows address memory through `vr40`, which no row writes, so the footprint
is `s.vregs 40 + 8k`: the value `vr40` holds when the inline starts. -/
def secp256k1DivrRdZeroStores : List StoreSlot :=
  [⟨.vreg 40, 0, .dword⟩, ⟨.vreg 40, 8, .dword⟩, ⟨.vreg 40, 16, .dword⟩,
    ⟨.vreg 40, 24, .dword⟩]

/-- Write set of `Secp256k1Divr` (rd = x0): pool registers `vr48..vr64`, no
architectural register, 4 store rows. -/
def secp256k1DivrRdZeroWriteSet : WriteSet where
  vregs := poolVRegs 17
  xregs := []
  stores := secp256k1DivrRdZeroStores

/-- Chunk 0 of `Secp256k1Divr` (rd = x0). -/
theorem secp256k1DivrRdZero_chunk0
    (rs1 rs2 : regidx) (advice : Nat → BitVec 64) :
    (Program.seq (secp256k1DivrRowsAutoRdZeroChunk0 rs1 rs2 advice)).rowsWithin (secp256k1DivrRdZeroWriteSet) = true ∧
      (Program.seq (secp256k1DivrRowsAutoRdZeroChunk0 rs1 rs2 advice)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 1 of `Secp256k1Divr` (rd = x0). -/
theorem secp256k1DivrRdZero_chunk1
    (rs1 rs2 : regidx) (advice : Nat → BitVec 64) :
    (Program.seq (secp256k1DivrRowsAutoRdZeroChunk1 rs1 rs2 advice)).rowsWithin (secp256k1DivrRdZeroWriteSet) = true ∧
      (Program.seq (secp256k1DivrRowsAutoRdZeroChunk1 rs1 rs2 advice)).storeSlots =
        [] :=
  ⟨rfl, rfl⟩

/-- Chunk 2 of `Secp256k1Divr` (rd = x0). -/
theorem secp256k1DivrRdZero_chunk2
    (rs1 rs2 : regidx) (advice : Nat → BitVec 64) :
    (Program.seq (secp256k1DivrRowsAutoRdZeroChunk2 rs1 rs2 advice)).rowsWithin (secp256k1DivrRdZeroWriteSet) = true ∧
      (Program.seq (secp256k1DivrRowsAutoRdZeroChunk2 rs1 rs2 advice)).storeSlots =
        [⟨.vreg 40, 0, .dword⟩, ⟨.vreg 40, 8, .dword⟩, ⟨.vreg 40, 16, .dword⟩, ⟨.vreg 40, 24, .dword⟩] :=
  ⟨rfl, rfl⟩

theorem secp256k1DivrRdZero_storeSlots
    (rs1 rs2 : regidx) (advice : Nat → BitVec 64) :
    (secp256k1DivrRowsAutoRdZero rs1 rs2 advice).storeSlots =
      secp256k1DivrRdZeroStores := by
  unfold secp256k1DivrRowsAutoRdZero secp256k1DivrRowsAutoRdZeroList
  simp only [Program.storeSlots_seq_append,
      (secp256k1DivrRdZero_chunk0 rs1 rs2 advice).2,
      (secp256k1DivrRdZero_chunk1 rs1 rs2 advice).2,
      (secp256k1DivrRdZero_chunk2 rs1 rs2 advice).2]
  rfl

theorem secp256k1DivrRdZero_writesWithin
    (rs1 rs2 : regidx) (advice : Nat → BitVec 64) :
    (secp256k1DivrRowsAutoRdZero rs1 rs2 advice).WritesWithin
      (secp256k1DivrRdZeroWriteSet) :=
  ⟨by
    unfold secp256k1DivrRowsAutoRdZero secp256k1DivrRowsAutoRdZeroList
    simp only [Program.rowsWithin_seq_append,
      (secp256k1DivrRdZero_chunk0 rs1 rs2 advice).1,
      (secp256k1DivrRdZero_chunk1 rs1 rs2 advice).1,
      (secp256k1DivrRdZero_chunk2 rs1 rs2 advice).1,
      Bool.and_self],
   by rw [secp256k1DivrRdZero_storeSlots]; exact List.Subset.refl _, rfl⟩

/-- The final chunks of `Secp256k1Divr` (rd = x0), which contain the last write of every
pool register. -/
theorem secp256k1DivrRdZero_tailResets
    (rs1 rs2 : regidx) (advice : Nat → BitVec 64) :
    (Program.seq (secp256k1DivrRowsAutoRdZeroChunk2 rs1 rs2 advice)).resetsPoolCheck (poolVRegs 17) = true := rfl

theorem secp256k1DivrRdZero_resetsPoolCheck
    (rs1 rs2 : regidx) (advice : Nat → BitVec 64) :
    (secp256k1DivrRowsAutoRdZero rs1 rs2 advice).resetsPoolCheck (poolVRegs 17) = true := by
  unfold secp256k1DivrRowsAutoRdZero secp256k1DivrRowsAutoRdZeroList
  exact Program.resetsPoolCheck_seq_append _ (secp256k1DivrRdZero_tailResets rs1 rs2 advice)

theorem secp256k1DivrRdZero_frame
    (rs1 rs2 : regidx) (advice : Nat → BitVec 64) {s s' : SailJoltState}
    (h : (secp256k1DivrRowsAutoRdZero rs1 rs2 advice).Run s s') :
    Frame (secp256k1DivrRdZeroWriteSet) s s' :=
  frame_of_run (secp256k1DivrRdZero_writesWithin rs1 rs2 advice) h

/-! ### `Secp256k1GlvrAdv`, rd ≠ x0 -/

/-- Store slots of `Secp256k1GlvrAdv` (rd ≠ x0). -/
def secp256k1GlvrAdvStores (rs3 : regidx) : List StoreSlot :=
  [⟨.xreg rs3, 0, .dword⟩, ⟨.xreg rs3, 8, .dword⟩, ⟨.xreg rs3, 16, .dword⟩,
    ⟨.xreg rs3, 24, .dword⟩, ⟨.xreg rs3, 32, .dword⟩, ⟨.xreg rs3, 40, .dword⟩]

/-- Write set of `Secp256k1GlvrAdv` (rd ≠ x0): pool registers `vr48..vr48`, no
architectural register, 6 store rows. -/
def secp256k1GlvrAdvWriteSet (rs3 : regidx) : WriteSet where
  vregs := poolVRegs 1
  xregs := []
  stores := secp256k1GlvrAdvStores rs3

/-- Chunk 0 of `Secp256k1GlvrAdv` (rd ≠ x0). -/
theorem secp256k1GlvrAdv_chunk0
    (rs1 rs2 rs3 : regidx) (advice : Nat → BitVec 64) :
    (Program.seq (secp256k1GlvrAdvRowsAutoChunk0 rs1 rs2 rs3 advice)).rowsWithin (secp256k1GlvrAdvWriteSet rs3) = true ∧
      (Program.seq (secp256k1GlvrAdvRowsAutoChunk0 rs1 rs2 rs3 advice)).storeSlots =
        [⟨.xreg rs3, 0, .dword⟩, ⟨.xreg rs3, 8, .dword⟩, ⟨.xreg rs3, 16, .dword⟩, ⟨.xreg rs3, 24, .dword⟩, ⟨.xreg rs3, 32, .dword⟩, ⟨.xreg rs3, 40, .dword⟩] :=
  ⟨rfl, rfl⟩

theorem secp256k1GlvrAdv_storeSlots
    (rs1 rs2 rs3 : regidx) (advice : Nat → BitVec 64) :
    (secp256k1GlvrAdvRowsAuto rs1 rs2 rs3 advice).storeSlots =
      secp256k1GlvrAdvStores rs3 := by
  unfold secp256k1GlvrAdvRowsAuto secp256k1GlvrAdvRowsAutoList
  rw [(secp256k1GlvrAdv_chunk0 rs1 rs2 rs3 advice).2]
  rfl

theorem secp256k1GlvrAdv_writesWithin
    (rs1 rs2 rs3 : regidx) (advice : Nat → BitVec 64) :
    (secp256k1GlvrAdvRowsAuto rs1 rs2 rs3 advice).WritesWithin
      (secp256k1GlvrAdvWriteSet rs3) :=
  ⟨(secp256k1GlvrAdv_chunk0 rs1 rs2 rs3 advice).1,
   by rw [secp256k1GlvrAdv_storeSlots]; exact List.Subset.refl _, rfl⟩

/-- The final chunks of `Secp256k1GlvrAdv` (rd ≠ x0), which contain the last write of every
pool register. -/
theorem secp256k1GlvrAdv_tailResets
    (rs1 rs2 rs3 : regidx) (advice : Nat → BitVec 64) :
    (Program.seq (secp256k1GlvrAdvRowsAutoChunk0 rs1 rs2 rs3 advice)).resetsPoolCheck (poolVRegs 1) = true := rfl

theorem secp256k1GlvrAdv_resetsPoolCheck
    (rs1 rs2 rs3 : regidx) (advice : Nat → BitVec 64) :
    (secp256k1GlvrAdvRowsAuto rs1 rs2 rs3 advice).resetsPoolCheck (poolVRegs 1) = true := secp256k1GlvrAdv_tailResets rs1 rs2 rs3 advice

theorem secp256k1GlvrAdv_frame
    (rs1 rs2 rs3 : regidx) (advice : Nat → BitVec 64) {s s' : SailJoltState}
    (h : (secp256k1GlvrAdvRowsAuto rs1 rs2 rs3 advice).Run s s') :
    Frame (secp256k1GlvrAdvWriteSet rs3) s s' :=
  frame_of_run (secp256k1GlvrAdv_writesWithin rs1 rs2 rs3 advice) h

/-! ### `Secp256k1GlvrAdv`, rd = x0 -/

/-- Store slots of `Secp256k1GlvrAdv` (rd = x0).
The store rows address memory through `vr40`, which no row writes, so the footprint
is `s.vregs 40 + 8k`: the value `vr40` holds when the inline starts. -/
def secp256k1GlvrAdvRdZeroStores : List StoreSlot :=
  [⟨.vreg 40, 0, .dword⟩, ⟨.vreg 40, 8, .dword⟩, ⟨.vreg 40, 16, .dword⟩,
    ⟨.vreg 40, 24, .dword⟩, ⟨.vreg 40, 32, .dword⟩, ⟨.vreg 40, 40, .dword⟩]

/-- Write set of `Secp256k1GlvrAdv` (rd = x0): pool registers `vr48..vr48`, no
architectural register, 6 store rows. -/
def secp256k1GlvrAdvRdZeroWriteSet : WriteSet where
  vregs := poolVRegs 1
  xregs := []
  stores := secp256k1GlvrAdvRdZeroStores

/-- Chunk 0 of `Secp256k1GlvrAdv` (rd = x0). -/
theorem secp256k1GlvrAdvRdZero_chunk0
    (rs1 rs2 : regidx) (advice : Nat → BitVec 64) :
    (Program.seq (secp256k1GlvrAdvRowsAutoRdZeroChunk0 rs1 rs2 advice)).rowsWithin (secp256k1GlvrAdvRdZeroWriteSet) = true ∧
      (Program.seq (secp256k1GlvrAdvRowsAutoRdZeroChunk0 rs1 rs2 advice)).storeSlots =
        [⟨.vreg 40, 0, .dword⟩, ⟨.vreg 40, 8, .dword⟩, ⟨.vreg 40, 16, .dword⟩, ⟨.vreg 40, 24, .dword⟩, ⟨.vreg 40, 32, .dword⟩, ⟨.vreg 40, 40, .dword⟩] :=
  ⟨rfl, rfl⟩

theorem secp256k1GlvrAdvRdZero_storeSlots
    (rs1 rs2 : regidx) (advice : Nat → BitVec 64) :
    (secp256k1GlvrAdvRowsAutoRdZero rs1 rs2 advice).storeSlots =
      secp256k1GlvrAdvRdZeroStores := by
  unfold secp256k1GlvrAdvRowsAutoRdZero secp256k1GlvrAdvRowsAutoRdZeroList
  rw [(secp256k1GlvrAdvRdZero_chunk0 rs1 rs2 advice).2]
  rfl

theorem secp256k1GlvrAdvRdZero_writesWithin
    (rs1 rs2 : regidx) (advice : Nat → BitVec 64) :
    (secp256k1GlvrAdvRowsAutoRdZero rs1 rs2 advice).WritesWithin
      (secp256k1GlvrAdvRdZeroWriteSet) :=
  ⟨(secp256k1GlvrAdvRdZero_chunk0 rs1 rs2 advice).1,
   by rw [secp256k1GlvrAdvRdZero_storeSlots]; exact List.Subset.refl _, rfl⟩

/-- The final chunks of `Secp256k1GlvrAdv` (rd = x0), which contain the last write of every
pool register. -/
theorem secp256k1GlvrAdvRdZero_tailResets
    (rs1 rs2 : regidx) (advice : Nat → BitVec 64) :
    (Program.seq (secp256k1GlvrAdvRowsAutoRdZeroChunk0 rs1 rs2 advice)).resetsPoolCheck (poolVRegs 1) = true := rfl

theorem secp256k1GlvrAdvRdZero_resetsPoolCheck
    (rs1 rs2 : regidx) (advice : Nat → BitVec 64) :
    (secp256k1GlvrAdvRowsAutoRdZero rs1 rs2 advice).resetsPoolCheck (poolVRegs 1) = true := secp256k1GlvrAdvRdZero_tailResets rs1 rs2 advice

theorem secp256k1GlvrAdvRdZero_frame
    (rs1 rs2 : regidx) (advice : Nat → BitVec 64) {s s' : SailJoltState}
    (h : (secp256k1GlvrAdvRowsAutoRdZero rs1 rs2 advice).Run s s') :
    Frame (secp256k1GlvrAdvRdZeroWriteSet) s s' :=
  frame_of_run (secp256k1GlvrAdvRdZero_writesWithin rs1 rs2 advice) h

end JoltISA.Inlines.FrameInstances
