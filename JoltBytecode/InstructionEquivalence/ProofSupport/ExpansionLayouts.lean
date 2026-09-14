import JoltBytecode.JoltISA.Expansions.ALU
import JoltBytecode.JoltISA.Expansions.Load
import JoltBytecode.JoltISA.Expansions.Store
import JoltBytecode.JoltISA.Expansions.Atomics
import JoltBytecode.InstructionEquivalence.ProofSupport.RegisterAccess
import JoltBytecode.InstructionEquivalence.ProofSupport.VirtualRegisters

/-!
# Proof-side allocator-layout characterisations for Jolt ISA expansion programs

For each expansion program in `JoltBytecode/JoltISA/Expansions/*.lean`, this file
states the Rust-allocator layout it relies on: which `inlineTmpN` virtual
register `allocateInstructionRegister` returns for each successive call from
the empty live set.

The expansion programs themselves stay in `JoltBytecode/JoltISA/Expansions/`;
these `decide`-proven layout theorems are proof support for instruction
equivalence and live with the rest of the proof-side machinery.
-/

namespace JoltISA

/-! ## ALU expansion layouts -/

/-- One top-level Rust `allocate()` call from an empty instruction-local live
set produces the single-scratch ALU shift guard. -/
theorem aluSingleScratch_allocate_layout :
    allocateInstructionRegister [] = some (aluPow2VReg, [0]) ∧
    allocateInstructionRegister [] = some (aluBitmaskVReg, [0]) ∧
    allocateInstructionRegister [] = some (shiftImmediateWordRs1VReg, [0]) := by
  decide

/-- Two top-level Rust `allocate()` calls from an empty instruction-local live
set produce `SRLW`'s `v_bitmask`, `v_rs1` guards. -/
theorem srlw_allocate_layout :
    allocateInstructionRegister [] = some (srlwBitmaskVReg, [0]) ∧
    allocateInstructionRegister [0] = some (srlwRs1VReg, [1, 0]) := by
  decide

/-- Two top-level Rust `allocate()` calls from an empty instruction-local live
set produce `SRAW`'s `v_rs1`, `v_bitmask` guards. -/
theorem sraw_allocate_layout :
    allocateInstructionRegister [] = some (srawRs1VReg, [0]) ∧
    allocateInstructionRegister [0] = some (srawBitmaskVReg, [1, 0]) := by
  decide

/-! ## Load expansion layout -/

/-- Rust load allocation layout on RV64: top-level `v0`, `v1`, then the
recursive shift helper's scratch while both guards are live. -/
theorem load_allocate_layout :
    allocateInstructionRegister [] = some (loadV0, [0]) ∧
    allocateInstructionRegister [0] = some (loadV1, [1, 0]) ∧
    allocateInstructionRegister [1, 0] = some (loadInlineTmp, [2, 1, 0]) := by
  decide

/-! Load expansion selector facts.

When Rust first rewrites a side-effecting `rd = x0` destination to a virtual
register, the ordinary load temporaries shift up by one allocator slot.  These
small facts keep the instruction proofs phrased in terms of the selector
functions rather than open-coding that branch. -/

@[simp] theorem loadV0For_writable (rd : regidx) :
    WritableVReg (loadV0For rd) := by
  unfold WritableVReg loadV0For loadV0
  split <;> decide

@[simp] theorem loadV1For_writable (rd : regidx) :
    WritableVReg (loadV1For rd) := by
  unfold WritableVReg loadV1For loadV1
  split <;> decide

@[simp] theorem loadInlineTmpFor_writable (rd : regidx) :
    WritableVReg (loadInlineTmpFor rd) := by
  unfold WritableVReg loadInlineTmpFor loadInlineTmp
  split <;> decide

@[simp] theorem loadV0For_not_protected (rd : regidx) :
    ¬ IsProtectedJoltRegister (loadV0For rd) := by
  unfold loadV0For loadV0
  split <;> simp

@[simp] theorem loadV1For_not_protected (rd : regidx) :
    ¬ IsProtectedJoltRegister (loadV1For rd) := by
  unfold loadV1For loadV1
  split <;> simp

@[simp] theorem loadInlineTmpFor_not_protected (rd : regidx) :
    ¬ IsProtectedJoltRegister (loadInlineTmpFor rd) := by
  unfold loadInlineTmpFor loadInlineTmp
  split <;> simp

@[simp] theorem loadV0For_ne_loadV1For (rd : regidx) :
    loadV0For rd ≠ loadV1For rd := by
  unfold loadV0For loadV1For loadV0 loadV1
  split <;> simp

@[simp] theorem loadV1For_ne_loadV0For (rd : regidx) :
    loadV1For rd ≠ loadV0For rd := by
  exact (loadV0For_ne_loadV1For rd).symm

@[simp] theorem loadV0For_ne_loadInlineTmpFor (rd : regidx) :
    loadV0For rd ≠ loadInlineTmpFor rd := by
  unfold loadV0For loadInlineTmpFor loadV0 loadInlineTmp
  split <;> simp

@[simp] theorem loadInlineTmpFor_ne_loadV0For (rd : regidx) :
    loadInlineTmpFor rd ≠ loadV0For rd := by
  exact (loadV0For_ne_loadInlineTmpFor rd).symm

@[simp] theorem loadV1For_ne_loadInlineTmpFor (rd : regidx) :
    loadV1For rd ≠ loadInlineTmpFor rd := by
  unfold loadV1For loadInlineTmpFor loadV1 loadInlineTmp
  split <;> simp

@[simp] theorem loadInlineTmpFor_ne_loadV1For (rd : regidx) :
    loadInlineTmpFor rd ≠ loadV1For rd := by
  exact (loadV1For_ne_loadInlineTmpFor rd).symm

/-! ## Store expansion layout -/

/-- Rust store allocation layout on RV64: the four fused-store temporaries. -/
theorem store_allocate_layout :
    allocateInstructionRegister [] = some (storeV0, [0]) ∧
    allocateInstructionRegister [0] = some (storeV1, [1, 0]) ∧
    allocateInstructionRegister [1, 0] = some (storeV2, [2, 1, 0]) ∧
    allocateInstructionRegister [2, 1, 0] = some (storeV3, [3, 2, 1, 0]) := by
  decide

/-! ## Atomic expansion layouts -/

/-- Rust allocation layout for `AMOSWAP.D`: one old-value guard. -/
theorem amoSwapDouble_allocate_layout :
    allocateInstructionRegister [] = some (amoOldVReg, [0]) := by
  decide

/-- Rust allocation layout for dword binop atomics: `v_rs2`, then `v_rd`. -/
theorem amoDoubleBinop_allocate_layout :
    allocateInstructionRegister [] = some (amoDoubleBinopNewVReg, [0]) ∧
    allocateInstructionRegister [0] = some (amoDoubleBinopOldVReg, [1, 0]) := by
  decide

/-- Rust allocation layout for dword min/max atomics: `v0`, `v1`, `v2`. -/
theorem amoDoubleSelect_allocate_layout :
    allocateInstructionRegister [] = some (amoOldVReg, [0]) ∧
    allocateInstructionRegister [0] = some (amoNewVReg, [1, 0]) ∧
    allocateInstructionRegister [1, 0] = some (amoTmpVReg, [2, 1, 0]) := by
  decide

/-- Rust allocation layout for word binop atomics on RV64, including the
recursive shift helper scratch while the five outer guards are live. -/
theorem amoWordBinop_allocate_layout :
    allocateInstructionRegister [] = some (amoOldVReg, [0]) ∧
    allocateInstructionRegister [0] = some (amoNewVReg, [1, 0]) ∧
    allocateInstructionRegister [1, 0] = some (amoMaskVReg, [2, 1, 0]) ∧
    allocateInstructionRegister [2, 1, 0] = some (amoDwordVReg, [3, 2, 1, 0]) ∧
    allocateInstructionRegister [3, 2, 1, 0] =
      some (amoShiftVReg, [4, 3, 2, 1, 0]) ∧
    allocateInstructionRegister [4, 3, 2, 1, 0] =
      some (amoInlineTmpVReg, [5, 4, 3, 2, 1, 0]) := by
  decide

/-- Rust allocation layout for `AMOSWAP.W` on RV64, including recursive shift
helper scratch while the four outer guards are live. -/
theorem amoWordSwap_allocate_layout :
    allocateInstructionRegister [] = some (amoWordSwapMaskVReg, [0]) ∧
    allocateInstructionRegister [0] = some (amoWordSwapDwordVReg, [1, 0]) ∧
    allocateInstructionRegister [1, 0] = some (amoWordSwapShiftVReg, [2, 1, 0]) ∧
    allocateInstructionRegister [2, 1, 0] =
      some (amoWordSwapOldVReg, [3, 2, 1, 0]) ∧
    allocateInstructionRegister [3, 2, 1, 0] =
      some (amoWordSwapInlineTmpVReg, [4, 3, 2, 1, 0]) := by
  decide

/-- Rust allocation layout for word min/max atomics on RV64.  The prelude's
recursive `SRL` scratch is freed before Rust allocates `v_rs2`; the postlude's
recursive shifts then use the next free register while `v_rd,v_dword,v_shift,
v_rs2,v0` are live. -/
theorem amoWordSelect_allocate_layout :
    allocateInstructionRegister [] = some (amoWordSelectOldVReg, [0]) ∧
    allocateInstructionRegister [0] = some (amoWordSelectDwordVReg, [1, 0]) ∧
    allocateInstructionRegister [1, 0] = some (amoWordSelectShiftVReg, [2, 1, 0]) ∧
    allocateInstructionRegister [2, 1, 0] =
      some (amoWordSelectNewVReg, [3, 2, 1, 0]) ∧
    allocateInstructionRegister [3, 2, 1, 0] =
      some (amoWordSelectMaskVReg, [4, 3, 2, 1, 0]) ∧
    allocateInstructionRegister [4, 3, 2, 1, 0] =
      some (amoWordSelectInlineTmpVReg, [5, 4, 3, 2, 1, 0]) := by
  decide

end JoltISA
