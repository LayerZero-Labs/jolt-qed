import JoltConstraints.Constraints.NextUnexpandedPCEqPCPlusImmIfShouldBranch
import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.honest_witness
import JoltConstraints.execution_conditions
import JoltConstraints.Completeness.NextUnexpandedPCUpdateOtherwise
import JoltConstraints.Constraints.TracePCProofHelpers

set_option autoImplicit false

open Sail PreSail LeanRV64D.Functions

namespace JoltConstraints

-- A taken branch is a branch instruction.
theorem branchTaken_is_branch (instr : JoltISA.Instr) (state : SailJoltState)
    (taken : JoltNextPCFrame.BranchTaken instr state = true) :
    ∃ lhs rhs imm, instr = .BEQ lhs rhs imm ∨ instr = .BNE lhs rhs imm ∨
      instr = .BLT lhs rhs imm ∨ instr = .BGE lhs rhs imm ∨
      instr = .BLTU lhs rhs imm ∨ instr = .BGEU lhs rhs imm := by
  cases instr
  all_goals first
    | exact ⟨_, _, _, Or.inl rfl⟩
    | exact ⟨_, _, _, Or.inr (Or.inl rfl)⟩
    | exact ⟨_, _, _, Or.inr (Or.inr (Or.inl rfl))⟩
    | exact ⟨_, _, _, Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩
    | exact ⟨_, _, _, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))⟩
    | exact ⟨_, _, _, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))⟩
    | simp [JoltNextPCFrame.BranchTaken] at taken

-- A branch row carries no runtime advice, so it runs as it is in the bytecode.
theorem withRuntimeAdvice_branch {instruction : JoltISA.Instr}
    (advice : instruction.RuntimeAdvice) {lhs rhs : JoltISA.Src} {imm : BitVec 128}
    (isBranch : instruction = .BEQ lhs rhs imm ∨ instruction = .BNE lhs rhs imm ∨
      instruction = .BLT lhs rhs imm ∨ instruction = .BGE lhs rhs imm ∨
      instruction = .BLTU lhs rhs imm ∨ instruction = .BGEU lhs rhs imm) :
    instruction.withRuntimeAdvice advice = instruction := by
  rcases isBranch with isBranch | isBranch | isBranch | isBranch | isBranch | isBranch
  all_goals
    subst isBranch
    rfl

-- A taken branch that retires writes its target, its PC plus its offset, into nextPC.
theorem execInstr_branch_target (instr : JoltISA.Instr) (lhs rhs : JoltISA.Src)
    (imm : BitVec 128)
    (isBranch : instr = .BEQ lhs rhs imm ∨ instr = .BNE lhs rhs imm ∨
      instr = .BLT lhs rhs imm ∨ instr = .BGE lhs rhs imm ∨
      instr = .BLTU lhs rhs imm ∨ instr = .BGEU lhs rhs imm)
    (state after : SailJoltState) (address : BitVec 64)
    (taken : JoltNextPCFrame.BranchTaken instr state = true)
    (pcIs : state.sail.regs.get? Register.PC = some address)
    (runs : JoltISA.execInstr instr state = .ok (.Retire_Success ()) after) :
    after.sail.regs.get? Register.nextPC = some (address + imm.setWidth 64) := by
  have readPC : liftSail (Sail.readReg Register.PC) state = .ok address state := by
    unfold liftSail
    rw [readReg_eq_of_get? Register.PC state.sail address pcIs]
  rcases isBranch with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    unfold JoltNextPCFrame.BranchTaken at taken
    dsimp only at taken
    simp only [JoltISA.execInstr] at runs
    cases leftRead : JoltISA.readSrc lhs state with
    | error failure middle =>
      simp only [bind, EStateM.bind, leftRead] at runs
      cases runs
    | ok leftValue middle =>
      obtain ⟨leftSame, leftIs⟩ := readSrc_value lhs state middle leftValue leftRead
      simp only [bind, EStateM.bind, leftRead] at runs
      rw [leftSame] at runs
      cases rightRead : JoltISA.readSrc rhs state with
      | error failure middle =>
        rw [rightRead] at runs
        cases runs
      | ok rightValue middle =>
        obtain ⟨rightSame, rightIs⟩ := readSrc_value rhs state middle rightValue rightRead
        rw [rightRead] at runs
        dsimp only at runs
        rw [rightSame] at runs
        rw [← leftIs, ← rightIs] at taken
        rw [if_pos taken] at runs
        -- the branch reads PC and jumps to PC plus its offset
        rw [EStateM.bind, readPC] at runs
        dsimp only at runs
        unfold liftSail at runs
        cases jumped : jump_to (address + imm.setWidth 64) state.sail with
        | error failure sail =>
          rw [jumped] at runs
          cases runs
        | ok result sail =>
          rw [jumped] at runs
          cases runs
          rw [jump_to_retires _ _ _ jumped]
          simp only [Std.ExtDHashMap.get?_insert, beq_iff_eq, ↓reduceDIte, cast_eq]

-- A branch moves the PC by its signed offset without wrapping: the offset is under
-- 4 KiB and both ends are at least RAM_START (2 GiB).
theorem branch_target_toNat (address : BitVec 64) (offset : BitVec 13)
    (fromRam : JoltISA.RAM_START_ADDRESS ≤ address.toNat)
    (toRam : JoltISA.RAM_START_ADDRESS ≤
      (address + (offset.signExtend 128).setWidth 64).toNat) :
    ((address + (offset.signExtend 128).setWidth 64).toNat : Int) =
      address.toNat + (offset.signExtend 128).toInt := by
  have extended : (offset.signExtend 128).setWidth 64 = offset.signExtend 64 := by bv_decide
  have sameInt : (offset.signExtend 128).toInt = offset.toInt :=
    BitVec.toInt_signExtend_of_le (by decide)
  have sameInt64 : (offset.signExtend 64).toInt = offset.toInt :=
    BitVec.toInt_signExtend_of_le (by decide)
  rw [extended] at toRam ⊢
  rw [sameInt]
  -- the offset is between -2^12 and 2^12
  have low := BitVec.le_toInt offset
  have high := BitVec.toInt_lt (x := offset)
  have offsetBits := BitVec.toInt_eq_toNat_cond (offset.signExtend 64)
  rw [sameInt64] at offsetBits
  have offsetFits := (offset.signExtend 64).isLt
  have addressFits := address.isLt
  have ramStart : JoltISA.RAM_START_ADDRESS = 2147483648 := rfl
  rw [BitVec.toNat_add] at toRam ⊢
  norm_num at low high offsetBits offsetFits addressFits
  split at offsetBits <;> omega

/-- Completeness for the taken-branch next-PC constraint. A taken branch is never the
last row, since Rust's prover requires the last row to be a jump (a16z/jolt#1968), so
the next row starts at the branch target. -/
theorem honestWitness_nextUnexpandedPCEqPCPlusImmIfShouldBranch
    {F : Type} [Field F] (params : WitnessParams)
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (ramFits : params.RamFits trace)
    (tracePadded : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor trace.bytecode.size)
    (lastIsJump : (trace.rows.back?.all fun last =>
      trace.bytecode[last.rowIndex].instruction.is_jump) = true) :
    nextUnexpandedPCEqPCPlusImmIfShouldBranch
      (HonestTrace.honestWitness (F := F) params trace) := by
  intro t
  change HonestWitness.ShouldBranch (F := F) params trace t *
      (HonestWitness.NextUnexpandedPC (F := F) params trace t -
        HonestWitness.UnexpandedPC (F := F) params trace t -
        HonestWitness.Imm (F := F) params trace t) = 0
  by_cases ht : t.val < trace.rows.size
  · rw [shouldBranch_eq_branchTaken params trace t ht]
    split
    · rename_i taken
      rw [one_mul]
      obtain ⟨lhs, rhs, imm, isBranch⟩ := branchTaken_is_branch _ _ taken
      obtain ⟨atEnd, offset, isOffset⟩ :=
        (trace.rowValid (trace.rows[t.val]'ht).rowIndex).branch isBranch
      -- a taken branch is not the last row: Rust's prover requires a jump there
      have hnext : t.val + 1 < trace.rows.size := by
        by_contra notNext
        have last : trace.rows.back? = some (trace.rows[t.val]'ht) := by
          rw [Array.back?_eq_getElem?, show trace.rows.size - 1 = t.val by omega,
            Array.getElem?_eq_getElem ht]
        rw [last, Option.all_some] at lastIsJump
        rcases isBranch with isBranch | isBranch | isBranch | isBranch | isBranch | isBranch
        all_goals
          rw [isBranch] at lastIsJump
          cases lastIsJump
      -- the branch ends its instruction, so the next row starts at the branch target
      have hsucc := trace.successor t.val ht hnext
      simp only [atEnd, Bool.false_eq_true, ↓reduceIte] at hsucc
      obtain ⟨nextAt, _, _⟩ := hsucc
      have runs := (trace.rows[t.val]'ht).executes
      rw [withRuntimeAdvice_branch _ isBranch] at runs
      have target := execInstr_branch_target _ lhs rhs imm isBranch _ _ _ taken
        (lookup_trace_PC trace t.val ht) runs
      rw [nextAt] at target
      have nextIs := Option.some.inj target
      -- both ends are bytecode addresses, at least RAM_START
      have accepted := accepted_pc_map_ok joltInstance trace.bytecode trace.expands trace.accepted
      have fromRam := pc_map_ok_addresses trace.bytecode accepted _
        (trace.rows[t.val]'ht).rowIndex.isLt
      have toRam := pc_map_ok_addresses trace.bytecode accepted _
        (trace.rows[t.val + 1]'hnext).rowIndex.isLt
      unfold bytecode_address_ok at fromRam toRam
      simp only [Bool.and_eq_true, decide_eq_true_eq] at fromRam toRam
      -- a branch's immediate is its offset
      have immIs : JoltMetadata.immediate trace.bytecode[(trace.rows[t.val]'ht).rowIndex].instruction =
          imm.toInt := by
        rcases isBranch with isBranch | isBranch | isBranch | isBranch | isBranch | isBranch
        all_goals
          rw [isBranch]
          rfl
      -- the witness reads the next row's address, this row's address and the offset
      have hnextWitness : t.val + 1 < params.traceLength := hnext.trans tracePadded.2
      simp only [HonestWitness.NextUnexpandedPC, dif_pos hnextWitness, HonestWitness.UnexpandedPC,
        dif_pos hnext, dif_pos ht, HonestWitness.Imm]
      simp only [Fin.getElem_fin] at nextIs immIs
      rw [immIs, nextIs]
      rw [nextIs] at toRam
      -- the target does not wrap, so it is the address plus the signed offset
      subst isOffset
      have intEq := branch_target_toNat _ offset fromRam.1 toRam.1
      have castEq := congrArg (fun value : Int => (value : F)) intEq
      push_cast at castEq
      rw [castEq]
      ring
    · rw [zero_mul]
  · simp [HonestWitness.ShouldBranch, ht]

end JoltConstraints
