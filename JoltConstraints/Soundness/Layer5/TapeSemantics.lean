import JoltBytecode.JoltISA.Semantics
import Mathlib.Tactic

/-! Provisional untrusted-answer semantics for tape reads and length queries.
Each answer is a full 64-bit word. Width checks and cursor increments remain,
but tape contents, remaining length and exhaustion do not constrain the answer.
The existing fixed-tape interpreter remains the specification for completeness.
Internal VirtualAdvice is unchanged and still needs its separate honesty proof. -/

set_option autoImplicit false

namespace JoltConstraints.Soundness

open Sail PreSail LeanRV64D.Functions JoltISA

/-- Execute one instruction with an independent tape answer. Non-tape
instructions ignore the answer and use the existing interpreter. -/
noncomputable def execWithTapeAnswer (instruction : Instr) (answer : BitVec 64) :
    JoltMonad ExecutionResult :=
  match instruction with
  | .VirtualAdviceLoad destination byteCount => fun state =>
      if byteCount.toNat = 1 ∨ byteCount.toNat = 2 ∨
          byteCount.toNat = 4 ∨ byteCount.toNat = 8 then
        (do
          writeDst destination answer
          pure RETIRE_SUCCESS)
          { state with adviceTape :=
            { state.adviceTape with readPosition := state.adviceTape.readPosition + byteCount.toNat } }
      else
        .error (Error.Assertion "VirtualAdviceLoad: invalid width") state
  | .VirtualAdviceLen destination _ _ => do
      writeDst destination answer
      pure RETIRE_SUCCESS
  | instruction => execInstr instruction

/-- The answer supplied by the existing fixed-tape interpreter, or zero for an
instruction with no tape answer or a read that fails. -/
def fixedTapeAnswer (instruction : Instr) (state : SailJoltState) : BitVec 64 :=
  match instruction with
  | .VirtualAdviceLoad _ byteCount =>
      ((readAdviceTape state.adviceTape byteCount).map Prod.fst).getD 0
  | .VirtualAdviceLen .. =>
      BitVec.ofNat 64 (state.adviceTape.bytes.size - state.adviceTape.readPosition)
  | _ => 0

private theorem readAdviceTape_shape (tape : JoltAdviceTape) (byteCount value : BitVec 64)
    (nextTape : JoltAdviceTape) (read : readAdviceTape tape byteCount = some (value, nextTape)) :
    (byteCount.toNat = 1 ∨ byteCount.toNat = 2 ∨
      byteCount.toNat = 4 ∨ byteCount.toNat = 8) ∧
    nextTape = { tape with readPosition := tape.readPosition + byteCount.toNat } := by
  unfold readAdviceTape at read
  dsimp only at read
  split at read
  · rename_i width
    split at read
    · exact ⟨width, (Prod.mk.inj (Option.some.inj read)).2.symm⟩
    · contradiction
  · contradiction

/-- A successful fixed-tape instruction has the identical result and post-state
under the relaxed interpreter when supplied with its actual tape answer. -/
theorem execWithTapeAnswer_of_fixed (instruction : Instr) (pre post : SailJoltState)
    (runs : execInstr instruction pre = .ok (.Retire_Success ()) post) :
    execWithTapeAnswer instruction (fixedTapeAnswer instruction pre) pre =
      .ok (.Retire_Success ()) post := by
  cases instruction <;> try exact runs
  case VirtualAdviceLoad destination byteCount =>
    cases read : readAdviceTape pre.adviceTape byteCount with
    | none => simp only [execInstr, read] at runs; contradiction
    | some pair =>
      rcases pair with ⟨value, nextTape⟩
      obtain ⟨width, tapeEq⟩ := readAdviceTape_shape pre.adviceTape byteCount value nextTape read
      simp only [execWithTapeAnswer, width, ↓reduceIte, fixedTapeAnswer, read,
        Option.map_some, Option.getD_some]
      simpa only [execInstr, read, tapeEq] using runs

end JoltConstraints.Soundness
