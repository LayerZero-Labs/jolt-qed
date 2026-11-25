import JoltBytecode.JoltISA.Semantics
import JoltConstraints.theorems.DeviceFrame
import JoltBytecode.MathlibTactics

open LeanRV64D

/-! Untrusted-answer semantics for tape reads.
Each answer is a full 64-bit word. Width checks and cursor increments remain,
but tape contents and exhaustion do not constrain the answer.
The existing fixed-tape interpreter remains the specification for completeness.
PR #2049 removes the length-query instruction and documents this separation:
https://github.com/a16z/jolt/pull/2049
Internal VirtualAdvice is unchanged and still needs its separate honesty proof. -/

set_option autoImplicit false

namespace JoltConstraints.Soundness

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail LeanRV64D LeanRV64D.Functions JoltISA

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
  | instruction => execInstr instruction

/-- `execWithTapeAnswer` by its defining match. Lean 4.35 generates the default
equation lemmas for this overlapping match over `Instr` very slowly (minutes per
use); this single lemma replaces them, and `simp` reduces the match on a
concrete instruction directly. -/
theorem execWithTapeAnswer_def (instruction : Instr) (answer : BitVec 64) :
    execWithTapeAnswer instruction answer =
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
      | instruction => execInstr instruction := rfl

attribute [eqns execWithTapeAnswer_def] execWithTapeAnswer

/-- Off tape reads the relaxed interpreter is the existing interpreter. Proved
per constructor, which avoids the slow default equation lemmas. -/
theorem execWithTapeAnswer_of_ne (instruction : Instr) (answer : BitVec 64)
    (notAdvice : ∀ destination byteCount,
      instruction ≠ .VirtualAdviceLoad destination byteCount) :
    execWithTapeAnswer instruction answer = execInstr instruction := by
  cases instruction <;> first | rfl | exact absurd rfl (notAdvice _ _)

/-- The relaxed interpreter preserves a state relation whenever its primitive
instruction rules and tape-cursor advance preserve that relation.
For example, code-region equality permits every primitive and tape advance. -/
theorem execWithTapeAnswer_relation
    (relation : SailJoltState → SailJoltState → Prop)
    (rules : InstructionFrame.Rules relation)
    (advance : ∀ state width, relation state
      { state with adviceTape := { state.adviceTape with
        readPosition := state.adviceTape.readPosition + width } })
    (instruction : Instr) (answer : BitVec 64) :
    StatePreservation.Preserves relation (execWithTapeAnswer instruction answer) := by
  by_cases advice : ∃ dst width, instruction = .VirtualAdviceLoad dst width
  · obtain ⟨destination, byteCount, rfl⟩ := advice
    intro before after value runs
    simp only [execWithTapeAnswer] at runs
    split at runs
    · have keeps := StatePreservation.bind_rule rules.trans
        (InstructionFrame.writeDst_rule relation rules.sail rules.vreg destination answer)
        (fun _ => StatePreservation.pure_rule rules.refl RETIRE_SUCCESS)
      exact rules.trans _ _ _ (advance before byteCount.toNat)
        (keeps _ after value runs)
    · cases runs
  · rw [execWithTapeAnswer_of_ne instruction answer
      (fun dst width same => advice ⟨dst, width, same⟩)]
    apply InstructionFrame.execInstr_rule rules instruction
    intro dst width same
    exact False.elim (advice ⟨dst, width, same⟩)

/-- Every relaxed instruction preserves a device relation compatible with halt updates.
For example, every tape read and both halts preserve the memory layout.
Stores change shared memory and no longer need device-store premises. -/
theorem execWithTapeAnswer_device_relation
    (relation : JoltDevice → JoltDevice → Prop)
    (refl : ∀ io, relation io io)
    (trans : ∀ a b c, relation a b → relation b c → relation a c)
    (halt : ∀ device kind,
      relation device { device with panic := (kind == JoltHaltKind.panic) })
    (instruction : Instr) (answer : BitVec 64) :
    StatePreservation.Preserves
      (fun s t : SailJoltState => relation s.jolt_device t.jolt_device)
      (execWithTapeAnswer instruction answer) :=
  execWithTapeAnswer_relation _ (deviceRelationRules relation refl trans halt)
    (fun state _ => refl state.jolt_device) instruction answer

/-- Every relaxed instruction retains the initialized code-word interval.
For example, an output store and a panic halt preserve the same protected code words.
Jolt at `ff6fc6568`: `tracer/src/emulator/mmu.rs` (`CodeGuard`, `assert_write_protected_store`). -/
theorem execWithTapeAnswer_codeRegion (instruction : Instr) (answer : BitVec 64) :
    StatePreservation.Preserves
      (fun s t : SailJoltState => s.codeRegion = t.codeRegion)
      (execWithTapeAnswer instruction answer) := by
  let rules : InstructionFrame.Rules
      (fun s t : SailJoltState => s.codeRegion = t.codeRegion) := {
    refl := fun _ => rfl
    trans := fun _ _ _ first next => first.trans next
    sail := fun _ _ _ => rfl
    vreg := fun _ _ _ => rfl
    store := store_doubleword_relation _ (fun _ => rfl)
      (fun _ _ _ first next => first.trans next) (fun _ _ => rfl)
    halt := fun _ _ => rfl
    append := fun _ _ => rfl }
  exact execWithTapeAnswer_relation _ rules (fun _ _ => rfl) instruction answer

/-- The answer supplied by the existing fixed-tape interpreter, or zero for an
instruction with no tape answer or a read that fails. -/
def fixedTapeAnswer (instruction : Instr) (state : SailJoltState) : BitVec 64 :=
  match instruction with
  | .VirtualAdviceLoad _ byteCount =>
      ((readAdviceTape state.adviceTape byteCount).map Prod.fst).getD 0
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
