import JoltBytecode.JoltISA.Semantics
import JoltBytecode.InstructionEquivalence.ProofSupport.DeviceFrame
import Mathlib.Tactic

/-! Untrusted-answer semantics for tape reads.
Each answer is a full 64-bit word. Width checks and cursor increments remain,
but tape contents and exhaustion do not constrain the answer.
The existing fixed-tape interpreter remains the specification for completeness.
PR #2049 removes the length-query instruction and documents this separation:
https://github.com/a16z/jolt/pull/2049
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
  | instruction => execInstr instruction

/-- Every relaxed instruction preserves a reflexive, transitive device
relation whose byte-store obligations cover SD and all floor stores.
For example, a relaxed advice load preserves equality of the entire device.
See Jolt's tracer at c6703570, `tracer/src/instruction/floor_access.rs`
(`store`) and `tracer/src/instruction/sd.rs` (`SD::exec`). -/
theorem execWithTapeAnswer_rule_of_device_relation_for_store
    (relation : JoltDevice → JoltDevice → Prop)
    (refl : ∀ io, relation io io)
    (trans : ∀ a b c, relation a b → relation b c → relation a c)
    (instruction : Instr) (answer : BitVec 64)
    (store : ∀ base source imm, instruction = .SD base source imm →
      ∀ io io' address value,
        JoltDevice.store? io address value = some io' → relation io io')
    (floorStore : ∀ base source imm fault,
      (instruction = .VirtualStoreB base source imm fault ∨
       instruction = .VirtualStoreH base source imm fault ∨
       instruction = .VirtualStoreW base source imm fault) →
      ∀ io io' address value,
        JoltDevice.store? io address value = some io' → relation io io') :
    StatePreservation.Preserves
      (fun s t : SailJoltState => relation s.jolt_device t.jolt_device)
      (execWithTapeAnswer instruction answer) := by
  cases instruction <;> simp only [execWithTapeAnswer]
  case VirtualAdviceLoad destination byteCount =>
    intro before after value runs
    split at runs
    · have keeps := StatePreservation.bind_rule
        (relation := fun s t : SailJoltState => relation s.jolt_device t.jolt_device)
        (fun a b c ab bc => trans _ _ _ ab bc)
        (JoltIOSetupFrame.writeDst_rule_of_device_relation relation refl destination answer)
        (fun _ => StatePreservation.pure_rule
          (fun s : SailJoltState => refl s.jolt_device) RETIRE_SUCCESS)
      have kept : relation
          ({ before with adviceTape := { before.adviceTape with
            readPosition := before.adviceTape.readPosition + byteCount.toNat } }).jolt_device
          after.jolt_device := keeps _ _ _ runs
      exact kept
    · cases runs
  all_goals
    exact JoltIOSetupFrame.execInstr_rule_of_device_relation_for_store
      relation refl trans _ store floorStore

/-- Every relaxed instruction preserves a reflexive, transitive device
relation that successful device byte stores preserve.
For example, both SD and VirtualStoreH preserve the device's memory layout. -/
theorem execWithTapeAnswer_rule_of_device_relation
    (relation : JoltDevice → JoltDevice → Prop)
    (refl : ∀ io, relation io io)
    (trans : ∀ a b c, relation a b → relation b c → relation a c)
    (store : ∀ io io' address value,
      JoltDevice.store? io address value = some io' → relation io io')
    (instruction : Instr) (answer : BitVec 64) :
    StatePreservation.Preserves
      (fun s t : SailJoltState => relation s.jolt_device t.jolt_device)
      (execWithTapeAnswer instruction answer) := by
  exact execWithTapeAnswer_rule_of_device_relation_for_store relation refl trans
    instruction answer (fun _ _ _ _ => store) (fun _ _ _ _ _ => store)

/-- A successful relaxed instruction other than SD or a floor store preserves
its entire device; `notStore` and `notFloorStore` exclude those constructors.
For example, LD and VirtualAdviceLoad leave the panic flag and output bytes fixed.
See Jolt's tracer at c6703570, `tracer/src/instruction/floor_access.rs` (`store`). -/
theorem execWithTapeAnswer_device_of_not_store (instruction : Instr) (answer : BitVec 64)
    (notStore : ∀ base source imm, instruction ≠ .SD base source imm)
    (notFloorStore : ∀ base source imm fault,
      ¬ (instruction = .VirtualStoreB base source imm fault ∨
         instruction = .VirtualStoreH base source imm fault ∨
         instruction = .VirtualStoreW base source imm fault)) :
    StatePreservation.Preserves
      (fun s t : SailJoltState => s.jolt_device = t.jolt_device)
      (execWithTapeAnswer instruction answer) := by
  apply execWithTapeAnswer_rule_of_device_relation_for_store Eq (fun _ => rfl)
    (fun _ _ _ first second => first.trans second)
  · intro base source imm isStore
    exact False.elim (notStore base source imm isStore)
  · intro base source imm fault isStore
    exact False.elim (notFloorStore base source imm fault isStore)

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
