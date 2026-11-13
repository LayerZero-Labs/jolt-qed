/-
Comparator challenge: the frozen statements of jolt-qed's headline theorems.

Each theorem below copies a headline statement verbatim and ends in `sorry`.
The comparator checks that the theorem of the same name in `Solution.lean`
proves the same statement, that the kernel accepts it, and that it depends on
no axiom outside `propext`, `Quot.sound` and `Classical.choice`
(`config.json`).

Keep each statement character for character in sync with its source theorem
and with `Solution.lean`. If a source statement changes, `Solution.lean` no
longer elaborates or the comparator reports a different statement; both stop
the gate until this file is updated, which is the point of freezing them.

This file lives outside JoltBytecode/ and JoltConstraints/ so that its
`sorry`s stay out of the roots of scripts/check_hygiene.py.
-/
import JoltConstraints.WholeRun.Top
import JoltBytecode.Decode.Compressed
import JoltBytecode.Step.Instructions

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail LeanRV64D
  LeanRV64D.Functions

namespace ComparatorGate

section WholeRun
open WholeRun

/-- Frozen statement of `WholeRun.HonestTrace.sail_reproduces`
(`JoltConstraints/WholeRun/Top.lean`). -/
theorem sail_reproduces {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    {elf : ElfSections} (hdecoded : joltInstance.program.DecodedFrom elf)
    (hrows : joltInstance.program.RowsAligned)
    (hheap : joltInstance.HeapNoWrap)
    (hcfg : (trace.prover_config joltInstance).isSome)
    {pre : List Block} {halt final : SailJoltState} (hp : HaltPrefix trace pre halt final)
    (hconf : ∀ b ∈ pre, BlockConforms joltInstance.program b) :
    ∃ (n : Nat) (s : SailState),
      WholeRun.sailRun n (sailInit trace.initialState) = .ok () s ∧
      Related halt s ∧
      trimTrailingZeros (sailOutputs trace.initialState.jolt_device s) =
        trimTrailingZeros final.jolt_device.outputs ∧
      (sailPanicWord trace.initialState.jolt_device s ≠ 0 ↔ final.jolt_device.panic = true) ∧
      (SailHalted joltInstance.program s ∨ halt = final) := sorry

/-- Frozen statement of `JoltInstance.sail_soundness`
(`JoltConstraints/WholeRun/Top.lean`). -/
theorem sail_soundness {F : Type} [Field F] (joltField : JoltField F)
    (joltInstance : JoltInstance SourceInstruction)
    (assumptions : joltInstance.SoundnessAssumptions)
    (restrictions : joltInstance.TemporaryRestrictions)
    (adviceBlockFits : joltInstance.UntrustedAdviceBlockFits)
    {params : WitnessParams} (untrustedAdvice : Nat → F)
    (witness : WitnessType F params)
    (satisfied : JoltConstraints.AllConstraints joltInstance untrustedAdvice witness)
    {elf : ElfSections} (hdecoded : joltInstance.program.DecodedFrom elf)
    (hrows : joltInstance.program.RowsAligned)
    (hheap : joltInstance.HeapNoWrap) :
    ∃ (privateInputs : JoltPrivateInputs) (trace : HonestTrace joltInstance privateInputs),
      trace.matches_outputs joltInstance ∧
      (trace.prover_config joltInstance).isSome ∧
      trace.SpoilAssertsPass ∧
      ∃ (pre : List Block) (halt final : SailJoltState),
        HaltPrefix trace pre halt final ∧
        ((∀ b ∈ pre, BlockConforms joltInstance.program b) →
          ∃ (n : Nat) (s : SailState),
            sailRun n (sailInit trace.initialState) = .ok () s ∧
            Related halt s ∧
            trimTrailingZeros (sailOutputs trace.initialState.jolt_device s) =
              trimTrailingZeros joltInstance.outputs ∧
            (sailPanicWord trace.initialState.jolt_device s ≠ 0 ↔ joltInstance.panic = true) ∧
            (SailHalted joltInstance.program s ∨ halt = final)) := sorry

end WholeRun

/-- Frozen statement of `JoltInstance.soundness`
(`JoltConstraints/Soundness/soundness.lean`). -/
theorem soundness {F : Type} [Field F] (joltField : JoltField F)
    (joltInstance : JoltInstance SourceInstruction)
    (assumptions : joltInstance.SoundnessAssumptions)
    (restrictions : joltInstance.TemporaryRestrictions)
    (adviceBlockFits : joltInstance.UntrustedAdviceBlockFits)
    {params : WitnessParams} (untrustedAdvice : Nat → F)
    (witness : WitnessType F params)
    (satisfied : JoltConstraints.AllConstraints joltInstance untrustedAdvice witness) :
    joltInstance.InLanguage := sorry

section Decode
open Decode

/-- Frozen statement of `Decode.joltDecode_agrees`
(`JoltBytecode/Decode/Agreement.lean`). -/
theorem joltDecode_agrees (w : BitVec 32) (advice : BitVec 64) (i : RiscvInstruction)
    (hi : joltDecode w advice = some i) (s : SailState) (hinv : _root_.Step.StepInvariant s)
    (hreset : s.regs.get? Register.misa = some resetMisa) :
    ∃ ast, ext_decode w s = .ok ast s ∧ _root_.Step.Matches i ast := sorry

/-- Frozen statement of `Decode.joltDecode_compressed_agrees`
(`JoltBytecode/Decode/Compressed.lean`). -/
theorem joltDecode_compressed_agrees (h : BitVec 16) (hc : h.extractLsb 1 0 ≠ 0b11#2)
    (advice : BitVec 64) (i : RiscvInstruction)
    (hi : joltDecode (joltUncompress h) advice = some i)
    (s : SailState) (hinv : _root_.Step.StepInvariant s)
    (hreset : s.regs.get? Register.misa = some resetMisa) :
    ∃ cast base, ext_decode_compressed h s = .ok cast s ∧ _root_.Step.Matches i base ∧
      ∀ s', _root_.Step.StepInvariant s' → _root_.Step.executeFull cast s' = _root_.Step.executeFull base s' := sorry

end Decode

section RiscvInstruction
open RiscvInstruction

/-- Frozen statement of `RiscvInstruction.joltRun_eq_execute`
(`JoltBytecode/Step/Instructions.lean`). -/
theorem joltRun_eq_execute :
    (i : RiscvInstruction) → i.Lifted → (ast : instruction) → Matches i ast →
    (js : SailJoltState) → (h : equivAssumptions i js) → AdviceHonest i js h →
    System.systemProjectResult (joltRun i js) = execute ast (System.systemProject js) := sorry

end RiscvInstruction

end ComparatorGate
