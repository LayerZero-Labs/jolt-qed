/-
Comparator solution: the frozen statements of `Challenge.lean`, proved by the
real theorems.

Each theorem has the name and the statement of its counterpart in
`Challenge.lean`, and its proof applies the jolt-qed theorem it freezes. The
comparator checks that each proves the challenge statement with only the axioms
in `config.json`; `JoltAudit/Axioms.lean` checks the same theorems in the build.
-/
import JoltConstraints.WholeRun.Top
import JoltBytecode.Decode.Compressed
import JoltBytecode.Step.Instructions

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail LeanRV64D
  LeanRV64D.Functions

namespace ComparatorGate

section WholeRun
open WholeRun

/-- Proof of the frozen statement of `WholeRun.HonestTrace.sail_reproduces`
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
      (SailHalted joltInstance.program s ∨ halt = final) :=
  WholeRun.HonestTrace.sail_reproduces trace hdecoded hrows hheap hcfg hp hconf

/-- Proof of the frozen statement of `JoltInstance.sail_soundness`
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
            (SailHalted joltInstance.program s ∨ halt = final)) :=
  JoltInstance.sail_soundness joltField joltInstance assumptions restrictions adviceBlockFits
    untrustedAdvice witness satisfied hdecoded hrows hheap

end WholeRun

/-- Proof of the frozen statement of `JoltInstance.soundness`
(`JoltConstraints/Soundness/soundness.lean`). -/
theorem soundness {F : Type} [Field F] (joltField : JoltField F)
    (joltInstance : JoltInstance SourceInstruction)
    (assumptions : joltInstance.SoundnessAssumptions)
    (restrictions : joltInstance.TemporaryRestrictions)
    (adviceBlockFits : joltInstance.UntrustedAdviceBlockFits)
    {params : WitnessParams} (untrustedAdvice : Nat → F)
    (witness : WitnessType F params)
    (satisfied : JoltConstraints.AllConstraints joltInstance untrustedAdvice witness) :
    joltInstance.InLanguage :=
  JoltInstance.soundness joltField joltInstance assumptions restrictions adviceBlockFits
    untrustedAdvice witness
    satisfied

section Decode
open Decode

/-- Proof of the frozen statement of `Decode.joltDecode_agrees`
(`JoltBytecode/Decode/Agreement.lean`). -/
theorem joltDecode_agrees (w : BitVec 32) (advice : BitVec 64) (i : RiscvInstruction)
    (hi : joltDecode w advice = some i) (s : SailState) (hinv : _root_.Step.StepInvariant s)
    (hreset : s.regs.get? Register.misa = some resetMisa) :
    ∃ ast, ext_decode w s = .ok ast s ∧ _root_.Step.Matches i ast :=
  Decode.joltDecode_agrees w advice i hi s hinv hreset

/-- Proof of the frozen statement of `Decode.joltDecode_compressed_agrees`
(`JoltBytecode/Decode/Compressed.lean`). -/
theorem joltDecode_compressed_agrees (h : BitVec 16) (hc : h.extractLsb 1 0 ≠ 0b11#2)
    (advice : BitVec 64) (i : RiscvInstruction)
    (hi : joltDecode (joltUncompress h) advice = some i)
    (s : SailState) (hinv : _root_.Step.StepInvariant s)
    (hreset : s.regs.get? Register.misa = some resetMisa) :
    ∃ cast base, ext_decode_compressed h s = .ok cast s ∧ _root_.Step.Matches i base ∧
      ∀ s', _root_.Step.StepInvariant s' → _root_.Step.executeFull cast s' = _root_.Step.executeFull base s' :=
  Decode.joltDecode_compressed_agrees h hc advice i hi s hinv hreset

end Decode

section RiscvInstruction
open RiscvInstruction

/-- Proof of the frozen statement of `RiscvInstruction.joltRun_eq_execute`
(`JoltBytecode/Step/Instructions.lean`). -/
theorem joltRun_eq_execute :
    (i : RiscvInstruction) → i.Lifted → (ast : instruction) → Matches i ast →
    (js : SailJoltState) → (h : equivAssumptions i js) → AdviceHonest i js h →
    System.systemProjectResult (joltRun i js) = execute ast (System.systemProject js) :=
  RiscvInstruction.joltRun_eq_execute

end RiscvInstruction

end ComparatorGate
