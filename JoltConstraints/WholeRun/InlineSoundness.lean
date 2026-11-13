import JoltConstraints.WholeRun.InlineContract
import JoltConstraints.Soundness.soundness

/-!
# Inline calls in an accepted run (R4)

`JoltInstance.soundness` turns a witness that satisfies `AllConstraints` into an honest trace
(`JoltInstance.InLanguage`). `HonestTrace.blocks` cuts every honest trace into blocks, one per
source instruction. This file adds that every inline block keeps the contract of its call
(`InlineKey.call_contract`): it keeps the frame of the call's write set, and it meets the
call's specification when the call's precondition holds in the state its rows start from.

The precondition is a premise of each call, not of the theorem: the result says nothing
about a call whose output buffer does not lie in RAM. "Accepted" means the modelled
`AllConstraints`. The result does not say that a guest computes SHA-256 or verifies an ECDSA
signature: it says what each call stores, and the specifications keep the gaps listed in
`InlineContract.lean`.
-/

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail
  LeanRV64D LeanRV64D.Functions
open JoltISA JoltISA.Inlines

set_option autoImplicit false

noncomputable section

namespace WholeRun

/-- **An inline block runs its call's rows.** A block whose row is the call
`key rd, rs1, rs2` has a call that Jolt's expansion accepts (`rd` is not `x0` when the call
reads it), and its rows, the call's expansion with some advice values patched in, run from
`Block.start` to `Block.post` and retire.
Example: a `SHA256` block runs the 36-register SHA-256 compression sequence. -/
theorem Block.Runs.inline_rows {program : Rv64ProgramImage SourceInstruction} {b : Block}
    (runs : b.Runs program) {key : InlineKey} {rs1 rs2 rd : regidx}
    (call : b.row.instruction = .inline key rs1 rs2 rd) :
    (key.readsRd = true → isX0 rd = false) ∧ ∃ values,
      execProgram (Program.seq (patchAdvice values (key.expandRows rs1 rs2 rd))) b.start =
        .ok RETIRE_SUCCESS b.post := by
  obtain ⟨values, instrs, -, patched, executed⟩ := runs.executes
  obtain ⟨rows, expanded, rfl⟩ := Option.map_eq_some_iff.mp patched
  obtain ⟨accepted, rowsEq⟩ := inline_expand_rows expanded call
  rw [rowsEq] at executed
  exact ⟨accepted, values, executed⟩

/-- **An inline block keeps the contract of its call.** A block of an honest trace whose
row is the call `key rd, rs1, rs2` keeps the frame of the call's write set from the state
its rows start from (`Block.start`) to the state after them (`Block.post`), and meets the
call's specification when the call's precondition holds in `Block.start`.
Example: a `BLAKE2` block whose state buffer at `rs1` lies in RAM leaves `Block.post` equal to
`Block.start` with the compression of the inputs stored at `rs1`, and every architectural
register unchanged. -/
theorem Block.Runs.inline_contract {program : Rv64ProgramImage SourceInstruction} {b : Block}
    (runs : b.Runs program) {key : InlineKey} {rs1 rs2 rd : regidx}
    (call : b.row.instruction = .inline key rs1 rs2 rd) :
    Frame (key.writeSet rs1 rs2 rd) b.start b.post ∧
      (key.Pre rs1 rs2 rd b.start → key.Spec rs1 rs2 rd b.start b.post) := by
  obtain ⟨accepted, values, executed⟩ := runs.inline_rows call
  exact InlineKey.call_contract key rs1 rs2 rd accepted values executed

/-- **Inline soundness under `AllConstraints` (R4).** Under the premises of
`JoltInstance.soundness`, the instance has an honest trace that witnesses
`JoltInstance.InLanguage` and cuts into blocks, one per source instruction, as
`HonestTrace.blocks` says. Every block whose row is an inline call `key rd, rs1, rs2` keeps
the frame of the call's write set, and meets the call's specification when the call's
precondition holds in the state its rows start from.
Example: if a guest calls `SECP256K1_MULQ` with its result buffer in RAM, and the witness
satisfies `AllConstraints`, then the accepted run stores some `c` with `a·b = w·p + c` at the
result buffer, and changes no architectural register at that call. -/
theorem JoltInstance.soundness_inline_calls {F : Type} [Field F] (joltField : JoltField F)
    (joltInstance : JoltInstance SourceInstruction)
    (assumptions : joltInstance.SoundnessAssumptions)
    (restrictions : joltInstance.TemporaryRestrictions)
    (adviceBlockFits : joltInstance.UntrustedAdviceBlockFits)
    {params : WitnessParams} (untrustedAdvice : Nat → F)
    (witness : WitnessType F params)
    (satisfied : JoltConstraints.AllConstraints joltInstance untrustedAdvice witness) :
    ∃ (privateInputs : JoltPrivateInputs) (trace : HonestTrace joltInstance privateInputs),
      trace.matches_outputs joltInstance ∧
      (trace.prover_config joltInstance).isSome ∧
      trace.SpoilAssertsPass ∧
      ∃ bs : List Block,
        bs ≠ [] ∧
        (∀ b ∈ bs, b.Runs joltInstance.program) ∧
        bs.head?.map (·.pre) = some trace.initialState ∧
        bs.IsChain (fun b c => b.post = c.pre) ∧
        bs.getLast?.map (·.post) = trace.rows.back?.map (·.postState) ∧
        (∀ b ∈ bs, ∃ k, b.FirstRowAt trace.toTrace k) ∧
        ∀ b ∈ bs, ∀ (key : InlineKey) (rs1 rs2 rd : regidx),
          b.row.instruction = .inline key rs1 rs2 rd →
          Frame (key.writeSet rs1 rs2 rd) b.start b.post ∧
            (key.Pre rs1 rs2 rd b.start → key.Spec rs1 rs2 rd b.start b.post) := by
  obtain ⟨privateInputs, trace, outputs, accepted, spoil⟩ :=
    JoltInstance.soundness joltField joltInstance assumptions restrictions adviceBlockFits
      untrustedAdvice witness satisfied
  obtain ⟨bs, nonempty, runs, head, chain, last, -, firstRows⟩ := HonestTrace.blocks trace
  exact ⟨privateInputs, trace, outputs, accepted, spoil, bs, nonempty, runs, head, chain, last,
    firstRows, fun b mem _ _ _ _ call => (runs b mem).inline_contract call⟩

end WholeRun
