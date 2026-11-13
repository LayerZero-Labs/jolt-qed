/-
Axiom allowlist for jolt-qed's headline theorems, checked during the build.

Building this module runs `Lean.collectAxioms`, the routine behind
`#print axioms`, on each headline theorem, and fails the build if a theorem
depends on an axiom other than `propext`, `Classical.choice` and `Quot.sound`.
For example `sorryAx` (from `sorry`), `Lean.ofReduceBool` and
`Lean.trustCompiler` (from `native_decide`), and the floating-point axioms of
`LeanRV64D/RiscvExtras.lean` all fail it.

CI runs `lake build JoltAudit` after the default build. The comparator gate in
`ci/comparator/` re-checks the whole-run and soundness statements with an
independent exporter and kernel.
-/
import Lean
import JoltConstraints.WholeRun.Top
import JoltBytecode.Decode.Agreement
import JoltBytecode.Decode.Compressed
import JoltBytecode.Step.Instructions
import JoltBytecode.Step.Ecall
import JoltConstraints.ExpansionGen.Equiv
import JoltConstraints.WholeRun.InlineSoundness
import JoltConstraints.WholeRun.Platform
import JoltConstraints.WholeRun.InlineCompleteness
import JoltConstraints.Completeness.completeness

open Lean Elab Command

namespace JoltAudit

/-- The axioms a headline theorem may depend on: Lean's three standard axioms.
For example `JoltInstance.soundness` depends on exactly these three. -/
def permittedAxioms : List Name :=
  [``propext, ``Classical.choice, ``Quot.sound]

/-- `#audit_axioms t₁, t₂, …` collects the axioms each theorem depends on and
throws an error, which fails the build, if any of them is outside
`permittedAxioms`. A name that no longer resolves fails too. On success it logs
each theorem's axioms, so the build log shows them. -/
syntax (name := auditAxiomsCmd) "#audit_axioms " ident,+ : command

/-- `#audit_axioms_known_sorry t₁, t₂, …` is `#audit_axioms` for theorems that
still depend on a known `sorry`: it also permits `sorryAx`, and logs whether each
theorem uses it. It fails the build on any other axiom outside `permittedAxioms`,
such as one from `native_decide`, but not on `sorryAx`, so CI does not require
these theorems to be sorry-free. -/
syntax (name := auditAxiomsKnownSorryCmd) "#audit_axioms_known_sorry " ident,+ : command

/-- Check each theorem in `ids` against `allowed`, log each theorem's axioms, and
fail if any theorem depends on an axiom outside `allowed`. -/
def auditAxioms (ids : Array Ident) (allowed : List Name) : CommandElabM Unit := do
  let mut failures : Array (Name × Array Name) := #[]
  for id in ids do
    let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    let axs ← collectAxioms name
    let bad := axs.filter (fun a => !allowed.contains a)
    if bad.isEmpty then
      logInfo m!"{name} depends on axioms: {axs.toList}"
    else
      failures := failures.push (name, bad)
  unless failures.isEmpty do
    let details := failures.toList.map fun (n, b) => m!"  {n}: {b.toList}"
    throwError m!"axiom audit failed; these theorems depend on axioms outside \
      {allowed}:\n{MessageData.joinSep details "\n"}"

@[command_elab auditAxiomsCmd]
def elabAuditAxioms : CommandElab := fun stx => do
  match stx with
  | `(#audit_axioms $ids,*) => auditAxioms ids.getElems permittedAxioms
  | _ => throwUnsupportedSyntax

@[command_elab auditAxiomsKnownSorryCmd]
def elabAuditAxiomsKnownSorry : CommandElab := fun stx => do
  match stx with
  | `(#audit_axioms_known_sorry $ids,*) =>
    auditAxioms ids.getElems (``sorryAx :: permittedAxioms)
  | _ => throwUnsupportedSyntax

/-! ## Gated theorems

The whole-run theorems and the soundness theorem they compose with
(`docs/whole-run-theorem.md`, `JoltConstraints/WholeRun/Top.lean`). -/

#audit_axioms
  WholeRun.HonestTrace.sail_reproduces,
  JoltInstance.sail_soundness,
  JoltInstance.soundness

/-! The decoder agreement theorems for 32-bit and compressed words
(`JoltBytecode/Decode/`, `docs/riscv-alignment.md`). -/

#audit_axioms
  Decode.joltDecode_agrees,
  Decode.joltDecode_compressed_agrees

/-! The bytecode expansion theorem the README names, and its lifts to Sail's
`try_step` for base and compressed instructions and for ECALL
(`JoltBytecode/Step/`). -/

#audit_axioms
  RiscvInstruction.joltRun_eq_execute,
  RiscvInstruction.joltStep_eq_try_step_base,
  RiscvInstruction.joltStep_eq_try_step_compressed,
  RiscvInstruction.joltStep_eq_try_step_ecall

/-! The proof that the model's expansion of every source instruction equals the
recipe the T6 generator derived from Jolt (`JoltConstraints/ExpansionGen/`,
`scripts/expansion-parity/EXPANSION-RECIPES.md`). -/

#audit_axioms
  ExpansionGen.expand_eq_generated

/-! The theorems for guests that call Jolt's twelve registered inlines
(`docs/inline-precompiles.md`, results R4 and R5): inline soundness under
`AllConstraints` (`JoltConstraints/WholeRun/InlineSoundness.lean`) and the
whole-run theorems with inlines (`JoltConstraints/WholeRun/Platform.lean`). -/

#audit_axioms
  WholeRun.JoltInstance.soundness_inline_calls,
  WholeRun.HonestTrace.sail_reproduces_with_inlines,
  JoltInstance.sail_soundness_with_inlines

/-! ## Known `sorry`

The completeness theorems depend on `sorryAx` through the five completeness gaps
listed in `JoltConstraints/model_review.md`, "Proofs owed":
- (01) `honestWitness_ramAddrEqRs1PlusImmMinusLookupIfLoadStore`,
  (08) `HonestTrace.floorAccess_address_nonneg` and
  (11) `HonestTrace.shiftData_address_noWrap`, false until a16z/jolt#1949 is
  fixed;
- (37) `honestWitness_ramValEqInitialPlusPrefixRamInc`, false until
  a16z/jolt#1950 is fixed;
- (38) `honestWitness_ramValFinalEqInitialPlusRamInc`, false until
  a16z/jolt#1951 item 1 is fixed.

`#audit_axioms_known_sorry` permits `sorryAx` for them and fails on any other
extra axiom. Move a theorem to `#audit_axioms` once those gaps are closed. -/

#audit_axioms_known_sorry
  JoltInstance.completeness,
  JoltInstance.completeness_someWitness,
  JoltInstance.completeness_jolt_inline_advice

end JoltAudit
