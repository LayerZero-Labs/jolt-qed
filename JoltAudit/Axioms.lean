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

@[command_elab auditAxiomsCmd]
def elabAuditAxioms : CommandElab := fun stx => do
  match stx with
  | `(#audit_axioms $ids,*) => do
    let mut failures : Array (Name × Array Name) := #[]
    for id in ids.getElems do
      let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
      let axs ← collectAxioms name
      let bad := axs.filter (fun a => !permittedAxioms.contains a)
      if bad.isEmpty then
        logInfo m!"{name} depends on axioms: {axs.toList}"
      else
        failures := failures.push (name, bad)
    unless failures.isEmpty do
      let details := failures.toList.map fun (n, b) => m!"  {n}: {b.toList}"
      throwError m!"axiom audit failed; these theorems depend on axioms outside \
        {permittedAxioms}:\n{MessageData.joinSep details "\n"}"
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

/-! Not gated: `JoltInstance.completeness` and
`JoltInstance.completeness_someWitness`
(`JoltConstraints/Completeness/completeness.lean`) depend on `sorryAx` through
the five completeness gaps listed in `JoltConstraints/model_review.md`, "Proofs
owed". Add them here once those gaps are closed. -/

end JoltAudit
