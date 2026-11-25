import JoltConstraints.theorems.WholeRun.Top
import JoltConstraints.theorems.Completeness.completeness

/-!
# The premises of the headline theorems, checked by the build

`assumptions.toml` at the repository root lists every premise of the headline theorems, every
`sorry`, every field of `Rv64ProgramImage` and the scope premises, each with the Jolt functions it
depends on and either a necessity witness (`JoltConstraints/Audit/Necessity.lean`) or the reason
it has none. `reports/2026-11-25-stale-assumptions.md` explains why: a premise that Jolt stops
needing must be found and removed, not left behind.

This file makes the build fail when the premises change. `#expect_binders T "x : A" …` checks
that the binders of the theorem `T` are exactly the listed ones, in order, each printed as
`name : type` on one line. `#expect_fields S "f : A" …` does the same for the fields of the
structure `S`. On a mismatch the error prints the actual list, ready to paste.

When a binder or field is added, removed or changed:

1. update its list here;
2. update `assumptions.toml` (`appears_in`), adding or removing the registry entry;
3. run `scripts/check-assumptions.py`, which checks that the two agree.

A premise that a new Jolt check makes provable should be removed, not kept; its necessity witness
stops building when that happens.
-/

open Lean Elab Command Meta

namespace JoltConstraints.Audit

/-- Collapse every run of whitespace to one space, so that a pretty-printed type does not depend
on the line width. For example, `"a\n    b"` becomes `"a b"`. -/
def oneLine (s : String) : String := Id.run do
  let mut out := ""
  let mut gap := false
  for c in s.toList do
    if c.isWhitespace then
      gap := true
    else
      if gap && !out.isEmpty then out := out.push ' '
      out := out.push c
      gap := false
  return out

/-- Print a local hypothesis as `name : type` on one line; for example `joltField : JoltField F`.
Macro scopes are erased, so the instance binder of `[Field F]` prints as `inst : Field F`. -/
def renderLocal (fvar : Expr) : MetaM String := do
  let decl ← fvar.fvarId!.getDecl
  return s!"{decl.userName.eraseMacroScopes} : {oneLine (toString (← ppExpr decl.type))}"

/-- The binders of the theorem `name`, in order; for example `JoltInstance.soundness` starts with
`F : Type` and `inst : Field F`. The conclusion is not unfolded, so a conclusion that is a
definition counts as no binder. -/
def binderLines (name : Name) : MetaM (Array String) := do
  forallTelescope (← getConstInfo name).type fun xs _ => xs.mapM renderLocal

/-- The fields of the structure `name`, in order, each as `field : type` with the structure's
parameters and the structure value in scope; for example `riscv : ∃ i, b.row.instruction = …`
for `WholeRun.BlockConforms`. -/
def fieldLines (name : Name) : MetaM (Array String) := do
  let env ← getEnv
  unless isStructure env name do throwError "{name} is not a structure"
  let .inductInfo info ← getConstInfo name | throwError "{name} is not an inductive type"
  (getStructureFields env name).mapM fun field => do
    let projection ← getConstInfo (name ++ field)
    forallBoundedTelescope projection.type (some (info.numParams + 1)) fun _ body =>
      return s!"{field} : {oneLine (toString (← ppExpr body))}"

/-- Fail unless `actual` equals `expected`, naming what was added and what was removed and
printing the actual list in the syntax of the command `command`. -/
def compareLines (command : String) (name : Name) (what : String) (expected actual : Array String) :
    CommandElabM Unit := do
  if expected == actual then return
  let added := actual.filter (!expected.contains ·)
  let removed := expected.filter (!actual.contains ·)
  let show_ (xs : Array String) : String :=
    if xs.isEmpty then "  (none)" else "\n".intercalate (xs.toList.map ("  " ++ ·))
  let paste := "\n".intercalate (actual.toList.map fun s => s!"  \"{s}\"")
  throwError m!"The {what} of {name} changed. Update this list and the registry \
    (assumptions.toml, `appears_in`), then run scripts/check-assumptions.py.\n\
    New or changed:\n{show_ added}\nRemoved or changed:\n{show_ removed}\n\
    Actual list:\n{command} {name}\n{paste}"

/-- `#expect_binders T "x : A" …`: the binders of the theorem `T` are exactly these. -/
syntax (name := expectBinders) "#expect_binders " ident (ppLine str)* : command

/-- `#expect_fields S "f : A" …`: the fields of the structure `S` are exactly these. -/
syntax (name := expectFields) "#expect_fields " ident (ppLine str)* : command

@[command_elab expectBinders]
def elabExpectBinders : CommandElab
  | `(#expect_binders $id:ident $[$lines:str]*) => do
    let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    let actual ← liftTermElabM <| binderLines name
    compareLines "#expect_binders" name "binders" (lines.map (·.getString)) actual
  | _ => throwUnsupportedSyntax

@[command_elab expectFields]
def elabExpectFields : CommandElab
  | `(#expect_fields $id:ident $[$lines:str]*) => do
    let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    let actual ← liftTermElabM <| fieldLines name
    compareLines "#expect_fields" name "fields" (lines.map (·.getString)) actual
  | _ => throwUnsupportedSyntax

end JoltConstraints.Audit

/-! ## The headline theorems

`JoltInstance.soundness` and `JoltInstance.completeness` (with its existential form) are the
constraint-level theorems; `HonestTrace.sail_reproduces` and `JoltInstance.sail_soundness` are the
whole-run theorems of `docs/whole-run-theorem.md`. -/

#expect_binders JoltInstance.soundness
  "F : Type"
  "inst : Field F"
  "joltField : JoltField F"
  "joltInstance : JoltInstance SourceInstruction"
  "params : WitnessParams"
  "privateInputs : JoltPrivateInputs"
  "witness : WitnessType F params"
  "satisfied : JoltConstraints.AllConstraints joltInstance privateInputs witness"

#expect_binders JoltInstance.completeness
  "F : Type"
  "inst : Field F"
  "joltInstance : JoltInstance SourceInstruction"
  "privateInputs : JoltPrivateInputs"
  "trace : HonestTrace joltInstance privateInputs"
  "claimsRunOutputs : Trace.matches_outputs joltInstance trace.toTrace"
  "spoilAssertsPass : trace.SpoilAssertsPass"
  "config : ProverConfig"
  "proverAccepts : Trace.prover_config joltInstance trace.toTrace = some config"

#expect_binders JoltInstance.completeness_someWitness
  "F : Type"
  "inst : Field F"
  "joltInstance : JoltInstance SourceInstruction"
  "inLanguage : joltInstance.InLanguage"

#expect_binders WholeRun.HonestTrace.sail_reproduces
  "joltInstance : JoltInstance SourceInstruction"
  "privateInputs : JoltPrivateInputs"
  "trace : HonestTrace joltInstance privateInputs"
  "elf : WholeRun.ElfSections"
  "hdecoded : joltInstance.program.DecodedFrom elf"
  "hcfg : (Trace.prover_config joltInstance trace.toTrace).isSome = true"
  "pre : List WholeRun.Block"
  "halt : SailJoltState"
  "final : SailJoltState"
  "hp : WholeRun.HaltPrefix trace pre halt final"
  "hconf : ∀ b ∈ pre, WholeRun.BlockConforms joltInstance.program b"

#expect_binders JoltInstance.sail_soundness
  "F : Type"
  "inst : Field F"
  "joltField : JoltField F"
  "joltInstance : JoltInstance SourceInstruction"
  "params : WitnessParams"
  "givenInputs : JoltPrivateInputs"
  "witness : WitnessType F params"
  "satisfied : JoltConstraints.AllConstraints joltInstance givenInputs witness"
  "elf : WholeRun.ElfSections"
  "hdecoded : joltInstance.program.DecodedFrom elf"

/-! ## Structures that carry premises

A premise can also hide in a field: `BlockConforms` is a premise of the whole-run theorems, and
each proof field of `Rv64ProgramImage` is a fact every instance must carry. -/

#expect_fields WholeRun.BlockConforms
  "riscv : ∃ i, b.row.instruction = SourceInstruction.riscv i"

#expect_fields Rv64ProgramImage
  "instructions : Array (SourceInstructionRow Source)"
  "memory_init : List (BitVec 64 × BitVec 8)"
  "program_end : BitVec 64"
  "entry_address : BitVec 64"
  "program_end_ge_ram_start : JoltISA.RAM_START_ADDRESS ≤ self.program_end.toNat"
  "memory_init_in_program : ∀ entry ∈ self.memory_init, JoltISA.RAM_START_ADDRESS ≤ entry.1.toNat ∧ entry.1.toNat < self.program_end.toNat"
  "next_pc_no_wrap : ∀ row ∈ self.instructions, (row.address.toNat + if row.is_compressed = true then 2 else 4) < 2 ^ 64"
  "instruction_loaded : ∀ row ∈ self.instructions, ∃ entry ∈ self.memory_init, row.address.toNat ≤ entry.1.toNat ∧ entry.1.toNat < row.address.toNat + 2"
