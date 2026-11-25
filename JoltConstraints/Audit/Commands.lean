import Lean

/-!
# Audit commands

The commands that `JoltConstraints/Audit/Premises.lean` and `JoltConstraints/Audit/Statements.lean`
use to make the build fail when the headline theorems change. This file imports only `Lean`, so a
test of a command builds in seconds.

* `#assert_axioms n₁ n₂ …` fails unless every axiom that each declaration depends on is one of
  `propext`, `Classical.choice` and `Quot.sound`. A `sorry`, `admit`, `native_decide`,
  `bv_decide` or new `axiom` in the dependency closure adds an axiom outside these three
  (`sorryAx`, `Lean.ofReduceBool`, or the new axiom) and makes it fail.
* `#expect_binders T "x : A" …` fails unless the binders of the theorem `T` are exactly the
  listed ones; `#expect_fields S "f : A" …` does the same for the fields of the structure `S`.
* `#audit_statements` names the headline theorems, necessity witnesses and derived facts. For
  each one it checks the axioms as `#assert_axioms` does, and compares its full statement and
  the fingerprints of the definitions its statement depends on with a table (see
  `statementTable`).

Every name these commands take is resolved exactly: `open` and the current namespace do not
apply, so a registered name that does not exist is an error.

## Updating the expected data

When the environment variable `JOLT_QED_AUDIT_OUT` names a directory, each of the commands
`#expect_binders`, `#expect_fields` and `#audit_statements` also writes its actual data to a
file in that directory, and still fails on a mismatch. `scripts/update-audit-tables.py` builds
the audit modules that way and pastes the files over the expected data.
-/

open Lean Elab Command Meta

namespace JoltConstraints.Audit

/-! ## Exact names and axioms -/

/-- The axioms a headline theorem may depend on. -/
def coreAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- The declaration `id` names, resolved exactly: `JoltInstance.soundness` resolves to
`JoltInstance.soundness` only, never to `Foo.JoltInstance.soundness` under `open Foo`. -/
def exactConst (id : Ident) : CommandElabM Name := do
  let name := id.getId
  unless (← getEnv).contains name do
    throwErrorAt id "unknown declaration {name}. Audit commands resolve names exactly, \
      without `open` or the current namespace."
  return name

/-- The axioms of `name` outside `coreAxioms`, sorted. For a theorem proved with `sorry` this is
`#[sorryAx]`; with `native_decide` it is `#[Lean.ofReduceBool]`. -/
def extraAxioms (name : Name) : CommandElabM (Array Name) := do
  return (← collectAxioms name).filter (!coreAxioms.contains ·)

/-- Log an error at `ref` if `name` depends on an axiom outside `coreAxioms`. -/
def checkAxiomsAt (ref : Syntax) (name : Name) : CommandElabM Unit := do
  let extra ← extraAxioms name
  unless extra.isEmpty do
    logErrorAt ref m!"{name} depends on axioms other than propext, Classical.choice and \
      Quot.sound: {extra.toList}"

/-- `#assert_axioms n₁ n₂ …`: each declaration depends only on `propext`, `Classical.choice` and
`Quot.sound`. -/
syntax (name := assertAxioms) "#assert_axioms" (ppSpace ident)+ : command

@[command_elab assertAxioms]
def elabAssertAxioms : CommandElab
  | `(#assert_axioms $ids*) => do
    for id in ids do
      checkAxiomsAt id (← exactConst id)
  | _ => throwUnsupportedSyntax

/-! ## Writing the actual data -/

/-- If `JOLT_QED_AUDIT_OUT` is set, write `text` to `<JOLT_QED_AUDIT_OUT>/<file>`. -/
def writeActual (file : String) (text : String) : CommandElabM Unit := do
  let some dir ← (IO.getEnv "JOLT_QED_AUDIT_OUT" : IO _) | return
  let dir : System.FilePath := dir
  IO.FS.createDirAll dir
  IO.FS.writeFile (dir / file) text

/-! ## Binders and fields -/

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
  let paste := "\n".intercalate (actual.toList.map fun s => s!"  \"{s}\"")
  writeActual s!"{command.drop 1}-{name}.txt" paste
  if expected == actual then return
  let added := actual.filter (!expected.contains ·)
  let removed := expected.filter (!actual.contains ·)
  let show_ (xs : Array String) : String :=
    if xs.isEmpty then "  (none)" else "\n".intercalate (xs.toList.map ("  " ++ ·))
  throwError m!"The {what} of {name} changed. Run scripts/update-audit-tables.py to update \
    this list, then update the registry (assumptions.toml, `appears_in`) and run \
    scripts/check-assumptions.py.\n\
    New or changed:\n{show_ added}\nRemoved or changed:\n{show_ removed}\n\
    Actual list:\n{command} {name}\n{paste}"

/-- `#expect_binders T "x : A" …`: the binders of the theorem `T` are exactly these. -/
syntax (name := expectBinders) "#expect_binders " ident (ppLine str)* : command

/-- `#expect_fields S "f : A" …`: the fields of the structure `S` are exactly these. -/
syntax (name := expectFields) "#expect_fields " ident (ppLine str)* : command

@[command_elab expectBinders]
def elabExpectBinders : CommandElab
  | `(#expect_binders $id:ident $[$lines:str]*) => do
    let name ← exactConst id
    let actual ← liftTermElabM <| binderLines name
    compareLines "#expect_binders" name "binders" (lines.map (·.getString)) actual
  | _ => throwUnsupportedSyntax

@[command_elab expectFields]
def elabExpectFields : CommandElab
  | `(#expect_fields $id:ident $[$lines:str]*) => do
    let name ← exactConst id
    let actual ← liftTermElabM <| fieldLines name
    compareLines "#expect_fields" name "fields" (lines.map (·.getString)) actual
  | _ => throwUnsupportedSyntax

/-! ## Statement fingerprints

A theorem's statement means what the definitions it mentions mean. To notice a changed
definition anywhere below a headline statement, `#audit_statements` walks the *dependency
closure of the statement*: the constants in the statement's type, then the constants in the
type and value of each definition among them, and so on. It follows only this repository's own
declarations (modules under `JoltConstraints` and `JoltBytecode`): Mathlib and the Sail runtime
are pinned in `lake-manifest.json`, and the generated Sail model `LeanRV64D` by
`sail-import/PROVENANCE.toml`. It does not enter proofs: for a theorem it reads the statement
only, so a changed proof changes no fingerprint.

The fingerprint of a declaration is `Expr.hash` of its type and, for a definition, of its value.
`Expr.hash` ignores binder names and binder kinds, and is the same on every platform.
Declarations that Lean generates for another one (`foo.match_1`, `foo._proof_1`, `foo._unary`,
constructors, recursors, `noConfusion`, structure projections) count as part of it, so the table
has one line per declaration a person wrote. -/

/-- Whether `name` comes from a module of this repository. -/
def isOwnDeclaration (env : Environment) (name : Name) : Bool :=
  match env.getModuleIdxFor? name with
  | some idx =>
    let module := env.header.moduleNames[idx.toNat]!
    (`JoltConstraints).isPrefixOf module || (`JoltBytecode).isPrefixOf module
  | none => false

/-- Whether the last component of a name marks a declaration Lean generated for its prefix,
such as `match_1`, `_proof_2`, `_unary`, `eq_1` or `eq_def`. -/
def isGeneratedSuffix (s : String) : Bool :=
  s.startsWith "_" || s.startsWith "match_" || s.startsWith "proof_" || s.startsWith "eq_"

/-- The declaration a person wrote that `name` belongs to. For example `Foo.bar.match_1` belongs
to `Foo.bar`, the constructor `Foo.mk` and the projection `Foo.x` to the structure `Foo`. -/
partial def ownerName (env : Environment) (name : Name) : Name :=
  match env.find? name with
  | some (.ctorInfo info) => ownerName env info.induct
  | some (.recInfo _) => ownerName env name.getPrefix
  | _ =>
    if isAuxRecursor env name || isNoConfusion env name then ownerName env name.getPrefix
    else if let some info := env.getProjectionFnInfo? name then
      ownerName env info.ctorName.getPrefix
    else match name with
      | .str parent s => if isGeneratedSuffix s && !parent.isAnonymous then ownerName env parent
                         else name
      | _ => name

/-- The hash of one declaration and the constants to visit next. A theorem contributes its
statement only; an auxiliary recursor or `noConfusion` its type only (its value is generated
from the inductive type, which is hashed). -/
def declarationHash (env : Environment) (name : Name) : Option (UInt64 × Array Name) :=
  let typeOnly (tag : UInt64) (type : Expr) := (mixHash tag type.hash, type.getUsedConstants)
  match env.find? name with
  | some (.defnInfo info) =>
    if isAuxRecursor env name || isNoConfusion env name then typeOnly 1 info.type
    else some (mixHash 2 (mixHash info.type.hash info.value.hash),
      info.type.getUsedConstants ++ info.value.getUsedConstants)
  | some (.thmInfo info) => typeOnly 3 info.type
  | some (.opaqueInfo info) => some (mixHash 4 (mixHash info.type.hash info.value.hash),
      info.type.getUsedConstants ++ info.value.getUsedConstants)
  | some (.inductInfo info) => some (mixHash 5 info.type.hash,
      info.type.getUsedConstants ++ info.ctors.toArray)
  | some (.ctorInfo info) => some (mixHash 6 info.type.hash,
      info.type.getUsedConstants.push info.induct)
  | some (.recInfo info) => typeOnly 7 info.type
  | some (.axiomInfo info) => typeOnly 8 info.type
  | _ => none

/-- The repository declarations in the dependency closure of `root`'s statement, each with its
hash. `root` itself contributes its statement. -/
def statementClosure (env : Environment) (root : Name) : Std.HashMap Name UInt64 := Id.run do
  let mut seen : Std.HashMap Name UInt64 := {}
  let mut todo : Array Name := #[root]
  while !todo.isEmpty do
    let name := todo.back!
    todo := todo.pop
    if seen.contains name || !isOwnDeclaration env name then continue
    match declarationHash env name with
    | none => seen := seen.insert name 0
    | some (hash, next) =>
      seen := seen.insert name hash
      todo := todo ++ next.filter (!seen.contains ·)
  return seen

/-- The fingerprint of each owner in a closure: the hashes of its members, in name order,
mixed together with their names. -/
def ownerFingerprints (env : Environment) (closure : Std.HashMap Name UInt64) :
    Std.HashMap Name UInt64 := Id.run do
  let members := closure.toArray.qsort (fun a b => Name.lt a.1 b.1)
  let mut out : Std.HashMap Name UInt64 := {}
  for (name, hash) in members do
    let owner := ownerName env name
    out := out.insert owner (mixHash (out.getD owner 7) (mixHash (Hashable.hash name) hash))
  return out

/-- A 64-bit hash as 16 hexadecimal digits. -/
def hex16 (h : UInt64) : String :=
  let digits := (Nat.toDigits 16 h.toNat)
  String.ofList (List.replicate (16 - digits.length) '0' ++ digits)

/-- The printed name of a declaration, without the `_private.<module>.0.` prefix. -/
def shownName (name : Name) : String := toString (privateToUserName name)

/-- The table `#audit_statements` compares: each root's statement, pretty-printed at width 100,
then one line `<fingerprint> <declaration>` per declaration in the union of the closures.
For example:

```text
statement JoltInstance.soundness
  ∀ {F : Type} [inst : Field F], JoltField F → …
fingerprint 3f2a9c0d81e4b7a6 JoltConstraints.AllConstraints
``` -/
structure StatementTable where
  statements : Array (String × String)
  fingerprints : Array (String × String)
  deriving BEq

/-- Render a table as text, the form checked into `JoltConstraints/Audit/Statements.lean`. -/
def StatementTable.render (t : StatementTable) : String :=
  let statements := t.statements.toList.map fun (name, text) =>
    s!"statement {name}\n" ++ "\n".intercalate ((text.splitOn "\n").map ("  " ++ ·))
  let prints := t.fingerprints.toList.map fun (name, hash) => s!"fingerprint {hash} {name}"
  "\n".intercalate (statements ++ prints) ++ "\n"

/-- Read a table from its text form. -/
def StatementTable.parse (text : String) : Except String StatementTable := do
  let mut statements : Array (String × String) := #[]
  let mut prints : Array (String × String) := #[]
  for line in text.splitOn "\n" do
    if line.isEmpty then continue
    if line.startsWith "statement " then
      statements := statements.push ((line.drop 10).toString, "")
    else if line.startsWith "  " then
      let some (name, body) := statements.back? | throw s!"text before the first statement: {line}"
      let body := if body.isEmpty then (line.drop 2).toString else body ++ "\n" ++ (line.drop 2).toString
      statements := statements.pop.push (name, body)
    else if line.startsWith "fingerprint " then
      match (line.drop 12).toString.splitOn " " with
      | [hash, name] => prints := prints.push (name, hash)
      | _ => throw s!"malformed fingerprint line: {line}"
    else throw s!"malformed line: {line}"
  return { statements, fingerprints := prints }

/-- The labels a root may carry in `#audit_statements`: `headline` for a headline theorem,
`witness` for a necessity witness, `derived` for a derived fact (`derived_by` in
`assumptions.toml`). -/
def rootLabels : List String := ["headline", "witness", "derived"]

/-- `#audit_statements` followed by lines `<label> <declaration>`, then `expect` and the table
as a raw string. -/
syntax (name := auditStatements)
  "#audit_statements" (ppLine ident ident)* ppLine "expect" ppSpace str : command

/-- Compute the actual table for `roots`, and for each fingerprinted declaration the roots whose
closure contains it. -/
def actualTable (roots : Array Name) :
    CommandElabM (StatementTable × Std.HashMap String (Array Name)) := do
  let env ← getEnv
  let mut statements := #[]
  let mut prints : Std.HashMap String String := {}
  let mut users : Std.HashMap String (Array Name) := {}
  for root in roots do
    let type := (← getConstInfo root).type
    let text ← liftTermElabM <| withOptions (fun o => o.set `format.width (100 : Nat)) do
      return toString (← ppExpr type)
    statements := statements.push (toString root, text)
    for (owner, hash) in ownerFingerprints env (statementClosure env root) do
      let key := shownName owner
      prints := prints.insert key (hex16 hash)
      users := users.insert key ((users.getD key #[]).push root)
  let fingerprints := prints.toArray.qsort (fun a b => a.1 < b.1) |>.map fun (n, h) => (n, h)
  return ({ statements, fingerprints }, users)

/-- Describe how `actual` differs from `expected`. -/
def describeChanges (expected actual : StatementTable)
    (users : Std.HashMap String (Array Name)) : MessageData := Id.run do
  let mut lines : Array MessageData := #[]
  for (name, text) in actual.statements do
    match expected.statements.find? (·.1 == name) with
    | none => lines := lines.push m!"New statement {name}:\n{text}"
    | some (_, old) =>
      if old != text then lines := lines.push m!"Statement of {name} changed. It was\n{old}\nand is\n{text}"
  for (name, _) in expected.statements do
    unless actual.statements.any (·.1 == name) do lines := lines.push m!"Statement {name} removed"
  let old : Std.HashMap String String := .ofList expected.fingerprints.toList
  let new : Std.HashMap String String := .ofList actual.fingerprints.toList
  let usedBy (name : String) : String :=
    ", ".intercalate ((users.getD name #[]).toList.map toString)
  for (name, hash) in actual.fingerprints do
    match old.get? name with
    | none => lines := lines.push m!"New dependency {name} (of {usedBy name})"
    | some h => if h != hash then lines := lines.push m!"Changed: {name} (a dependency of {usedBy name})"
  for (name, _) in expected.fingerprints do
    unless new.contains name do lines := lines.push m!"No longer a dependency: {name}"
  return MessageData.joinSep lines.toList "\n"

@[command_elab auditStatements]
def elabAuditStatements : CommandElab
  | `(#audit_statements $[$labels:ident $ids:ident]* expect $table:str) => do
    let mut roots := #[]
    for label in labels, id in ids do
      unless rootLabels.contains (toString label.getId) do
        throwErrorAt label "unknown label {label.getId}; expected one of {rootLabels}"
      let name ← exactConst id
      checkAxiomsAt id name
      if roots.contains name then throwErrorAt id "{name} is listed twice"
      roots := roots.push name
    let (actual, users) ← actualTable roots
    writeActual "audit_statements.txt" actual.render
    let expected ← match StatementTable.parse table.getString with
      | .ok t => pure t
      | .error e => throwErrorAt table "cannot read the expected table: {e}"
    unless expected == actual do
      throwErrorAt table m!"The statements of the audited theorems, or definitions they depend \
        on, changed. Review the changes below. If they are intended, run \
        scripts/update-audit-tables.py to rewrite the expected table, and check whether a \
        registry entry in assumptions.toml needs updating.\n{describeChanges expected actual users}"
  | _ => throwUnsupportedSyntax

end JoltConstraints.Audit
