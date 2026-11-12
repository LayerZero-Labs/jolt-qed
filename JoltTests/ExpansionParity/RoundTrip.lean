import JoltTests.ExpansionParity.Report
import JoltTests.ExpansionParity.Inline

/-!
# Inline round trip

`compareInlineFixture` takes one `inline_fixture` record of the driver's
`rows.jsonl`, instantiates the generated rows (`JoltBytecode/Inlines/Generated`)
at its operands, stamps them with `stamp_sequence` and compares every row, flags
included.

`compareTemplate` instantiates one inline template of `inline_templates.json` at
an operand triple on both sides and compares every field the template carries.
The Rust side substitutes the triple into the template's `param` fields; the Lean
side applies the generated `<name>RowsAuto` (or `RowsAutoRdZero`) definition and
renders the resulting `JoltISA.Instr` rows with `RowView.ofLeanRow`
(`Row.lean`), which reads the constructors directly and shares no code with the
generator (`scripts/expansion-parity/src/lean.rs`).

`runInline` runs both over a whole driver output.
-/

open Lean LeanRV64D

namespace ExpansionParity

/-- The generated rows of an inline fixture record, stamped like a source row. -/
def compareInlineFixture (r : RecordInfo) : List Mismatch :=
  let s := r.source
  let name := s.inlineName.getD ""
  match findInline name, r.rows with
  | none, _ =>
      [r.mismatch "inline_fixture" none "inline" name "no generated definition"
        s!"no generated Lean rows for {name}"]
  | some _, none =>
      [r.mismatch "inline_fixture" none "result" (r.error.getD "error") "generated rows"
        s!"Lean defines rows, Rust rejects: {name} with rd = {showOpt s.rd}"]
  | some e, some rustRows =>
      let instrs := e.rows (s.rs1.getD 0) (s.rs2.getD 0) (s.rd.getD 0)
      let lean := stamp_sequence (BitVec.ofNat 64 s.address) s.compressed instrs
      compareRowLists r "inline_fixture" rustRows (lean.map RowView.ofLeanRow)

/-! ## Templates -/

/-- A register field of a template row. -/
inductive TReg where
  | none
  | param (name : String)
  | lit (n : Nat)

def TReg.ofJson (j : Json) : Except String TReg :=
  match j with
  | .null => pure .none
  | _ =>
    match j.getObjVal? "param", j.getObjVal? "lit" with
    | .ok p, _ => TReg.param <$> p.getStr?
    | _, .ok n => TReg.lit <$> n.getNat?
    | _, _ => throw s!"bad template register {j.compress}"

/-- Operands of one instantiation: `rs1`, `rs2` and `rs3` (the source `rd`). -/
structure Triple where
  rs1 : Nat
  rs2 : Nat
  rs3 : Nat

def TReg.inst (t : Triple) : TReg → Except String (Option Nat)
  | .none => pure Option.none
  | .lit n => pure (some n)
  | .param "rs1" => pure (some t.rs1)
  | .param "rs2" => pure (some t.rs2)
  | .param "rs3" => pure (some t.rs3)
  | .param p => throw s!"unknown template parameter {p}"

structure TemplateRow where
  kind : String
  address : Nat
  rd : TReg
  rs1 : TReg
  rs2 : TReg
  imm : Int
  vsr : Option Nat
  first : Bool
  compressed : Bool

def TemplateRow.ofJson (j : Json) : Except String TemplateRow := do
  pure
    { kind := ← (← getField j "kind").getStr?
      address := ← (← getField j "address").getNat?
      rd := ← TReg.ofJson (← getField j "rd")
      rs1 := ← TReg.ofJson (← getField j "rs1")
      rs2 := ← TReg.ofJson (← getField j "rs2")
      imm := ← intOfString "imm" (← (← getField j "imm").getStr?)
      vsr := ← optNat j "vsr"
      first := ← (← getField j "first").getBool?
      compressed := ← (← getField j "compressed").getBool? }

/-- Rust's rows at a triple: the template with its parameters replaced. -/
def TemplateRow.inst (t : Triple) (row : TemplateRow) : Except String RowView := do
  pure
    { kind := row.kind, address := row.address, imm := row.imm, vsr := row.vsr,
      first := row.first, compressed := row.compressed,
      rd := ← row.rd.inst t, rs1 := ← row.rs1.inst t, rs2 := ← row.rs2.inst t }

/-- Drops the fields templates do not carry, so the comparison skips them. -/
def RowView.withoutFlags (v : RowView) : RowView :=
  { v with circuitFlags := none, instructionFlags := none, lookupTable := none, raf := none }

/-- Compares one template case at one triple. The case is `normal` (Lean's
`RowsAuto rs1 rs2 rs3`) or `rd_zero` (Lean's `RowsAutoRdZero rs1 rs2`). -/
def compareTemplate (e : InlineEntry) (caseName : String) (rows : Array TemplateRow)
    (t : Triple) : Except String (List Mismatch) := do
  let rust ← rows.toList.mapM (·.inst t)
  let instrs := e.rows t.rs1 t.rs2 (if caseName == "rd_zero" then 0 else t.rs3)
  let address := (rows[0]?.map (·.address)).getD 0
  let compressed := rows.any (·.compressed)
  let lean := (stamp_sequence (BitVec.ofNat 64 address) compressed instrs).map
    (RowView.withoutFlags ∘ RowView.ofLeanRow)
  let source : SourceView :=
    { kind := "Inline", address, rd := some t.rs3, rs1 := some t.rs1, rs2 := some t.rs2,
      imm := 0, compressed, inlineName := some e.name }
  let info : RecordInfo :=
    { case := s!"{e.name}::{caseName}@({t.rs1},{t.rs2},{t.rs3})", group := "template",
      allocator := "-", source, rows := none, error := none }
  pure (compareRowLists info "inline_template" rust lean)

/-- xorshift64, for reproducible random triples. -/
def nextRand (s : UInt64) : UInt64 :=
  let s := s ^^^ (s <<< 13)
  let s := s ^^^ (s >>> 7)
  s ^^^ (s <<< 17)

def randomTriples (seed : Nat) (n : Nat) : Array Triple := Id.run do
  let mut s : UInt64 := UInt64.ofNat seed ||| 1
  let mut out := #[]
  for _ in [0:n] do
    s := nextRand s
    let a := (s % 32).toNat
    s := nextRand s
    let b := (s % 32).toNat
    s := nextRand s
    let c := (s % 31).toNat + 1
    out := out.push ⟨a, b, c⟩
  return out

/-! ## Completeness of the driver output -/

/-- The fixture scenarios the driver writes for every inline (the scenarios of
`registered_inline_expand_parity_hashes.jsonl`). Each appears once per
allocator: `NAME::SCENARIO` with `fresh` and `NAME::SCENARIO@shared` with
`shared`. -/
def fixtureScenarios : List String := ["normal", "compressed", "rd_zero", "aliased_operands"]

/-- What `inline_templates.json` gives for one inline: whether its `normal` and
`rd_zero` cases are present and not null. -/
structure TemplateCases where
  name : String
  normal : Bool
  rdZero : Bool

def templateCases (tj : Json) : Except String (Array TemplateCases) := do
  let inlines ← (← tj.getObjVal? "inlines").getArr?
  inlines.mapM fun inl => do
    let name ← (← inl.getObjVal? "name").getStr?
    let cases ← (← inl.getObjVal? "cases").getObj?
    let present (k : String) : Bool := match cases.get? k with
      | none | some .null => false
      | some _ => true
    pure { name, normal := present "normal", rdZero := present "rd_zero" }

def coverageMismatch (case field rust lean cause : String) : Mismatch :=
  { check := "inline_coverage", case, group := "coverage", allocator := "-",
    sourceKind := "Inline", row := none, field, rust, lean, cause }

/-- Checks that the driver output covers every inline of `inlineEntries`.
Each inline needs exactly one template entry, with a `normal` case that is not
null, and exactly one fixture record per scenario and allocator. Its `rd_zero`
fixture records must hold rows when its `rd_zero` template is not null and
Jolt's error when it is null. A fixture record outside this set is reported
too. An inline with no template entry at all is reported by `runInline`. -/
def inlineCoverage (fixtures : Array RecordInfo) (templates : Array TemplateCases) :
    List Mismatch := Id.run do
  let mut out : Array Mismatch := #[]
  let mut expected : Array (String × String) := #[]
  for e in inlineEntries do
    let ts := templates.filter (·.name == e.name)
    if ts.size > 1 then
      out := out.push <| coverageMismatch e.name "inline" s!"{ts.size} template entries"
        "1 template entry" "repeated template entry"
    let rdZero := ts.any (·.rdZero)
    if ts.size == 1 && !ts.any (·.normal) then
      out := out.push <| coverageMismatch e.name "normal" "missing or null" "generated rows"
        "no normal template"
    for sc in fixtureScenarios do
      for (alloc, suffix) in [("fresh", ""), ("shared", "@shared")] do
        let case := s!"{e.name}::{sc}{suffix}"
        expected := expected.push (case, alloc)
        let rs := fixtures.filter (fun r => r.case == case && r.allocator == alloc)
        if rs.size != 1 then
          out := out.push <| coverageMismatch case "fixture" s!"{rs.size} records" "1 record"
            "fixture record missing or repeated"
        for r in rs do
          if sc == "rd_zero" && r.rows.isSome != rdZero then
            out := out.push <| coverageMismatch case "rd_zero"
              (if r.rows.isSome then "rows" else "error")
              (if rdZero then "rows (template present)" else "error (template null)")
              "rd_zero fixture record disagrees with the rd_zero template"
  for r in fixtures do
    if !expected.contains (r.case, r.allocator) then
      out := out.push <| coverageMismatch r.case "fixture" r.allocator "not expected"
        "unexpected fixture record"
  return out.toList

/-- A template-level disagreement that concerns a whole inline, not one row. -/
def templateMismatch (name field rust lean cause : String) : Mismatch :=
  { check := "inline_template", case := name, group := "template", allocator := "-",
    sourceKind := "Inline", row := none, field, rust, lean, cause }

def runInline (rowsPath templatesPath outDir : String) (triples seed : Nat) : IO UInt32 := do
  IO.FS.createDirAll outDir
  let mut all : Array Mismatch := #[]
  let mut summary : Summary := {}
  -- Fixture records.
  let lines ← readLines rowsPath
  let mut fixtures := 0
  let mut fixtureRows := 0
  let mut fixtureAgree := 0
  let mut fixtureRecords : Array RecordInfo := #[]
  for line in lines do
    let r ← parseRecord line
    if r.group != "inline_fixture" then continue
    fixtures := fixtures + 1
    fixtureRecords := fixtureRecords.push r
    fixtureRows := fixtureRows + (r.rows.map List.length).getD 0
    let ms := compareInlineFixture r
    if ms.isEmpty then fixtureAgree := fixtureAgree + 1
    for m in ms do
      all := all.push m
      summary := summary.add m
  -- Templates.
  let tj ← match Json.parse (← IO.FS.readFile templatesPath) with
    | .ok j => pure j
    | .error e => throw <| IO.userError s!"cannot parse {templatesPath}: {e}"
  let tri (key : String) : IO Triple := do
    match (do
        let arr ← (← (← tj.getObjVal? "triples").getObjVal? key).getArr?
        pure (⟨← arr[0]!.getNat?, ← arr[1]!.getNat?, ← arr[2]!.getNat?⟩ : Triple)) with
    | .ok t => pure t
    | .error e => throw <| IO.userError e
  let fixed := #[← tri "A", ← tri "B"]
  let coverage := inlineCoverage fixtureRecords (← IO.ofExcept (templateCases tj))
  for m in coverage do
    all := all.push m
    summary := summary.add m
  let inlines ← IO.ofExcept ((tj.getObjVal? "inlines") >>= (·.getArr?))
  let mut templateNames : Array String := #[]
  let mut instantiations := 0
  let mut templateRows := 0
  for inl in inlines do
    let name ← IO.ofExcept ((inl.getObjVal? "name") >>= (·.getStr?))
    templateNames := templateNames.push name
    let some e := findInline name
      | let m := templateMismatch name "inline" name "no generated definition"
          s!"no generated Lean rows for {name}"
        all := all.push m
        summary := summary.add m
        continue
    let cases ← IO.ofExcept ((inl.getObjVal? "cases") >>= (·.getObj?))
    -- The driver writes `"rd_zero": null` when Jolt rejects rd = x0 for the inline.
    let rdZeroRejected := match cases.get? "rd_zero" with
      | none | some .null => true
      | some _ => false
    if rdZeroRejected then
      let m := templateMismatch name "rd_zero" "Jolt rejects rd = x0"
        s!"{name} has RowsAutoRdZero rows" "Lean defines rd = x0 rows that Jolt rejects"
      all := all.push m
      summary := summary.add m
    for (caseName, caseJson) in cases.toArray do
      if caseJson matches .null then continue
      let rowsJ ← IO.ofExcept ((caseJson.getObjVal? "rows") >>= (·.getArr?))
      let rows ← IO.ofExcept (rowsJ.mapM TemplateRow.ofJson)
      -- The case seed depends on the inline and case so cases draw different triples.
      let caseSeed := seed + name.hash.toNat + caseName.hash.toNat
      for t in fixed ++ randomTriples caseSeed triples do
        let t := if caseName == "rd_zero" then { t with rs3 := 0 } else t
        let ms ← IO.ofExcept (compareTemplate e caseName rows t)
        instantiations := instantiations + 1
        templateRows := templateRows + rows.size
        for m in ms do
          all := all.push m
          summary := summary.add m
  for e in inlineEntries do
    if !templateNames.contains e.name then
      let m := templateMismatch e.name "inline" "not registered" e.name
        s!"generated Lean rows for an inline Jolt does not register: {e.name}"
      all := all.push m
      summary := summary.add m
  writeMismatches (outDir ++ "/inline-mismatches.jsonl") all
  let text :=
    s!"Inline round trip: {rowsPath}, {templatesPath}\n" ++
    s!"fixture records: {fixtures} ({fixtureRows} rows), agreeing: {fixtureAgree}\n" ++
    s!"inlines in templates: {templateNames.size}; Lean entries: {inlineEntries.length}\n" ++
    s!"template instantiations: {instantiations} ({templateRows} rows); " ++
    s!"triples per case: 2 fixed + {triples} random, seed {seed}\n" ++
    s!"coverage mismatches (missing or unexpected inputs): {coverage.length}\n" ++
    s!"field mismatches: {all.size}\n\n" ++
    "Disagreements by cause:\n" ++ summary.render
  IO.FS.writeFile (outDir ++ "/inline-summary.txt") text
  IO.println text
  return if all.isEmpty then 0 else 1

/-- Deletes and repeats inputs of the round trip and checks that
`inlineCoverage` reports each change; the unchanged inputs must give no
coverage mismatch. -/
def coverageMutationCheck (rowsPath templatesPath : String) : IO Bool := do
  let mut fixtures : Array RecordInfo := #[]
  for line in ← readLines rowsPath do
    let r ← parseRecord line
    if r.group == "inline_fixture" then fixtures := fixtures.push r
  let tj ← IO.ofExcept (Json.parse (← IO.FS.readFile templatesPath))
  let templates ← IO.ofExcept (templateCases tj)
  let some first := templates[0]? | throw <| IO.userError "no inline template"
  let n := first.name
  let clean := inlineCoverage fixtures templates
  IO.println s!"coverage: unchanged inputs give {clean.length} coverage mismatches"
  let dropCase (c : String) := fixtures.filter (·.case != c)
  let muts : List (String × Array RecordInfo × Array TemplateCases) :=
    [ (s!"drop the normal template of {n}", fixtures,
        templates.map fun t => if t.name == n then { t with normal := false } else t),
      (s!"drop the fixture record {n}::normal", dropCase s!"{n}::normal", templates),
      (s!"drop the fixture record {n}::normal@shared", dropCase s!"{n}::normal@shared", templates),
      (s!"drop the fixture record {n}::rd_zero", dropCase s!"{n}::rd_zero", templates),
      (s!"repeat the fixture record {n}::compressed",
        fixtures ++ fixtures.filter (·.case == s!"{n}::compressed"), templates),
      (s!"turn the rows of {n}::rd_zero into an error",
        fixtures.map fun r =>
          if r.case == s!"{n}::rd_zero" then { r with rows := none, error := some "x" } else r,
        templates) ]
  let mut ok := clean.isEmpty
  for (name, fs, ts) in muts do
    let ms := inlineCoverage fs ts
    IO.println s!"  {name}: {if ms.isEmpty then "NOT DETECTED" else s!"detected ({ms.length} coverage mismatches)"}"
    ok := ok && !ms.isEmpty
  return ok

/-- The first `inline_fixture` record with rows, for the mutation check. -/
def firstInlineFixture (rowsPath : String) : IO Json := do
  for line in ← readLines rowsPath do
    let j ← IO.ofExcept (Json.parse line)
    let r ← IO.ofExcept (RecordInfo.ofJson j)
    if r.group == "inline_fixture" && r.rows.isSome then return j
  throw <| IO.userError "no inline fixture record"

end ExpansionParity
