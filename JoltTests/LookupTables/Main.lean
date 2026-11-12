import Lean.Data.Json.Parser
import Lean.Data.Json.Basic
import Std.Data.HashMap
import JoltTests.LookupTables.Twin

/-!
# lookup-tables: the T4 comparator

The Rust emitter `scripts/expansion-parity/src/bin/lookup-tables.rs` evaluates
Jolt's `LookupTableKind::<64>::materialize_entry` at edge and random indices of
every table and writes one JSON line per (table, index)
(`scripts/expansion-parity/LOOKUP-TABLES.md`).
This module evaluates the computable twin `lookupTableEntryNat`
(`JoltTests/LookupTables/Twin.lean`) at the same indices and compares values.
`lookupTableEntry_eq_twin` carries each agreement over to the field table
`JoltConstraints.lookupTableEntry`.
The check samples indices: it does not prove agreement at every index.

Usage (from the repository root, after `lake build JoltTests.LookupTables.Main`):

```
LOOKUP_TABLES_ARGS="compare OUT_DIR REPORT_DIR" lake env lean JoltTests/LookupTables/Run.lean
LOOKUP_TABLES_ARGS="mutation OUT_DIR" lake env lean JoltTests/LookupTables/Run.lean
```

`OUT_DIR` holds the emitter's `lookup_vectors.jsonl` and `lookup_summary.json`.

* `compare` checks every vector and writes `REPORT_DIR/lookup-mismatches.jsonl`
  (one JSON line per disagreeing vector or unknown table name) and
  `REPORT_DIR/lookup-summary.txt` (counts per table and the name gaps).
  It fails on a value mismatch, on a vector whose table has no Lean constructor,
  on a Rust variant with no Lean constructor, on a Lean constructor with no
  Rust variant, and when the vectors do not match the summary's counts (in
  total, and per table for edge and random vectors).
* `mutation` corrupts the vectors in memory and runs the same comparison
  (`compareVectors`) on them: it adds one to the value of the first vector of
  every table (modulo 2^64), renames one vector's table, drops the last vector,
  and keeps only the first vector of each table. Each corruption must be
  reported and counted as a failure.
-/

open Lean

namespace LookupTables

deriving instance Repr for LookupTableKind

/-- Every Lean table, in constructor order. `LookupTableKind.ctorIdx_lt`
(`JoltConstraints/witness.lean`) bounds the constructor index by 55. -/
def leanKinds : List LookupTableKind :=
  (List.range 55).map LookupTableKind.ofNat

/-- The constructor name, which is Jolt's `LookupTableKind` variant name by
construction (for example `VirtualXORROTW16`). -/
def kindName (t : LookupTableKind) : String :=
  ((toString (repr t)).splitOn ".").getLast!

/-- Lean's tables by name. -/
def kindByName : Std.HashMap String LookupTableKind :=
  leanKinds.foldl (fun m t => m.insert (kindName t) t) {}

/-- One line of `lookup_vectors.jsonl`. -/
structure Vector where
  table : String
  index : Nat
  value : Nat
  cls : String
  deriving Inhabited

def natField (j : Json) (key : String) (bound : Nat) : Except String Nat := do
  let s ← j.getObjValAs? String key
  let some n := s.toNat? | throw s!"{key}: not a decimal natural number: {s}"
  unless n < bound do throw s!"{key}: {n} is out of range"
  pure n

def parseVector (line : String) : Except String Vector := do
  let j ← Json.parse line
  pure { table := ← j.getObjValAs? String "table"
         index := ← natField j "index" (2 ^ 128)
         value := ← natField j "value" (2 ^ 64)
         cls := ← j.getObjValAs? String "class" }

/-- The outcome of checking one vector. -/
inductive Outcome where
  | agree
  | mismatch (lean : Nat)
  | unknownTable

/-- Evaluate the twin at the vector's table and index. -/
def check (v : Vector) : Outcome :=
  match kindByName[v.table]? with
  | none => .unknownTable
  | some t =>
    if h : v.index < 2 ^ 128 then
      let lean := lookupTableEntryNat t ⟨v.index, h⟩
      if lean == v.value then .agree else .mismatch lean
    else .unknownTable

def mismatchJson (v : Vector) (o : Outcome) : Json :=
  match o with
  | .mismatch lean =>
    Json.mkObj [("table", v.table), ("index", toString v.index), ("class", v.cls),
      ("rust", toString v.value), ("lean", toString lean)]
  | _ =>
    Json.mkObj [("table", v.table), ("index", toString v.index), ("class", v.cls),
      ("rust", toString v.value), ("error", "no Lean LookupTableKind constructor")]

def readVectors (path : String) : IO (Array Vector) := do
  let h ← IO.FS.Handle.mk path .read
  let mut out := #[]
  repeat
    let line ← h.getLine
    if line.isEmpty then break
    let line := line.trimAsciiEnd.toString
    if line.isEmpty then continue
    match parseVector line with
    | .ok v => out := out.push v
    | .error e => throw <| IO.userError s!"{path}: {e}: {line}"
  return out

/-- What the emitter says it wrote, from `lookup_summary.json`. -/
structure Summary where
  rustVariants : List String
  /-- Per table: the number of edge vectors and of random vectors. -/
  counts : Std.HashMap String (Nat × Nat)
  total : Nat
  randomPerTable : Nat

def readSummary (outDir : String) : IO Summary := do
  let text ← IO.FS.readFile s!"{outDir}/lookup_summary.json"
  let j ← IO.ofExcept (Json.parse text)
  let rust ← IO.ofExcept (j.getObjValAs? (Array String) "rust_variants")
  let total ← IO.ofExcept (j.getObjValAs? Nat "total_vectors")
  let randomPerTable ← IO.ofExcept (j.getObjValAs? Nat "random_per_table")
  let countsJson ← IO.ofExcept (j.getObjVal? "counts")
  let mut counts : Std.HashMap String (Nat × Nat) := {}
  for name in rust do
    let c ← IO.ofExcept (countsJson.getObjVal? name)
    let edge ← IO.ofExcept (c.getObjValAs? Nat "edge")
    let random ← IO.ofExcept (c.getObjValAs? Nat "random")
    counts := counts.insert name (edge, random)
  return { rustVariants := rust.toList, counts, total, randomPerTable }

/-- Per-table counts. -/
structure Counts where
  checked : Nat := 0
  agree : Nat := 0
  edge : Nat := 0
  random : Nat := 0

/-- The result of comparing a set of vectors. -/
structure Result where
  mismatches : Nat
  unknown : Nat
  /-- Tables with at least one value mismatch. -/
  mismatchedTables : List String
  /-- Disagreements between the vectors and the emitter's summary: a total or
  per-table count that differs, a table with no edge vectors or fewer random
  vectors than requested, or a vector of an unknown class. -/
  coverageErrors : Array String
  rustOnly : List String
  leanOnly : List String
  bad : Array Json
  text : String

def Result.failures (r : Result) : Nat :=
  r.mismatches + r.unknown + r.coverageErrors.size + r.rustOnly.length + r.leanOnly.length

/-- Compare every vector with the twin and the vector counts with the emitter's
summary. `compare` and `mutation` both go through this function. -/
def compareVectors (vectors : Array Vector) (sum : Summary) : Result := Id.run do
  let mut counts : Std.HashMap String Counts := {}
  let mut bad : Array Json := #[]
  let mut mismatches := 0
  let mut unknown := 0
  let mut mismatchedTables : List String := []
  let mut coverage : Array String := #[]
  for v in vectors do
    let o := check v
    unless v.cls == "edge" || v.cls == "random" do
      coverage := coverage.push s!"{v.table} index {v.index}: unknown class {v.cls}"
    let c := counts.getD v.table {}
    let c := { c with checked := c.checked + 1,
                      edge := c.edge + (if v.cls == "edge" then 1 else 0),
                      random := c.random + (if v.cls == "random" then 1 else 0) }
    match o with
    | .agree => counts := counts.insert v.table { c with agree := c.agree + 1 }
    | .mismatch _ =>
      counts := counts.insert v.table c
      mismatches := mismatches + 1
      unless mismatchedTables.contains v.table do
        mismatchedTables := v.table :: mismatchedTables
      bad := bad.push (mismatchJson v o)
    | .unknownTable =>
      counts := counts.insert v.table c
      unknown := unknown + 1
      bad := bad.push (mismatchJson v o)
  let rust := sum.rustVariants
  let lean := leanKinds.map kindName
  let rustOnly := rust.filter (!lean.contains ·)
  let leanOnly := lean.filter (!rust.contains ·)
  if vectors.size != sum.total then
    coverage := coverage.push s!"{vectors.size} vectors, but the summary reports {sum.total}"
  for name in rust do
    let c := counts.getD name {}
    let (edge, random) := sum.counts.getD name (0, 0)
    if c.edge != edge || c.random != random then
      coverage := coverage.push
        s!"{name}: {c.edge} edge + {c.random} random vectors, but the summary reports {edge} + {random}"
    if c.edge == 0 then coverage := coverage.push s!"{name}: no edge vectors"
    if c.random < sum.randomPerTable then
      coverage := coverage.push
        s!"{name}: {c.random} random vectors, fewer than the requested {sum.randomPerTable}"
  let mut s := s!"lookup-tables: {vectors.size} vectors, {mismatches} value mismatches, " ++
    s!"{unknown} vectors with no Lean table, {coverage.size} coverage errors\n"
  s := s ++ s!"Rust variants: {rust.length}; Lean constructors: {lean.length}\n"
  s := s ++ s!"Rust variants with no Lean constructor: {rustOnly}\n"
  s := s ++ s!"Lean constructors with no Rust variant: {leanOnly}\n"
  s := s ++ "per table (checked, agreeing; edge + random):\n"
  for name in rust ++ leanOnly do
    let c := counts.getD name {}
    s := s ++ s!"  {name}: {c.checked} checked, {c.agree} agree ({c.edge} edge + {c.random} random)\n"
  for e in coverage.toList.take 50 do
    s := s ++ s!"  coverage error: {e}\n"
  for j in bad.toList.take 50 do
    s := s ++ s!"  mismatch: {j.compress}\n"
  return { mismatches, unknown, mismatchedTables, coverageErrors := coverage, rustOnly, leanOnly,
           bad, text := s }

def runCompare (outDir reportDir : String) : IO UInt32 := do
  IO.FS.createDirAll reportDir
  let start ← IO.monoMsNow
  let vectors ← readVectors s!"{outDir}/lookup_vectors.jsonl"
  let sum ← readSummary outDir
  let parsed ← IO.monoMsNow
  let r := compareVectors vectors sum
  let failures := r.failures
  let evaluated ← IO.monoMsNow
  IO.FS.withFile s!"{reportDir}/lookup-mismatches.jsonl" .write fun h => do
    for j in r.bad do h.putStrLn j.compress
  let s := r.text ++ s!"time: {parsed - start} ms reading, {evaluated - parsed} ms evaluating\n"
  IO.FS.writeFile s!"{reportDir}/lookup-summary.txt" s
  IO.println s
  IO.println s!"lookup-tables: {failures} failures; details in {reportDir}/lookup-mismatches.jsonl"
  return if failures == 0 then 0 else 1

/-- Corrupt the vectors in memory and check that `compareVectors`, the function
`compare` uses, reports each corruption and counts it as a failure. -/
def runMutation (outDir : String) : IO UInt32 := do
  let vectors ← readVectors s!"{outDir}/lookup_vectors.jsonl"
  let sum ← readSummary outDir
  let rust := sum.rustVariants
  -- The position of the first vector of each table.
  let mut first : Std.HashMap String Nat := {}
  for i in [0:vectors.size] do
    let v := vectors[i]!
    unless first.contains v.table do first := first.insert v.table i
  let missing := rust.filter (!first.contains ·)
  -- One value corrupted in every table at once.
  let corrupted := first.fold (init := vectors) fun acc _ i =>
    acc.modify i fun v => { v with value := (v.value + 1) % 2 ^ 64 }
  let rc := compareVectors corrupted sum
  let valuesOk := missing.isEmpty && rc.mismatches == rust.length &&
    rust.all rc.mismatchedTables.contains && rc.failures > 0
  IO.println s!"  value corrupted in each of {rust.length} tables: {rc.mismatches} mismatches in {rc.mismatchedTables.length} tables, {if valuesOk then "detected" else "MISSED"}"
  -- One vector's table renamed.
  let renamed := vectors.modify 0 fun v => { v with table := v.table ++ "Renamed" }
  let rr := compareVectors renamed sum
  let renamedOk := rr.unknown == 1 && rr.failures > 0
  IO.println s!"  table renamed: {if renamedOk then "detected" else "MISSED"}"
  -- The last vector dropped.
  let rd := compareVectors vectors.pop sum
  let droppedOk := rd.coverageErrors.size > 0 && rd.failures > 0
  IO.println s!"  last vector dropped: {if droppedOk then "detected" else "MISSED"}"
  -- Only the first vector of each table kept.
  let firsts := (first.toList.map (·.2)).toArray.qsort (· < ·) |>.map (vectors[·]!)
  let rf := compareVectors firsts sum
  let firstsOk := rf.coverageErrors.size > 0 && rf.failures > 0
  IO.println s!"  only the first vector of each table kept: {if firstsOk then "detected" else "MISSED"}"
  let ok := valuesOk && renamedOk && droppedOk && firstsOk
  IO.println (if ok then "mutation check: every corruption detected" else "mutation check: FAILED")
  return if ok then 0 else 1

/-- The command line, called by `Run.lean`. There is no executable because
`LeanRV64D.lean` declares a root `main`, which any executable importing the
model would inherit (see `lakefile.toml`). -/
def cli (args : List String) : IO UInt32 := do
  match args with
  | ["compare", out, report] => runCompare out report
  | ["mutation", out] => runMutation out
  | _ =>
    IO.eprintln "usage: LOOKUP_TABLES_ARGS='compare OUT_DIR REPORT_DIR | mutation OUT_DIR'"
    return 2

end LookupTables
