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
  on a Rust variant with no Lean constructor and on a Lean constructor with no
  Rust variant.
* `mutation` adds one to the value of the first vector of each table (modulo
  2^64), in memory, and checks that the comparison reports each corruption.
  It also renames one vector's table to an unknown name and checks that the
  vector is flagged.
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

/-- The Rust variant names in `lookup_summary.json`. -/
def rustVariants (outDir : String) : IO (List String) := do
  let text ← IO.FS.readFile s!"{outDir}/lookup_summary.json"
  let j ← IO.ofExcept (Json.parse text)
  let arr ← IO.ofExcept (j.getObjValAs? (Array String) "rust_variants")
  return arr.toList

/-- Per-table counts. -/
structure Counts where
  checked : Nat := 0
  agree : Nat := 0
  edge : Nat := 0
  random : Nat := 0

def runCompare (outDir reportDir : String) : IO UInt32 := do
  IO.FS.createDirAll reportDir
  let start ← IO.monoMsNow
  let vectors ← readVectors s!"{outDir}/lookup_vectors.jsonl"
  let parsed ← IO.monoMsNow
  let mut counts : Std.HashMap String Counts := {}
  let mut bad : Array Json := #[]
  let mut mismatches := 0
  let mut unknown := 0
  for v in vectors do
    let o := check v
    let c := counts.getD v.table {}
    let c := { c with checked := c.checked + 1,
                      edge := c.edge + (if v.cls == "edge" then 1 else 0),
                      random := c.random + (if v.cls == "random" then 1 else 0) }
    match o with
    | .agree => counts := counts.insert v.table { c with agree := c.agree + 1 }
    | .mismatch _ =>
      counts := counts.insert v.table c
      mismatches := mismatches + 1
      bad := bad.push (mismatchJson v o)
    | .unknownTable =>
      counts := counts.insert v.table c
      unknown := unknown + 1
      bad := bad.push (mismatchJson v o)
  let evaluated ← IO.monoMsNow
  let rust ← rustVariants outDir
  let lean := leanKinds.map kindName
  let rustOnly := rust.filter (!lean.contains ·)
  let leanOnly := lean.filter (!rust.contains ·)
  IO.FS.withFile s!"{reportDir}/lookup-mismatches.jsonl" .write fun h => do
    for j in bad do h.putStrLn j.compress
  let mut s := s!"lookup-tables: {vectors.size} vectors, {mismatches} value mismatches, " ++
    s!"{unknown} vectors with no Lean table\n"
  s := s ++ s!"Rust variants: {rust.length}; Lean constructors: {lean.length}\n"
  s := s ++ s!"Rust variants with no Lean constructor: {rustOnly}\n"
  s := s ++ s!"Lean constructors with no Rust variant: {leanOnly}\n"
  s := s ++ "per table (checked, agreeing; edge + random):\n"
  for name in rust ++ leanOnly do
    let c := counts.getD name {}
    s := s ++ s!"  {name}: {c.checked} checked, {c.agree} agree ({c.edge} edge + {c.random} random)\n"
  for j in bad.toList.take 50 do
    s := s ++ s!"  mismatch: {j.compress}\n"
  s := s ++ s!"time: {parsed - start} ms reading, {evaluated - parsed} ms evaluating\n"
  IO.FS.writeFile s!"{reportDir}/lookup-summary.txt" s
  IO.println s
  let failures := mismatches + unknown + rustOnly.length + leanOnly.length
  IO.println s!"lookup-tables: {failures} failures; details in {reportDir}/lookup-mismatches.jsonl"
  return if failures == 0 then 0 else 1

/-- Corrupt one vector per table in memory and check that each corruption is
reported. -/
def runMutation (outDir : String) : IO UInt32 := do
  let vectors ← readVectors s!"{outDir}/lookup_vectors.jsonl"
  let mut seen : Std.HashMap String Vector := {}
  for v in vectors do
    unless seen.contains v.table do seen := seen.insert v.table v
  let rust ← rustVariants outDir
  let mut ok := true
  let mut detected := 0
  for name in rust do
    match seen[name]? with
    | none =>
      IO.println s!"  {name}: no vector to corrupt"
      ok := false
    | some v =>
      let v' := { v with value := (v.value + 1) % 2 ^ 64 }
      if check v' matches .agree then
        IO.println s!"  {name}: value corruption MISSED at index {v.index}"
        ok := false
      else detected := detected + 1
  let renamed := (vectors[0]?).any fun v =>
    check { v with table := v.table ++ "Renamed" } matches .unknownTable
  IO.println s!"  value corrupted in {detected} of {rust.length} tables and detected"
  IO.println s!"  table renamed: {if renamed then "detected" else "MISSED"}"
  ok := ok && renamed
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
