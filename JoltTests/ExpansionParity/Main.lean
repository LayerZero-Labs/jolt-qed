import JoltTests.ExpansionParity.Report

/-!
# expansion-parity: the T1 comparator

Usage (from the repository root, after `lake build JoltTests.ExpansionParity.Main`):

```
EXPANSION_PARITY_ARGS="t1 ROWS.jsonl OUT_DIR" lake env lean JoltTests/ExpansionParity/Run.lean
EXPANSION_PARITY_ARGS="mutation ROWS.jsonl" lake env lean JoltTests/ExpansionParity/Run.lean
```

The arguments travel in an environment variable because `Run.lean` runs the
comparison with `#eval` (see `cli` below for why there is no executable).

`ROWS.jsonl` is the driver's `rows.jsonl` (`scripts/expansion-parity/README.md`).

* `t1` compares every non-inline record with `expand_instruction` and
  `metadata.lean`, and writes `OUT_DIR/t1-mismatches.jsonl` and
  `OUT_DIR/t1-summary.txt`.
* `mutation` corrupts one field of one row of a T1 record, once per field
  kind, and checks that the comparison reports each corruption.

`Run.lean` fails (and `lean` exits with 1) when a mode finds a disagreement.
-/

open Lean

namespace ExpansionParity

def runT1 (rowsPath outDir : String) : IO UInt32 := do
  IO.FS.createDirAll outDir
  let lines ← readLines rowsPath
  let mut all : Array Mismatch := #[]
  let mut summary : Summary := {}
  let mut perGroup : Std.HashMap String Nat := {}
  let mut agreeGroup : Std.HashMap String Nat := {}
  let mut rejectHow : Std.HashMap String Nat := {}
  let mut inlineSkipped := 0
  for line in lines do
    let r ← parseRecord line
    match compareT1 r with
    | .inline => inlineSkipped := inlineSkipped + 1
    | .bothReject how =>
        perGroup := bump perGroup r.group
        agreeGroup := bump agreeGroup r.group
        rejectHow := bump rejectHow s!"{r.source.kind}: Rust {r.error.getD "?"}; Lean: {how}"
    | .compared ms =>
        perGroup := bump perGroup r.group
        if ms.isEmpty then agreeGroup := bump agreeGroup r.group
        for m in ms do
          all := all.push m
          summary := summary.add m
  writeMismatches (outDir ++ "/t1-mismatches.jsonl") all
  let mismatched := (all.map (fun m => (m.case, m.allocator))).toList.eraseDups.length
  let text :=
    s!"T1 expansion parity: {rowsPath}\n" ++
    s!"records compared per group: {renderCounts perGroup}\n" ++
    s!"records that agree per group: {renderCounts agreeGroup}\n" ++
    s!"inline records left to the inline round trip: {inlineSkipped}\n" ++
    s!"records with a disagreement: {mismatched}; field mismatches: {all.size}\n" ++
    s!"Lean source kinds with no Rust decoder kind: {leanOnlySourceKinds}\n\n" ++
    "Rejected by both sides:\n" ++
    String.join ((rejectHow.toList.toArray.qsort (fun a b => a.1 < b.1)).toList.map
      fun (k, n) => s!"- {k} ({n} records)\n") ++
    "\nDisagreements by cause:\n" ++ summary.render
  IO.FS.writeFile (outDir ++ "/t1-summary.txt") text
  IO.println text
  return if all.isEmpty then 0 else 1

/-- The mutation check on the first T1 record with at least ten rows. -/
def runMutation (rowsPath : String) : IO UInt32 := do
  let mut t1Rec : Option Json := none
  for line in ← readLines rowsPath do
    let j ← IO.ofExcept (Json.parse line)
    let r ← IO.ofExcept (RecordInfo.ofJson j)
    if r.source.kind != "Inline" && (r.rows.map List.length).getD 0 ≥ 10 then
      t1Rec := some j
      break
  let some tj := t1Rec | throw <| IO.userError "no T1 record with 10 rows"
  let t1cmp (r : RecordInfo) : List Mismatch :=
    match compareT1 r with
    | .compared ms => ms
    | _ => []
  let ok ← mutationCheck "t1" tj t1cmp
  IO.println (if ok then "mutation check: every corruption detected" else "mutation check: FAILED")
  return if ok then 0 else 1

/-- The command line. `LeanRV64D.lean` declares a root `main` (the Sail model's
entry point), so no executable that imports the model can declare its own;
`Run.lean` calls this function instead. -/
def cli (args : List String) : IO UInt32 := do
  match args with
  | ["t1", rows, out] => runT1 rows out
  | ["mutation", rows] => runMutation rows
  | _ =>
    IO.eprintln "usage: EXPANSION_PARITY_ARGS='t1 ROWS OUT | mutation ROWS'"
    return 2

end ExpansionParity
