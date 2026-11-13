import Std.Data.HashMap
import Std.Data.HashSet
import JoltTests.ExpansionParity.Compare

/-!
# Summaries, file input and output, and the mutation check

Shared by the T1 comparator (`Main.lean`) and the inline round trip
(`RoundTrip.lean`).
-/

open Lean

namespace ExpansionParity

/-- Mismatches grouped by cause, with the number of records and up to three
example records per cause. -/
structure Summary where
  counts : Std.HashMap String Nat := {}
  records : Std.HashMap String (Array String) := {}
  sourceKinds : Std.HashMap String (Array String) := {}
  examples : Std.HashMap String (Array Mismatch) := {}

def Summary.add (s : Summary) (m : Mismatch) : Summary :=
  let recs := s.records.getD m.cause #[]
  let kinds := s.sourceKinds.getD m.cause #[]
  let exs := s.examples.getD m.cause #[]
  { counts := s.counts.insert m.cause (s.counts.getD m.cause 0 + 1)
    records := s.records.insert m.cause (if recs.contains m.case then recs else recs.push m.case)
    sourceKinds := s.sourceKinds.insert m.cause
      (if kinds.contains m.sourceKind then kinds else kinds.push m.sourceKind)
    examples := s.examples.insert m.cause (if exs.size < 3 then exs.push m else exs) }

def Summary.render (s : Summary) : String := Id.run do
  let causes := s.counts.toList.toArray.qsort (fun a b => a.2 > b.2 || (a.2 == b.2 && a.1 < b.1))
  let mut out := ""
  for (cause, n) in causes do
    let recs := s.records.getD cause #[]
    let kinds := s.sourceKinds.getD cause #[]
    out := out ++ s!"- {cause}: {n} field mismatches in {recs.size} records; source kinds {kinds.toList}\n"
    for m in s.examples.getD cause #[] do
      out := out ++ s!"    e.g. {m.case} [{m.allocator}] row {showOpt m.row}: {m.field} Rust {m.rust} / Lean {m.lean}\n"
  return out

def readLines (path : String) : IO (Array String) := do
  let h ← IO.FS.Handle.mk path .read
  let mut lines := #[]
  repeat
    let line ← h.getLine
    if line.isEmpty then break
    let line := line.trimAsciiEnd.toString
    if !line.isEmpty then lines := lines.push line
  return lines

def parseRecord (line : String) : IO RecordInfo := do
  match Json.parse line >>= RecordInfo.ofJson with
  | .ok r => pure r
  | .error e => throw <| IO.userError s!"cannot read record: {e}"

def bump (m : Std.HashMap String Nat) (k : String) : Std.HashMap String Nat :=
  m.insert k (m.getD k 0 + 1)

def renderCounts (m : Std.HashMap String Nat) : String :=
  let l := m.toList.toArray.qsort (fun a b => a.1 < b.1)
  ", ".intercalate (l.toList.map fun (k, v) => s!"{k} {v}")

def writeMismatches (path : String) (ms : Array Mismatch) : IO Unit := do
  IO.FS.withFile path .write fun h => do
    for m in ms do h.putStrLn m.toJson.compress

def setRowField (record : Json) (row : Nat) (key : String) (f : Json → Json) :
    Except String Json := do
  let result ← record.getObjVal? "result"
  let rows ← (← result.getObjVal? "rows").getArr?
  let some r := rows[row]? | throw s!"no row {row}"
  let r' := r.setObjVal! key (f (← r.getObjVal? key))
  let result' := result.setObjVal! "rows" (Json.arr (rows.set! row r'))
  pure (record.setObjVal! "result" result')

def bumpNat (j : Json) : Json :=
  match j.getNat? with
  | .ok n => Json.num ((n + 1 : Nat) : Int)
  | .error _ => Json.num (1 : Int)

def bumpIntString (j : Json) : Json :=
  match j.getStr? with
  | .ok s => Json.str (toString ((s.toInt?.getD 0) + 1))
  | .error _ => j

def dropFirstFlag (j : Json) : Json :=
  match j.getArr? with
  | .ok a => Json.arr (a.extract 1 a.size)
  | .error _ => j

def flipBool (j : Json) : Json :=
  match j.getBool? with
  | .ok b => Json.bool (!b)
  | .error _ => j

/-- The mutations: one per compared row field (13), each on one row. -/
def mutations : List (String × Nat × String × (Json → Json)) :=
  [ ("kind", 0, "kind", fun _ => Json.str "ADD"),
    ("address", 1, "address", bumpNat),
    ("rs1", 1, "rs1", bumpNat),
    ("rs2", 2, "rs2", bumpNat),
    ("rd", 2, "rd", bumpNat),
    ("imm", 3, "imm", bumpIntString),
    ("vsr", 4, "vsr", bumpNat),
    ("first", 0, "first", flipBool),
    ("compressed", 5, "compressed", flipBool),
    ("circuit_flags", 6, "circuit_flags", dropFirstFlag),
    ("instruction_flags", 7, "instruction_flags", dropFirstFlag),
    ("lookup_table", 8, "lookup_table", fun _ => Json.str "Xor"),
    ("raf", 9, "raf", flipBool) ]

/-- The mutations a row-metadata comparison must detect: the four metadata
fields of row 0. -/
def metadataMutations : List (String × Nat × String × (Json → Json)) :=
  [ ("circuit_flags", 0, "circuit_flags", dropFirstFlag),
    ("instruction_flags", 0, "instruction_flags", dropFirstFlag),
    ("lookup_table", 0, "lookup_table", fun _ => Json.str "Xor"),
    ("raf", 0, "raf", flipBool) ]

/-- Applies every mutation to one record and checks that `cmp` reports each at
the mutated row and field; the unmutated record must give no mismatch. -/
def mutationCheck (label : String) (j : Json) (cmp : RecordInfo → List Mismatch)
    (muts : List (String × Nat × String × (Json → Json)) := mutations) : IO Bool := do
  let base ← IO.ofExcept (RecordInfo.ofJson j)
  let clean := cmp base
  IO.println s!"{label}: {base.case}: unmutated record gives {clean.length} mismatches"
  let mut ok := clean.isEmpty
  for (name, row, key, f) in muts do
    let j' ← IO.ofExcept (setRowField j row key f)
    let r' ← IO.ofExcept (RecordInfo.ofJson j')
    let ms := cmp r'
    let caught := ms.any (fun m => m.row == some row && m.field == key)
    IO.println s!"  {name} on row {row}: {if caught then "detected" else "NOT DETECTED"} ({ms.length} mismatches)"
    ok := ok && caught
  return ok

/-! ## Record-level corruptions

A corrupted source kind or `result` object must not pass: the record must
either fail to read (`RecordInfo.ofJson`) or give a mismatch. -/

def setSourceKind (k : String) (j : Json) : Except String Json := do
  let src ← j.getObjVal? "source"
  pure (j.setObjVal! "source" (src.setObjVal! "kind" (Json.str k)))

def setResult (res : Json) (j : Json) : Except String Json :=
  pure (j.setObjVal! "result" res)

/-- The record's `result` with an `error` string added next to its `rows`. -/
def addError (j : Json) : Except String Json := do
  let res ← j.getObjVal? "result"
  pure (j.setObjVal! "result" (res.setObjVal! "error" (Json.str "x")))

/-- How a record fares: `none` when it passes (agrees, or both sides reject),
`some why` when it is flagged. -/
def t1Verdict (j : Json) : Option String :=
  match RecordInfo.ofJson j with
  | .error e => some s!"read error: {e}"
  | .ok r =>
      match compareT1 r with
      | .compared (m :: _) | .metadataOnly (m :: _) => some s!"mismatch: {m.cause}"
      | _ => none

/-- Applies each corruption to one record and checks that `t1Verdict` flags
it; the unmutated record must pass. -/
def recordMutationCheck (label : String) (j : Json)
    (muts : List (String × (Json → Except String Json))) : IO Bool := do
  let case := ((j.getObjVal? "case").bind Json.getStr?).toOption.getD "?"
  let clean := t1Verdict j
  IO.println s!"{label}: {case}: unmutated record {(clean.map (s!"is flagged: " ++ ·)).getD "passes"}"
  let mut ok := clean.isNone
  for (name, f) in muts do
    let v := t1Verdict (← IO.ofExcept (f j))
    IO.println s!"  {name}: {match v with | some why => s!"detected ({why})" | none => "NOT DETECTED"}"
    ok := ok && v.isSome
  return ok

/-- Corruptions of the source kind and of the `result` object. -/
def recordMutations (j : Json) : List (String × (Json → Except String Json)) :=
  let rows := ((j.getObjVal? "result").bind (·.getObjVal? "rows")).toOption
  [ ("source kind UNKNOWN_KIND", setSourceKind "UNKNOWN_KIND"),
    ("result {}", setResult (Json.mkObj [])),
    ("result with a non-string error", setResult (Json.mkObj [("error", Json.num (5 : Int))])),
    ("result with a null error", setResult (Json.mkObj [("error", Json.null)])),
    ("result with a non-array rows", setResult (Json.mkObj [("rows", Json.str "x")])) ] ++
  (if rows.isSome then [("result with both rows and error", addError)] else [])

end ExpansionParity
