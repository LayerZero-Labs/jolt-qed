import Std.Data.HashMap
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

/-- The mutations: one per field kind, each on one row. -/
def mutations : List (String × Nat × String × (Json → Json)) :=
  [ ("kind", 0, "kind", fun _ => Json.str "ADD"),
    ("rs1", 1, "rs1", bumpNat),
    ("rd", 2, "rd", bumpNat),
    ("imm", 3, "imm", bumpIntString),
    ("vsr", 4, "vsr", bumpNat),
    ("first", 0, "first", flipBool),
    ("compressed", 5, "compressed", flipBool),
    ("circuit_flags", 6, "circuit_flags", dropFirstFlag),
    ("instruction_flags", 7, "instruction_flags", dropFirstFlag),
    ("lookup_table", 8, "lookup_table", fun _ => Json.str "Xor"),
    ("raf", 9, "raf", flipBool) ]

/-- Applies every mutation to one record and checks that `cmp` reports each at
the mutated row and field; the unmutated record must give no mismatch. -/
def mutationCheck (label : String) (j : Json) (cmp : RecordInfo → List Mismatch) : IO Bool := do
  let base ← IO.ofExcept (RecordInfo.ofJson j)
  let clean := cmp base
  IO.println s!"{label}: {base.case}: unmutated record gives {clean.length} mismatches"
  let mut ok := clean.isEmpty
  for (name, row, key, f) in mutations do
    let j' ← IO.ofExcept (setRowField j row key f)
    let r' ← IO.ofExcept (RecordInfo.ofJson j')
    let ms := cmp r'
    let caught := ms.any (fun m => m.row == some row && m.field == key)
    IO.println s!"  {name} on row {row}: {if caught then "detected" else "NOT DETECTED"} ({ms.length} mismatches)"
    ok := ok && caught
  return ok

end ExpansionParity
