import JoltTests.InlineKat.Layout
import Lean.Data.Json.Parser

/-!
# `inline-kat`: Jolt's hash inlines against their specifications

`lake exe inline-kat CASES.json` reads the cases that `scripts/inline-kat` recorded from Jolt's
tracer and checks each one against the specifications in `JoltBytecode/Inlines`.

For each case the JSON holds the bytes at `rs1` and `rs2` before and after the inline ran.
`JoltTests.InlineKat.Layout` turns the bytes before into the specification's arguments and its
result back into bytes. A judged case passes when:

- the bytes the tracer left at `rs1` equal the specification's result;
- the bytes at `rs2` did not change;
- the bytes at `rs1` start with the published answer, when the case has one;
- the registers `x1` to `x31` did not change.

The program prints one line per case and a summary per inline, and exits with status 1 if any
judged case fails. Cases marked as not judged (BLAKE2 with a final-block flag other than 0 or 1)
are reported but cannot fail.
-/

open Lean JoltTests.InlineKat JoltSpec

namespace JoltTests.InlineKat.Main

/-- What the BLAKE2 builder computes for any flag value: the model's compression with
`0 - flag` XORed into word 14 of the work vector.

This is not a specification. With flag 1 the mask is all ones and this is
`Blake2b.Spec.compress 12 h m t true`, and with flag 0 it is the same with `false`. The program
uses it only to describe the informational cases, whose flags the specification does not cover. -/
def blake2WithMask (h : Vector Blake2b.Spec.Word 8) (m : Vector Blake2b.Spec.Word 16)
    (t : BitVec 128) (mask : Blake2b.Spec.Word) : Vector Blake2b.Spec.Word 8 :=
  let v : Vector Blake2b.Spec.Word 16 := h ++ Blake2b.IV.map UInt64.toBitVec
  let v := v.set 12 (v[12] ^^^ t.setWidth 64)
  let v := v.set 13 (v[13] ^^^ (t >>> 64).setWidth 64)
  let v := v.set 14 (v[14] ^^^ mask)
  let v := Blake2b.Spec.rounds m v 12
  Vector.ofFn fun i => h[i] ^^^ v[i] ^^^ v[i.val + 8]

/-- The size of the words the state is made of: 4 bytes for SHA-256, 8 for the others. -/
def wordSize (inline : String) : Nat :=
  if inline.startsWith "SHA256" then 4 else 8

/-- The first word at which two byte strings differ, as `word i: tracer 0x.., spec 0x..`,
reading each word little-endian as the inline stores it. -/
def firstDifference (inline : String) (tracer spec : ByteArray) : String :=
  let n := wordSize inline
  let words := (max tracer.size spec.size + n - 1) / n
  match (List.range words).find? (fun i => leNat tracer (n * i) n ≠ leNat spec (n * i) n) with
  | some i =>
    let hex (v : Nat) := "0x" ++ toHex ⟨(leBytes v n).reverse.toArray⟩
    s!"word {i}: tracer {hex (leNat tracer (n * i) n)}, spec {hex (leNat spec (n * i) n)}"
  | none => s!"sizes differ: tracer {tracer.size} bytes, spec {spec.size} bytes"

/-- One case of the JSON file. -/
structure Case where
  inline : String
  name : String
  group : String
  judged : Bool
  rs1Before : ByteArray
  rs2Before : ByteArray
  rs1After : ByteArray
  rs2After : ByteArray
  rows : Nat
  registersPreserved : Bool
  expected : Option (ByteArray × String)

/-- Read a hexadecimal field. -/
def hexField (j : Json) (key : String) : Except String ByteArray := do
  let s ← j.getObjValAs? String key
  match ofHex? s with
  | some b => pure b
  | none => throw s!"field {key} is not hexadecimal"

/-- Read one case. -/
def Case.ofJson (j : Json) : Except String Case := do
  let expected ← match j.getObjVal? "expected_rs1_after_prefix" with
    | .ok _ => do
      let bytes ← hexField j "expected_rs1_after_prefix"
      let source ← j.getObjValAs? String "expected_source"
      pure (some (bytes, source))
    | .error _ => pure none
  return {
    inline := ← j.getObjValAs? String "inline"
    name := ← j.getObjValAs? String "name"
    group := ← j.getObjValAs? String "group"
    judged := ← j.getObjValAs? Bool "judged"
    rs1Before := ← hexField j "rs1_before"
    rs2Before := ← hexField j "rs2_before"
    rs1After := ← hexField j "rs1_after"
    rs2After := ← hexField j "rs2_after"
    rows := ← j.getObjValAs? Nat "rows"
    registersPreserved := ← j.getObjValAs? Bool "registers_preserved"
    expected
  }

/-- The specification's result at `rs1` for a judged case, or why there is none. -/
def specResult (c : Case) : Except String ByteArray :=
  match c.inline with
  | "SHA256" => .ok (sha256Result c.rs1Before c.rs2Before)
  | "SHA256_INIT" => .ok (sha256InitResult c.rs2Before)
  | "KECCAK256" => .ok (keccak256Result c.rs1Before)
  | "KECCAK256_ABSORB_PERMUTE" => .ok (keccak256AbsorbResult c.rs1Before c.rs2Before)
  | "BLAKE2" =>
    match blake2Flag c.rs2Before with
    | 0 => .ok (blake2Result c.rs1Before c.rs2Before false)
    | 1 => .ok (blake2Result c.rs1Before c.rs2Before true)
    | f => .error s!"final-block flag {f} is outside the specification"
  | other => .error s!"unknown inline {other}"

/-- Whether `pre` is a prefix of `bytes`. -/
def isPrefix (pre bytes : ByteArray) : Bool :=
  pre.size ≤ bytes.size && (List.range pre.size).all fun i => pre[i]! == bytes[i]!

/-- The failed checks of a judged case; empty when it passes. -/
def failures (c : Case) : List String := Id.run do
  let mut out := []
  match specResult c with
  | .error e => out := out ++ [e]
  | .ok spec =>
    if spec.data != c.rs1After.data then
      out := out ++ [s!"rs1 differs from the specification at {firstDifference c.inline c.rs1After spec}"]
  if c.rs2After.data != c.rs2Before.data then
    out := out ++ ["the bytes at rs2 changed"]
  if let some (pre, source) := c.expected then
    if !isPrefix pre c.rs1After then
      out := out ++ [s!"rs1 does not start with the published answer ({source})"]
  if !c.registersPreserved then
    out := out ++ ["a register among x1 to x31 changed"]
  return out

/-- A description of an informational BLAKE2 case: which computations the tracer's result
matches. -/
def describeInformational (c : Case) : String :=
  if c.inline != "BLAKE2" then "not judged" else
  let h := blake2Words 8 c.rs1Before 0
  let m := blake2Words 16 c.rs2Before 0
  let t := BitVec.ofNat 128 (blake2Counter c.rs2Before)
  let f := blake2Flag c.rs2Before
  let same (r : ByteArray) := r.data == c.rs1After.data
  let asFinal := same (blake2Result c.rs1Before c.rs2Before true)
  let asNotFinal := same (blake2Result c.rs1Before c.rs2Before false)
  let asMask := same (blake2Bytes (blake2WithMask h m t (0 - BitVec.ofNat 64 f)))
  s!"flag {f}: equals spec with f = true: {asFinal}; with f = false: {asNotFinal}; " ++
    s!"with word 14 XORed by 0 - flag: {asMask}"

/-- Per-inline counts. -/
structure Tally where
  pass : Nat := 0
  fail : Nat := 0
  info : Nat := 0
  rows : List Nat := []

end JoltTests.InlineKat.Main

open JoltTests.InlineKat.Main in
def main (args : List String) : IO UInt32 := do
  let [path] := args
    | IO.eprintln "usage: lake exe inline-kat CASES.json"; return 2
  let text ← IO.FS.readFile path
  let json ← IO.ofExcept (Json.parse text)
  let commit := (json.getObjValAs? String "jolt_commit").toOption.getD "unknown"
  IO.println s!"inline-kat: cases from Jolt commit {commit}"
  let inlines ← IO.ofExcept (json.getObjValAs? (Array Json) "inlines")
  let mut sequenceRows : List (String × Nat) := []
  for i in inlines do
    let name ← IO.ofExcept (i.getObjValAs? String "name")
    let rows ← IO.ofExcept (i.getObjValAs? Nat "sequence_rows")
    sequenceRows := sequenceRows ++ [(name, rows)]
  let cases ← IO.ofExcept (json.getObjValAs? (Array Json) "cases")
  let mut tallies : List (String × Tally) := sequenceRows.map fun (n, _) => (n, {})
  let mut anyFailure := false
  for j in cases do
    let c ← IO.ofExcept (Case.ofJson j)
    let mut tally := (tallies.lookup c.inline).getD {}
    if c.rows ∉ tally.rows then
      tally := { tally with rows := tally.rows ++ [c.rows] }
    if !c.judged then
      IO.println s!"INFO {c.inline} | {c.name} | {describeInformational c}"
      tally := { tally with info := tally.info + 1 }
    else
      match failures c with
      | [] =>
        IO.println s!"PASS {c.inline} | {c.name}"
        tally := { tally with pass := tally.pass + 1 }
      | fs =>
        anyFailure := true
        IO.println s!"FAIL {c.inline} | {c.name} | {"; ".intercalate fs}"
        tally := { tally with fail := tally.fail + 1 }
    tallies := (tallies.filter (·.1 != c.inline)) ++ [(c.inline, tally)]
  IO.println "inline-kat: summary"
  for (name, seqRows) in sequenceRows do
    let t := (tallies.lookup name).getD {}
    IO.println s!"  {name}: {t.pass} passed, {t.fail} failed, {t.info} informational; \
      rows per call {t.rows} (expansion length {seqRows})"
  return if anyFailure then 1 else 0
