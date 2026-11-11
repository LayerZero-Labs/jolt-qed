import JoltBytecode.Inlines.Secp256k1.Advice
import Lean.Data.Json

/-!
# secp256k1 advice known-answer test

`lake exe secp256k1-kat OUT.json` reads the JSON that `scripts/secp256k1-kat` writes from Jolt's
Rust code and checks:

- (a) the Lean transcriptions in `JoltBytecode/Inlines/Secp256k1/Advice.lean` return exactly
  Jolt's advice words on every input, and return `none` exactly where Jolt's code panics;
- (b) every inline run in Jolt's tracer with Jolt's advice satisfies the integer relation of
  `Spec.lean` (`MulRel` or `DivRel`) with a canonical result, and for `GLVR_ADV` stores the
  encoding of the Lean `decomposeScalar`, with sign words in `{0, 1}`, magnitudes below `2^128`
  and `k ≡ ±k1 ± λ·k2 (mod n)`; a run panics exactly when the Lean advice is `none` or violates
  the relation.

It prints one line per failing check and a summary, and exits with status 1 on any failure.
-/

open Lean JoltISA.Inlines.Secp256k1

namespace JoltTests.Secp256k1Kat

/-- Parse `0x…` or `-0x…` hexadecimal. -/
def parseHexInt (s : String) : Option Int := do
  let (neg, body) :=
    if s.startsWith "-" then (true, (s.drop 1).toString) else (false, s)
  guard (body.startsWith "0x")
  let digits := (body.drop 2).toString
  guard (!digits.isEmpty)
  let v ← digits.foldl (fun acc c => do
    let a ← acc
    let d ← if c.isDigit then some (c.toNat - '0'.toNat)
      else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
      else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
      else none
    pure (16 * a + d)) (some 0)
  pure (if neg then -(v : Int) else v)

def parseHexNat (s : String) : Option Nat := do
  let v ← parseHexInt s
  guard (0 ≤ v)
  pure v.toNat

abbrev M := ExceptT String IO

def field (j : Json) (k : String) : M Json :=
  match j.getObjVal? k with
  | .ok v => pure v
  | .error _ => throw s!"missing field {k}"

def str (j : Json) : M String :=
  match j.getStr? with
  | .ok v => pure v
  | .error e => throw e

def bool (j : Json) : M Bool :=
  match j.getBool? with
  | .ok v => pure v
  | .error e => throw e

def arr (j : Json) : M (Array Json) :=
  match j.getArr? with
  | .ok v => pure v
  | .error e => throw e

def hexNat (j : Json) : M Nat := do
  let s ← str j
  match parseHexNat s with
  | some v => pure v
  | none => throw s!"bad hex {s}"

def hexInt (j : Json) : M Int := do
  let s ← str j
  match parseHexInt s with
  | some v => pure v
  | none => throw s!"bad hex {s}"

def wordList (j : Json) : M (List (BitVec 64)) := do
  let a ← arr j
  let ns ← a.toList.mapM hexNat
  unless ns.all (· < 2 ^ 64) do throw "word out of range"
  pure (ns.map (BitVec.ofNat 64))

def limbs (j : Json) : M Limbs := do
  let ws ← wordList j
  match ws with
  | [w0, w1, w2, w3] => pure #v[w0, w1, w2, w3]
  | _ => throw s!"expected 4 words, got {ws.length}"

def toLimbs? : List (BitVec 64) → Option Limbs
  | [w0, w1, w2, w3] => some #v[w0, w1, w2, w3]
  | _ => none

def opOfName : String → Option Secp256k1Inline
  | "SECP256K1_MULQ" => some .mulq
  | "SECP256K1_SQUAREQ" => some .squareq
  | "SECP256K1_DIVQ" => some .divq
  | "SECP256K1_MULR" => some .mulr
  | "SECP256K1_SQUARER" => some .squarer
  | "SECP256K1_DIVR" => some .divr
  | "SECP256K1_GLVR_ADV" => some .glvrAdv
  | _ => none

/-- Rust's outcome: `ok` with a value, or a panic or error message. -/
def outcome (j : Json) : M (Except String Json) := do
  match j.getObjVal? "ok" with
  | .ok v => pure (.ok v)
  | .error _ =>
    match j.getObjVal? "panic", j.getObjVal? "error" with
    | .ok m, _ => pure (.error s!"panic: {m.compress}")
    | _, .ok m => pure (.error s!"error: {m.compress}")
    | _, _ => throw "outcome is neither ok, panic nor error"

structure Tally where
  checks : Nat := 0
  failures : Array String := #[]

abbrev T := StateT Tally M

def check (cond : Bool) (msg : Unit → String) : T Unit :=
  modify fun t =>
    { t with checks := t.checks + 1,
             failures := if cond then t.failures else t.failures.push (msg ()) }

def wordsStr (ws : List (BitVec 64)) : String :=
  toString (ws.map fun w => s!"0x{String.ofList (Nat.toDigits 16 w.toNat)}")

def isSquare : Secp256k1Inline → Bool
  | .squareq | .squarer => true
  | _ => false

def isDiv : Secp256k1Inline → Bool
  | .divq | .divr => true
  | _ => false

/-! ## (a) advice transcriptions -/

def checkAdviceCase (j : Json) : T Unit := do
  let name ← str (← field j "inline")
  let some op := opOfName name | throw s!"unknown inline {name}"
  let case ← str (← field j "case")
  let a ← limbs (← field j "a")
  let bj ← field j "b"
  let b ← if bj.isNull then pure (natToLimbs 0) else limbs bj
  let tag := s!"advice {name} [{case}]"
  -- Runtime words.
  let lean := joltAdvice op a b
  match ← outcome (← field j "words") with
  | .ok ws =>
    let rust ← wordList ws
    check (lean == some rust) fun _ =>
      s!"{tag}: words differ: Rust {wordsStr rust}, Lean {lean.map wordsStr}"
  | .error m =>
    check lean.isNone fun _ => s!"{tag}: Rust {m}, Lean {lean.map wordsStr}"
  -- Typed advice.
  match ← outcome (← field j "typed") with
  | .error m =>
    let leanNone := match op with
      | .mulq | .mulr => (mulqQuotientAdvice op.modulus a b).isNone
      | .squareq | .squarer => (mulqQuotientAdvice op.modulus a a).isNone
      | .divq | .divr => (mulqDivisionAdvice op.modulus a b).isNone
      | .glvrAdv => false
    check leanNone fun _ => s!"{tag}: typed advice: Rust {m}, Lean returns a value"
  | .ok t =>
    match op with
    | .mulq | .mulr | .squareq | .squarer =>
      let w ← limbs (← field t "quotient")
      let l := mulqQuotientAdvice op.modulus a (if isSquare op then a else b)
      check (l == some w) fun _ =>
        s!"{tag}: mulq_quotient_advice: Rust {wordsStr w.toList}, Lean {l.map (wordsStr ·.toList)}"
    | .divq | .divr =>
      let c ← limbs (← field t "result")
      let w ← limbs (← field t "quotient")
      let l := mulqDivisionAdvice op.modulus a b
      check (l == some (c, w)) fun _ =>
        s!"{tag}: mulq_division_advice: Rust {wordsStr c.toList} {wordsStr w.toList}, \
          Lean {l.map fun cw => (wordsStr cw.1.toList, wordsStr cw.2.toList)}"
    | .glvrAdv =>
      let s1 ← bool (← field t "k1_negative")
      let m1 ← wordList (← field t "k1")
      let s2 ← bool (← field t "k2_negative")
      let m2 ← wordList (← field t "k2")
      let mag : List (BitVec 64) → Nat := fun ws => (ws.zip (List.range ws.length)).foldl
        (fun acc (w, i) => acc + 2 ^ (64 * i) * w.toNat) 0
      let d := decomposeScalar (limbsToNat a % n : Nat)
      check (d == ((s1, mag m1), (s2, mag m2))) fun _ =>
        s!"{tag}: GlvrAdvBuilder::advice: Rust ({s1}, {mag m1}), ({s2}, {mag m2}), Lean {repr d}"

/-! ## (a) GLV on scalars -/

structure GlvMax where
  count : Nat := 0
  k1Bits : Nat := 0
  k2Bits : Nat := 0
  over128 : Nat := 0

def checkGlvCase (j : Json) : StateT GlvMax T Unit := do
  let case ← str (← field j "case")
  let k ← hexInt (← field j "k")
  let inRange ← bool (← field j "in_range")
  let rk1 ← hexInt (← field j "raw_k1")
  let rk2 ← hexInt (← field j "raw_k2")
  let tag := s!"glv [{case}]"
  let (k1, k2) := glvSplit k
  check (k1 == rk1 ∧ k2 == rk2) fun _ =>
    s!"{tag}: untruncated split: Rust ({rk1}, {rk2}), Lean ({k1}, {k2})"
  match ← outcome (← field j "decompose") with
  | .error m => check false fun _ => s!"{tag}: decompose_scalar: Rust {m}"
  | .ok t =>
    let s1 ← bool (← field t "k1_negative")
    let m1 ← wordList (← field t "k1")
    let s2 ← bool (← field t "k2_negative")
    let m2 ← wordList (← field t "k2")
    let mag : List (BitVec 64) → Nat := fun ws => (ws.zip (List.range ws.length)).foldl
      (fun acc (w, i) => acc + 2 ^ (64 * i) * w.toNat) 0
    let d := decomposeScalar k
    check (d == ((s1, mag m1), (s2, mag m2))) fun _ =>
      s!"{tag}: decompose_scalar: Rust ({s1}, {mag m1}), ({s2}, {mag m2}), Lean {repr d}"
  match ← outcome (← field j "u64s") with
  | .error m => check false fun _ => s!"{tag}: decompose_scalar_to_u64s: Rust {m}"
  | .ok t =>
    let ws ← wordList t
    let l := (decomposeScalarToU64s k).toList
    check (l == ws) fun _ =>
      s!"{tag}: decompose_scalar_to_u64s: Rust {wordsStr ws}, Lean {wordsStr l}"
  if inRange then
    -- The untruncated split recombines and fits in 128 bits.
    check ((k1 + (glvLambda : Int) * k2 - k) % (n : Int) == 0) fun _ =>
      s!"{tag}: k1 + λ·k2 ≢ k (mod n)"
    let bits : Nat → Nat := fun x => if x = 0 then 0 else Nat.log2 x + 1
    let b1 := bits k1.natAbs
    let b2 := bits k2.natAbs
    let over : Nat := if k1.natAbs < 2 ^ 128 ∧ k2.natAbs < 2 ^ 128 then 0 else 1
    modify fun g =>
      GlvMax.mk (g.count + 1) (max g.k1Bits b1) (max g.k2Bits b2) (g.over128 + over)

/-! ## (b) runs in Jolt's tracer -/

/-- Whether the rows accept these advice words, by the relations of `Spec.lean`. -/
def rowsAccept (op : Secp256k1Inline) (a b : Limbs) (ws : List (BitVec 64)) : Bool :=
  let q := op.modulus
  let av := limbsToNat a
  let bv := limbsToNat (if isSquare op then a else b)
  match op with
  | .glvrAdv => ws.length == 6
  | .divq | .divr =>
    match ws with
    | [c0, w0, c1, w1, c2, w2, c3, w3] =>
      decide (DivRel q av bv (limbsToNat #v[w0, w1, w2, w3]) (limbsToNat #v[c0, c1, c2, c3]))
    | _ => false
  | _ =>
    match toLimbs? ws with
    | some w =>
      let wv := limbsToNat w
      -- MulRel holds for some 256-bit `c` exactly when `w·q ≤ a·b < w·q + 2^256`.
      decide (wv * q ≤ av * bv) && decide (MulRel q av bv wv (av * bv - wv * q))
    | none => false

def checkRun (j : Json) : T Unit := do
  let name ← str (← field j "inline")
  let some op := opOfName name | throw s!"unknown inline {name}"
  let case ← str (← field j "case")
  let a ← limbs (← field j "a")
  let bj ← field j "b"
  let b ← if bj.isNull then pure (natToLimbs 0) else limbs bj
  let tag := s!"run {name} [{case}]"
  let q := op.modulus
  let predicted := (joltAdvice op a b).map (rowsAccept op a b) |>.getD false
  match ← outcome (← field j "outcome") with
  | .error m =>
    check (!predicted) fun _ => s!"{tag}: Jolt's tracer {m}, but Lean predicts a passing run"
  | .ok r =>
    check predicted fun _ => s!"{tag}: Jolt's tracer passes, but Lean predicts a failure"
    let advice ← wordList (← field r "advice")
    let output ← wordList (← field r "output")
    let aAfter ← limbs (← field r "a_after")
    check (joltAdvice op a b == some advice) fun _ =>
      s!"{tag}: VirtualAdvice words {wordsStr advice} differ from Lean {(joltAdvice op a b).map wordsStr}"
    check (aAfter == a) fun _ => s!"{tag}: input at rs1 changed"
    unless bj.isNull do
      let bAfter ← limbs (← field r "b_after")
      check (bAfter == b) fun _ => s!"{tag}: input at rs2 changed"
    let av := limbsToNat a
    match op with
    | .mulq | .mulr | .squareq | .squarer =>
      let bv := limbsToNat (if isSquare op then a else b)
      match toLimbs? advice, toLimbs? output with
      | some w, some c =>
        let wv := limbsToNat w
        let cv := limbsToNat c
        check (decide (MulRel q av bv wv cv)) fun _ => s!"{tag}: MulRel fails"
        check (decide (Canonical q cv)) fun _ => s!"{tag}: result {cv} is not below q"
      | _, _ => check false fun _ => s!"{tag}: wrong advice or output length"
    | .divq | .divr =>
      match advice, toLimbs? output with
      | [c0, w0, c1, w1, c2, w2, c3, w3], some c =>
        let cv := limbsToNat c
        let wv := limbsToNat #v[w0, w1, w2, w3]
        check (c == #v[c0, c1, c2, c3]) fun _ => s!"{tag}: stored result is not the advice result"
        check (decide (DivRel q av (limbsToNat b) wv cv)) fun _ => s!"{tag}: DivRel fails"
        check (decide (Canonical q cv)) fun _ => s!"{tag}: result {cv} is not below q"
      | _, _ => check false fun _ => s!"{tag}: wrong advice or output length"
    | .glvrAdv =>
      check (output == (glvrAdvice a).toList) fun _ =>
        s!"{tag}: stored words {wordsStr output} differ from Lean {wordsStr (glvrAdvice a).toList}"
      match output with
      | [s1, k1lo, k1hi, s2, k2lo, k2hi] =>
        check (s1.toNat ≤ 1 ∧ s2.toNat ≤ 1) fun _ => s!"{tag}: sign word not 0 or 1"
        let m1 : Nat := k1lo.toNat + 2 ^ 64 * k1hi.toNat
        let m2 : Nat := k2lo.toNat + 2 ^ 64 * k2hi.toNat
        check (m1 < 2 ^ 128 ∧ m2 < 2 ^ 128) fun _ => s!"{tag}: magnitude not below 2^128"
        let k1 : Int := if s1.toNat = 1 then -(m1 : Int) else m1
        let k2 : Int := if s2.toNat = 1 then -(m2 : Int) else m2
        check ((k1 + (glvLambda : Int) * k2 - (av : Int)) % (n : Int) == 0) fun _ =>
          s!"{tag}: k ≢ ±k1 ± λ·k2 (mod n)"
      | _ => check false fun _ => s!"{tag}: expected 6 stored words"

/-! ## Driver -/

def countBy (cases : Array Json) (key : String) : Nat :=
  cases.foldl (fun acc j =>
    match j.getObjVal? "outcome" with
    | .ok o => if (o.getObjVal? key).toOption.isSome then acc + 1 else acc
    | .error _ => acc) 0

def run (path : String) : M UInt32 := do
  let text ← IO.FS.readFile path
  let doc ← match Json.parse text with
    | .ok d => pure d
    | .error e => throw s!"cannot parse {path}: {e}"
  let commit ← str (← field doc "jolt_commit")
  let moduli ← field doc "moduli"
  let advice ← arr (← field doc "advice")
  let runs ← arr (← field doc "runs")
  let glv ← arr (← field doc "glv")
  let body : T GlvMax := do
    check ((← hexNat (← field moduli "p")) == p) fun _ => "Rust's p differs from Lean's p"
    check ((← hexNat (← field moduli "n")) == n) fun _ => "Rust's n differs from Lean's n"
    check ((← hexNat (← field moduli "lambda")) == glvLambda) fun _ =>
      "Rust's λ differs from Lean's glvLambda"
    let c0 := (← get).checks
    for j in advice do checkAdviceCase j
    let c1 := (← get).checks
    let (_, g) ← (glv.forM checkGlvCase).run {}
    let c2 := (← get).checks
    for j in runs do checkRun j
    let c3 := (← get).checks
    IO.println s!"Jolt commit {commit}"
    IO.println s!"advice cases: {advice.size} ({c1 - c0} checks)"
    IO.println s!"GLV scalars: {glv.size} ({c2 - c1} checks); in range: {g.count}, \
      max |k1| {g.k1Bits} bits, max |k2| {g.k2Bits} bits, {g.over128} at or above 2^128"
    IO.println s!"tracer runs: {runs.size} ({countBy runs "ok"} passed, \
      {countBy runs "panic"} panicked; {c3 - c2} checks)"
    pure g
  let (_, tally) ← body.run {}
  for f in tally.failures do IO.println s!"FAIL {f}"
  IO.println s!"{tally.checks} checks, {tally.failures.size} failures"
  pure (if tally.failures.isEmpty then 0 else 1)

end JoltTests.Secp256k1Kat

def main (args : List String) : IO UInt32 := do
  match args with
  | [path] =>
    match ← (JoltTests.Secp256k1Kat.run path).run with
    | .ok code => pure code
    | .error e => IO.eprintln s!"secp256k1-kat: {e}"; pure 2
  | _ => IO.eprintln "usage: secp256k1-kat OUT.json"; pure 2
