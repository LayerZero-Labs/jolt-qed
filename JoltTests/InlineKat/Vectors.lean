import JoltTests.InlineKat.Manifest

/-!
# Known answers for the hash specifications

This module checks the specifications in `JoltBytecode/Inlines` on published test vectors,
without Jolt. Each check is a `#guard`, so a wrong answer fails `lake build
JoltTests.InlineKat.Vectors`.

- SHA-256: digests of FIPS 180-4 examples (one and two blocks), and the derivation of `IV` and
  `K` from the primes (EthLib's `IV_from_primes` and `K_from_primes`, as Boolean checks).
- Keccak: Keccak-256 digests, the Keccak-f[1600] known answers of the Keccak team, the
  derivation of `RC` and `RHO` (EthLib's `roundConstants_eq` and `rhoOffsets_eq`), the three
  constant facts behind EthLib's proof that the lane code equals the bit model (`rhoOffset_eq`,
  `rhoOffset_lt`, `roundConstantBit_eq`) on all their inputs, and that equation itself on sample
  states.
- BLAKE2b: the compression function on the EIP-152 vectors 4 to 7 and on RFC 7693's examples,
  and the checks of EthLib's `IV_sqrt` and `SIGMA_perm`.

EthLib proves the Boolean checks with `decide` and the `+kernel` option, which jolt-qed's
checking standard forbids, so the copies in `JoltBytecode/Inlines` leave them out and this test
module evaluates them instead.

The bit model of Keccak builds each state as a chain of closures, which costs exponential time
to evaluate. The section `KeccakBitsEval` evaluates it through tables, and proves that each table
version equals the model (`permutationTable_eq`, `roundConstantBitTab_eq`), so the checks there
are about the model itself.
-/

namespace JoltTests.InlineKat.Vectors

open JoltSpec JoltTests.InlineKat

/-- Whether the bytes are the ones the hexadecimal string spells. -/
def bytesAre (bytes : List UInt8) (hex : String) : Bool := bytes == (ofHex hex).toList

/-! ## SHA-256 -/

#guard bytesAre (Sha256.Spec.hash "abc".toUTF8).toList
  "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
#guard bytesAre (Sha256.Spec.hash "".toUTF8).toList
  "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
-- Two blocks.
#guard bytesAre
  (Sha256.Spec.hash "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq".toUTF8).toList
  "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"

-- `IV_from_primes`: the initial words are the square-root fractions of the first 8 primes.
#guard (Sha256.smallPrimes 20).length == 8 && Sha256.IV.toList.length == 8 &&
  ((Sha256.smallPrimes 20).zip (Sha256.IV.toList.map UInt32.toNat)).all
    (fun pair => Sha256.squareRootFraction pair.1 pair.2)

-- `K_from_primes`: the round constants are the cube-root fractions of the first 64 primes.
#guard (Sha256.smallPrimes 312).length == 64 && Sha256.K.toList.length == 64 &&
  ((Sha256.smallPrimes 312).zip (Sha256.K.toList.map UInt32.toNat)).all
    (fun pair => Sha256.cubeRootFraction pair.1 pair.2)

-- The model's initial state is `IV`.
#guard Sha256.Spec.initial.words.toList.map BitVec.toNat == Sha256.IV.toList.map UInt32.toNat

/-! ## Keccak -/

#guard bytesAre (Keccak.keccak256 "".toUTF8).toList
  "c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470"
#guard bytesAre (Keccak.keccak256 "abc".toUTF8).toList
  "4e03657aea45a94fc7d47ba826c8d667c0d1e6e33a64a036ec44f58fa12d6c45"

-- `keccakFZero` and `keccakFZeroTwice` (in `JoltTests.InlineKat.Manifest`) are the Keccak-f[1600]
-- answers of the Keccak team's `KeccakKAT-3` for the zero state and for its image.
#guard bytesAre (keccakBytes (Keccak.keccakF Keccak.State.zero)).toList keccakFZero
#guard bytesAre (keccakBytes (Keccak.keccakF (keccakState (ofHex keccakFZero)))).toList
  keccakFZeroTwice

-- `roundConstants_eq`: the round constants are the ones FIPS 202 Algorithm 6 derives.
#guard Keccak.RC == Vector.ofFn fun ir => Keccak.Internal.roundConstant ir

-- `rhoOffsets_eq`: the rotation offsets are the ones FIPS 202 Algorithm 2 derives.
#guard Keccak.RHO.map UInt64.toNat == Keccak.Internal.rhoOffsets

/-! ## The Keccak bit model -/

namespace KeccakBitsEval

open JoltSpec.KeccakBits

/-! The tables are data (`Vector Bool 1600` and `Vector Bool 8`), not functions.
A function that returns a state would not share its table between calls: the compiler
eta-expands it to its full arity, so every bit read would rebuild the table. -/

/-- The 1600 bits of a state, bit `(x, y, z)` at index `64 (x + 5y) + z`. -/
def toTable (a : State) : Vector Bool 1600 :=
  Vector.ofFn fun i => a (xy (i.val / 64)) (xy (i.val / 320)) (zcoord i.val)

/-- The state whose bits a table lists. -/
def ofTable (t : Vector Bool 1600) : State := fun x y z =>
  t[64 * (x.val + 5 * y.val) + z.val]'(by
    have := x.isLt; have := y.isLt; have := z.isLt; omega)

theorem ofTable_toTable (a : State) : ofTable (toTable a) = a := by
  funext x y z
  have := x.isLt; have := y.isLt; have := z.isLt
  simp only [ofTable, toTable, Vector.getElem_ofFn]
  congr <;> apply Fin.ext <;> simp only [xy, zcoord] <;> omega

/-- The eight bits of a register. -/
def registerTable (r : Register) : Vector Bool 8 := Vector.ofFn r

/-- `rc`, with the register kept as a table between steps. -/
def rcTab (t : Nat) : Bool :=
  ((List.range (t % 255)).foldl (fun v _ => registerTable (registerStep fun i => v[i]))
    (registerTable fun i => i.val == 0))[0]

theorem rcTab_eq : rcTab = rc := by
  funext t
  have step : ∀ (l : List Nat) (v : Vector Bool 8),
      (fun i : Fin 8 => (l.foldl (fun v _ => registerTable (registerStep fun i => v[i])) v)[i]) =
        l.foldl (fun r _ => registerStep r) (fun i => v[i]) := by
    intro l
    induction l with
    | nil => intro v; rfl
    | cons n l ih =>
      intro v
      simp only [List.foldl_cons]
      rw [ih]
      congr 1
      funext i
      simp [registerTable]
  have := congrFun (step (List.range (t % 255)) (registerTable fun i => i.val == 0)) 0
  simp only [rcTab, rc]
  refine Eq.trans this ?_
  simp [registerTable]

/-- `roundConstantBit`, through `rcTab`. -/
def roundConstantBitTab (round : Nat) (z : Fin 64) : Bool :=
  (List.range 7).foldl (fun bit j =>
    if z.val = 2 ^ j - 1 then rcTab (j + 7 * round) else bit) false

theorem roundConstantBitTab_eq : roundConstantBitTab = roundConstantBit := by
  funext round z
  simp only [roundConstantBitTab, roundConstantBit, rcTab_eq]

/-- The rho offsets of all 25 lanes, lane `(x, y)` at index `x + 5y`. -/
def rhoOffsetTable : Vector Nat 25 :=
  Vector.ofFn fun i => rhoOffset (xy i.val) (xy (i.val / 5))

/-- `rho`, with the offsets read from `rhoOffsetTable`. -/
def rhoTab (a : State) : State := fun x y z =>
  a x y (zcoord (z.val + 64 - rhoOffsetTable[x.val + 5 * y.val]'(by
    have := x.isLt; have := y.isLt; omega)))

theorem rhoTab_eq : rhoTab = rho := by
  funext a x y z
  have := x.isLt; have := y.isLt
  have hx : xy (x.val + 5 * y.val) = x := by apply Fin.ext; simp only [xy]; omega
  have hy : xy ((x.val + 5 * y.val) / 5) = y := by apply Fin.ext; simp only [xy]; omega
  simp only [rhoTab, rho, rhoOffsetTable, Vector.getElem_ofFn, hx, hy]

/-- `iota`, through `roundConstantBitTab`. -/
def iotaTab (round : Nat) (a : State) : State := fun x y z =>
  if x.val = 0 ∧ y.val = 0 then Bool.xor (a x y z) (roundConstantBitTab round z)
  else a x y z

theorem iotaTab_eq : iotaTab = iota := by
  funext round a x y z
  simp only [iotaTab, iota, roundConstantBitTab_eq]

/-- `round` on tables. -/
def roundTable (ir : Nat) (t : Vector Bool 1600) : Vector Bool 1600 :=
  toTable (iotaTab ir (chi (pi (rhoTab (theta (ofTable t))))))

theorem ofTable_roundTable (ir : Nat) (t : Vector Bool 1600) :
    ofTable (roundTable ir t) = round ir (ofTable t) := by
  simp only [roundTable, ofTable_toTable, iotaTab_eq, rhoTab_eq, round]

/-- `permutation` on tables. -/
def permutationTable (t : Vector Bool 1600) : Vector Bool 1600 :=
  (List.range 24).foldl (fun t ir => roundTable ir t) t

theorem permutationTable_eq (a : State) :
    ofTable (permutationTable (toTable a)) = permutation a := by
  have step : ∀ (l : List Nat) (t : Vector Bool 1600),
      ofTable (l.foldl (fun t ir => roundTable ir t) t) =
        l.foldl (fun s ir => round ir s) (ofTable t) := by
    intro l
    induction l with
    | nil => intro t; rfl
    | cons n l ih => intro t; simp only [List.foldl_cons, ih, ofTable_roundTable]
  simp only [permutationTable, permutation, step, ofTable_toTable]

-- `rhoOffset_eq`: the rho walk of the model gives the lane table's offset at every lane.
#guard (List.finRange 5).all fun x => (List.finRange 5).all fun y =>
  rhoOffset x y == (Keccak.RHO[x.val + 5 * y.val]'(by
    simp only [Keccak.LANES]; have := x.isLt; have := y.isLt; omega)).toNat

-- `rhoOffset_lt`: every offset is below the lane width.
#guard (List.finRange 5).all fun x => (List.finRange 5).all fun y => rhoOffset x y < 64

-- `roundConstantBit_eq`, through `roundConstantBitTab_eq`: every round-constant bit of the model
-- is the bit of the lane table.
#guard (List.finRange Keccak.ROUNDS).all fun ir => (List.finRange 64).all fun z =>
  roundConstantBitTab ir.val z == (Keccak.RC[ir]).toBitVec.getLsbD z.val

/-- Sample lane states for the equation between the lane code and the bit model. -/
def samples : List Keccak.State :=
  let pattern := Keccak.State.ofLanes fun x y => UInt64.ofNat (3 * (x.val + 5 * y.val) + 5)
  [Keccak.State.zero,
   Keccak.State.ofLanes fun _ _ => 0xFFFFFFFFFFFFFFFF,
   pattern,
   keccakState (ofHex keccakFZero),
   Keccak.keccakF pattern]

-- `toLanes_permutation`, through `permutationTable_eq`, on the samples: the lane code computes
-- the bit model's permutation.
#guard samples.all fun S => toLanes (ofTable (permutationTable (toTable (ofLanes S)))) ==
  Keccak.keccakF S

end KeccakBitsEval

/-! ## BLAKE2b -/

/-- The state `h` of the EIP-152 vectors: the BLAKE2b-512 IV with the parameter block of an
unkeyed 64-byte digest XORed into word 0. -/
def eip152H : Vector Blake2b.Spec.Word 8 :=
  blake2Words 8 (ofHex ("48c9bdf267e6096a3ba7ca8485ae67bb2bf894fe72f36e3cf1361d5f3af54fa5" ++
    "d182e6ad7f520e511f6c3e2b8c68059b6bbd41fbabd9831f79217e1319cde05b")) 0

/-- The message block of the EIP-152 vectors: "abc" and 125 zero bytes. -/
def abcBlock : Vector Blake2b.Spec.Word 16 := blake2Words 16 "abc".toUTF8 0

/-- Whether `Spec.compress` with these arguments gives the state the hexadecimal string spells,
as eight little-endian words. -/
def compressGives (r : Nat) (h : Vector Blake2b.Spec.Word 8) (m : Vector Blake2b.Spec.Word 16)
    (t : Nat) (f : Bool) (hex : String) : Bool :=
  bytesAre (blake2Bytes (Blake2b.Spec.compress r h m (BitVec.ofNat 128 t) f)).toList hex

-- EIP-152 vectors 4 to 7: 0 rounds; 12 rounds final (RFC 7693 appendix A, BLAKE2b-512("abc"));
-- 12 rounds not final; 1 round.
#guard compressGives 0 eip152H abcBlock 3 true
  ("08c9bcf367e6096a3ba7ca8485ae67bb2bf894fe72f36e3cf1361d5f3af54fa5" ++
    "d282e6ad7f520e511f6c3e2b8c68059b9442be0454267ce079217e1319cde05b")
#guard compressGives 12 eip152H abcBlock 3 true
  ("ba80a53f981c4d0d6a2797b69f12f6e94c212f14685ac4b74b12bb6fdbffa2d1" ++
    "7d87c5392aab792dc252d5de4533cc9518d38aa8dbf1925ab92386edd4009923")
#guard compressGives 12 eip152H abcBlock 3 false
  ("75ab69d3190a562c51aef8d88f1c2775876944407270c42c9844252c26d28752" ++
    "98743e7f6d5ea2f2d3e8d226039cd31b4e426ac4f2d3d666a610c2116fde4735")
#guard compressGives 1 eip152H abcBlock 3 true
  ("b63a380cb2897d521994a85234ee2c181b5f844d2c624c002677e9703449d2fb" ++
    "a551b3a8333bcdf5f2f7e08993d53923de3d64fcc68c034e717b9293fed7a421")

-- BLAKE2b-512 of the empty message: one zero block, counter 0, final.
#guard compressGives 12 eip152H (Vector.replicate 16 0) 0 true
  ("786a02f742015903c6c6fd852552d272912f4740e15847618a86e217f71f5419" ++
    "d25e1031afee585313896444934eb04b903a685b1448b755d56f701afe9be2ce")

-- `IV_sqrt`: each IV word is the first 64 fractional bits of the square root of a prime.
#guard (List.finRange 8).all fun i =>
  let p := #v[2, 3, 5, 7, 11, 13, 17, 19][i]
  let s := 2 ^ 64 * #v[1, 1, 2, 2, 3, 3, 4, 4][i] + Blake2b.IV[i].toNat
  s ^ 2 ≤ 2 ^ 128 * p && 2 ^ 128 * p < (s + 1) ^ 2

-- `SIGMA_perm`: each row of the message schedule is a permutation of 0 to 15.
#guard (List.finRange 10).all fun i => Blake2b.SIGMA[i].toList.isPerm (List.finRange 16)

end JoltTests.InlineKat.Vectors
