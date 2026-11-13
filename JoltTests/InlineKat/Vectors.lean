import JoltTests.InlineKat.Manifest

/-!
# Known answers for the hash specifications

This module checks the specifications in `JoltBytecode/Inlines` on published test vectors,
without Jolt. Each check is a `#guard`, so a wrong answer fails `lake build
JoltTests.InlineKat.Vectors`.

- SHA-256: digests of FIPS 180-4 examples (one and two blocks), and that the model's initial
  state is `IV`.
- Keccak: Keccak-256 digests, and the Keccak-f[1600] known answers of the Keccak team.
- BLAKE2b: the compression function on the EIP-152 vectors 4 to 7 and on RFC 7693's examples.

The facts about the constants (EthLib's `IV_from_primes`, `K_from_primes`, `roundConstants_eq`,
`rhoOffsets_eq`, `IV_sqrt` and `SIGMA_perm`) and the agreement of the Keccak lane code with the
bit model (`toLanes_permutation`) are theorems of the copies in `JoltBytecode/Inlines`, so this
module does not check them again.
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

end JoltTests.InlineKat.Vectors
