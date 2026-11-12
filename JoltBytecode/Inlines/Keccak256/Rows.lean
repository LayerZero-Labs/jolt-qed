import JoltBytecode.Inlines.Generated.Keccak256
import JoltBytecode.Inlines.Generated.Keccak256AbsorbPermute
import JoltBytecode.Inlines.LoadStoreRows

/-!
# The rows of `KECCAK256` and `KECCAK256_ABSORB_PERMUTE`, block by block

Jolt builds both Keccak inlines with one builder (`jolt-inlines/keccak256/src/sequence_builder.rs`
at a16z/jolt `580084fcf`): `KECCAK256` applies Keccak-f[1600] to the 25-lane state at `rs1`, and
`KECCAK256_ABSORB_PERMUTE` first XORs the 17-lane block at `rs2` into the state. This module
restates that builder in Lean, so that the proofs can follow the rounds.

| Block | `KECCAK256` rows | `ABSORB_PERMUTE` rows | What the rows do |
|---|---|---|---|
| `loadRows` | 0–24 | 0–24 | load the 25 lanes at `rs1` into `vr48..72` |
| `absorbRows` | none | 25–58 | 17 pairs: load block lane `i` into `vr84`, XOR into lane `i` |
| `roundRows` (24 times) | 25–3024 | 59–3058 | 125 a round: theta 50, rho-pi 24, chi 50, iota 1 |
| `storeRows` | 3025–3049 | 3059–3083 | store `vr48..72` to the 25 lanes at `rs1` |
| `resetRows` | 3050–3086 | 3084–3120 | reset `vr48..84` to zero |

`Keccak256.Shape` proves that the generated rows are these blocks.

## Registers

Jolt allocates 37 pool registers in order: lane `(x, y)` lives in `vr(48 + x + 5y)`, the column
parities `C[0..4]` in `vr73..77`, `D[0..2]` in `vr78..80`, the rho-pi temporary in `vr81`, the
chi temporaries in `vr82` and `vr83`, and the scratch register in `vr84`. `D[3]` and `D[4]` reuse
`C[1]` (`vr74`) and `C[2]` (`vr75`), which are dead by then.

## Rows as data

Every row of a round reads and writes pool registers only, so a round is a list of `Op`, each
with a destination and source register number; `Op.toInstr` is the row. The rounds differ only
in the round constant of the last row.
-/

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail LeanRV64D
  LeanRV64D.Functions

set_option autoImplicit false

namespace JoltISA.Inlines.Keccak256

/-! ## Registers -/

/-- Virtual register number `n`.
Example: `vr 48` holds lane `(0, 0)`. -/
abbrev vr (n : Nat) : VReg := BitVec.ofNat 7 n

/-- The register number of lane `(x, y)`: `48 + x + 5y`.
Example: `lane 1 2 = 59`. -/
abbrev lane (x y : Nat) : Nat := 48 + x + 5 * y

/-- The register number of the column parity `C[x]`: `73 + x`.
Example: `cReg 4 = 77`. -/
abbrev cReg (x : Nat) : Nat := 73 + x

/-- The register number of `D[x]`: `vr78..80` for `x < 3`, then `C[1]` and `C[2]`.
Example: `dReg 3 = 74`. -/
def dReg : Nat → Nat
  | 0 => 78
  | 1 => 79
  | 2 => 80
  | 3 => cReg 1
  | _ => cReg 2

/-- The rho-pi temporary `vr81`. -/
abbrev piTemp : Nat := 81

/-- The first chi temporary `vr82`. -/
abbrev chiT3 : Nat := 82

/-- The second chi temporary `vr83`. -/
abbrev chiT4 : Nat := 83

/-- The scratch register `vr84`: the chi scratch, and the block lane during absorption. -/
abbrev scratch : Nat := 84

/-! ## Ops -/

/-- A register row of a round, by register numbers.
Example: `Op.xor 73 48 53` is `XOR vr73, vr48, vr53`. -/
inductive Op where
  /-- `XOR d, a, b`: `d := a ^ b`. -/
  | xor (d a b : Nat)
  /-- `VirtualXORROTL1 d, a, b`: `d := a ^ rotl(b, 1)`. -/
  | xorRotl1 (d a b : Nat)
  /-- `VirtualROTRI d, a, mask`, the rotation of `a` left by `k`. -/
  | rotl (d a k : Nat)
  /-- `ANDN d, a, b`: `d := a & ~b`. -/
  | andn (d a b : Nat)
  /-- `XORI d, a, imm`: `d := a ^ imm`. -/
  | xori (d a : Nat) (imm : BitVec 64)

/-- The immediate of Jolt's `VirtualROTRI` for a left rotation by `k`: the mask whose trailing
zeros count `64 - k`, the right rotation.
Example: `rotlMask 1 = 2 ^ 63`. -/
def rotlMask (k : Nat) : Nat := 2 ^ 64 - 2 ^ (64 - k)

/-- The row of an op.
Example: `(Op.rotl 81 49 1).toInstr = VirtualROTRI vr81, vr49, 2^63`. -/
def Op.toInstr : Op → Instr
  | .xor d a b => .XOR (.vreg (vr d)) (.vreg (vr a)) (.vreg (vr b))
  | .xorRotl1 d a b => .VirtualXORROTL1 (.vreg (vr d)) (.vreg (vr a)) (.vreg (vr b))
  | .rotl d a k => .VirtualROTRI (.vreg (vr d)) (.vreg (vr a)) (rotlMask k)
  | .andn d a b => .ANDN (.vreg (vr d)) (.vreg (vr a)) (.vreg (vr b))
  | .xori d a imm => .XORI (.vreg (vr d)) (.vreg (vr a)) imm

/-! ## Constants (Rust `ROUND_CONSTANTS` and `ROTATION_OFFSETS`) -/

/-- The 24 round constants of the builder.
Example: `roundConstants[1]! = 0x8082`. -/
def roundConstants : List (BitVec 64) := [
  0x0000000000000001, 0x0000000000008082,
  0x800000000000808a, 0x8000000080008000,
  0x000000000000808b, 0x0000000080000001,
  0x8000000080008081, 0x8000000000008009,
  0x000000000000008a, 0x0000000000000088,
  0x0000000080008009, 0x000000008000000a,
  0x000000008000808b, 0x800000000000008b,
  0x8000000000008089, 0x8000000000008003,
  0x8000000000008002, 0x8000000000000080,
  0x000000000000800a, 0x800000008000000a,
  0x8000000080008081, 0x8000000000008080,
  0x0000000080000001, 0x8000000080008008]

/-- The rotation offsets of the builder, indexed `[x][y]`.
Example: `rotationOffsets[1]![1]! = 44`. -/
def rotationOffsets : List (List Nat) := [
  [ 0, 36,  3, 41, 18],
  [ 1, 44, 10, 45,  2],
  [62,  6, 43, 15, 61],
  [28, 55, 25, 21, 56],
  [27, 20, 39,  8, 14]]

/-- The rotation offset of lane `(x, y)`. Example: `rhoOffset 1 0 = 1`. -/
def rhoOffset (x y : Nat) : Nat := (rotationOffsets[x]!)[y]!

/-! ## A round -/

/-- Theta (`theta` in Rust): the five column parities, the five `D[x]`, and the 25 lane updates.
Example: the first row is `XOR vr73, vr48, vr53`. -/
def thetaOps : List Op :=
  (List.range 5).flatMap (fun x =>
      Op.xor (cReg x) (lane x 0) (lane x 1) ::
        [2, 3, 4].map fun y => Op.xor (cReg x) (cReg x) (lane x y)) ++
    (List.range 5).map (fun x => Op.xorRotl1 (dReg x) (cReg ((x + 4) % 5)) (cReg ((x + 1) % 5))) ++
    (List.range 5).flatMap (fun x =>
      (List.range 5).map fun y => Op.xor (lane x y) (lane x y) (dReg x))

/-- The inverse of pi's lane map (`pi_source` in Rust): `(x, y) ↦ ((x + 3y) mod 5, x)`.
Example: `piSource (1, 0) = (1, 1)`. -/
def piSource (p : Nat × Nat) : Nat × Nat := ((p.1 + 3 * p.2) % 5, p.1)

/-- The 24 lanes of the rho-pi cycle, from `(1, 0)` (`RHO_PI_FIRST_SOURCE`), each the pi source
of the one before.
Example: `rhoPiCycle.take 3 = [(1, 0), (1, 1), (1, 4)]`. -/
def rhoPiCycle : List (Nat × Nat) := List.iterate piSource (1, 0) 24

/-- Rho and pi (`rho_and_pi` in Rust): lane `(1, 0)` is rotated into the temporary, then each
lane of the cycle is rotated into the register of the lane before it.
Example: the first two rows are `VirtualROTRI vr81, vr49` (by 1) and `VirtualROTRI vr49, vr54`
(by 44). -/
def rhoPiOps : List Op :=
  Op.rotl piTemp (lane 1 0) (rhoOffset 1 0) ::
    (rhoPiCycle.zip rhoPiCycle.tail).map fun p =>
      Op.rotl (lane p.1.1 p.1.2) (lane p.2.1 p.2.2) (rhoOffset p.2.1 p.2.2)

/-- Where chi reads lane `(x, y)` after rho and pi (`rho_pi_lane` in Rust): lane `(0, 2)`, the
pi image of `(1, 0)`, is in the temporary.
Example: `rhoPiLane 0 2 = 81` and `rhoPiLane 1 2 = 59`. -/
def rhoPiLane (x y : Nat) : Nat := if x = 0 ∧ y = 2 then piTemp else lane x y

/-- Chi on row `y` (`chi` in Rust): three `ANDN`s into the temporaries, then the five lanes.
Example: for `y = 0` the first row is `ANDN vr84, vr50, vr49`. -/
def chiRowOps (y : Nat) : List Op :=
  let b := fun x => rhoPiLane x y
  let d := fun x => lane x y
  [Op.andn scratch (b 2) (b 1), Op.andn chiT3 (b 0) (b 4), Op.andn chiT4 (b 1) (b 0),
    Op.xor (d 0) (b 0) scratch,
    Op.andn scratch (b 3) (b 2), Op.xor (d 1) (b 1) scratch,
    Op.andn scratch (b 4) (b 3), Op.xor (d 2) (b 2) scratch,
    Op.xor (d 3) (b 3) chiT3, Op.xor (d 4) (b 4) chiT4]

/-- Chi on the five rows. -/
def chiOps : List Op := (List.range 5).flatMap chiRowOps

/-- The rows of a round before iota: theta, rho and pi, chi (124 rows). -/
def bodyOps : List Op := thetaOps ++ rhoPiOps ++ chiOps

/-- The ops of a round with round constant `rc`: the body, then `XORI vr48, vr48, rc` (iota).
Example: round 0 ends with `XORI vr48, vr48, 1`. -/
def roundOps (rc : BitVec 64) : List Op := bodyOps ++ [Op.xori (lane 0 0) (lane 0 0) rc]

/-- The ops of round `i`; past round 23 there are none.
Example: `roundOpsAt 1` ends with `Op.xori 48 48 0x8082`. -/
def roundOpsAt (i : Nat) : List Op := if i < 24 then roundOps roundConstants[i]! else []

/-- The 125 rows of round `i`.
Example: `roundRows 0` ends with `XORI vr48, vr48, 1`. -/
def roundRows (i : Nat) : List Instr := (roundOpsAt i).map Op.toInstr

/-! ## Loads, absorption, stores and resets -/

/-- The 25 lanes and their offsets at `rs1`: lane `i` is the doubleword at `8i`.
Example: `laneLds[3] = (vr51, 24)`. -/
def laneLds : List (VReg × BitVec 64) :=
  (List.range 25).map fun i => (vr (48 + i), BitVec.ofNat 64 (8 * i))

/-- The 25 loads of the lanes at `rs1` (`load_state`).
Example: the first row is `LD vr48, 0(rs1)`. -/
def loadRows (rs1 : regidx) : List Instr := ldRows rs1 laneLds

/-- The two rows that absorb block lane `i` (`load_state` with `absorb_block`): load it into the
scratch register and XOR it into lane `i`.
Example: `absorbLaneRows rs2 1 = [LD vr84, 8(rs2), XOR vr49, vr49, vr84]`. -/
def absorbLaneRows (rs2 : regidx) (i : Nat) : List Instr :=
  [.LD .normal (.vreg (vr scratch)) (.xreg rs2) (BitVec.ofNat 64 (8 * i)),
    Op.toInstr (.xor (48 + i) (48 + i) scratch)]

/-- The 34 rows that absorb the 17 lanes of the block at `rs2`. -/
def absorbRows (rs2 : regidx) : List Instr := (List.range 17).flatMap (absorbLaneRows rs2)

/-- The lane registers `vr48..72`, in order. -/
def laneRegs : List VReg := (List.range 25).map fun i => vr (48 + i)

/-- The 25 stores of the lanes to `rs1` (`store_state`).
Example: the second row is `SD rs1, vr49, 8`. -/
def storeRows (rs1 : regidx) : List Instr := sdRows rs1 0 laneRegs

/-- The 37 rows that reset the pool registers `vr48..84` to zero.
Example: the first row is `ADDI vr48, x0, 0`. -/
def resetRows : List Instr :=
  (List.range 37).map fun k => .ADDI (.vreg (vr (48 + k))) (.xreg (regidx.Regidx 0)) 0

/-- All 24 rounds. -/
def roundsRows : List Instr := (List.range 24).flatMap roundRows

end JoltISA.Inlines.Keccak256
