/-
What the soundness theorem assumes, grouped by what each assumption is about:
the field, the instance, and temporary workarounds for known issues.
Nothing is assumed about the witness.
-/
import Mathlib.Algebra.CharP.Defs
import JoltConstraints.honest_trace
import JoltConstraints.Soundness.Layer3.Layout
import JoltConstraints.Soundness.Layer5.MemoryAccessRestriction

set_option autoImplicit false

-- The fields the base theorem covers. Jolt's Rust code has a `JoltField` trait for
-- the fields it supports; this models only the one property our proofs use: the
-- characteristic is above 2^128, so every 128-bit lookup address has a distinct
-- field encoding. BN254 satisfies this. Akita's prime, about 2^128 - 2^32, does not;
-- Akita is modeled separately.
-- NOTE: the field is not fully modeled yet. Everything else the Rust trait provides
-- (field size, encoding, arithmetic implementation) is outside this model.
def JoltField (F : Type) [Field F] : Prop :=
  2 ^ 128 < ringChar F

-- What the soundness theorem assumes about the instance. Each field's comment says
-- whether a16z has confirmed it or it is still awaiting confirmation. Workarounds
-- for known issues are not here; they are in `JoltInstance.TemporaryRestrictions`.
structure JoltInstance.SoundnessAssumptions
    (joltInstance : JoltInstance SourceInstruction) : Prop where
  -- No instruction's next PC, its address plus its length (2 or 4), passes 2^64.
  -- Confirmed by a16z on 2026-10-07: an ELF that breaks this is illegal.
  pcNoWrap : joltInstance.program.NextPCNoWrap
  -- No run of the program changes its own code.
  -- Confirmed by a16z on 2026-10-07 (a16z/jolt#1952).
  codeUnchanged : joltInstance.CodeUnchanged
  -- The whole maximum padded RAM region, including all eight bytes of every word,
  -- lies below 2^64. Approved by Ari on 2026-10-10.
  -- NOTE: to confirm with a16z.
  ramRegionFits : joltInstance.RamRegionFits

-- No source row is SC.W or SC.D, including unreachable rows. LR.W and LR.D remain
-- allowed. Used only by `JoltInstance.TemporaryRestrictions`.
def Rv64ProgramImage.NoStoreConditional (program : Rv64ProgramImage SourceInstruction) : Prop :=
  ∀ row ∈ program.instructions,
    match row.instruction with
    | .riscv (.SC_W _ _ _ _ _) | .riscv (.SC_D _ _ _ _ _) => False
    | _ => True

-- Workarounds for known issues. Each one excludes programs that would expose a
-- reported or suspected bug, so that the rest of the proof can go ahead. None of
-- them is a check Jolt's verifier makes. Each must be removed once its issue is
-- resolved in Jolt and in the model, and the proof without it is established.
structure JoltInstance.TemporaryRestrictions
    (joltInstance : JoltInstance SourceInstruction) : Prop where
  -- FIXME: no source row is SC.W or SC.D (a16z/jolt#2037).
  -- Fixed upstream by a16z/jolt#2039 (merged 2026-10-12) and already in the model.
  -- Remove once Layer 5b proves the steps of SC's expansion rows.
  noStoreConditional : joltInstance.program.NoStoreConditional
  -- FIXME: every load and store the program attempts passes Jolt's tracer address
  -- checks (a16z/jolt#2044, plus four candidates in methods/soundness.md: stores
  -- at zero, the I/O gap, stack-canary stores, and accesses at or above heap_end).
  -- Narrow or remove it as each case is resolved.
  tracerAddressChecks : joltInstance.TracerAddressChecks
