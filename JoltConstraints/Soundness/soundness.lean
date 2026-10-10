/-
The base non-succinct soundness statement: a witness that satisfies every modeled
constraint shows the instance is in Jolt's language, under the premises below.
Source programs are limited to the instructions represented by `SourceInstruction`.
Jolt's inline/precompile opcodes 0x0B and 0x2B, including the SHA-256 and Keccak
inlines, are outside that type. Guests using them are outside this theorem's scope.
Akita's extra constraints are to be modeled separately; PCS security is out of scope.
The proof is left as `sorry`; it is not expected to hold yet
(methods/review_completeness_and_soundness.md, B6).
-/
import JoltConstraints.Constraints.All
import JoltConstraints.honest_trace
import JoltConstraints.Soundness.Layer3.Layout

set_option autoImplicit false

-- The instance is in Jolt's language: for some private inputs, Jolt's tracer runs
-- the program to the PC stall with the outputs (trailing zero bytes dropped) and the
-- panic flag the instance claims.
-- See : jolt/jolt-sdk/src/host_utils.rs:320 (the claim is the tracer's final device)
--       jolt/book/src/usage/guests_hosts/guests.md:144, 223
def JoltInstance.InLanguage (joltInstance : JoltInstance SourceInstruction) : Prop :=
  ∃ (privateInputs : JoltPrivateInputs) (trace : HonestTrace joltInstance privateInputs), trace.matches_outputs

-- Temporary scope restriction for the SC advice mismatch (a16z/jolt#2037).
-- Exclude SC.W and SC.D from every source row, including unreachable rows.
-- LR.W and LR.D remain allowed; the mismatch concerns SC's outcome advice.
-- This is a restriction on this theorem, not a check made by Jolt's verifier.
def Rv64ProgramImage.NoStoreConditional (program : Rv64ProgramImage SourceInstruction) : Prop :=
  ∀ row ∈ program.instructions,
    match row.instruction with
    | .riscv (.SC_W _ _ _ _ _) | .riscv (.SC_D _ _ _ _ _) => False
    | _ => True

-- Soundness: if some private inputs and witness satisfy every constraint, the instance
-- is in Jolt's language, under the program restrictions below.
-- The private inputs of the run need not be the ones given.
-- FIXME: expected to fail today for programs that stop or panic in ways SDK guests
-- never do (B6, "Known not sound for this L").
theorem JoltInstance.soundness {F : Type} [Field F]
    -- The base relation uses full 128-bit lookup addresses, so their field
    -- encodings must be injective. BN254 satisfies this bound; Akita does not.
    -- Ari approved this scope on 2026-10-10. Akita's address guard and field
    -- will be modeled separately, without taking on PCS security here.
    (charAbove2pow128 : 2 ^ 128 < ringChar F)
    (joltInstance : JoltInstance SourceInstruction)
    -- assumed: a legal ELF's PC does not wrap (a16z confirmed)
    (noWrap : joltInstance.program.NextPCNoWrap)
    -- NOTE: to confirm with a16z. Approved by Ari on 2026-10-10: the entire
    -- maximum padded RAM region, including each word's eight bytes, fits below 2^64.
    (ramRegionFits : joltInstance.RamRegionFits)
    -- assumed: the program does not change its own code (a16z, a16z/jolt#1952)
    (codeUnchanged : joltInstance.CodeUnchanged)
    -- FIXME: This will be removed once the SC.W/SC.D constraints enforce the honest
    -- tracer's outcome and that fix is reflected in the model (a16z/jolt#2037).
    -- Temporary restriction approved by Ari on 2026-10-10.
    (noStoreConditional : joltInstance.program.NoStoreConditional)
    {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params)
    (satisfied : JoltConstraints.AllConstraints joltInstance privateInputs witness) :
    joltInstance.InLanguage := by
  sorry
