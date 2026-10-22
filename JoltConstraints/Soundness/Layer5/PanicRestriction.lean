import JoltConstraints.Soundness.Layer5.MemoryAccessRestriction

/-! Temporary restrictions for the two known panic issues, written up in
`blog/content/blog/completeness-and-soundness/index.md` and
`blog/content/blog/proof-stops-at-any-jump/index.md`.

Jolt's tracer sets its panic flag on any store to the panic address, whatever
value is stored, and then loads every byte of the panic word as that flag. The
RAM table keeps the stored bytes instead. So a store of 0 leaves the table at 0
while Jolt's tracer has panicked, and a later load of the panic word would read
different values from the device and from the table.

Separately, the constraints let the last cycle before the padding be any JAL or
JALR, while Jolt's tracer stops only at a PC stall. For a "no panic" claim the
verifier also needs the termination word to be 1, and `TerminationThenStall`
makes the jump after that store the stall. For a "panicked" claim nothing does.

The SDK's panic path stores the byte 1 once; its SB expansion loads the panic
word only before that store, when the device and the table both read 0.
At public pin 8bbb2357:
See : jolt/common/src/jolt_device.rs:121-148, 175-178
See : jolt/crates/jolt-program/src/preprocess/public_io.rs:42-52
See : jolt/crates/jolt-claims/src/protocols/composed/r1cs/rv64.rs:312-317, 392-394
See : jolt/jolt-sdk/src/runtime/exit.rs:34-40
See : jolt/jolt-sdk/macros/src/lib.rs:899-903 -/

set_option autoImplicit false

namespace JoltConstraints.Soundness

open Sail PreSail LeanRV64D.Functions JoltISA

/-- An eight-byte access at `address` touches the panic region
`[panic, termination)` of `device`. -/
def TouchesPanic (device : JoltDevice) (address : BitVec 64) : Prop :=
  ∃ offset < 8, device.is_panic (address.toNat + offset) = true

/-- Completed row `i` of the run is an SD that touches the panic region. -/
def UntrustedAnswerRun.StoresPanicAt
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (run : UntrustedAnswerRun joltInstance privateInputs) (i : Fin run.rows.size) : Prop :=
  match run.bytecode[run.rows[i].rowIndex].instruction with
  | .SD base _ imm =>
      TouchesPanic run.rows[i].preState.jolt_device
        (sourceValue base run.rows[i].preState + imm)
  | _ => False

end JoltConstraints.Soundness

/-- FIXME: Temporary program restriction for the panic word's device/table
mismatch (`blog/content/blog/completeness-and-soundness/index.md`). This is a
Jolt bug that must be fixed in Jolt; it cannot remain a restriction. Remove it
once Jolt's constraints treat the panic word as Jolt's tracer does, the model
reflects that, and the unrestricted proof is established. This is not a
verifier check.

For every private input and relaxed execution prefix, the next attempted row is:
- if a store touching the panic region, one that stores the word 1;
- if a load, once a store touching the panic region has completed, one that does
  not touch the panic region.
Like `TracerAddressChecks`, it depends on the program's execution, not on a
witness, and does not assume the next row succeeds. -/
def JoltInstance.PanicStoresOne (joltInstance : JoltInstance SourceInstruction) : Prop :=
  ∀ (privateInputs : JoltPrivateInputs)
    (run : JoltConstraints.Soundness.UntrustedAnswerRun joltInstance privateInputs)
    (next : Fin run.bytecode.size) (pre : SailJoltState),
    run.NextStep next pre →
      match run.bytecode[next].instruction with
      | .SD base value imm =>
          JoltConstraints.Soundness.TouchesPanic pre.jolt_device
              (JoltISA.sourceValue base pre + imm) →
            JoltISA.sourceValue value pre = 1
      | .LD _ _ base imm =>
          (∃ i, run.StoresPanicAt i) →
            ¬ JoltConstraints.Soundness.TouchesPanic pre.jolt_device
              (JoltISA.sourceValue base pre + imm)
      | _ => True

/-- FIXME: Temporary restriction to "no panic" claims, for stopping early on a
"panicked" claim (`blog/content/blog/proof-stops-at-any-jump/index.md`). This is
a Jolt bug that must be fixed in Jolt; it cannot remain a restriction. Remove it
once Jolt's constraints require the last cycle before the padding to be a PC
stall, the model reflects that, and the unrestricted proof is established. This
is not a verifier check.

With `PanicStoresOne`, an execution that stores to the panic word leaves 1
there, so no witness for it satisfies the constraints for a "no panic" claim. -/
def JoltInstance.ClaimsNoPanic (joltInstance : JoltInstance SourceInstruction) : Prop :=
  joltInstance.panic = false
