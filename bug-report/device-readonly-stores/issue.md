# Input/advice stores: potential soundness gap

We found a possible mismatch while proving Jolt's constraint soundness in Lean:
the tracer rejects stores to input and advice regions, but we have not found
the constraint that excludes those stores from a prover-supplied witness.

**This is an unconfirmed candidate. We have not constructed a witness satisfying
all constraints or obtained a proof accepted by Jolt's verifier.** We could not
complete a concrete reproduction because our AI-assisted workflow is blocked
in Daybreak: we do not currently have AI clearance in that workflow to create
a real example. This is our reported workflow limitation, not evidence that
the candidate is valid or invalid. Another constraint may rule it out. We are
opening this issue to identify that constraint or clarify the intended execution
semantics before continuing the proof.

## 1. The program behaviour under question

Consider a guest that attempts an ordinary store to an input, trusted-advice or
untrusted-advice word. These are the memory-mapped regions, not the runtime
advice tape.

Jolt's MMU permits device stores only to the output, panic or termination
regions. An input/advice store fails its address check
([`assert_effective_address`, L143–160](https://github.com/a16z/jolt/blob/00508a09fd3850e1f45a5515260a3e133a180940/tracer/src/emulator/mmu.rs#L143-L160)).
This follows from reading the code; we have not run a concrete guest for this
report. Our Lean translation implements the same rejection.

## 2. Where a witness could deviate from Jolt's tracer

The potential deviation is to record the store as an ordinary RAM update and
continue execution. A later load would then read the stored value, although
Jolt's tracer would already have aborted at the store.

For an input word, restoring the original value before the end would make its
final value agree with the public input. For an advice word, the final
public-I/O check does not cover its address. These observations concern those
checks individually; we have not shown that a complete witness can pass every
other check.

## 3. The constraints we checked

The RV64 load/store constraints enforce the address calculation, the value
read by a load, and the value written by a store
([`rv64_eq_constraint_rows`, L213–239](https://github.com/a16z/jolt/blob/00508a09fd3850e1f45a5515260a3e133a180940/crates/jolt-r1cs/src/constraints/rv64.rs#L213-L239)).
For a store, these include:

```text
RamAddress = Rs1Value + Imm
RamWriteValue = Rs2Value
```

The RAM read/write relation connects the selected word's value and increment
to the read and write columns
([`ReadWriteChecking`, L65–79](https://github.com/a16z/jolt/blob/00508a09fd3850e1f45a5515260a3e133a180940/crates/jolt-claims/src/protocols/jolt/relations/ram/read_write_checking.rs#L65-L79)).
The RAM value relation connects the initial values, including advice, to the
history of increments
([`RamValCheck`, L130–147](https://github.com/a16z/jolt/blob/00508a09fd3850e1f45a5515260a3e133a180940/crates/jolt-claims/src/protocols/jolt/relations/ram/val_check.rs#L130-L147)).
We found no device write-permission condition in these relations.

The public-output relation checks `RamValFinal` against the public-I/O values
under its mask
([`RamOutputCheck`, L118–124](https://github.com/a16z/jolt/blob/00508a09fd3850e1f45a5515260a3e133a180940/crates/jolt-claims/src/protocols/jolt/relations/ram/output_check.rs#L118-L124)).
That mask starts at `input_start` and ends before `RAM_START_ADDRESS`
([`PublicIoMemory::new`, L21–32](https://github.com/a16z/jolt/blob/00508a09fd3850e1f45a5515260a3e133a180940/crates/jolt-program/src/preprocess/public_io.rs#L21-L32)).
Both advice regions lie below `input_start`
([layout construction, L404–434](https://github.com/a16z/jolt/blob/00508a09fd3850e1f45a5515260a3e133a180940/common/src/jolt_device.rs#L404-L434)).
So this check fixes final input values, but does not by itself prohibit
intermediate input writes, and does not check final advice values.

The cited files were inspected at our local merge revision `43cc043332762034b5f65379441576e06e7a3890`.
We checked that they are unchanged from upstream `00508a09fd3850e1f45a5515260a3e133a180940`
(#1968), which the links above reference. We have not established whether a
later upstream revision changes this behaviour.

## 4. What we have and have not established

| Check | Status |
|---|---|
| The MMU rejects input/advice stores | Checked by reading the source |
| The audited constraints enforce the same write permissions | No such condition found; another constraint may provide it |
| A concrete guest reproduces the rejection | Not run |
| A proposed witness satisfies every constraint | Not constructed |
| `jolt_verifier::verify` accepts a proof for such a witness | Not run |

This report supplies the source audit and proof obligation, without a
counterexample or an accepted-proof claim.

## Why this blocks our soundness proof

Our proof starts with a satisfying witness and must recover an execution whose
outputs match the public instance. At an LD/SD step, recovering the address and
the RAM-table value is not enough: we must also show that the MMU permits the
access and execution succeeds.

If all constraints permit a store that execution necessarily rejects, that
would be a soundness gap relative to this execution semantics. Establishing
that condition is still open. We have not added a premise assuming these stores
away.

This is separate from the termination-store mismatch in #1950/#1951 item 2.
There, the device accepts but ignores a write. Here, the MMU rejects the write.
A restriction on later termination reads does not address this case.

## Question

Which constraint prevents a satisfying witness from storing into an input,
trusted-advice or untrusted-advice region?

If these permissions are only restrictions of the honest tracer, what execution
semantics should a Jolt proof attest to for those accesses? If they are intended
to be enforced by the verifier, could you help identify the missing argument
or confirm whether a constraint is needed? This would let us complete the
memory-access step of the formal soundness proof.
