# Tracer address checks for floor rows: Step 3 review

Date: 2026-11-03.
Jolt commit checked: `c6703570588e88033b8722bd4dec47c7f46f3b16` (`c6703570`), the migration target; the recorded pin remains `5def437f`.
Lean commit checked: `fcf21c8ebf5c98f5f22238d776ac13ffbfadfa64` (`fcf21c8`), on `review/audit-completeness-soundness`, plus the two namespace edits and approved restriction extension described below.
Jolt's sources were read with `git -C /Users/ari.biswas/Work-with-A16z/jolt show c6703570:<path>`.
This report completes tasks A and B of `methods/constraints-migration-step3.md` and stops for review.
Ari approved applying the proposed soundness definition on 2026-11-03, with the six new cases grouped into two arms using `|` patterns.
That extension and the approved docstring are now applied; validation stops at the existing import failure recorded in the approval follow-up below.

## Task A: namespace style and build

`HonestTrace.shiftData_address_noWrap` is now declared outside `namespace JoltConstraints` in `JoltConstraints/Completeness/RightLookupEqRightInputOtherwise.lean:49`.
`HonestTrace.floorAccess_address_nonneg` is now declared outside that namespace in `JoltConstraints/Completeness/RightLookupAdd.lean:50`.
Each declaration uses a local `open JoltConstraints in` to resolve its existing selector, followed by reopening the namespace for the remaining declarations.
The two declaration names no longer contain `_root_`.
Their fully qualified names, statements, approved docstrings and existing `sorry` bodies are unchanged, and their callers still use dot notation.
No theorem statement, hypothesis or proof body changed.

`pgrep -fl lake` found no running Lake process before the single build invocation.
`lake build JoltConstraints.Completeness` exited 0 and completed successfully with 8690 jobs.
Lake reported 8.4 seconds for `RightLookupEqRightInputOtherwise`, 8.9 seconds for `RightLookupAdd` and 3.4 seconds for the completeness root.
These are whole-module times; no new proof was written, and neither edited module exceeded ten seconds in this build.
The build retains the existing admission and linter warnings.
No new `sorry`, `native_decide`, `decide +kernel` or `bv_decide` use was introduced, and no limit was changed.

## Restriction before the approved extension

The original definition is `JoltInstance.TracerAddressChecks` at `JoltConstraints/Soundness/Layer5/MemoryAccessRestriction.lean:86` in Lean commit `fcf21c8`.
It is carried by `JoltInstance.TemporaryRestrictions.tracerAddressChecks` at `JoltConstraints/Soundness/Assumptions.lean:86`.
Its quantifiers range over private inputs, an initialized partial execution `UntrustedAnswerRun` (`Soundness/Layer5/TapeTrace.lean:21`) and a next attempted row satisfying `UntrustedAnswerRun.NextStep` (`MemoryAccessRestriction.lean:29`).
The next-step certificate supplies honest internal runtime advice for the prefix and the entry, linkage and stopping conditions, without requiring the next row to execute successfully.
The original docstring and definition follow in full; only the docstring's line wrapping is changed here.

```lean
/-- FIXME: Temporary program restriction, approved by Ari, for https://github.com/a16z/jolt/issues/2044 (following #2041) and four separate candidates in methods/soundness.md: stores at zero, the I/O padding gap, stores to the stack canary, and accesses at or above heap_end.
Narrow or remove this premise as each case is resolved, its resolution is reflected in the model, and the corresponding unrestricted proof is established.
This is not a verifier check; the four additional candidates have no complete witnesses yet.

For every private input and relaxed execution prefix, the next attempted LD or SD passes Mmu.effective_address_ok at the addresses checked by the tracer.
LD and SD are the only memory accesses after expansion, so this also covers the accesses generated for narrower instructions and atomics.
The predicate depends on program execution, not on a purported satisfying witness, and does not assume that the next row successfully executes. -/
def JoltInstance.TracerAddressChecks
    (joltInstance : JoltInstance SourceInstruction) : Prop :=
  ∀ (privateInputs : JoltPrivateInputs)
    (run : JoltConstraints.Soundness.UntrustedAnswerRun joltInstance privateInputs)
    (next : Fin run.bytecode.size) (pre : SailJoltState),
    run.NextStep next pre →
      match run.bytecode[next].instruction with
      | .LD _ _ base imm => JoltConstraints.Soundness.DoublewordAddressChecks
          pre.jolt_device (JoltISA.sourceValue base pre + imm) false
      | .SD base _ imm => JoltConstraints.Soundness.DoublewordAddressChecks
          pre.jolt_device (JoltISA.sourceValue base pre + imm) true
      | _ => True
```

The sentence claiming that LD and SD are the only memory accesses after expansion is obsolete.
All six floor rows took the `True` arm before the approved extension.

## Which address is checked

For any of the six new rows, let `ea := JoltISA.sourceValue base pre + imm`, a wrapping 64-bit sum.
Jolt's tracer computes the same sum with `wrapping_add` in `tracer/src/instruction/floor_access.rs` (`addresses`).
Let `recorded := ea - (ea &&& mask)`, with mask 7, 6 or 4 for B, H or W, respectively.
Let `doubleword := ea &&& ~~~(7 : BitVec 64)`, the start of the eight-byte word actually accessed.
These are three distinct expressions, and alignment is a separate condition.
Lean records `recorded` through `TraceRow.ram_address` (`JoltConstraints/trace.lean:50`) and `TraceWitness.ramAccessAddress` (`JoltConstraints/witness_helpers/ram_address.lean:16`).
Jolt's tracer returns `recorded` in `RamRead.address` or `RamWrite.address` from `floor_access::load` or `floor_access::store`.
Both implementations pass `doubleword` to the doubleword MMU operation.

| Row width | Recorded RAM address | Lean guard on `ea` before the MMU call | Jolt's ordinary tracer guard in `addresses` | Accessed address |
|---|---|---|---|---|
| B | `ea - (ea &&& 7)` | No additional alignment guard | `recorded % 8 = 0`, always satisfied for B | `doubleword` |
| H | `ea - (ea &&& 6)` | `ea &&& 1 = 0` | `recorded % 8 = 0`, equivalent to the Lean guard | `doubleword` |
| W | `ea - (ea &&& 4)` | `ea &&& 3 = 0` | `recorded % 8 = 0`, equivalent to the Lean guard | `doubleword` |

For a concrete H row with base value 16 and immediate -6, `ea = 10`, `recorded = 10 - (10 &&& 6) = 8`, `doubleword = 8`, and `ea &&& 1 = 0`.
The alignment guard concerns `ea` in Lean and `recorded` in Jolt's tracer; the permission checks concern `doubleword` in both.
If instead `ea = 11`, the H row would record 9 and access the doubleword at 8, but the ordinary execution stops at its alignment guard before that access.
Thus replacing `doubleword` by `recorded` in the premise would silently rely on an alignment fact that `NextStep` does not supply.
The existing `JoltConstraints.floor_recorded_address` (`JoltConstraints/Completeness/Helpers/FloorMemory.lean:87`) proves their equality when the natural-alignment bits vanish.

`DoublewordAddressChecks` (`JoltConstraints/Soundness/Layer5/MemoryAccessRestriction.lean:63`) uses `JoltISA.Mmu.effective_address_ok` (`JoltBytecode/JoltISA/DeviceMemory.lean:41`).
If `doubleword.toNat ≥ RAM_START_ADDRESS`, it checks only `doubleword.toNat`.
Below RAM, it checks all eight byte addresses `doubleword.toNat + offset` for `offset < 8`.
The read flag is `false`; the write flag is `true`.
There is no extra permission check at the original `ea` or at `recorded`.

Lean's `Mmu.load_doubleword` and `Mmu.store_doubleword` (`DeviceMemory.lean:130` and `:147`) check their argument's doubleword alignment, then use the starting address for RAM or the byte operations `load_raw?` and `store_raw?` for device memory.
Jolt's tracer follows the corresponding paths in `tracer/src/emulator/mmu.rs` (`Mmu::load_doubleword`, `Mmu::store_doubleword`, `Mmu::load_bytes`, `Mmu::store_bytes`, `Mmu::load_doubleword_raw`, `Mmu::store_doubleword_raw`, `Mmu::load_raw`, `Mmu::store_raw`, and `Mmu::assert_effective_address`).
Jolt's `Mmu::trace_store` also checks the starting address before recording the old value; for these rows that address is again `doubleword`, so this repeats a condition already covered by the extended predicate.
Clearing the low three bits guarantees doubleword alignment, prevents the eight-byte access from wrapping at `2^64`, and keeps it within one 4096-byte page.
Consequently Jolt's raw RAM fast path applies whenever this doubleword is in RAM, and checking all eight RAM bytes would unnecessarily strengthen its heap and canary checks.

## Approved restriction, applied

This is the complete replacement applied to the existing docstring and definition, at the same namespace position in `MemoryAccessRestriction.lean`.
The original six-arm proposal is grouped into two arms as Ari requested, with no change to its conditions or docstring.
The FIXME retains the issue, four candidates and removal conditions from the existing definition and `methods/soundness.md`, Layer 5b.

```lean
/-- FIXME: Temporary program restriction, approved by Ari, for https://github.com/a16z/jolt/issues/2044 (following #2041) and four separate candidates in methods/soundness.md: stores at zero, the I/O padding gap, stores to the stack canary, and accesses at or above heap_end.
Narrow or remove this premise as each case is resolved, its resolution is reflected in the model, and the corresponding unrestricted proof is established.
This is not a verifier check; the four additional candidates have no complete witnesses yet.
The extension to VirtualLoadB/H/W and VirtualStoreB/H/W was approved by Ari on 2026-11-02 and is added only to fit the new ISA.

For every private input and relaxed execution prefix, the next attempted LD, SD, VirtualLoadB/H/W or VirtualStoreB/H/W passes Mmu.effective_address_ok at the addresses used by its doubleword MMU operation.
Here a relaxed prefix is an UntrustedAnswerRun, and NextStep supplies its honest internal runtime advice, stopping and next-row conditions without assuming that the next row succeeds.
The effective address ea is the wrapping 64-bit sum of the base register value and immediate.
LD and SD check ea; each floor row checks the containing doubleword at ea &&& ~~~7.
DoublewordAddressChecks uses read permissions for loads and write permissions for stores, checking only the starting address in RAM and all eight byte addresses below RAM.
For example, VirtualLoadH with ea = 10 accesses the doubleword at 8, so it checks read permissions at 8 through 15 below RAM.
The recorded RAM address of a floor row is ea - (ea &&& mask), with masks 7, 6 and 4 for B, H and W; it equals the accessed doubleword when the row's natural-alignment condition holds.
Alignment, register availability, unsupported peripheral dispatch and device-value agreement remain separate proof obligations.
The predicate depends on program execution, not on a purported satisfying witness, and does not assume that the next row successfully executes.
Jolt's tracer at c6703570: tracer/src/instruction/floor_access.rs (addresses, load, store) and tracer/src/emulator/mmu.rs (Mmu::load_doubleword, Mmu::store_doubleword, Mmu::assert_effective_address). -/
def JoltInstance.TracerAddressChecks
    (joltInstance : JoltInstance SourceInstruction) : Prop :=
  ∀ (privateInputs : JoltPrivateInputs)
    (run : JoltConstraints.Soundness.UntrustedAnswerRun joltInstance privateInputs)
    (next : Fin run.bytecode.size) (pre : SailJoltState),
    run.NextStep next pre →
      match run.bytecode[next].instruction with
      | .LD _ _ base imm => JoltConstraints.Soundness.DoublewordAddressChecks
          pre.jolt_device (JoltISA.sourceValue base pre + imm) false
      | .SD base _ imm => JoltConstraints.Soundness.DoublewordAddressChecks
          pre.jolt_device (JoltISA.sourceValue base pre + imm) true
      | .VirtualLoadB _ _ base imm _ | .VirtualLoadH _ _ base imm _
      | .VirtualLoadW _ _ base imm _ => JoltConstraints.Soundness.DoublewordAddressChecks
          pre.jolt_device ((JoltISA.sourceValue base pre + imm) &&& ~~~(7 : BitVec 64)) false
      | .VirtualStoreB base _ imm _ | .VirtualStoreH base _ imm _
      | .VirtualStoreW base _ imm _ => JoltConstraints.Soundness.DoublewordAddressChecks
          pre.jolt_device ((JoltISA.sourceValue base pre + imm) &&& ~~~(7 : BitVec 64)) true
      | _ => True
```

Each new arm checks the same containing doubleword, with its load or store permission flag.
The per-constructor correspondence is below; all Jolt paths refer to `c6703570`.
Each named tracer `exec` delegates to the shared `floor_access::load` or `floor_access::store`, which calls `addresses` with the indicated alignment class and the MMU operation described above.

| New constructor case | Argument to `DoublewordAddressChecks` | Lean execution source | Jolt tracer source and shared operation |
|---|---|---|---|
| `VirtualLoadB` | `doubleword`, `false` | `JoltBytecode/JoltISA/Semantics.lean:419`, `JoltISA.execInstr`, B case | `tracer/src/instruction/virtual_load_b.rs`, `VirtualLoadB::exec`; `floor_access.rs`, `load` and `addresses`, `AlignmentClass::Byte` |
| `VirtualLoadH` | `doubleword`, `false` | `JoltBytecode/JoltISA/Semantics.lean:428`, `JoltISA.execInstr`, H case | `tracer/src/instruction/virtual_load_h.rs`, `VirtualLoadH::exec`; `floor_access.rs`, `load` and `addresses`, `AlignmentClass::Halfword` |
| `VirtualLoadW` | `doubleword`, `false` | `JoltBytecode/JoltISA/Semantics.lean:440`, `JoltISA.execInstr`, W case | `tracer/src/instruction/virtual_load_w.rs`, `VirtualLoadW::exec`; `floor_access.rs`, `load` and `addresses`, `AlignmentClass::Word` |
| `VirtualStoreB` | `doubleword`, `true` | `JoltBytecode/JoltISA/Semantics.lean:452`, `JoltISA.execInstr`, B case | `tracer/src/instruction/virtual_store_b.rs`, `VirtualStoreB::exec`; `floor_access.rs`, `store` and `addresses`, `AlignmentClass::Byte` |
| `VirtualStoreH` | `doubleword`, `true` | `JoltBytecode/JoltISA/Semantics.lean:460`, `JoltISA.execInstr`, H case | `tracer/src/instruction/virtual_store_h.rs`, `VirtualStoreH::exec`; `floor_access.rs`, `store` and `addresses`, `AlignmentClass::Halfword` |
| `VirtualStoreW` | `doubleword`, `true` | `JoltBytecode/JoltISA/Semantics.lean:471`, `JoltISA.execInstr`, W case | `tracer/src/instruction/virtual_store_w.rs`, `VirtualStoreW::exec`; `floor_access.rs`, `store` and `addresses`, `AlignmentClass::Word` |

The approved extension strengthens the existing restriction on exactly these six constructors, replacing `True` with the doubleword address-permission condition.
The quantifiers, `NextStep` antecedent, LD and SD arms, other-row arm and definition of `DoublewordAddressChecks` stay unchanged.
There is no new theorem premise, no integer nonwrapping assumption and no extra alignment hypothesis.
Like the existing LD/SD arms, the new arms demand the address-permission condition independently of whether execution reaches the MMU call.
In particular, they neither assume nor prove the H/W alignment guard; an alignment proof still has to come from elsewhere before proving successful execution.

## Execution differences and scope

The ordinary tracer's floor-address calculation, natural-alignment acceptance condition and MMU permission-check addresses agree with the inspected Lean cases.
The different formulas for the alignment guard are equivalent, rather than an address mismatch.
There are nevertheless differences in failure representation and supported execution modes.

1. Lean's misaligned H/W cases return `ExecutionResult.Memory_Exception (Virtaddr ea, fault)`; Jolt's tracer panics in `floor_access::addresses`.
   Both prevent successful ordinary execution of the row, but they do not have identical exception behavior.
2. With the `test-utils` feature or in tests, Jolt's tracer can enable `floor_access::allow_misaligned_floor_accesses` on the serial tracing thread.
   In that mode `addresses` permits an unaligned `recorded` address while still accessing `doubleword`; for example, H at `ea = 11` records 9 and accesses 8.
   Lean's `execInstr` has no such override and still returns the alignment exception.
   The extension follows the address passed to the MMU in either tracer mode and does not claim that Lean models this testing override.
3. Jolt's MMU also performs trace bookkeeping through `Mmu::trace_load`, `Mmu::trace_store` and `Mmu::traced_doubleword`, including reading the old word before the actual access.
   Lean's doubleword execution rules operate directly on the modeled RAM or device, while the constraints model derives recorded values separately.
   Jolt's raw stores also invalidate its decode cache; these Lean MMU rules have no decode cache operation.
   These execution details are not supplied by `DoublewordAddressChecks`, and this review does not establish a full MMU or trace-bookkeeping equivalence.

The existing MMU abstractions also remain: `Mmu::assert_effective_address` skips its assertions when Jolt's tracer has no device, whereas Lean's `SailJoltState` always carries a `JoltDevice`.
For a present device, the inspected `Mmu.effective_address_ok` branches match the tracer's device-region, read/write, canary and heap assertions.
Unsupported peripheral dispatch, RAM backing availability and the panic/termination value behavior remain separate from those assertions.
The total projection `JoltISA.sourceValue` (`JoltBytecode/JoltISA/RegisterAccess.lean:56`) defaults missing architectural registers to zero, whereas `readSrc` (`:94`) can fail; relating an attempted row's operands to successful execution remains a separate obligation, as for LD and SD.
None of these observations was used to change an execution definition or to add another restriction.

## Approval follow-up (2026-11-03)

The only additional Lean edit is the approved docstring and definition of `JoltInstance.TracerAddressChecks` in `JoltConstraints/Soundness/Layer5/MemoryAccessRestriction.lean:87`.
The three `VirtualLoad` patterns share one arm with `false`, and the three `VirtualStore` patterns share one arm with `true`.
The definition's quantifiers, existing arms and surrounding declarations are unchanged.
In particular, `UntrustedAnswerRun.NextStep`, `DoublewordAddressChecks`, `ld_address_checks` and `sd_address_checks` were not edited.
No theorem gained a premise; the existing temporary restriction was extended exactly as approved.
The earlier namespace edits remain unchanged, and the follow-up changes only `MemoryAccessRestriction.lean` and this report.

`pgrep -fl lake` found no running Lake process before the follow-up build.
`lake build JoltConstraints.Soundness.Layer5.MemoryAccessRestriction` exited 1 after 6.1 seconds.
The import chain stops at `JoltConstraints.Soundness.Layer5.TapeSemantics`, whose build took 3.7 seconds and reported the existing type mismatch at `JoltConstraints/Soundness/Layer5/TapeSemantics.lean:67:12`.
Its application of `JoltIOSetupFrame.execInstr_rule_of_device_relation_for_store` still lacks the floor-store preservation argument added during the migration.
This is the same first failure recorded in the Step 2 report; that proof was not changed.
Lake did not reach `MemoryAccessRestriction.lean`, so this build does not establish elaboration of the extended definition or its existing callers.
The report's applied definition and docstring match the source exactly, and a source comparison confirms that the rest of the module is unchanged from `fcf21c8`.
No proof was added or changed, no proof slower than ten seconds was measured in this follow-up, and no new admission, prohibited tactic or limit increase was introduced.

## Review boundary

The working-tree changes for this step are the two task A Lean files, the approved `TracerAddressChecks` docstring and definition, and this report.
All soundness proof bodies, `model_review.md` and the migration instructions remain unchanged.
The existing soundness migration failures were left in place, and no full soundness build or repair was attempted.
`git diff --check` passes.
No commit was made.
The step 3 instruction file remains until review, as it requests.
