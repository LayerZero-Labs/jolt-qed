import JoltConstraints.Soundness.Layer5.TapeTrace

open LeanRV64D

/-! Temporary program restriction for https://github.com/a16z/jolt/issues/2044
(reproduction following #2041) and the separate candidates recorded in
methods/soundness.md: stores at zero, the I/O padding gap, stores to the stack
canary, and accesses at or above heap_end. Each candidate remains to be checked
against all constraints; #2044's reproduction does not establish those cases.

The restriction quantifies over initialized execution prefixes with independent
tape answers and honest internal runtime advice. It checks the next attempted
row, without assuming that row executes. Thus an address check that aborts is
excluded, including at the first row. No witness columns occur here.

Use Mmu.effective_address_ok at the addresses the tracer checks: the starting
address for ordinary RAM doubleword accesses, every byte for device accesses.
Alignment, raw peripheral dispatch, and device value agreement are separate
proof obligations. In particular, panic and termination mismatches remain. -/

set_option autoImplicit false

namespace JoltConstraints.Soundness

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail LeanRV64D LeanRV64D.Functions JoltISA

/-- The prefix uses honest internal runtime advice, has not continued past a
stable stall, and is about to attempt `next` in `pre`. The row need not succeed.
The boundary cases follow the entry and linkage rules of UntrustedAnswerRun.
The stopping rule follows a16z/jolt PR #2109, merge commit 0249591a. -/
structure UntrustedAnswerRun.NextStep
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (run : UntrustedAnswerRun joltInstance privateInputs)
    (next : Fin run.bytecode.size) (pre : SailJoltState) : Prop where
  honestRuntimeAdvice : ∀ n : Fin run.rows.size,
    run.rows[n].someTracerAdvice? =
      honestTracerAdviceAtStepN joltInstance.program run.rows n
  noEarlierStop : ∀ (i : Nat) (current following : TraceRow run.bytecode),
    run.rows[i]? = some current → run.rows[i + 1]? = some following →
    ¬ current.StableStall
  ready :
    match run.rows.back? with
    | none =>
      run.bytecode[next].address = joltInstance.program.entry_address ∧
      run.bytecode[next].starts_source ∧
      pre = advance_pc joltInstance.program.entry_address
        (source_is_compressed run.bytecode next) run.initialState
    | some last =>
      if run.bytecode[last.rowIndex].virtual_sequence_remaining.getD 0 ≠ 0 then
        next.val = last.rowIndex.val + 1 ∧ pre = last.postState
      else
        ∃ address, last.postState.sail.regs.get? Register.nextPC = some address ∧
          ¬ last.StableStall ∧
          run.bytecode[next].address = address ∧
          run.bytecode[next].starts_source ∧
          pre = advance_pc address (source_is_compressed run.bytecode next) last.postState

/-- The address assertions used by Mmu.load_doubleword and Mmu.store_doubleword.
RAM checks only the starting address; device memory checks each of eight bytes.
Checking all eight RAM bytes would strengthen Jolt's rule at an unaligned
heap or canary boundary. This predicate does not assume execution succeeds.
At public pin 8bbb2357:
See : jolt/tracer/src/emulator/mmu.rs:611-628
See : jolt/tracer/src/emulator/mmu.rs:721-740 -/
def DoublewordAddressChecks (device : JoltDevice) (address : BitVec 64)
    (isWrite : Bool) : Prop :=
  if RAM_START_ADDRESS ≤ address.toNat then
    Mmu.effective_address_ok device address.toNat isWrite = true
  else
    ∀ offset < 8, Mmu.effective_address_ok device (address.toNat + offset) isWrite = true

end JoltConstraints.Soundness

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
