import JoltConstraints.Soundness.Layer5.TapeTrace

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

open Sail PreSail LeanRV64D.Functions JoltISA

/-- The prefix uses honest internal runtime advice, has not continued past a
PC stall, and is about to attempt `next` in `pre`. The row need not succeed.
The boundary cases follow the entry and linkage rules of UntrustedAnswerRun;
entry address zero and a completed PC stall have no next source instruction. -/
structure UntrustedAnswerRun.NextStep
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (run : UntrustedAnswerRun joltInstance privateInputs)
    (next : Fin run.bytecode.size) (pre : SailJoltState) : Prop where
  entryNonzero : joltInstance.program.entry_address ≠ 0
  honestRuntimeAdvice : ∀ n : Fin run.rows.size,
    run.rows[n].someTracerAdvice? =
      honestTracerAdviceAtStepN joltInstance.program run.rows n
  noEarlierStop : ∀ (i : Nat) (current following : TraceRow run.bytecode),
    run.rows[i]? = some current → run.rows[i + 1]? = some following →
    run.bytecode[current.rowIndex].virtual_sequence_remaining.getD 0 = 0 →
    current.postState.sail.regs.get? Register.nextPC ≠
      some run.bytecode[current.rowIndex].address
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
          address ≠ run.bytecode[last.rowIndex].address ∧
          run.bytecode[next].address = address ∧
          run.bytecode[next].starts_source ∧
          pre = advance_pc address (source_is_compressed run.bytecode next) last.postState

/-- The address assertions used by Mmu.load_doubleword and Mmu.store_doubleword.
RAM checks only the starting address; device memory checks each of eight bytes.
Checking all eight RAM bytes would strengthen Jolt's rule at an unaligned
heap or canary boundary. This predicate does not assume execution succeeds.
Rust: tracer/src/emulator/mmu.rs:619–635, 729–748 at 00508a09. -/
def DoublewordAddressChecks (device : JoltDevice) (address : BitVec 64)
    (isWrite : Bool) : Prop :=
  if RAM_START_ADDRESS ≤ address.toNat then
    Mmu.effective_address_ok device address.toNat isWrite = true
  else
    ∀ offset < 8, Mmu.effective_address_ok device (address.toNat + offset) isWrite = true

end JoltConstraints.Soundness

/-- FIXME: Temporary program restriction, approved by Ari, for
https://github.com/a16z/jolt/issues/2044 (following #2041) and four separate
candidates in methods/soundness.md: stores at zero, the I/O padding gap,
stores to the stack canary, and accesses at or above heap_end. Narrow or remove
this premise as each case is resolved, its resolution is reflected in the
model, and the corresponding unrestricted proof is established. This is not
a verifier check; the four additional candidates have no complete witnesses yet.

For every private input and relaxed execution prefix, the next attempted LD
or SD passes Mmu.effective_address_ok at the addresses checked by the tracer.
LD and SD are the only memory accesses after expansion, so this also covers
the accesses generated for narrower instructions and atomics.
The predicate depends on program execution, not on a purported satisfying
witness, and does not assume that the next row successfully executes. -/
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

namespace JoltConstraints.Soundness

/-- Obtain the tracer's load-address checks before executing a selected LD.
The restriction does not require that load to have successfully executed. -/
theorem ld_address_checks
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (restricted : joltInstance.TracerAddressChecks)
    (run : UntrustedAnswerRun joltInstance privateInputs)
    (next : Fin run.bytecode.size) (pre : SailJoltState)
    (ready : run.NextStep next pre) (fault : JoltISA.LoadFaultClass)
    (destination : JoltISA.Dst) (base : JoltISA.Src) (imm : BitVec 64)
    (instruction : run.bytecode[next].instruction = .LD fault destination base imm) :
    DoublewordAddressChecks pre.jolt_device (JoltISA.sourceValue base pre + imm) false := by
  have checked := restricted privateInputs run next pre ready
  simpa only [instruction] using checked

/-- Obtain the tracer's store-address checks before executing a selected SD.
The restriction does not require that store to have successfully executed. -/
theorem sd_address_checks
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (restricted : joltInstance.TracerAddressChecks)
    (run : UntrustedAnswerRun joltInstance privateInputs)
    (next : Fin run.bytecode.size) (pre : SailJoltState)
    (ready : run.NextStep next pre) (base value : JoltISA.Src) (imm : BitVec 64)
    (instruction : run.bytecode[next].instruction = .SD base value imm) :
    DoublewordAddressChecks pre.jolt_device (JoltISA.sourceValue base pre + imm) true := by
  have checked := restricted privateInputs run next pre ready
  simpa only [instruction] using checked

end JoltConstraints.Soundness
