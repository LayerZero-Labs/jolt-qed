import JoltConstraints.Soundness.Layer5.MemoryAccessRestriction

/-! Temporary program restriction for the termination word (B6, stopping early;
related to a16z/jolt#1950 and #1951 item 2).

Jolt's tracer stops a run only at a PC stall, a jump to itself. The constraints
let a witness end its real rows after any jump, and accept a "no panic" claim
once the final termination word holds 1. A program that stores to termination
and then keeps running can therefore be cut at a later jump, and its earlier
outputs proved. Separately, Jolt's tracer ignores stores to the termination
region and loads it as 0, while the RAM table keeps the stored bytes, so a load
after such a store would disagree with the table.

The SDK's exit stores 1 to termination and then stalls with `j .`; the store's
expansion loads the word only before storing to it. Not checked: whether the
compiler places `j .` directly after that store, with no jump in between.
At public pin 8bbb2357:
See : jolt/jolt-sdk/macros/src/lib.rs:880-887
See : jolt/common/src/jolt_device.rs:146-150
See : jolt/common/src/jolt_device.rs:175-181
See : jolt/crates/jolt-program/src/preprocess/public_io.rs:47-52 -/

set_option autoImplicit false

namespace JoltConstraints.Soundness

open Sail PreSail LeanRV64D.Functions JoltISA

/-- An eight-byte access at `address` touches the termination region
`[termination, io_end)` of `device`. -/
def TouchesTermination (device : JoltDevice) (address : BitVec 64) : Prop :=
  ∃ offset < 8, device.is_termination (address.toNat + offset) = true

/-- Completed row `i` of the run is an SD that touches the termination region. -/
def UntrustedAnswerRun.StoresTerminationAt
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (run : UntrustedAnswerRun joltInstance privateInputs) (i : Fin run.rows.size) : Prop :=
  match run.bytecode[run.rows[i].rowIndex].instruction with
  | .SD base _ imm =>
      TouchesTermination run.rows[i].preState.jolt_device
        (sourceValue base run.rows[i].preState + imm)
  | _ => False

end JoltConstraints.Soundness

/-- FIXME: Temporary program restriction for B6, stopping early, and the
termination word's device/table mismatch. To raise with a16z together with the
other FIXMEs. Remove once Jolt either makes the constraints stop only at the PC
stall and agree with the device on the termination word, or documents this
exit discipline as a requirement; the model must reflect that, and the
unrestricted proof must be established. This is not a verifier check.

For every private input and relaxed execution prefix that has already completed
a store touching the termination region, the next attempted row is:
- if a jump, a JAL with offset 0, a jump to itself. A JALR is not allowed;
- if a load, one that does not touch the termination region.
Like `TracerAddressChecks`, it depends on the program's execution, not on a
witness, and does not assume the next row succeeds. -/
def JoltInstance.TerminationThenStall (joltInstance : JoltInstance SourceInstruction) : Prop :=
  ∀ (privateInputs : JoltPrivateInputs)
    (run : JoltConstraints.Soundness.UntrustedAnswerRun joltInstance privateInputs)
    (next : Fin run.bytecode.size) (pre : SailJoltState),
    run.NextStep next pre →
    (∃ i, run.StoresTerminationAt i) →
      match run.bytecode[next].instruction with
      | .JAL _ imm => imm = 0
      | .JALR _ _ _ => False
      | .LD _ _ base imm => ¬ JoltConstraints.Soundness.TouchesTermination
          pre.jolt_device (JoltISA.sourceValue base pre + imm)
      | _ => True

namespace JoltConstraints.Soundness

open Sail PreSail LeanRV64D.Functions JoltISA

/-- After a completed termination store, an attempted direct jump is the
self-jump required for the tracer to stop. -/
theorem termination_next_jal_zero
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (restricted : joltInstance.TerminationThenStall)
    (run : UntrustedAnswerRun joltInstance privateInputs)
    (next : Fin run.bytecode.size) (pre : SailJoltState)
    (ready : run.NextStep next pre) (stored : ∃ i, run.StoresTerminationAt i)
    (dst : JoltISA.Dst) (imm : BitVec 64)
    (instruction : run.bytecode[next].instruction = .JAL dst imm) : imm = 0 := by
  have rule := restricted privateInputs run next pre ready stored
  simpa only [instruction] using rule

/-- An attempted indirect jump cannot follow a completed termination store. -/
theorem termination_next_no_jalr
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (restricted : joltInstance.TerminationThenStall)
    (run : UntrustedAnswerRun joltInstance privateInputs)
    (next : Fin run.bytecode.size) (pre : SailJoltState)
    (ready : run.NextStep next pre) (stored : ∃ i, run.StoresTerminationAt i)
    (dst : JoltISA.Dst) (base : JoltISA.Src) (imm : BitVec 64)
    (instruction : run.bytecode[next].instruction = .JALR dst base imm) : False := by
  have rule := restricted privateInputs run next pre ready stored
  rw [instruction] at rule
  exact rule

/-- A later attempted load cannot touch any byte of the termination word. -/
theorem termination_next_ld_disjoint
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (restricted : joltInstance.TerminationThenStall)
    (run : UntrustedAnswerRun joltInstance privateInputs)
    (next : Fin run.bytecode.size) (pre : SailJoltState)
    (ready : run.NextStep next pre) (stored : ∃ i, run.StoresTerminationAt i)
    (fault : JoltISA.LoadFaultClass) (dst : JoltISA.Dst)
    (base : JoltISA.Src) (imm : BitVec 64)
    (instruction : run.bytecode[next].instruction = .LD fault dst base imm) :
    ¬ TouchesTermination pre.jolt_device (JoltISA.sourceValue base pre + imm) := by
  have rule := restricted privateInputs run next pre ready stored
  simpa only [instruction] using rule

/-- Executing a zero-offset JAL sets the next PC to the current instruction's
address. This is the local stall fact needed after the termination restriction
has ruled out other jumps. -/
theorem jal_zero_exec_stalls (dst : JoltISA.Dst) (pre post : SailJoltState)
    (address link : BitVec 64)
    (pc : pre.sail.regs.get? Register.PC = some address)
    (nextPC : pre.sail.regs.get? Register.nextPC = some link)
    (runs : JoltISA.execInstr (.JAL dst 0) pre = .ok RETIRE_SUCCESS post) :
    post.sail.regs.get? Register.nextPC = some address := by
  have readNext : liftSail (Sail.readReg Register.nextPC) pre = .ok link pre := by
    unfold liftSail
    rw [readReg_eq_of_get? Register.nextPC pre.sail link nextPC]
  have readPC : liftSail (Sail.readReg Register.PC) pre = .ok address pre := by
    unfold liftSail
    rw [readReg_eq_of_get? Register.PC pre.sail address pc]
  simp only [JoltISA.execInstr, bind, EStateM.bind, readNext, readPC] at runs
  cases write : JoltISA.writeDst dst link pre with
  | error err state => simp only [write] at runs; cases runs
  | ok result middle =>
      cases result
      have setPC : liftSail (Sail.writeReg Register.nextPC (address + 0)) middle =
          .ok () { middle with sail := { middle.sail with
            regs := middle.sail.regs.insert Register.nextPC (address + 0) } } := by rfl
      simp only [write, setPC, pure, EStateM.pure] at runs
      cases runs
      simp only [Std.ExtDHashMap.get?_insert, beq_iff_eq, ↓reduceDIte,
        cast_eq, add_zero]

/-- Under the temporary restriction, a selected direct jump after a
termination store actually leaves the tracer's next PC at its own address. -/
theorem termination_next_jal_stalls
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (restricted : joltInstance.TerminationThenStall)
    (run : UntrustedAnswerRun joltInstance privateInputs)
    (next : Fin run.bytecode.size) (pre post : SailJoltState)
    (ready : run.NextStep next pre) (stored : ∃ i, run.StoresTerminationAt i)
    (dst : JoltISA.Dst) (imm address link : BitVec 64)
    (instruction : run.bytecode[next].instruction = .JAL dst imm)
    (pc : pre.sail.regs.get? Register.PC = some address)
    (nextPC : pre.sail.regs.get? Register.nextPC = some link)
    (runs : JoltISA.execInstr (.JAL dst imm) pre = .ok RETIRE_SUCCESS post) :
    post.sail.regs.get? Register.nextPC = some address := by
  have zero := termination_next_jal_zero restricted run next pre ready stored dst imm instruction
  subst imm
  exact jal_zero_exec_stalls dst pre post address link pc nextPC runs

end JoltConstraints.Soundness
