# NextPC issue

The Rust Jolt [`Cpu`](https://github.com/abiswas3/jolt/blob/7dfe8a0f829a4ab3e9126eb5ac5b5b15208cf5fc/tracer/src/emulator/cpu.rs#L342-L374) has a single program-counter field, `pc`, and no separate `nextPC` field.
Sail's register file has two distinct keys, `PC` and `nextPC`, both holding 64-bit values, as defined in [`Defs.lean`](../LeanRV64D/Defs.lean#L1856-L1857).

### Example:

`JAL x1, +20` at address `1000`, occupying four bytes.
All numbers are decimal; assume `x1` initially holds `77`.
The target `1020` is aligned.

“Before” means immediately before the instruction body runs, after PC preparation.

| Implementation | Field | Before JAL | After JAL body | After Sail’s later `tick_pc` |
|---|---|---:|---:|---:|
| Sail | `PC` | 1000 | 1000 | 1020 |
| Sail | `nextPC` | 1004 | 1020 | 1020 |
| Sail | `x1` | 77 | 1004 | 1004 |
| Rust | `self.address` | 1000 | 1000 | — |
| Rust | `cpu.pc` | 1004 | 1020 | — |
| Rust | `cpu.x[1]` | 77 | 1004 | — |

Rust has no separate `tick_pc` step here: its instruction body already sets `cpu.pc` to `1020`.

The proof witness columns describe trace rows rather than fields changing during execution:

| Witness column for this JAL row | Value |
|---|---|
| `PC` | This row’s bytecode index |
| `UnexpandedPC` | 1000 |
| `NextPC` | Successor row’s bytecode index |
| `NextUnexpandedPC` | 1020, assuming the next instruction is traced |

If there is no successor row, both successor witness values are zero.

## Why This Is Not an Execution Issue in the Normal World

For the aligned example above, both executions save `1004` into `x1` and continue at `1020`.
They update their program-counter fields at different stages.

Sail's [`execute_JAL`](../LeanRV64D/InstsEnd.lean#L68906-L68913) is:

```lean
def execute_JAL (imm : (BitVec 21)) (rd : regidx) : SailM ExecutionResult := do
  let link_address ← do (get_next_pc ())
  match (← (jump_to ((← readReg PC) + (sign_extend (m := 64) imm)))) with
  | .Retire_Success () =>
    (do
      (wX_bits rd link_address)
      (pure (Retire_Success ())))
  | failure => (pure failure)
```

Here `get_next_pc` reads `nextPC`, which holds `1004` before execution.
On success, [`jump_to`](../LeanRV64D/BaseInsts.lean#L244-L255) sets `nextPC` to the target `1020`, and `execute_JAL` writes the saved `1004` into `x1`.
`PC` still holds `1000` at the end of this instruction body.
Sail's execution loop subsequently calls [`tick_pc`](../LeanRV64D/PcAccess.lean#L213-L215):

```lean
def tick_pc (_ : Unit) : SailM Unit := do
  writeReg PC (← readReg nextPC)
  (pure (pc_write_callback (← readReg PC)))
```

The copy is **from `nextPC` into `PC`**: `PC` becomes `1020`.
The [`pc_write_callback`](../LeanRV64D/Callbacks.lean#L216-L217) ignores its argument and returns `()`, the sole value of `Unit`, making no state change.

Rust's [`JAL::exec`](https://github.com/abiswas3/jolt/blob/7dfe8a0f829a4ab3e9126eb5ac5b5b15208cf5fc/tracer/src/instruction/jal.rs#L17-L30) is:

```rust
impl JAL {
    // cpu.pc is pre-incremented by 4 (or 2 for compressed) in tick_operate() before execution,
    // self.address is the instruction address.
    fn exec(&self, cpu: &mut Cpu, _: &mut <JAL as RISCVInstruction>::RAMAccess) {
        if self.operands.rd != 0 {
            if self.operands.rd == 1 {
                // Track function call if we're saving a return address (rd != 0)
                cpu.track_call(self.address);
            }
            cpu.write_register(self.operands.rd as usize, cpu.sign_extend(cpu.pc as i64));
        }
        cpu.pc = ((self.address as i64).wrapping_add(normalize_imm(self.operands.imm))) as u64;
    }
}
```

Rust has already advanced `cpu.pc` to `1004` before calling this body, while `self.address` retains `1000`.
The [decoding path](https://github.com/abiswas3/jolt/blob/7dfe8a0f829a4ab3e9126eb5ac5b5b15208cf5fc/tracer/src/emulator/cpu.rs#L730-L748) shows this preparation explicitly.
The body saves `1004` into `x1`, then sets `cpu.pc` directly to `1020`.

In this sense, Rust performs the final PC update earlier: the target is in `cpu.pc` when the instruction body finishes, whereas Sail puts it in `PC` during the later `tick_pc`.
Rust's earlier increment to `1004` prepares the value to save into `x1`; the assignment to `1020` performs the jump.
After Sail's `tick_pc`, the architectural PC and `x1` agree with Rust's values.
This explains the successful aligned example; it does not establish agreement when Sail rejects a misaligned target, because Rust's JAL body has no corresponding alignment check.

### How Did the Old Proof Pass

On `main` at commit `0efd66819feebf4704a330a2aad02fe0f1b52d70`, the [Jolt ISA definition of JAL](https://github.com/LayerZero-Labs/jolt-qed/blob/0efd66819feebf4704a330a2aad02fe0f1b52d70/JoltBytecode/JoltISA/Semantics.lean#L73-L80) follows Sail's instruction body:

```lean
  | .JAL dst imm => do
      let link ← liftSail (get_next_pc ())
      let pc ← liftSail (Sail.readReg Register.PC)
      match ← liftSail (jump_to (pc + sign_extend (m := 64) imm)) with
      | .Retire_Success () =>
          writeDst dst link
          pure RETIRE_SUCCESS
      | other => pure other
```

Expanding `execute_JAL` on the trusted Sail side gives the following [definition](../LeanRV64D/InstsEnd.lean#L68906-L68913):

```lean
def execute_JAL (imm : (BitVec 21)) (rd : regidx) : SailM ExecutionResult := do
  let link_address ← do (get_next_pc ())
  match (← (jump_to ((← readReg PC) + (sign_extend (m := 64) imm)))) with
  | .Retire_Success () =>
    (do
      (wX_bits rd link_address)
      (pure (Retire_Success ())))
  | failure => (pure failure)
```

These implementations may look different, but they are literally the same computation via `liftSail`, so the proofs pass.

> [!WARNING]
> This happened because the translations were AI-generated from the Rust source, and I missed this when proofreading.
> The AI was asked to model Rust semantics, and after it got a few correct, I asked it to implement them all, and I did not catch this.
> It makes sense why it did this, as it gets the reward of closing a theorem, but the dangers of going too quickly are clear.
> The fault is mine for not checking the translation, not the AI's.

## How Did We Fix This?

We made the correspondence between the Rust instruction context and the Lean state explicit at the instruction-body boundary.
The embedded Sail `PC` represents Rust's `self.address`, the address stored in the decoded instruction.
The embedded Sail `nextPC` represents Rust's `cpu.pc`, which has already been advanced before the body runs.
Both values exist in Rust, although only `cpu.pc` is a CPU field.

These lines from [Rust's `JAL::exec`](https://github.com/abiswas3/jolt/blob/7dfe8a0f829a4ab3e9126eb5ac5b5b15208cf5fc/tracer/src/instruction/jal.rs#L26-L28) show their different roles:

```rust
// Inside the rd != 0 branch: save the old cpu.pc into the destination.
cpu.write_register(self.operands.rd as usize, cpu.sign_extend(cpu.pc as i64));

// Then update cpu.pc using the decoded instruction's address.
cpu.pc = ((self.address as i64).wrapping_add(normalize_imm(self.operands.imm))) as u64;
```

The [updated Lean semantics](../JoltBytecode/JoltISA/Semantics.lean#L76-L91) follows these operations using that correspondence:

```lean
  | .JAL dst imm => do
      let rustPC ← liftSail (Sail.readReg Register.nextPC)
      let instructionAddress ← liftSail (Sail.readReg Register.PC)
      writeDst dst rustPC
      liftSail (Sail.writeReg Register.nextPC (instructionAddress + imm))
      pure RETIRE_SUCCESS
```

Here `imm` is the decoded 64-bit offset, addition wraps at 64 bits, and `writeDst` discards writes to `x0`.
Like Rust's instruction body, this translation performs no alignment check.
Rust's diagnostic `track_call` bookkeeping is outside this architectural model.

No new assumption predicates were added to `Assumptions.lean`.
The [JAL bundle](../JoltBytecode/Bundles.lean#L127-L134) reuses existing predicates for three explicit requirements:

1. `nextPC_readable`: the embedded Sail `nextPC` contains a value that can be read, representing Rust's already advanced `cpu.pc`.
2. `pc_readable`: the embedded Sail `PC` contains a value that can be read, representing Rust's `self.address`.
3. `target_aligned`: Sail's `align_pc` succeeds without changing the jump target or state, including successfully reading the configuration needed to determine alignment.

The third requirement means the target is a multiple of two when Sail enables compressed instructions, or a multiple of four otherwise.
The bundle also retains the existing requirement that the six linked Sail CSRs initially equal their virtual-register copies.
The [updated equivalence proof](../JoltBytecode/InstructionEquivalence/Instructions/Natives/Jal.lean) establishes equality under this bundle; it does not establish equivalence for misaligned targets.

A Pull request will shortly fix this.
