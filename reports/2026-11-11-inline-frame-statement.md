# Generic inline frame lemma: statement (I0(e))

This note explains the statement in `JoltBytecode/Inlines/Frame.lean` and the per-inline instances in `JoltBytecode/Inlines/FrameInstances.lean`.
It covers spec section 5.4 ("Frame and footprint") and the I0(e) row of `docs/inline-precompiles.md`.
The statement is ready for review; the per-row lemmas are staged with `sorry`.

## Pins

- jolt-qed: the statement was checked at `c1f8c0f` on `inline/i0e-frame` (review range `41b09cc..c1f8c0f`).
- Model Jolt pin: `c97e93004fbf804409f0374fe8457c8f1562ce71` (`JoltConstraints/model_review.md`), the commit the Lean model of Jolt's semantics follows.
- Generated-row Jolt pin: `a6b6dc7177ec5ea5a3c60bd5cea4409c07ca6dc5`, the commit whose inline expansions `JoltBytecode/Inlines/Generated/` holds.

## Statement

`frame_of_run` says: if `p.WritesWithin ws` holds and `p.Run s s'` (that is, `(execProgram p).run s = .ok RETIRE_SUCCESS s'`), then `Frame ws s s'`.
It has no hypothesis on `s`, on the inputs or on the advice values.

A write set `ws : WriteSet` has three fields.

- `vregs : List VReg` lists the virtual registers the rows may write.
- `xregs : List regidx` lists the architectural registers the rows may write.
  It is empty for every in-scope inline; the field keeps the check honest for programs that do write one.
- `stores : List StoreSlot` lists the store rows.
  A `StoreSlot` records the base operand, the immediate, and whether the row stores at `base + imm` (`SD`) or at the doubleword containing it (`VirtualStoreB/H/W`).

`Program.WritesWithin p ws` is the conjunction of three checks.

- `p.rowsWithin ws = true`: every row passes `Instr.writesWithin ws`.
  A row passes when `Instr.isFrameRow` accepts it and its `destination?` is allowed.
- `p.storeSlots ⊆ ws.stores`: every store row is listed.
- `ws.basesKept = true`: every listed store base is an architectural register (`.xreg`), and no allowed destination is a listed store base.

`Instr.isFrameRow` matches every constructor explicitly, in the style of `Instr.WritesProtectedVReg`.
It rejects branches, `JAL` and `JALR` (they write `PC` or `nextPC`), `VirtualAdviceLoad` (it moves the tape cursor) and `VirtualHostIO` (it can change the tape, the device and the host settings).
It accepts every other row, including `AUIPC`, which only reads `PC`.
A destination `.xreg x0` is always allowed, since `wX` ignores `x0`.

The third check makes the footprint a function of the start state.
`ws.Footprint s a` holds when `a` lies in `[address, address + 8)` for some listed slot, where `address` is the slot's doubleword address with the base read in `s`.
This is the same byte range as `InDword` in `JoltConstraints/WholeRun/CodeInv.lean:122`.

The base check requires `.xreg`, as the brief asks ("an architectural register parameter").
A virtual base would make the footprint depend on a register value that is not an operand of the source instruction.
This happens in exactly one place: the `rd = x0` variants of the seven secp256k1 inlines store their result through `vr40`, the instruction temporary that Jolt's `rd = x0` rewrite allocates, and no row writes `vr40` first.
Decision D7 (section 5.2 of `docs/inline-precompiles.md`) excludes these encodings, because they read `rd` before writing it, so no frame lemma is owed for them.
At the generated-row pin `a6b6dc717` Jolt still accepts them.
The open pull request a16z/jolt#2414 implements the rejection upstream.
The check rejects them as a second guard, and `FrameInstances.lean` omits them.
The `rd = x0` variants of the five hash inlines never read `rs3`, store through `rs1`, and keep their instances.

The floor stores (`VirtualStoreB/H/W`) have footprint the doubleword containing `base + imm`; `SD` has `base + imm .. base + imm + 7`.
No in-scope inline has a floor store, so the instances do not exercise the floor case.

## Fields of `Frame`

The list gives each field, what it says, and where the whole-run layer reads the component it protects.
Paths are relative to `JoltConstraints/WholeRun/`.

- `sailRegs`: every Sail register outside the write set keeps its value.
  - This covers `x1..x31`, `PC`, `nextPC`, `misa`, the platform registers and every CSR and reservation register that Sail holds.
  - It is stronger than "`x1..x31` outside the write set" because `Related.regs` compares the whole register file.
  - Readers: `Relation.lean:141-142` (`Related.regs` compares all Sail registers through `sailRegs`, and reads `nextPC`); `Basic.lean:100` (`Block.Runs.continues` reads `nextPC`); `Bundles.lean:226-227` (`pma_regions`, `htif_tohost_base`); `Bundles.lean:578` (`PC` parity); `Halt.lean:33` (`nextPC` at EBREAK); `SystemInv.lean:648-649` (`PC`, `nextPC`).
- `choiceState`, `cycleCount`, `sailOutput`: the remaining Sail fields are unchanged; `tags` has type `Unit`.
  - No whole-run file reads them today; `Ghost.lean:21` says a shadow may differ in them.
  - The fields cost nothing to keep and make `Frame` a full description of the Sail state.
- `vregs`: every virtual register outside `ws.vregs` keeps its value.
  - Readers: `SystemInv.lean:20-23` (`mstatusVReg`, `trapHandlerVReg`, `mepcVReg`, `vr32`, `vr33`); `Relation.lean:133` through `System.systemProject`, which reads the CSR and reservation overlay from `vr32..39`; `Ghost.lean:27`.
- `mem`: a Sail memory byte outside the footprint is unchanged.
  - Readers: `Relation.lean:149` (`ram`), `Relation.lean:155-156` (`io`); `CodeInv.lean:868-872` (`JoltCodeIntact`, code bytes in `sail.mem`); `CodeInv.lean:885-887` (`NoCodeStore`, the store footprint of a block).
- `mem_present`: a present byte stays present.
  - Readers: `Relation.lean:151-152` (`present`); `Ghost.lean:35` (`MemoryFrame.present`); `Bundles.lean:229-230`.
- `mem_belowRam`: Sail memory below `RAM_START_ADDRESS` is unchanged.
  - Readers: `Ghost.lean:36` (`MemoryFrame.below`); `Relation.lean:155-156`.
- `device`: the device changes only by successful `JoltDevice.store?` steps at footprint addresses below RAM.
  - Its corollaries are `Frame.device_same` (layout, inputs, trusted and untrusted advice unchanged, as `JoltIOSetupFrame.Same`), `Frame.panic_mono` and `Frame.outputs_size`.
  - Readers: `Relation.lean:158` (`panic`), `Relation.lean:160` (`layout`), `Relation.lean:162-163` (`outputs_size`, through `Frame.outputs_size`), `Relation.lean:120` (`load?` of the I/O window); `RunInv.lean:285` (`heap_no_wrap` reads `heap_end`); `RunInv.lean:299-303` (`Block.Runs.layout_eq`); `Halt.lean:16` (outputs and panic flag).
- `adviceTape`: the advice tape (bytes and cursor) is unchanged.
  - Readers: `Ghost.lean:29`; `NonInterference.lean:365-372`; `CodeInv.lean:405-411` (the `VirtualAdviceLoad` case of the memory frame).
- `hostIO`: the host-I/O settings are unchanged.
  - Reader: `Ghost.lean:30`.

The advice-tape clause is equality.
`VirtualAdvice dst value` writes its literal `value` and never reads the tape (`JoltBytecode/JoltISA/Semantics.lean:507-509`).
Only `VirtualAdviceLoad` reads the tape and advances `readPosition` (`Semantics.lean:510-516`, `AdviceTape.lean:14-25`), and only `VirtualHostIO` can append to it.
The static check rejects both, so the twelve inlines, which use `VirtualAdvice` but neither of the others, satisfy the equality.

The device clause is exact rather than "the device is unchanged outside the footprint".
`JoltDevice.store?` (`JoltBytecode/JoltISA/JoltDevice.lean:221-229`) changes `panic` at the panic address and grows `outputs` with zero fill in the output region, so a device store changes a whole-device field, not one byte.
The reflexive-transitive closure of `DeviceStoreAt` records exactly those effects.

## Pool reset

The pool-reset clause is per program: `Program.ResetsPool p pool` says that every successful run ends with every register in `pool` equal to zero.
`Program.resetsPoolCheck p pool` checks statically that, for each `v` in `pool`, the last row of `p` that writes `v` is `ADDI (.vreg v) (.xreg x0) 0`.
`Program.resetsPool_of_check` (staged) turns the check into the predicate, given `p.WritesWithin ws`.

## Proof plan and reuse

`frame_of_run` is proved from the per-row lemma `execInstr_frame`, by induction on the program with `execProgram_instr_run_retire_inv` (`ProofSupport/Lemmas.lean:60`) and `Frame.trans`.
`Frame.refl`, `Frame.trans`, `Frame.footprint_eq`, `Frame.sailRegs_eq_of_xregs_nil`, `Frame.device_same`, `Frame.panic_mono`, `Frame.outputs_size` and the Boolean soundness lemmas are proved.

`Frame.outputs_size` gives `Related.outputs_size` in the end state from the same bound in the start state and the output span of the layout (`panic = output_start + max_output_size`).
The proof is an induction on the `device` clause with `JoltIOSetupFrame.storeDeviceByte_outputs_fit` (`ProofSupport/DeviceFrame.lean:42`).
The whole-run layer gets the span from `new_io_geometry` (`JoltConstraints/layout_facts.lean:339`) and `Related.layout`.

Four lemmas are staged with `sorry`.

- `execInstr_sail_effect`: for a frame row, the Sail registers change only by `wX_update_regs rd v` on an `.xreg rd` destination, and `choiceState`, `cycleCount` and `sailOutput` are unchanged.
  Proof: case on the row.
  `readSrc` and `Mmu.load_doubleword` preserve the state, `writeDst (.vreg _)` touches only `vregs`, `writeDst (.xreg rd)` is `wX_regs_spec` (`ProofSupport/RegisterAccess.lean:240`), and `Mmu.store_doubleword` changes only `sail.mem` and `jolt_device`.
- `execInstr_frame`: the frame of one row.
  Proof: `execInstr_sail_effect` gives the Sail clauses, and `writeDst` gives `vregs`.
  For a store row, `Mmu.store_doubleword` at `slot.address s` either writes RAM bytes `address + k` (`Mmu.write_ram_doubleword`) or folds `Mmu.store_raw?` over them.
  `InstructionFrame.storeFold_rule_of_step` (`ProofSupport/InstructionFrame.lean:133`) handles the fold with the relation "the device changes by `DeviceStoreAt`".
- `Frame.sourceValue_xreg_eq`: an architectural register that no row writes keeps its `sourceValue`, which is the value `rX_bits` returns.
  Proof: a 32-case split on the register index.
- `Program.resetsPool_of_check`.

The existing preservation machinery is too coarse for most of `Frame`, so the proof can reuse only parts of it.
`InstructionFrame.Rules` and `NonStoreRules` (`ProofSupport/InstructionFrame.lean:26-55`) require the relation to hold for an arbitrary replacement of the Sail state (`sail`), an arbitrary virtual-register write (`vreg`) and a store at an arbitrary address (`store`).
`Frame` holds for none of these: it constrains which Sail registers, which virtual registers and which addresses change.
These rules can still prove the clauses that do not mention registers or addresses: `hostIO`, and `JoltIOSetupFrame.Same` through `JoltIOSetupFrame.execProgram_rule` (`ProofSupport/DeviceFrame.lean:154`).
`StatePreservation.Preserves` (`ProofSupport/Preservation.lean:17`) and its `bind_rule`, `modify_rule` and `liftSail_rule` fit the per-row proof once the relation is fixed to `Frame ws s0`, with `s0` the row's start state.
`ProgramComposition` provides `Program.Run` and the append lemmas, so a program assembled with `Program.append` composes through `Frame.trans`.

## Deciding `WritesWithin`

`Program.rowsWithin` is a structurally recursive `Bool` function on `Program.rows`, and `Program.rowsWithin_iff` and `Program.rowsWithin_seq_append` relate it to the per-row meaning.
A `Decidable` instance for `p.rowsWithin ws = true` exists, but `decide` does not apply to the generated programs, because their rows contain the free parameters `rs1 rs2 rs3` (and `advice` for secp256k1).
`rfl` does apply: with `xregs = []` the check never compares two architectural registers, so it reduces on the open terms.

A single check on a whole program is too deep for the default limits.
I measured with `lake env lean --profile` on a scratch file, under heavy machine load.

- `rfl` on `(sha256RowsAuto rs1 rs2 rs3).rowsWithin ws = true` (1,900 rows) fails with "maximum recursion depth" and then a 200,000-heartbeat timeout in `whnf`, after about 20 s.
- The same `rfl` on `keccak256AbsorbPermuteRowsAuto` (3,121 rows) fails the same way, after about 20 s.
- `decide` with concrete registers in place of the parameters also hits the recursion limit.
- `rfl` on one generated chunk (about 100 rows) succeeds in under 50 ms.

The checks therefore run per chunk, with no recursion-depth or heartbeat override.
`Program.rowsWithin_seq_append`, `Program.storeSlots_seq_append`, `Program.resetsPoolCheck_seq_append` and `Program.resetsPoolCheck_seq_append_append` split a `Program.seq` of concatenated chunks.
`FrameInstances.lean` states one lemma per generated chunk (`_chunkN`, the row check and the store slots of that chunk, both by `rfl`) and assembles them with these lemmas.
For the pool reset, only the final chunks that contain the last write of each pool register need checking: the last chunk, or the last two for `Keccak256AbsorbPermute` and `Secp256k1Squarer`.
`scripts/expansion-parity/gen_frame_instances.py` writes the file from the generated rows; `--check` confirms that the committed file matches its output byte for byte.

Two further limits shaped the instance file.
Checking all chunks of a 31-chunk Keccak program inside one declaration exceeds the 200,000-heartbeat budget, so each chunk gets its own lemma.
`simp only [keccak256RowsAutoList]` and `rw [keccak256RowsAutoList]` also exceed the budget on the 31-chunk definition, while `unfold` is cheap, so the assembly proofs start with `unfold`.
With this layout `lake build JoltBytecode.Inlines.FrameInstances` takes 51 s to 143 s, depending on machine load, for the 17 programs (twelve `rd ≠ x0` cases and five hash `rd = x0` cases), and no proof in the file needs an option override.
The `_writesWithin` and `_resetsPoolCheck` lemmas depend only on `propext` and `Quot.sound`; the `_frame` corollaries inherit the staged `sorry` of `execInstr_frame` through `frame_of_run`.

A later per-inline file can reuse this pattern directly; the generator could also emit the per-chunk lemmas next to the rows.

## Resolved questions

The coordinator settled the four questions of the first draft.

1. Store bases must be architectural registers, and the seven secp256k1 `rd = x0` instances are dropped (decision D7).
   The hash `rd = x0` instances stay.
2. The floor-store clause stays; no instance exercises it.
3. `Frame.sailRegs` stays over every Sail register, because `Related.regs` compares the whole register file.
4. `Frame.outputs_size` states the `outputs_size` corollary, and it is proved.
