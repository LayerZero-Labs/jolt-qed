# Changes to the trusted Sail translation in PR 71

Date: 2026-11-24.
Jolt commit checked: `fe1cc674aa40a6036ff7310ee2344644bb45093a` (`fe1cc674`), Jolt's `main`.
Lean commit checked: `19d36c5be59c8189126acc1b5cd21dbcbb4f376e` (`19d36c5b`), the head of PR 71 (`split/a-sail`).
This report records every change PR 71 makes to the inputs of the trusted model `LeanRV64D`: the configuration file, the module list, and the edits the regeneration script makes to the generated Lean.
The Sail patch `sail-import/patches/sail-riscv-jolt-hart.patch` is not covered here.

## Changes to the config

### The extensions we turn on

The Sail compiler reads the configuration file [`sail-import/rv64d_jolt.json`](https://github.com/LayerZero-Labs/jolt-qed/blob/19d36c5be59c8189126acc1b5cd21dbcbb4f376e/sail-import/rv64d_jolt.json#L157) to decide which RISC-V extensions to support.
An extension is a named part of RISC-V that a machine may or may not have, such as multiplication.
Before [PR 71](https://github.com/LayerZero-Labs/jolt-qed/pull/71), this file turned on 77 extensions.
Jolt's tracer accepts far fewer instructions, and it panics on every other instruction.
After PR 71, the file turns on only these 7, so that the Sail model describes the same machine as Jolt.
This also matters for instructions Jolt does run.
For example, what `MRET` does depends on whether the machine has a user mode, which is the extension `U`.

- `M` adds integer multiplication and division, for example `MUL` and `DIV`.
- `A` adds atomic instructions, for example `AMOADD.W`, and the load-reserved and store-conditional pair `LR` and `SC`.
- `Zca` adds 16-bit compressed forms of common instructions, for example `C.ADDI`.
- `Zicsr` adds instructions that read and write control and status registers (CSRs), for example `CSRRW`.
  Jolt, on its main branch at `fe1cc674`, accepts all six of these instructions (`CSRRW`, `CSRRS`, `CSRRC`, `CSRRWI`, `CSRRSI` and `CSRRCI`).
  It accepts them only on six CSRs, `mstatus`, `mtvec`, `mscratch`, `mepc`, `mcause` and `mtval` ([`Instruction::decode`](https://github.com/a16z/jolt/blob/fe1cc674aa40a6036ff7310ee2344644bb45093a/tracer/src/instruction/mod.rs#L1330-L1393) and [`is_supported_csr`](https://github.com/a16z/jolt/blob/fe1cc674aa40a6036ff7310ee2344644bb45093a/tracer/src/utils/virtual_registers.rs#L229-L234)).

These extensions add no instructions.
They describe how memory behaves.

- `Svbare` allows the mode in which addresses are not translated.
  The machine runs only in machine mode (M-mode), the most privileged mode, and every virtual-memory mode (`Sv39`, `Sv48`, `Sv57`) is off.
  So the function that translates virtual addresses to physical addresses is the identity function.
- `Ziccamoa` means main memory supports the atomic instructions of `A`.
- `Ziccrse` means an `LR` and `SC` pair on main memory eventually succeeds.

The base integer instruction set `I`, with instructions such as `ADD` and `LW`, is always on and has no entry in the file.

The other 70 extensions are now off, for example floating point (`F` and `D`) and vector (`V`).
No extension that was off before is on now.

### The memory regions

The configuration lists the address ranges that a program may access ([lines 81–134](https://github.com/LayerZero-Labs/jolt-qed/blob/19d36c5be59c8189126acc1b5cd21dbcbb4f376e/sail-import/rv64d_jolt.json#L81-L134)).
Sail checks every load, store and instruction fetch against this list, and an access outside every region faults.
Before PR 71 there were three regions, upstream's defaults: a ROM at `0x1000` that held the device tree, an MMIO region at `0x0200_0000` that held the timer device (the CLINT), and 2 GiB of RAM at `0x8000_0000`.
After PR 71 there are two.
The first runs from `0x4000_0000` to `0x8000_0000`, where Jolt's I/O window lies, and is readable and writable but not executable.
The second is RAM, from `0x8000_0000` to the top of the 64-bit address space, and is readable, writable and executable.
The CLINT setting itself is unchanged, but its address now lies outside both regions, so Sail faults on any access to it.
Jolt's tracer does not support the CLINT either ([`unsupported_peripheral`](https://github.com/a16z/jolt/blob/fe1cc674aa40a6036ff7310ee2344644bb45093a/tracer/src/emulator/mmu.rs#L187)).

Both regions allow the atomic instructions of `A` (`AMOArithmetic`).
Only RAM allows `LR` and `SC` (`RsrvEventual`), and Jolt's `LR` expansion likewise requires an address at or above `0x8000_0000` ([`expand_lrw`](https://github.com/a16z/jolt/blob/fe1cc674aa40a6036ff7310ee2344644bb45093a/crates/jolt-program/src/expand/memory/lrw.rs#L11)).
The remaining attribute changes, `supports_cbo_zero`, `supports_pte_read`, `supports_pte_write` and the idempotence flags, only matter for extensions that are now off.
The diff below has the comment lines removed.
The first two old regions are removed, a new first region is added, and the RAM region is compared line by line.

```diff
 "regions": [
-  {
-    "base": {
-      "len": 64,
-      "value": "0x1000"
-    },
-    "size": {
-      "len": 64,
-      "value": "0x1000"
-    },
-    "attributes": {
-      "cacheable": true,
-      "coherent": false,
-      "executable": false,
-      "readable": true,
-      "writable": false,
-      "read_idempotent": true,
-      "write_idempotent": true,
-      "misaligned_fault": "NoFault",
-      "atomic_support": "AMONone",
-      "reservability": "RsrvNone",
-      "supports_cbo_zero": false,
-      "supports_pte_read": false,
-      "supports_pte_write": false
-    },
-    "include_in_device_tree": false
-  },
-  {
-    "base": {
-      "len": 64,
-      "value": "0x2000000"
-    },
-    "size": {
-      "len": 64,
-      "value": "0x2000000"
-    },
-    "attributes": {
-      "cacheable": false,
-      "coherent": true,
-      "executable": false,
-      "readable": true,
-      "writable": true,
-      "read_idempotent": false,
-      "write_idempotent": false,
-      "misaligned_fault": "AlignmentFault",
-      "atomic_support": "AMONone",
-      "reservability": "RsrvNone",
-      "supports_cbo_zero": false,
-      "supports_pte_read": false,
-      "supports_pte_write": false
-    },
-    "include_in_device_tree": false
-  },
+  {
+    "base": {
+      "len": 64,
+      "value": "0x40000000"
+    },
+    "size": {
+      "len": 64,
+      "value": "0x40000000"
+    },
+    "attributes": {
+      "cacheable": false,
+      "coherent": true,
+      "executable": false,
+      "readable": true,
+      "writable": true,
+      "read_idempotent": true,
+      "write_idempotent": true,
+      "misaligned_fault": "AlignmentFault",
+      "atomic_support": "AMOArithmetic",
+      "reservability": "RsrvNone",
+      "supports_cbo_zero": false,
+      "supports_pte_read": false,
+      "supports_pte_write": false
+    },
+    "include_in_device_tree": false
+  },
   {
     "base": {
       "len": 64,
       "value": "0x80000000"
     },
     "size": {
       "len": 64,
-      "value": "0x80000000"
+      "value": "0xFFFFFFFF80000000"
     },
     "attributes": {
       "cacheable": true,
       "coherent": true,
       "executable": true,
       "readable": true,
       "writable": true,
       "read_idempotent": true,
       "write_idempotent": true,
       "misaligned_fault": "NoFault",
-      "atomic_support": "AMOCASQ",
+      "atomic_support": "AMOArithmetic",
       "reservability": "RsrvEventual",
-      "supports_cbo_zero": true,
-      "supports_pte_read": true,
-      "supports_pte_write": true
+      "supports_cbo_zero": false,
+      "supports_pte_read": false,
+      "supports_pte_write": false
     },
     "include_in_device_tree": true
   }
 ]
```

### Memory protection (PMP)

PMP entries are address ranges that a running program sets up through CSRs such as `pmpcfg0` and `pmpaddr0`, to forbid some accesses.
The number of entries drops from 16 to 0 ([lines 60–67](https://github.com/LayerZero-Labs/jolt-qed/blob/19d36c5be59c8189126acc1b5cd21dbcbb4f376e/sail-import/rv64d_jolt.json#L60-L67)).
With no entries, Sail's PMP check never faults ([`pmpCheck`](https://github.com/LayerZero-Labs/jolt-qed/blob/19d36c5be59c8189126acc1b5cd21dbcbb4f376e/LeanRV64D/PmpControl.lean#L283)), and the PMP CSRs do not exist.
Jolt's tracer implements no memory protection, and it rejects every CSR other than its six, so a Jolt program cannot set up PMP entries anyway.

```diff
   "pmp": {
     "grain": 0,
-    "count": 16,
-    "usable_count": 16,
+    "count": 0,
+    "usable_count": 0,
     "tor_supported": true,
     "na4_supported": true,
```

### Control and status registers

Four settings make parts of the CSRs read-only ([lines 21–30](https://github.com/LayerZero-Labs/jolt-qed/blob/19d36c5be59c8189126acc1b5cd21dbcbb4f376e/sail-import/rv64d_jolt.json#L21-L30)).
`writable_misa` becomes false, so `misa`, the CSR that lists the extensions, is fixed.
`writable_fiom` becomes false, so the FIOM bit of `menvcfg` is fixed.
`writable_hpm_counters` and `scounteren_writable_bits` become 0, so the performance counters, and the `scounteren` bits that control them, are read-only zero.
Jolt accepts none of these CSRs, so a Jolt program never writes them.

```diff
   "xlen": 64,
   "E": false,
-  "writable_misa": true,
-  "writable_fiom": true,
+  "writable_misa": false,
+  "writable_fiom": false,
   "writable_hpm_counters": {
     "len": 32,
-    "value": "0xFFFF_FFFF"
+    "value": "0x0"
   },
   "scounteren_writable_bits": {
     "len": 32,
-    "value": "0xFFFF_FFFF"
+    "value": "0x0"
   },
   "xtval_nonzero": {
```

A new setting, `base.mstatus.fs_legal_states`, is set to `ExtContext_Off` ([lines 55–57](https://github.com/LayerZero-Labs/jolt-qed/blob/19d36c5be59c8189126acc1b5cd21dbcbb4f376e/sail-import/rv64d_jolt.json#L55-L57)).
It fixes the floating-point state field `mstatus.FS` to Off, which fits a machine without `F` and `D`.
Sail at our pinned commit has no such setting.
The patch in this PR backports it from upstream sail-riscv `81184531`.

```diff
     "xtvec_mode": "Xtvec_Ignore",
     "rv32zdinx_odd_register": "Zdinx_Illegal"
+  },
+  "mstatus": {
+    "fs_legal_states": "ExtContext_Off"
   }
 },
```

### The device-tree address

`memory.dtb_address` changes from `0x1000` to `0x0` ([lines 77–80](https://github.com/LayerZero-Labs/jolt-qed/blob/19d36c5be59c8189126acc1b5cd21dbcbb4f376e/sail-import/rv64d_jolt.json#L77-L80)).
It was the address of the device tree in the ROM region, which is removed.
The generated Lean model does not contain this value.
Its only mention of a device-tree address is the configuration check `dtb_within_configured_pma_memory`, which takes the address as an argument ([`ValidateConfig.lean`, line 566](https://github.com/LayerZero-Labs/jolt-qed/blob/19d36c5be59c8189126acc1b5cd21dbcbb4f376e/LeanRV64D/ValidateConfig.lean#L566)).

```diff
   "dtb_address": {
     "len": 64,
-    "value": "0x1000"
+    "value": "0x0"
   },
```

### LR and SC reservations

A new setting, `platform.reservation`, says when a store-conditional `SC` succeeds ([lines 151–155](https://github.com/LayerZero-Labs/jolt-qed/blob/19d36c5be59c8189126acc1b5cd21dbcbb4f376e/sail-import/rv64d_jolt.json#L151-L155)).

- `require_exact_reservation_addr = true`: only at the exact address of the matching `LR`.
- `require_width_within = true`: only if the `SC` is no wider than that `LR`.
- `invalidate_on_xret = false`: `MRET` does not cancel the reservation.

These are Jolt's rules.
Jolt's `SC` succeeds only if a reservation is set at exactly its address with a width at least its own ([`Cpu::reservation_covers`](https://github.com/a16z/jolt/blob/fe1cc674aa40a6036ff7310ee2344644bb45093a/tracer/src/emulator/cpu.rs#L575)), and Jolt's `MRET` keeps the reservation ([`expand_mret`](https://github.com/a16z/jolt/blob/fe1cc674aa40a6036ff7310ee2344644bb45093a/crates/jolt-program/src/expand/control_flow/mret.rs#L14)).
Sail at our pinned commit has no such setting, because it left reservations to uninterpreted functions.
The patch in this PR makes reservations part of Sail's state, adds `require_exact_reservation_addr` and `invalidate_on_xret` as upstream sail-riscv later defined them, and adds `require_width_within`, which is new.

```diff
   "instructions_per_tick": 2,
   "wfi_is_nop": false,
-  "max_time_to_wait": 10
+  "max_time_to_wait": 10,
+  "reservation": {
+    "require_exact_reservation_addr": true,
+    "require_width_within": true,
+    "invalidate_on_xret": false
+  }
 },
```

## Changes to the module list

`sail-import/PROVENANCE.toml` lists the Sail modules the compiler translates ([`[modules]`, lines 67–118](https://github.com/LayerZero-Labs/jolt-qed/blob/19d36c5be59c8189126acc1b5cd21dbcbb4f376e/sail-import/PROVENANCE.toml#L67-L118)).
Before PR 71 it selected 68 modules.
PR 71 keeps 29 and lists the other 39 under `not_selected`.

| Why it is kept | Modules |
| --- | --- |
| Sail infrastructure | `prelude`, `core`, `sys`, `exceptions`, `pmp`, `main`, `postlude` |
| Instructions Jolt's decoder accepts (RV64IMAC with Zicsr) | `I_types`, `I_insts`, `M_types`, `M_insts`, `A_types`, `Zaamo`, `Zalrsc`, `Zca`, `Zicsr_types`, `Zicsr_insts` |
| `ANDN`, which Jolt's own expansions use | `Zbb` |
| Required by the modules above in `model/riscv.sail_project` | `B_types`, `V_core`, `FD_core`, `Smcntrpmf`, `Stateen_csrs`, `Stateen_regs`, `Zicbom_types`, `Zicbop_types`, `Zicfilp_regs`, `Zicfilp_insts`, `CFI_types` |

Every dropped module is for an extension that the configuration turns off and that Jolt never runs.
Dropping them shrinks the generated model by about 22,000 lines, and it removes the three AES and SM4 S-box tables in `TypesKext.lean`, which an earlier version of this PR had to rewrite in the script.

Dropping a module changes one thing in the code that stays.
The dropped modules hold the `currentlyEnabled` clauses of their extensions.
For B, H, Sscofpmf, Ssqosid, Zfhmin, Zicbom, Zicboz, Zicntr and Zkr, which the kept code still names, `currentlyEnabled` now fails a Sail assertion where the full model returns false.
According to the comment in `PROVENANCE.toml`, the kept code asks about these extensions only in S-mode, after decoding a Zbb instruction, and when accessing `mseccfg`, `menvcfg`, `mip`, `mstateen0`, the Smcntrpmf CSRs or `hstateen`.
Jolt's hart never enters S-mode, and Jolt rejects those encodings and CSRs.

## Edits to trusted code with python script

After the Sail compiler writes the Lean files, `scripts/regen-sail-model.sh` runs a `python3` program that edits those files in place ([lines 116–178](https://github.com/LayerZero-Labs/jolt-qed/blob/19d36c5be59c8189126acc1b5cd21dbcbb4f376e/scripts/regen-sail-model.sh#L116-L178)).
It makes two edits.
Each edit fails the script if the generated text is not exactly what it expects, so a change in Sail's output cannot slip through.
Neither edit changes what a definition means.
Both change only the limits Lean checks the files under.
Before the Python program, the script also applies the `sed` rewrite of `print_rvfi_exec` from PR 70 ([lines 71–84](https://github.com/LayerZero-Labs/jolt-qed/blob/19d36c5be59c8189126acc1b5cd21dbcbb4f376e/scripts/regen-sail-model.sh#L71-L84)).

### 1. The file-wide limits are removed

Sail's Lean backend starts every generated file with two lines that make the file's limits effectively unlimited.
The program deletes both lines from every generated file ([lines 121–148](https://github.com/LayerZero-Labs/jolt-qed/blob/19d36c5be59c8189126acc1b5cd21dbcbb4f376e/scripts/regen-sail-model.sh#L121-L148)).
It skips `FakeReal.lean`, `RiscvExtras.lean` and `SpecializationV1.lean`, which are copied unchanged from lean-sail and sail-riscv and carry no such lines.
It fails unless every other file has exactly one copy of each line, and unless no line in the finished tree mentions `maxHeartbeats`, `maxRecDepth` or `maxSize`.
For example, in `LeanRV64D/ZicsrInsts.lean` the edit is this.

```diff
-set_option maxHeartbeats 1_000_000_000
-set_option maxRecDepth 1_000_000
 set_option linter.unusedVariables false
 set_option match.ignoreUnusedAlts true
```

The generated model is then checked at Lean's default limits, 200,000 heartbeats and a recursion depth of 512.
This lowers the limits.
A `set_option` at the top of a file applies only inside that file, so the old lines never affected our proofs.

### 2. Five declarations get their own recursion depth

A few declarations still exceed the default recursion depth.
The program puts `set_option maxRecDepth ... in` directly before each one, so the raised limit applies to that declaration only ([lines 150–176](https://github.com/LayerZero-Labs/jolt-qed/blob/19d36c5be59c8189126acc1b5cd21dbcbb4f376e/scripts/regen-sail-model.sh#L150-L176)).
No declaration gets more heartbeats.

| File | Declaration | Limit |
| --- | --- | --- |
| `LeanRV64D/SysControl.lean` | `is_CSR_accessible` | `maxRecDepth 750` |
| `LeanRV64D/ZicsrInsts.lean` | `read_CSR` | `maxRecDepth 700` |
| `LeanRV64D/ZicsrInsts.lean` | `write_CSR` | `maxRecDepth 800` |
| `LeanRV64D/InstsEnd.lean` | `encdec_backwards` | `maxRecDepth 750` |
| `LeanRV64D/InstsEnd.lean` | `encdec_backwards_matches` | `maxRecDepth 750` |

The first three are one generated chain of cases over every CSR address, and the last two are Sail's decoder over every 32-bit instruction.
The program fails unless it finds each declaration exactly once, preceded by a blank line, and unless the finished tree mentions a limit option exactly on the lines it inserted.
For example, `read_CSR` now starts like this ([`ZicsrInsts.lean`, line 236](https://github.com/LayerZero-Labs/jolt-qed/blob/19d36c5be59c8189126acc1b5cd21dbcbb4f376e/LeanRV64D/ZicsrInsts.lean#L236)).

```lean
set_option maxRecDepth 700 in
def read_CSR (b__0 : (BitVec 12)) : SailM (BitVec 64) := do
```
