# JoltBytecode re-pin statement inventory

Date: 2026-11-24.
Jolt pin: `ff6fc656813d950565c9f6e1258b78bdaf0e60e8`.
Lean baseline: `5d7d40eb7ca66229a5d3fc4c3e7438ce469dae0b`.
The source locations refer to the code revision named in the companion closing report.

## Premise meanings

The old RAM-store premise had a start-address heap bound and excluded the canary.
The new premise takes the actual little-endian value and byte width, uses the padded backing bound from the device layout, and requires every touched protected byte to keep its old value.
RAM membership, alignment, populated Sail bytes and Sail access checks remain the existing caller premises.
The protected code span and full-word input/advice/canary tests come from the MMU state and layout.
Narrow-store and word-AMO premises refer to the complete merged doubleword written by their lowered rows.
The old RAM-load heap bound becomes the padded backing bound.
Setup transport across an arbitrary intermediate state previously needed layout equality; it now also needs code-interval equality.
Word-prelude conclusions that now return `SetupSame` strengthen the old layout-only conclusion.
The generic frame Sail premise now permits memory-preserving Sail effects; the old premise permitted arbitrary Sail replacements.
Its store premise now refers to a checked MMU doubleword store, and it includes an explicit halt-metadata preservation rule.

## Direct statement changes

Each diff gives the complete changed theorem header, or the declaration and fields of a changed bundled premise.
A minus line belongs to the baseline; a plus line belongs to this migration.
Definitions are included where their signature changed.
Only declaration text is inventoried; comments and proof bodies are not theorem statements.

### `JoltRamLoadOk` (structure)

File: `JoltBytecode/Assumptions.lean:202`.

```diff
@@ -1,2 +1,2 @@
 structure JoltRamLoadOk (addr : BitVec 64) (js : SailJoltState) : Prop where
-  below_heap_end : addr.toNat < js.jolt_device.memory_layout.heap_end.toNat
+  below_backing_end : addr.toNat < JoltISA.Mmu.ram_backing_end js.jolt_device
```

### `JoltRamStoreOk` (structure)

File: `JoltBytecode/Assumptions.lean:210`.

```diff
@@ -1,5 +1,4 @@
-structure JoltRamStoreOk (addr : BitVec 64) (js : SailJoltState) : Prop where
-  below_heap_end : addr.toNat < js.jolt_device.memory_layout.heap_end.toNat
-  outside_canary :
-    addr.toNat < js.jolt_device.memory_layout.stack_end.toNat ∨
-      js.jolt_device.memory_layout.stack_end.toNat + JoltISA.STACK_CANARY_SIZE ≤ addr.toNat
+structure JoltRamStoreOk (addr : BitVec 64) (js : SailJoltState)
+    (value : BitVec 64) (width : Nat) : Prop where
+  below_backing_end : addr.toNat < JoltISA.Mmu.ram_backing_end js.jolt_device
+  preserves_protected : JoltISA.Mmu.protected_store_ok js addr.toNat value width = true
```

### `StoreProgramEqSailAssumptions` (structure)

File: `JoltBytecode/Bundles.lean:234`.

```diff
@@ -1,8 +1,11 @@
 structure StoreProgramEqSailAssumptions
-    (imm : BitVec 12) (rs2 rs1 : regidx) (js : SailJoltState)
+    (imm : BitVec 12) (rs2 rs1 : regidx) (js : SailJoltState) (storeWidth : Nat := 8)
     extends LoadProgramEqSailAssumptions imm rs1 js,
       DwordWriteWindowAssumptions
         (compute_aligned_dword_base_address rs1_val imm) js.sail where
   rs2_val : BitVec 64
   rs2_read : rX_bits rs2 js.sail = .ok rs2_val js.sail
   jolt_ram_store : Assumptions.JoltRamStoreOk (compute_aligned_dword_base_address rs1_val imm) js
+    (JoltISA.storeDwordValue storeWidth (rs1_val + sign_extend (m := 64) imm)
+      (JoltISA.Mmu.ram_doubleword js.sail.mem
+        (compute_aligned_dword_base_address rs1_val imm).toNat) rs2_val) 8
```

### `StoreProgramEqSailAssumptions.linkedCSRs` (theorem)

File: `JoltBytecode/Bundles.lean:246`.

```diff
@@ -1,4 +1,4 @@
 theorem StoreProgramEqSailAssumptions.linkedCSRs
-    {imm : BitVec 12} {rs2 rs1 : regidx} {js : SailJoltState}
-    (h : StoreProgramEqSailAssumptions imm rs2 rs1 js) :
+    {imm : BitVec 12} {rs2 rs1 : regidx} {js : SailJoltState} {storeWidth : Nat}
+    (h : StoreProgramEqSailAssumptions imm rs2 rs1 js storeWidth) :
     LinkedCSRs js
```

### `AmoDwordProgramEqSailAssumptions` (structure)

File: `JoltBytecode/Bundles.lean:279`.

```diff
@@ -1,8 +1,9 @@
 structure AmoDwordProgramEqSailAssumptions
     (op : amoop) (rs2 rs1 rd : regidx) (js : SailJoltState)
     extends AmoRegisterAssumptions rs2 rs1 rd js,
       DwordAtomicWindowAssumptions op rs1_val js.sail where
   cur_privilege : Assumptions.CurPrivilegeMachine js.sail
   mstatus_mprv : Assumptions.MstatusMprvZero js.sail
   jolt_ram_load : Assumptions.JoltRamLoadOk rs1_val js
   jolt_ram_store : Assumptions.JoltRamStoreOk rs1_val js
+    (JoltISA.amoValue op rs2_val (JoltISA.Mmu.ram_doubleword js.sail.mem rs1_val.toNat)) 8
```

### `AmoWordProgramEqSailAssumptions` (structure)

File: `JoltBytecode/Bundles.lean:303`.

```diff
@@ -1,8 +1,10 @@
 structure AmoWordProgramEqSailAssumptions
     (op : amoop) (rs2 rs1 rd : regidx) (js : SailJoltState)
     extends AmoRegisterAssumptions rs2 rs1 rd js,
       DwordAtomicWindowAssumptions op (amoWordBase rs1_val) js.sail where
   cur_privilege : Assumptions.CurPrivilegeMachine js.sail
   mstatus_mprv : Assumptions.MstatusMprvZero js.sail
   jolt_ram_load : Assumptions.JoltRamLoadOk (amoWordBase rs1_val) js
   jolt_ram_store : Assumptions.JoltRamStoreOk (amoWordBase rs1_val) js
+    (JoltISA.amoWordStoreValue op rs1_val
+      (JoltISA.Mmu.ram_doubleword js.sail.mem (amoWordBase rs1_val).toNat) rs2_val) 8
```

### `amo_word_swap_pre64_aligned_run_for` (theorem)

File: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/Amoswapw.lean:32`.

```diff
@@ -1,19 +1,19 @@
 theorem amo_word_swap_pre64_aligned_run_for
     (rd : regidx) (tail : JoltISA.Program) (rs1 : regidx) (js : SailJoltState)
     (addr : BitVec 64) (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
     (hbytes : MemBytesPresentAt js.sail (amoWordBase addr) 8)
     (hread : Assumptions.NotReadableMmio (amoWordBase addr) 8 js.sail)
     (h_no_ovf : (amoWordBase addr).toNat + 7 < 2 ^ 64)
     (halign : addr &&& (3 : BitVec 64) = 0)
     (hjolt : Assumptions.JoltRamLoadOk (amoWordBase addr) js) :
     ∃ pre,
       (JoltISA.execProgram (JoltISA.amoPre64Program rs1 (JoltISA.amoWordOldVRegFor rd)
         (JoltISA.amoWordDwordVRegFor rd) (JoltISA.amoWordLaneVRegFor rd) tail)).run js =
         (JoltISA.execProgram tail).run pre ∧
       pre.sail = js.sail ∧
       pre.vregs (JoltISA.amoWordDwordVRegFor rd) =
         loaded_dword_at js.sail (amoWordBase addr) hbytes h_no_ovf ∧
       pre.vregs (JoltISA.amoWordLaneVRegFor rd) = amoWordLaneMask addr ∧
       pre.vregs (JoltISA.amoWordOldVRegFor rd) = amoWordLaneOld addr
         (loaded_dword_at js.sail (amoWordBase addr) hbytes h_no_ovf) ∧
-      pre.jolt_device.memory_layout = js.jolt_device.memory_layout
+      JoltIOSetupFrame.SetupSame js pre
```

### `amo_word_swap_sd_spliced_dword_run` (theorem)

File: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/Amoswapw.lean:764`.

```diff
@@ -1,20 +1,20 @@
 theorem amo_word_swap_sd_spliced_dword_run
     (js : SailJoltState) (s : SailState) (addr dwordNew old : BitVec 64)
     (hpriv : Assumptions.CurPrivilegeMachine s)
     (hmprv : Assumptions.MstatusMprvZero s)
     (hstore_pmp : Assumptions.StorePmpOk (amoWordBase addr) 8 s)
     (hwrite_mmio : Assumptions.NotWritableMmio (amoWordBase addr) 8 s)
     (h_no_ovf : (amoWordBase addr).toNat + 7 < 2 ^ 64)
     (h_sail : js.sail = s)
     (h_base : js.vregs JoltISA.amoWordSwapMaskVReg = amoWordBase addr)
     (h_dword : js.vregs JoltISA.amoWordSwapDwordVReg = dwordNew)
     (h_old : js.vregs JoltISA.amoWordSwapOldVReg = old)
-    (hjolt : Assumptions.JoltRamStoreOk (amoWordBase addr) js) :
+    (hjolt : Assumptions.JoltRamStoreOk (amoWordBase addr) js dwordNew 8) :
     ∃ js',
       js'.sail = state_after_dword_store s (amoWordBase addr) dwordNew ∧
       js'.vregs JoltISA.amoWordSwapOldVReg = old ∧
       ∀ tail,
         (JoltISA.execProgram
           (.instr (JoltISA.Encoded.SD (.vreg JoltISA.amoWordSwapMaskVReg)
             (.vreg JoltISA.amoWordSwapDwordVReg) (0 : BitVec 12)) tail)).run js =
           (JoltISA.execProgram tail).run js'
```

### `amo_word_swap_sd_spliced_dword_run_for` (theorem)

File: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/Amoswapw.lean:827`.

```diff
@@ -1,22 +1,22 @@
 theorem amo_word_swap_sd_spliced_dword_run_for
     (rd : regidx)
     (js : SailJoltState) (s : SailState) (addr dwordNew old : BitVec 64)
     (hpriv : Assumptions.CurPrivilegeMachine s)
     (hmprv : Assumptions.MstatusMprvZero s)
     (hstore_pmp : Assumptions.StorePmpOk (amoWordBase addr) 8 s)
     (hwrite_mmio : Assumptions.NotWritableMmio (amoWordBase addr) 8 s)
     (h_no_ovf : (amoWordBase addr).toNat + 7 < 2 ^ 64)
     (h_sail : js.sail = s)
     (h_base : js.vregs (JoltISA.amoWordSwapMaskVRegFor rd) = amoWordBase addr)
     (h_dword : js.vregs (JoltISA.amoWordSwapDwordVRegFor rd) = dwordNew)
     (h_old : js.vregs (JoltISA.amoWordSwapOldVRegFor rd) = old)
-    (hjolt : Assumptions.JoltRamStoreOk (amoWordBase addr) js) :
+    (hjolt : Assumptions.JoltRamStoreOk (amoWordBase addr) js dwordNew 8) :
     ∃ js',
       js'.sail = state_after_dword_store s (amoWordBase addr) dwordNew ∧
       js'.vregs (JoltISA.amoWordSwapOldVRegFor rd) = old ∧
       ∀ tail,
         (JoltISA.execProgram
           (.instr (JoltISA.Encoded.SD (.vreg (JoltISA.amoWordSwapMaskVRegFor rd))
             (.vreg (JoltISA.amoWordSwapDwordVRegFor rd))
             (0 : BitVec 12)) tail)).run js =
           (JoltISA.execProgram tail).run js'
```

### `amo_word_swap_post64_amoswap_aligned_run` (theorem)

File: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/Amoswapw.lean:937`.

```diff
@@ -1,40 +1,40 @@
 theorem amo_word_swap_post64_amoswap_aligned_run
     (rs2 rs1 rd : regidx) (js js_pre : SailJoltState)
     (hpriv : Assumptions.CurPrivilegeMachine js.sail)
     (hmprv : Assumptions.MstatusMprvZero js.sail)
     (addr rs2Val : BitVec 64) (oldWord : BitVec 32)
     (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
     (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
     (hbytes_base : MemBytesPresentAt js.sail (amoWordBase addr) 8)
     (hstore_pmp : Assumptions.StorePmpOk (amoWordBase addr) 8 js.sail)
     (hwrite_mmio : Assumptions.NotWritableMmio (amoWordBase addr) 8 js.sail)
     (h_no_ovf : (amoWordBase addr).toNat + 7 < 2 ^ 64)
     (h_align : addr &&& (3 : BitVec 64) = 0)
     (hpre_sail : js_pre.sail = js.sail)
     (hpre_dword :
       js_pre.vregs JoltISA.amoWordSwapDwordVReg =
         loaded_dword_at js.sail (amoWordBase addr) hbytes_base h_no_ovf)
     (hpre_shift :
       js_pre.vregs JoltISA.amoWordSwapShiftVReg =
         shift_bits_left addr (3 : BitVec 6))
     (hpre_old :
       js_pre.vregs JoltISA.amoWordSwapOldVReg =
         amoWordShiftedOld addr
           (loaded_dword_at js.sail (amoWordBase addr) hbytes_base h_no_ovf))
     (hold :
       (Sail.BitVec.extractLsb
         (amoWordShiftedOld addr
           (loaded_dword_at js.sail (amoWordBase addr) hbytes_base h_no_ovf))
         31 0 : BitVec 32) = oldWord)
-    (hjolt_store : Assumptions.JoltRamStoreOk (amoWordBase addr) js)
-    (hpre_layout : js_pre.jolt_device.memory_layout = js.jolt_device.memory_layout) :
+    (hjolt_store : Assumptions.JoltRamStoreOk (amoWordBase addr) js (amoWordSplicedDword addr rs2Val (JoltISA.Mmu.ram_doubleword js.sail.mem (amoWordBase addr).toNat)) 8)
+    (hpre_setup : JoltIOSetupFrame.SetupSame js js_pre) :
     ∃ jsf : SailJoltState,
       (JoltISA.execProgram
         (JoltISA.amoPost64ProgramWithScratch rs1 rd (.xreg rs2)
           JoltISA.amoWordSwapDwordVReg JoltISA.amoWordSwapShiftVReg
           JoltISA.amoWordSwapMaskVReg JoltISA.amoWordSwapOldVReg
           JoltISA.amoWordSwapInlineTmpVReg)).run js_pre =
         .ok RETIRE_SUCCESS jsf ∧
       jsf.sail =
         amoWordFinalSailState rd js.sail addr
           (Sail.BitVec.extractLsb rs2Val 31 0) oldWord
```

### `amo_word_swap_post64_amoswap_aligned_run_for` (theorem)

File: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/Amoswapw.lean:1062`.

```diff
@@ -1,42 +1,42 @@
 theorem amo_word_swap_post64_amoswap_aligned_run_for
     (rs2 rs1 rd : regidx) (js js_pre : SailJoltState)
     (hpriv : Assumptions.CurPrivilegeMachine js.sail)
     (hmprv : Assumptions.MstatusMprvZero js.sail)
     (addr rs2Val : BitVec 64) (oldWord : BitVec 32)
     (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
     (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
     (hbytes_base : MemBytesPresentAt js.sail (amoWordBase addr) 8)
     (hstore_pmp : Assumptions.StorePmpOk (amoWordBase addr) 8 js.sail)
     (hwrite_mmio : Assumptions.NotWritableMmio (amoWordBase addr) 8 js.sail)
     (h_no_ovf : (amoWordBase addr).toNat + 7 < 2 ^ 64)
     (h_align : addr &&& (3 : BitVec 64) = 0)
     (hpre_sail : js_pre.sail = js.sail)
     (hpre_dword :
       js_pre.vregs (JoltISA.amoWordSwapDwordVRegFor rd) =
         loaded_dword_at js.sail (amoWordBase addr) hbytes_base h_no_ovf)
     (hpre_shift :
       js_pre.vregs (JoltISA.amoWordSwapShiftVRegFor rd) =
         shift_bits_left addr (3 : BitVec 6))
     (hpre_old :
       js_pre.vregs (JoltISA.amoWordSwapOldVRegFor rd) =
         amoWordShiftedOld addr
           (loaded_dword_at js.sail (amoWordBase addr) hbytes_base h_no_ovf))
     (hold :
       (Sail.BitVec.extractLsb
         (amoWordShiftedOld addr
           (loaded_dword_at js.sail (amoWordBase addr) hbytes_base h_no_ovf))
         31 0 : BitVec 32) = oldWord)
-    (hjolt_store : Assumptions.JoltRamStoreOk (amoWordBase addr) js)
-    (hpre_layout : js_pre.jolt_device.memory_layout = js.jolt_device.memory_layout) :
+    (hjolt_store : Assumptions.JoltRamStoreOk (amoWordBase addr) js (amoWordSplicedDword addr rs2Val (JoltISA.Mmu.ram_doubleword js.sail.mem (amoWordBase addr).toNat)) 8)
+    (hpre_setup : JoltIOSetupFrame.SetupSame js js_pre) :
     ∃ jsf : SailJoltState,
       (JoltISA.execProgram
         (JoltISA.amoPost64ProgramWithScratch rs1 rd (.xreg rs2)
           (JoltISA.amoWordSwapDwordVRegFor rd)
           (JoltISA.amoWordSwapShiftVRegFor rd)
           (JoltISA.amoWordSwapMaskVRegFor rd)
           (JoltISA.amoWordSwapOldVRegFor rd)
           (JoltISA.amoWordSwapInlineTmpVRegFor rd))).run js_pre =
         .ok RETIRE_SUCCESS jsf ∧
       jsf.sail =
         amoWordFinalSailState rd js.sail addr
           (Sail.BitVec.extractLsb rs2Val 31 0) oldWord
```

### `amoswapwProgram_concrete_aligned` (theorem)

File: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/Amoswapw.lean:1204`.

```diff
@@ -1,28 +1,28 @@
 theorem amoswapwProgram_concrete_aligned
     (rs2 rs1 rd : regidx) (js : SailJoltState)
     (hpriv : Assumptions.CurPrivilegeMachine js.sail)
     (hmprv : Assumptions.MstatusMprvZero js.sail)
     (addr rs2Val : BitVec 64) (oldWord : BitVec 32)
     (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
     (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
     (hbytes_base : MemBytesPresentAt js.sail (amoWordBase addr) 8)
     (hload_pmp : Assumptions.LoadPmpOk (amoWordBase addr) 8 js.sail)
     (hread_mmio : Assumptions.NotReadableMmio (amoWordBase addr) 8 js.sail)
     (hstore_pmp : Assumptions.StorePmpOk (amoWordBase addr) 8 js.sail)
     (hwrite_mmio : Assumptions.NotWritableMmio (amoWordBase addr) 8 js.sail)
     (h_align : addr &&& (3 : BitVec 64) = 0)
     (hjolt_load : Assumptions.JoltRamLoadOk (amoWordBase addr) js)
-    (hjolt_store : Assumptions.JoltRamStoreOk (amoWordBase addr) js)
+    (hjolt_store : Assumptions.JoltRamStoreOk (amoWordBase addr) js (amoWordSplicedDword addr rs2Val (JoltISA.Mmu.ram_doubleword js.sail.mem (amoWordBase addr).toNat)) 8)
     (hold :
       (Sail.BitVec.extractLsb
         (amoWordShiftedOld addr
           (loaded_dword_at js.sail (amoWordBase addr) hbytes_base
             ((amo_word_base_no_ovf addr) :
               (amoWordBase addr).toNat + 7 < 2 ^ 64)))
         31 0 : BitVec 32) = oldWord) :
     ∃ jsf : SailJoltState,
       (JoltISA.execProgram (JoltISA.amoswapwProgramAuto rd rs1 rs2)).run js =
         .ok RETIRE_SUCCESS jsf ∧
       jsf.sail =
         amoWordFinalSailState rd js.sail addr
           (Sail.BitVec.extractLsb rs2Val 31 0) oldWord
```

### `amo_dword_sd_result_run` (theorem)

File: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/Dword.lean:232`.

```diff
@@ -1,24 +1,24 @@
 theorem amo_dword_sd_result_run
     (rs2 rs1 : regidx) (js_afterLoad : SailJoltState)
     (addr result : BitVec 64)
     (hrs1 : rX_bits rs1 js_afterLoad.sail = .ok addr js_afterLoad.sail)
     (hrs2 : rX_bits rs2 js_afterLoad.sail = .ok result js_afterLoad.sail)
     (h_align : addr &&& (7 : BitVec 64) = 0)
     (hwrite :
       vmem_write_addr (Virtaddr addr) 8 result
         (Store Data) false false false js_afterLoad.sail =
         .ok (Ok true)
           (state_after_dword_store js_afterLoad.sail addr result))
     (h_ram : JoltISA.RAM_START_ADDRESS ≤ addr.toNat)
     (hpriv : Assumptions.CurPrivilegeMachine js_afterLoad.sail)
     (hmprv : Assumptions.MstatusMprvZero js_afterLoad.sail)
     (hpmp : Assumptions.StorePmpOk addr 8 js_afterLoad.sail)
     (hmmio : Assumptions.NotWritableMmio addr 8 js_afterLoad.sail)
-    (hjolt : Assumptions.JoltRamStoreOk addr js_afterLoad) :
+    (hjolt : Assumptions.JoltRamStoreOk addr js_afterLoad result 8) :
     ∃ js_afterStore : SailJoltState,
       (JoltISA.execInstr
         (JoltISA.Encoded.SD (.xreg rs1) (.xreg rs2) (0 : BitVec 12))).run js_afterLoad =
         .ok RETIRE_SUCCESS js_afterStore ∧
       js_afterStore.sail =
         state_after_dword_store js_afterLoad.sail addr result ∧
       js_afterStore.vregs = js_afterLoad.vregs
```

### `amo_dword_sd_xreg_vreg_run_of_write` (theorem)

File: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/Dword.lean:290`.

```diff
@@ -1,19 +1,19 @@
 theorem amo_dword_sd_xreg_vreg_run_of_write
     (base : regidx) (value : JoltISA.VReg) (imm : BitVec 12)
     (js : SailJoltState) (baseValue stored : BitVec 64) (s' : SailState)
     (hbase : rX_bits base js.sail = .ok baseValue js.sail)
     (hvalue : js.vregs value = stored)
     (h_align :
       (baseValue + sign_extend (m := 64) imm) &&& (7 : BitVec 64) = 0)
     (hwrite :
       vmem_write_addr (Virtaddr (baseValue + sign_extend (m := 64) imm)) 8
         stored (Store Data) false false false js.sail =
         .ok (Ok true) s')
     (h_ram : JoltISA.RAM_START_ADDRESS ≤ (baseValue + sign_extend (m := 64) imm).toNat)
     (hpriv : Assumptions.CurPrivilegeMachine js.sail)
     (hmprv : Assumptions.MstatusMprvZero js.sail)
     (hpmp : Assumptions.StorePmpOk (baseValue + sign_extend (m := 64) imm) 8 js.sail)
     (hmmio : Assumptions.NotWritableMmio (baseValue + sign_extend (m := 64) imm) 8 js.sail)
-    (hjolt : Assumptions.JoltRamStoreOk (baseValue + sign_extend (m := 64) imm) js) :
+    (hjolt : Assumptions.JoltRamStoreOk (baseValue + sign_extend (m := 64) imm) js stored 8) :
     (JoltISA.execInstr (JoltISA.Encoded.SD (.xreg base) (.vreg value) imm)).run js =
       .ok RETIRE_SUCCESS { js with sail := s' }
```

### `amo_dword_sd_vreg_result_run` (theorem)

File: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/Dword.lean:323`.

```diff
@@ -1,24 +1,24 @@
 theorem amo_dword_sd_vreg_result_run
     (rs1 : regidx) (valueReg : JoltISA.VReg) (js : SailJoltState)
     (addr result : BitVec 64)
     (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
     (hvalue : js.vregs valueReg = result)
     (h_align : addr &&& (7 : BitVec 64) = 0)
     (hwrite :
       vmem_write_addr (Virtaddr addr) 8 result
         (Store Data) false false false js.sail =
         .ok (Ok true)
           (state_after_dword_store js.sail addr result))
     (h_ram : JoltISA.RAM_START_ADDRESS ≤ addr.toNat)
     (hpriv : Assumptions.CurPrivilegeMachine js.sail)
     (hmprv : Assumptions.MstatusMprvZero js.sail)
     (hpmp : Assumptions.StorePmpOk addr 8 js.sail)
     (hmmio : Assumptions.NotWritableMmio addr 8 js.sail)
-    (hjolt : Assumptions.JoltRamStoreOk addr js) :
+    (hjolt : Assumptions.JoltRamStoreOk addr js result 8) :
     ∃ js_afterStore : SailJoltState,
       (JoltISA.execInstr
         (JoltISA.Encoded.SD (.xreg rs1) (.vreg valueReg) (0 : BitVec 12))).run js =
         .ok RETIRE_SUCCESS js_afterStore ∧
       js_afterStore.sail =
         state_after_dword_store js.sail addr result ∧
       js_afterStore.vregs = js.vregs
```

### `amo_dword_store_xreg_result_after_load_aligned_run` (theorem)

File: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/Dword.lean:510`.

```diff
@@ -1,20 +1,20 @@
 theorem amo_dword_store_xreg_result_after_load_aligned_run
     (rs2 rs1 : regidx) (js js_afterLoad : SailJoltState)
     (hpriv : Assumptions.CurPrivilegeMachine js.sail)
     (hmprv : Assumptions.MstatusMprvZero js.sail)
     (addr result : BitVec 64)
     (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
     (hrs2 : rX_bits rs2 js.sail = .ok result js.sail)
     (hstore_pmp : Assumptions.StorePmpOk addr 8 js.sail)
     (hwrite_mmio : Assumptions.NotWritableMmio addr 8 js.sail)
     (h_align : addr &&& (7 : BitVec 64) = 0)
     (hld_sail : js_afterLoad.sail = js.sail)
-    (hjolt : Assumptions.JoltRamStoreOk addr js)
-    (hld_layout : js_afterLoad.jolt_device.memory_layout = js.jolt_device.memory_layout) :
+    (hjolt : Assumptions.JoltRamStoreOk addr js result 8)
+    (hld_setup : JoltIOSetupFrame.SetupSame js js_afterLoad) :
     ∃ js_afterStore : SailJoltState,
       (JoltISA.execInstr
         (JoltISA.Encoded.SD (.xreg rs1) (.xreg rs2) (0 : BitVec 12))).run js_afterLoad =
         .ok RETIRE_SUCCESS js_afterStore ∧
       js_afterStore.sail =
         state_after_dword_store js_afterLoad.sail addr result ∧
       js_afterStore.vregs = js_afterLoad.vregs
```

### `amo_dword_store_vreg_result_after_middle_aligned_run_from` (theorem)

File: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/Dword.lean:2577`.

```diff
@@ -1,22 +1,22 @@
 theorem amo_dword_store_vreg_result_after_middle_aligned_run_from
     (valueReg : JoltISA.VReg)
     (rs1 : regidx) (js js_afterMiddle : SailJoltState)
     (hpriv : Assumptions.CurPrivilegeMachine js.sail)
     (hmprv : Assumptions.MstatusMprvZero js.sail)
     (addr result : BitVec 64)
     (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
     (hstore_pmp : Assumptions.StorePmpOk addr 8 js.sail)
     (hwrite_mmio : Assumptions.NotWritableMmio addr 8 js.sail)
     (h_align : addr &&& (7 : BitVec 64) = 0)
     (hmiddle_sail : js_afterMiddle.sail = js.sail)
     (hmiddle_result : js_afterMiddle.vregs valueReg = result)
-    (hjolt : Assumptions.JoltRamStoreOk addr js)
-    (hmiddle_layout : js_afterMiddle.jolt_device.memory_layout = js.jolt_device.memory_layout) :
+    (hjolt : Assumptions.JoltRamStoreOk addr js result 8)
+    (hmiddle_setup : JoltIOSetupFrame.SetupSame js js_afterMiddle) :
     ∃ js_afterStore : SailJoltState,
       (JoltISA.execInstr
         (JoltISA.Encoded.SD (.xreg rs1) (.vreg valueReg) (0 : BitVec 12))).run
           js_afterMiddle =
         .ok RETIRE_SUCCESS js_afterStore ∧
       js_afterStore.sail =
         state_after_dword_store js_afterMiddle.sail addr result ∧
       js_afterStore.vregs = js_afterMiddle.vregs
```

### `amo_dword_store_vreg_result_after_middle_aligned_run` (theorem)

File: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/Dword.lean:2627`.

```diff
@@ -1,21 +1,21 @@
 theorem amo_dword_store_vreg_result_after_middle_aligned_run
     (rs1 : regidx) (js js_afterMiddle : SailJoltState)
     (hpriv : Assumptions.CurPrivilegeMachine js.sail)
     (hmprv : Assumptions.MstatusMprvZero js.sail)
     (addr result : BitVec 64)
     (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
     (hstore_pmp : Assumptions.StorePmpOk addr 8 js.sail)
     (hwrite_mmio : Assumptions.NotWritableMmio addr 8 js.sail)
     (h_align : addr &&& (7 : BitVec 64) = 0)
     (hmiddle_sail : js_afterMiddle.sail = js.sail)
     (hmiddle_result : js_afterMiddle.vregs JoltISA.amoNewVReg = result)
-    (hjolt : Assumptions.JoltRamStoreOk addr js)
-    (hmiddle_layout : js_afterMiddle.jolt_device.memory_layout = js.jolt_device.memory_layout) :
+    (hjolt : Assumptions.JoltRamStoreOk addr js result 8)
+    (hmiddle_setup : JoltIOSetupFrame.SetupSame js js_afterMiddle) :
     ∃ js_afterStore : SailJoltState,
       (JoltISA.execInstr
         (JoltISA.Encoded.SD (.xreg rs1) (.vreg JoltISA.amoNewVReg) (0 : BitVec 12))).run
           js_afterMiddle =
         .ok RETIRE_SUCCESS js_afterStore ∧
       js_afterStore.sail =
         state_after_dword_store js_afterMiddle.sail addr result ∧
       js_afterStore.vregs = js_afterMiddle.vregs
```

### `amo_dword_double_binop_program_concrete_aligned` (theorem)

File: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/Dword.lean:2698`.

```diff
@@ -1,36 +1,36 @@
 theorem amo_dword_double_binop_program_concrete_aligned
     (op : amoop) (binop : JoltISA.Dst → JoltISA.Src → JoltISA.Src → JoltISA.Instr)
     (rs2 rs1 rd : regidx) (js : SailJoltState)
     (hpriv : Assumptions.CurPrivilegeMachine js.sail)
     (hmprv : Assumptions.MstatusMprvZero js.sail)
     (addr result : BitVec 64)
     (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
     (hbytes : MemBytesPresentAt js.sail addr 8)
     (hload_pmp : Assumptions.LoadPmpOk addr 8 js.sail)
     (hread_mmio : Assumptions.NotReadableMmio addr 8 js.sail)
     (hstore_pmp : Assumptions.StorePmpOk addr 8 js.sail)
     (hwrite_mmio : Assumptions.NotWritableMmio addr 8 js.sail)
     (h_align : addr &&& (7 : BitVec 64) = 0)
     (hjolt_load : Assumptions.JoltRamLoadOk addr js)
-    (hjolt_store : Assumptions.JoltRamStoreOk addr js)
+    (hjolt_store : Assumptions.JoltRamStoreOk addr js result 8)
     (hmiddle :
       ∀ oldReg newReg : JoltISA.VReg,
       WritableVReg newReg →
       oldReg ≠ newReg →
       ∀ js_afterLoad : SailJoltState,
         js_afterLoad.sail = js.sail →
         js_afterLoad.vregs oldReg =
           loaded_dword_at js.sail addr hbytes
             (amo_dword_aligned_no_ovf addr h_align) →
         ∃ js_afterMiddle : SailJoltState,
           AmoDwordMiddleStepInto newReg oldReg
             (binop (.vreg newReg) (.vreg oldReg) (.xreg rs2))
             (loaded_dword_at js.sail addr hbytes
               (amo_dword_aligned_no_ovf addr h_align)) result
             js_afterLoad js_afterMiddle) :
     ∃ jsf : SailJoltState,
       (JoltISA.execProgram (JoltISA.amoDoubleBinopProgram binop rs2 rs1 rd)).run js =
         .ok RETIRE_SUCCESS jsf ∧
       jsf.sail = amoDwordFinalSailState rd js.sail addr result
         (loaded_dword_at js.sail addr hbytes
           (amo_dword_aligned_no_ovf addr h_align))
```

### `amo_dword_double_binop_program_eq_sail_aligned` (theorem)

File: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/Dword.lean:3246`.

```diff
@@ -1,48 +1,48 @@
 theorem amo_dword_double_binop_program_eq_sail_aligned
     (op : amoop) (binop : JoltISA.Dst → JoltISA.Src → JoltISA.Src → JoltISA.Instr)
     (rs2 rs1 rd : regidx) (js : SailJoltState)
     (hpriv : Assumptions.CurPrivilegeMachine js.sail)
     (hmprv : Assumptions.MstatusMprvZero js.sail)
     (addr rs2Val result : BitVec 64)
     (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
     (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
     (hrd : ∃ rdVal, rX_bits rd js.sail = .ok rdVal js.sail)
     (hbytes : MemBytesPresentAt js.sail addr 8)
     (hload_pmp : Assumptions.LoadPmpOk addr 8 js.sail)
     (hstore_pmp : Assumptions.StorePmpOk addr 8 js.sail)
     (hatomic_pmp : Assumptions.AtomicPmpOk op addr 8 js.sail)
     (hread_mmio : Assumptions.NotReadableMmio addr 8 js.sail)
     (hwrite_mmio : Assumptions.NotWritableMmio addr 8 js.sail)
     (h_align : addr &&& (7 : BitVec 64) = 0)
     (hjolt_load : Assumptions.JoltRamLoadOk addr js)
-    (hjolt_store : Assumptions.JoltRamStoreOk addr js)
+    (hjolt_store : Assumptions.JoltRamStoreOk addr js result 8)
     (hnot_cas : (op == amoop.AMOCAS) = false)
     (hlinked : LinkedCSRs js)
     (hsafe : JoltISA.ProgramWritesNoProtectedVReg
       (JoltISA.amoDoubleBinopProgram binop rs2 rs1 rd))
     (hmiddle :
       ∀ oldReg newReg : JoltISA.VReg,
       WritableVReg newReg →
       oldReg ≠ newReg →
       ∀ js_afterLoad : SailJoltState,
         js_afterLoad.sail = js.sail →
         js_afterLoad.vregs oldReg =
           loaded_dword_at js.sail addr hbytes
             (amo_dword_aligned_no_ovf addr h_align) →
         ∃ js_afterMiddle : SailJoltState,
           AmoDwordMiddleStepInto newReg oldReg
             (binop (.vreg newReg) (.vreg oldReg) (.xreg rs2))
             (loaded_dword_at js.sail addr hbytes
               (amo_dword_aligned_no_ovf addr h_align)) result
             js_afterLoad js_afterMiddle)
     (hresult :
       amoDwordSailResult op
         (show BitVec (8 * 8) from
           trunc (m := (((8 : Nat) : Int) * (8 : Int)).toNat) rs2Val)
         (BitVec.setWidth (8 * 8)
           (loaded_dword_at js.sail addr hbytes
             (amo_dword_aligned_no_ovf addr h_align))) =
       result) :
     System.systemProjectResult ((JoltISA.execProgram
       (JoltISA.amoDoubleBinopProgram binop rs2 rs1 rd)).run js) =
       (execute_AMO op false false rs2 rs1 8 rd).run js.sail
```

### `amo_dword_double_binop_program_project_eq_sail` (theorem)

File: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/Dword.lean:3376`.

```diff
@@ -1,49 +1,49 @@
 theorem amo_dword_double_binop_program_project_eq_sail
     (op : amoop) (binop : JoltISA.Dst → JoltISA.Src → JoltISA.Src → JoltISA.Instr)
     (rs2 rs1 rd : regidx) (js : SailJoltState)
     (hpriv : Assumptions.CurPrivilegeMachine js.sail)
     (hmprv : Assumptions.MstatusMprvZero js.sail)
     (addr rs2Val result : BitVec 64)
     (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
     (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
     (hrd : ∃ rdVal, rX_bits rd js.sail = .ok rdVal js.sail)
     (hbytes : MemBytesPresentAt js.sail addr 8)
     (hload_pmp : Assumptions.LoadPmpOk addr 8 js.sail)
     (hstore_pmp : Assumptions.StorePmpOk addr 8 js.sail)
     (hatomic_pmp : Assumptions.AtomicPmpOk op addr 8 js.sail)
     (hread_mmio : Assumptions.NotReadableMmio addr 8 js.sail)
     (hwrite_mmio : Assumptions.NotWritableMmio addr 8 js.sail)
     (hjolt_load : Assumptions.JoltRamLoadOk addr js)
-    (hjolt_store : Assumptions.JoltRamStoreOk addr js)
+    (hjolt_store : Assumptions.JoltRamStoreOk addr js result 8)
     (hnot_cas : (op == amoop.AMOCAS) = false)
     (hlinked : LinkedCSRs js)
     (hsafe : JoltISA.ProgramWritesNoProtectedVReg
       (JoltISA.amoDoubleBinopProgram binop rs2 rs1 rd))
     (hmiddle :
       ∀ h_align : addr &&& (7 : BitVec 64) = 0,
       ∀ oldReg newReg : JoltISA.VReg,
       WritableVReg newReg →
       oldReg ≠ newReg →
       ∀ js_afterLoad : SailJoltState,
         js_afterLoad.sail = js.sail →
         js_afterLoad.vregs oldReg =
           loaded_dword_at js.sail addr hbytes
             (amo_dword_aligned_no_ovf addr h_align) →
         ∃ js_afterMiddle : SailJoltState,
           AmoDwordMiddleStepInto newReg oldReg
             (binop (.vreg newReg) (.vreg oldReg) (.xreg rs2))
             (loaded_dword_at js.sail addr hbytes
               (amo_dword_aligned_no_ovf addr h_align)) result
             js_afterLoad js_afterMiddle)
     (hresult :
       ∀ h_align : addr &&& (7 : BitVec 64) = 0,
       amoDwordSailResult op
         (show BitVec (8 * 8) from
           trunc (m := (((8 : Nat) : Int) * (8 : Int)).toNat) rs2Val)
         (BitVec.setWidth (8 * 8)
           (loaded_dword_at js.sail addr hbytes
             (amo_dword_aligned_no_ovf addr h_align))) =
       result) :
     System.systemProjectResult ((JoltISA.execProgram
       (JoltISA.amoDoubleBinopProgram binop rs2 rs1 rd)).run js) =
       (execute_AMO op false false rs2 rs1 8 rd).run js.sail
```

### `amo_dword_double_select_program_concrete_aligned` (theorem)

File: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/Dword.lean:3440`.

```diff
@@ -1,38 +1,38 @@
 theorem amo_dword_double_select_program_concrete_aligned
     (op : amoop)
     (cmpInstr : JoltISA.Dst → JoltISA.Src → JoltISA.Src → JoltISA.Instr)
     (cmpLhs cmpRhs : JoltISA.Src)
     (rs2 rs1 rd : regidx) (js : SailJoltState)
     (hpriv : Assumptions.CurPrivilegeMachine js.sail)
     (hmprv : Assumptions.MstatusMprvZero js.sail)
     (addr result : BitVec 64)
     (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
     (hbytes : MemBytesPresentAt js.sail addr 8)
     (hload_pmp : Assumptions.LoadPmpOk addr 8 js.sail)
     (hread_mmio : Assumptions.NotReadableMmio addr 8 js.sail)
     (hstore_pmp : Assumptions.StorePmpOk addr 8 js.sail)
     (hwrite_mmio : Assumptions.NotWritableMmio addr 8 js.sail)
     (h_align : addr &&& (7 : BitVec 64) = 0)
     (hjolt_load : Assumptions.JoltRamLoadOk addr js)
-    (hjolt_store : Assumptions.JoltRamStoreOk addr js)
+    (hjolt_store : Assumptions.JoltRamStoreOk addr js result 8)
     (hmiddle :
       ∀ js_afterLoad : SailJoltState,
         js_afterLoad.sail = js.sail →
         js_afterLoad.vregs (JoltISA.amoOldVRegFor rd) =
           loaded_dword_at js.sail addr hbytes
             (amo_dword_aligned_no_ovf addr h_align) →
         ∃ js_afterMiddle : SailJoltState,
           AmoDwordSelectMiddleStepInto
             (JoltISA.amoNewVRegFor rd) (JoltISA.amoTmpVRegFor rd)
             (JoltISA.amoOldVRegFor rd)
             cmpInstr cmpLhs cmpRhs rs2
             (loaded_dword_at js.sail addr hbytes
               (amo_dword_aligned_no_ovf addr h_align)) result
             js_afterLoad js_afterMiddle) :
     ∃ jsf : SailJoltState,
       (JoltISA.execProgram
         (JoltISA.amoDoubleSelectProgram cmpInstr cmpLhs cmpRhs rs2 rs1 rd)).run js =
         .ok RETIRE_SUCCESS jsf ∧
       jsf.sail = amoDwordFinalSailState rd js.sail addr result
         (loaded_dword_at js.sail addr hbytes
           (amo_dword_aligned_no_ovf addr h_align))
```

### `amo_dword_double_select_program_eq_sail_aligned` (theorem)

File: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/Dword.lean:3592`.

```diff
@@ -1,49 +1,49 @@
 theorem amo_dword_double_select_program_eq_sail_aligned
     (op : amoop)
     (cmpInstr : JoltISA.Dst → JoltISA.Src → JoltISA.Src → JoltISA.Instr)
     (cmpLhs cmpRhs : JoltISA.Src)
     (rs2 rs1 rd : regidx) (js : SailJoltState)
     (hpriv : Assumptions.CurPrivilegeMachine js.sail)
     (hmprv : Assumptions.MstatusMprvZero js.sail)
     (addr rs2Val result : BitVec 64)
     (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
     (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
     (hrd : ∃ rdVal, rX_bits rd js.sail = .ok rdVal js.sail)
     (hbytes : MemBytesPresentAt js.sail addr 8)
     (hload_pmp : Assumptions.LoadPmpOk addr 8 js.sail)
     (hstore_pmp : Assumptions.StorePmpOk addr 8 js.sail)
     (hatomic_pmp : Assumptions.AtomicPmpOk op addr 8 js.sail)
     (hread_mmio : Assumptions.NotReadableMmio addr 8 js.sail)
     (hwrite_mmio : Assumptions.NotWritableMmio addr 8 js.sail)
     (h_align : addr &&& (7 : BitVec 64) = 0)
     (hjolt_load : Assumptions.JoltRamLoadOk addr js)
-    (hjolt_store : Assumptions.JoltRamStoreOk addr js)
+    (hjolt_store : Assumptions.JoltRamStoreOk addr js result 8)
     (hnot_cas : (op == amoop.AMOCAS) = false)
     (hlinked : LinkedCSRs js)
     (hsafe : JoltISA.ProgramWritesNoProtectedVReg
       (JoltISA.amoDoubleSelectProgram cmpInstr cmpLhs cmpRhs rs2 rs1 rd))
     (hmiddle :
       ∀ js_afterLoad : SailJoltState,
         js_afterLoad.sail = js.sail →
         js_afterLoad.vregs (JoltISA.amoOldVRegFor rd) =
           loaded_dword_at js.sail addr hbytes
             (amo_dword_aligned_no_ovf addr h_align) →
         ∃ js_afterMiddle : SailJoltState,
           AmoDwordSelectMiddleStepInto
             (JoltISA.amoNewVRegFor rd) (JoltISA.amoTmpVRegFor rd)
             (JoltISA.amoOldVRegFor rd)
             cmpInstr cmpLhs cmpRhs rs2
             (loaded_dword_at js.sail addr hbytes
               (amo_dword_aligned_no_ovf addr h_align)) result
             js_afterLoad js_afterMiddle)
     (hresult :
       amoDwordSailResult op
         (show BitVec (8 * 8) from
           trunc (m := (((8 : Nat) : Int) * (8 : Int)).toNat) rs2Val)
         (BitVec.setWidth (8 * 8)
           (loaded_dword_at js.sail addr hbytes
             (amo_dword_aligned_no_ovf addr h_align))) =
       result) :
     System.systemProjectResult ((JoltISA.execProgram
       (JoltISA.amoDoubleSelectProgram cmpInstr cmpLhs cmpRhs rs2 rs1 rd)).run js) =
       (execute_AMO op false false rs2 rs1 8 rd).run js.sail
```

### `amo_dword_double_select_program_project_eq_sail` (theorem)

File: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/Dword.lean:3692`.

```diff
@@ -1,50 +1,50 @@
 theorem amo_dword_double_select_program_project_eq_sail
     (op : amoop)
     (cmpInstr : JoltISA.Dst → JoltISA.Src → JoltISA.Src → JoltISA.Instr)
     (cmpLhs cmpRhs : JoltISA.Src)
     (rs2 rs1 rd : regidx) (js : SailJoltState)
     (hpriv : Assumptions.CurPrivilegeMachine js.sail)
     (hmprv : Assumptions.MstatusMprvZero js.sail)
     (addr rs2Val result : BitVec 64)
     (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
     (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
     (hrd : ∃ rdVal, rX_bits rd js.sail = .ok rdVal js.sail)
     (hbytes : MemBytesPresentAt js.sail addr 8)
     (hload_pmp : Assumptions.LoadPmpOk addr 8 js.sail)
     (hstore_pmp : Assumptions.StorePmpOk addr 8 js.sail)
     (hatomic_pmp : Assumptions.AtomicPmpOk op addr 8 js.sail)
     (hread_mmio : Assumptions.NotReadableMmio addr 8 js.sail)
     (hwrite_mmio : Assumptions.NotWritableMmio addr 8 js.sail)
     (hjolt_load : Assumptions.JoltRamLoadOk addr js)
-    (hjolt_store : Assumptions.JoltRamStoreOk addr js)
+    (hjolt_store : Assumptions.JoltRamStoreOk addr js result 8)
     (hnot_cas : (op == amoop.AMOCAS) = false)
     (hlinked : LinkedCSRs js)
     (hsafe : JoltISA.ProgramWritesNoProtectedVReg
       (JoltISA.amoDoubleSelectProgram cmpInstr cmpLhs cmpRhs rs2 rs1 rd))
     (hmiddle :
       ∀ h_align : addr &&& (7 : BitVec 64) = 0,
       ∀ js_afterLoad : SailJoltState,
         js_afterLoad.sail = js.sail →
         js_afterLoad.vregs (JoltISA.amoOldVRegFor rd) =
           loaded_dword_at js.sail addr hbytes
             (amo_dword_aligned_no_ovf addr h_align) →
         ∃ js_afterMiddle : SailJoltState,
           AmoDwordSelectMiddleStepInto
             (JoltISA.amoNewVRegFor rd) (JoltISA.amoTmpVRegFor rd)
             (JoltISA.amoOldVRegFor rd)
             cmpInstr cmpLhs cmpRhs rs2
             (loaded_dword_at js.sail addr hbytes
               (amo_dword_aligned_no_ovf addr h_align)) result
             js_afterLoad js_afterMiddle)
     (hresult :
       ∀ h_align : addr &&& (7 : BitVec 64) = 0,
       amoDwordSailResult op
         (show BitVec (8 * 8) from
           trunc (m := (((8 : Nat) : Int) * (8 : Int)).toNat) rs2Val)
         (BitVec.setWidth (8 * 8)
           (loaded_dword_at js.sail addr hbytes
             (amo_dword_aligned_no_ovf addr h_align))) =
       result) :
     System.systemProjectResult ((JoltISA.execProgram
       (JoltISA.amoDoubleSelectProgram cmpInstr cmpLhs cmpRhs rs2 rs1 rd)).run js) =
       (execute_AMO op false false rs2 rs1 8 rd).run js.sail
```

### `amo_word_pre64_aligned_run_with` (theorem)

File: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/Word.lean:1051`.

```diff
@@ -1,24 +1,24 @@
 theorem amo_word_pre64_aligned_run_with
     (rs1 : regidx) (oldReg dwordReg laneReg : JoltISA.VReg)
     (tail : JoltISA.Program) (js : SailJoltState) (addr : BitVec 64)
     (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
     (hbytes : MemBytesPresentAt js.sail (amoWordBase addr) 8)
     (hread_mmio : Assumptions.NotReadableMmio (amoWordBase addr) 8 js.sail)
     (h_no_ovf : (amoWordBase addr).toNat + 7 < 2 ^ 64)
     (h_align : addr &&& (3 : BitVec 64) = 0)
     (hlane_w : WritableVReg laneReg) (hdword_w : WritableVReg dwordReg)
     (hold_w : WritableVReg oldReg)
     (hlane_ne_dword : laneReg ≠ dwordReg)
     (hdword_ne_old : dwordReg ≠ oldReg) (hlane_ne_old : laneReg ≠ oldReg)
     (hjolt : Assumptions.JoltRamLoadOk (amoWordBase addr) js) :
     ∃ js_pre : SailJoltState,
       (JoltISA.execProgram
         (JoltISA.amoPre64ProgramWithScratch rs1 oldReg dwordReg laneReg tail)).run js =
         (JoltISA.execProgram tail).run js_pre ∧
       js_pre.sail = js.sail ∧
       js_pre.vregs dwordReg =
         loaded_dword_at js.sail (amoWordBase addr) hbytes h_no_ovf ∧
       js_pre.vregs laneReg = amoWordLaneMask addr ∧
       js_pre.vregs oldReg = amoWordLaneOld addr
         (loaded_dword_at js.sail (amoWordBase addr) hbytes h_no_ovf) ∧
-      js_pre.jolt_device.memory_layout = js.jolt_device.memory_layout
+      JoltIOSetupFrame.SetupSame js js_pre
```

### `amo_word_pre64_aligned_run_for` (theorem)

File: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/Word.lean:1095`.

```diff
@@ -1,20 +1,20 @@
 theorem amo_word_pre64_aligned_run_for
     (rd : regidx) (tail : JoltISA.Program) (rs1 : regidx) (js : SailJoltState)
     (addr : BitVec 64) (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
     (hbytes : MemBytesPresentAt js.sail (amoWordBase addr) 8)
     (hread_mmio : Assumptions.NotReadableMmio (amoWordBase addr) 8 js.sail)
     (h_no_ovf : (amoWordBase addr).toNat + 7 < 2 ^ 64)
     (h_align : addr &&& (3 : BitVec 64) = 0)
     (hjolt : Assumptions.JoltRamLoadOk (amoWordBase addr) js) :
     ∃ js_pre : SailJoltState,
       (JoltISA.execProgram
         (JoltISA.amoPre64Program rs1 (JoltISA.amoWordOldVRegFor rd)
           (JoltISA.amoWordDwordVRegFor rd) (JoltISA.amoWordLaneVRegFor rd) tail)).run js =
         (JoltISA.execProgram tail).run js_pre ∧
       js_pre.sail = js.sail ∧
       js_pre.vregs (JoltISA.amoWordDwordVRegFor rd) =
         loaded_dword_at js.sail (amoWordBase addr) hbytes h_no_ovf ∧
       js_pre.vregs (JoltISA.amoWordLaneVRegFor rd) = amoWordLaneMask addr ∧
       js_pre.vregs (JoltISA.amoWordOldVRegFor rd) = amoWordLaneOld addr
         (loaded_dword_at js.sail (amoWordBase addr) hbytes h_no_ovf) ∧
-      js_pre.jolt_device.memory_layout = js.jolt_device.memory_layout
+      JoltIOSetupFrame.SetupSame js js_pre
```

### `amo_word_sd_spliced_dword_run` (theorem)

File: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/Word.lean:2689`.

```diff
@@ -1,21 +1,21 @@
 theorem amo_word_sd_spliced_dword_run
     {op : amoop}
     (js : SailJoltState) (s : SailState) (addr dwordNew old : BitVec 64)
     (hpriv : Assumptions.CurPrivilegeMachine s)
     (hmprv : Assumptions.MstatusMprvZero s)
     (hstore_pmp : Assumptions.StorePmpOk (amoWordBase addr) 8 s)
     (hwrite_mmio : Assumptions.NotWritableMmio (amoWordBase addr) 8 s)
     (h_no_ovf : (amoWordBase addr).toNat + 7 < 2 ^ 64)
     (h_sail : js.sail = s)
     (h_base : js.vregs JoltISA.amoMaskVReg = amoWordBase addr)
     (h_dword : js.vregs JoltISA.amoDwordVReg = dwordNew)
     (h_old : js.vregs JoltISA.amoOldVReg = old)
-    (hjolt : Assumptions.JoltRamStoreOk (amoWordBase addr) js) :
+    (hjolt : Assumptions.JoltRamStoreOk (amoWordBase addr) js dwordNew 8) :
     ∃ js',
       js'.sail = state_after_dword_store s (amoWordBase addr) dwordNew ∧
       js'.vregs JoltISA.amoOldVReg = old ∧
       ∀ tail,
         (JoltISA.execProgram
           (.instr (JoltISA.Encoded.SD (.vreg JoltISA.amoMaskVReg)
             (.vreg JoltISA.amoDwordVReg) (0 : BitVec 12)) tail)).run js =
           (JoltISA.execProgram tail).run js'
```

### `amo_word_sd_spliced_dword_run_for` (theorem)

File: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/Word.lean:2753`.

```diff
@@ -1,21 +1,21 @@
 theorem amo_word_sd_spliced_dword_run_for
     {op : amoop} (rd : regidx)
     (js : SailJoltState) (s : SailState) (addr dwordNew old : BitVec 64)
     (hpriv : Assumptions.CurPrivilegeMachine s)
     (hmprv : Assumptions.MstatusMprvZero s)
     (hstore_pmp : Assumptions.StorePmpOk (amoWordBase addr) 8 s)
     (hwrite_mmio : Assumptions.NotWritableMmio (amoWordBase addr) 8 s)
     (h_no_ovf : (amoWordBase addr).toNat + 7 < 2 ^ 64)
     (h_sail : js.sail = s)
     (h_base : js.vregs (JoltISA.amoMaskVRegFor rd) = amoWordBase addr)
     (h_dword : js.vregs (JoltISA.amoDwordVRegFor rd) = dwordNew)
     (h_old : js.vregs (JoltISA.amoOldVRegFor rd) = old)
-    (hjolt : Assumptions.JoltRamStoreOk (amoWordBase addr) js) :
+    (hjolt : Assumptions.JoltRamStoreOk (amoWordBase addr) js dwordNew 8) :
     ∃ js',
       js'.sail = state_after_dword_store s (amoWordBase addr) dwordNew ∧
       js'.vregs (JoltISA.amoOldVRegFor rd) = old ∧
       ∀ tail,
         (JoltISA.execProgram
           (.instr (JoltISA.Encoded.SD (.vreg (JoltISA.amoMaskVRegFor rd))
             (.vreg (JoltISA.amoDwordVRegFor rd)) (0 : BitVec 12)) tail)).run js =
           (JoltISA.execProgram tail).run js'
```

### `amo_word_post64_vreg_aligned_run` (theorem)

File: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/Word.lean:2912`.

```diff
@@ -1,38 +1,38 @@
 theorem amo_word_post64_vreg_aligned_run
     {op : amoop} (rs1 rd : regidx)
     (js js_pre : SailJoltState)
     (hpriv : Assumptions.CurPrivilegeMachine js.sail)
     (hmprv : Assumptions.MstatusMprvZero js.sail)
     (addr newValue dword : BitVec 64) (oldWord : BitVec 32)
     (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
     (hbytes_base : MemBytesPresentAt js.sail (amoWordBase addr) 8)
     (hstore_pmp : Assumptions.StorePmpOk (amoWordBase addr) 8 js.sail)
     (hwrite_mmio : Assumptions.NotWritableMmio (amoWordBase addr) 8 js.sail)
     (h_no_ovf : (amoWordBase addr).toNat + 7 < 2 ^ 64)
     (h_align : addr &&& (3 : BitVec 64) = 0)
     (hdword :
       dword =
         loaded_dword_at js.sail (amoWordBase addr) hbytes_base h_no_ovf)
     (hpre_sail : js_pre.sail = js.sail)
     (hpre_new : js_pre.vregs JoltISA.amoNewVReg = newValue)
     (hpre_dword : js_pre.vregs JoltISA.amoDwordVReg = dword)
     (hpre_shift :
       js_pre.vregs JoltISA.amoShiftVReg =
         shift_bits_left addr (3 : BitVec 6))
     (hpre_old :
       js_pre.vregs JoltISA.amoOldVReg =
         amoWordShiftedOld addr dword)
     (hold :
       (Sail.BitVec.extractLsb (amoWordShiftedOld addr dword) 31 0 :
         BitVec 32) = oldWord)
-    (hjolt_store : Assumptions.JoltRamStoreOk (amoWordBase addr) js)
-    (hpre_layout : js_pre.jolt_device.memory_layout = js.jolt_device.memory_layout) :
+    (hjolt_store : Assumptions.JoltRamStoreOk (amoWordBase addr) js (amoWordSplicedDword addr newValue dword) 8)
+    (hpre_setup : JoltIOSetupFrame.SetupSame js js_pre) :
     ∃ jsf : SailJoltState,
       (JoltISA.execProgram
         (JoltISA.amoPost64Program rs1 rd (.vreg JoltISA.amoNewVReg)
           JoltISA.amoDwordVReg JoltISA.amoShiftVReg
           JoltISA.amoMaskVReg JoltISA.amoOldVReg)).run js_pre =
         .ok RETIRE_SUCCESS jsf ∧
       jsf.sail =
         amoWordFinalSailState rd js.sail addr
           (Sail.BitVec.extractLsb newValue 31 0) oldWord
```

### `amo_word_post64_vreg_aligned_run_for` (theorem)

File: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/Word.lean:3033`.

```diff
@@ -1,40 +1,40 @@
 theorem amo_word_post64_vreg_aligned_run_for
     {op : amoop} (rs1 rd : regidx)
     (js js_pre : SailJoltState)
     (hpriv : Assumptions.CurPrivilegeMachine js.sail)
     (hmprv : Assumptions.MstatusMprvZero js.sail)
     (addr newValue dword : BitVec 64) (oldWord : BitVec 32)
     (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
     (hbytes_base : MemBytesPresentAt js.sail (amoWordBase addr) 8)
     (hstore_pmp : Assumptions.StorePmpOk (amoWordBase addr) 8 js.sail)
     (hwrite_mmio : Assumptions.NotWritableMmio (amoWordBase addr) 8 js.sail)
     (h_no_ovf : (amoWordBase addr).toNat + 7 < 2 ^ 64)
     (h_align : addr &&& (3 : BitVec 64) = 0)
     (hdword :
       dword =
         loaded_dword_at js.sail (amoWordBase addr) hbytes_base h_no_ovf)
     (hpre_sail : js_pre.sail = js.sail)
     (hpre_new : js_pre.vregs (JoltISA.amoNewVRegFor rd) = newValue)
     (hpre_dword : js_pre.vregs (JoltISA.amoDwordVRegFor rd) = dword)
     (hpre_shift :
       js_pre.vregs (JoltISA.amoShiftVRegFor rd) =
         shift_bits_left addr (3 : BitVec 6))
     (hpre_old :
       js_pre.vregs (JoltISA.amoOldVRegFor rd) =
         amoWordShiftedOld addr dword)
     (hold :
       (Sail.BitVec.extractLsb (amoWordShiftedOld addr dword) 31 0 :
         BitVec 32) = oldWord)
-    (hjolt_store : Assumptions.JoltRamStoreOk (amoWordBase addr) js)
-    (hpre_layout : js_pre.jolt_device.memory_layout = js.jolt_device.memory_layout) :
+    (hjolt_store : Assumptions.JoltRamStoreOk (amoWordBase addr) js (amoWordSplicedDword addr newValue dword) 8)
+    (hpre_setup : JoltIOSetupFrame.SetupSame js js_pre) :
     ∃ jsf : SailJoltState,
       (JoltISA.execProgram
         (JoltISA.amoPost64ProgramWithScratch rs1 rd
           (.vreg (JoltISA.amoNewVRegFor rd))
           (JoltISA.amoDwordVRegFor rd) (JoltISA.amoShiftVRegFor rd)
           (JoltISA.amoMaskVRegFor rd) (JoltISA.amoOldVRegFor rd)
           (JoltISA.amoInlineTmpVRegFor rd))).run js_pre =
         .ok RETIRE_SUCCESS jsf ∧
       jsf.sail =
         amoWordFinalSailState rd js.sail addr
           (Sail.BitVec.extractLsb newValue 31 0) oldWord
```

### `amo_word_merge_program_aligned_run` (theorem)

File: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/Word.lean:3217`.

```diff
@@ -1,20 +1,20 @@
 theorem amo_word_merge_program_aligned_run
     (rs1 rd : regidx) (dword lane old : JoltISA.VReg) (source : JoltISA.Src)
     (js : SailJoltState) (addr value : BitVec 64) (oldWord : BitVec 32)
     (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
     (hbytes : MemBytesPresentAt js.sail (amoWordBase addr) 8)
     (horiginal : js.vregs dword =
       loaded_dword_at js.sail (amoWordBase addr) hbytes (amo_word_base_no_ovf addr))
     (hmask : js.vregs lane = amoWordLaneMask addr)
     (hvalue : (JoltISA.readSrc source).run
       (stateAfterVRegWrite js dword (js.vregs dword &&& ~~~amoWordLaneMask addr)) =
       .ok value (stateAfterVRegWrite js dword (js.vregs dword &&& ~~~amoWordLaneMask addr)))
     (hold : js.vregs old = sign_extend (m := 64) oldWord)
     (hdword : WritableVReg dword) (hlane : WritableVReg lane)
     (hdl : dword ≠ lane) (hod : old ≠ dword) (hol : old ≠ lane)
     (halign : addr &&& (3 : BitVec 64) = 0)
     (hwrite_mmio : Assumptions.NotWritableMmio (amoWordBase addr) 8 js.sail)
-    (hjolt : Assumptions.JoltRamStoreOk (amoWordBase addr) js) :
+    (hjolt : Assumptions.JoltRamStoreOk (amoWordBase addr) js (amoWordLaneMerged addr (js.vregs dword) value) 8) :
     ∃ jsf, JoltISA.Program.Run (JoltISA.amoWordMergeProgram rs1 rd source dword lane old)
       js jsf ∧ jsf.sail = amoWordFinalSailState rd js.sail addr
         (Sail.BitVec.extractLsb value 31 0) oldWord
```

### `amo_word_binop_program_concrete_aligned` (theorem)

File: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/Word.lean:3261`.

```diff
@@ -1,42 +1,42 @@
 theorem amo_word_binop_program_concrete_aligned
     (binop : JoltISA.Dst → JoltISA.Src → JoltISA.Src → JoltISA.Instr)
     (rs2 rs1 rd : regidx) (js : SailJoltState)
     (addr result64 : BitVec 64) (result : BitVec 32)
     (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
     (hbytes_base : MemBytesPresentAt js.sail (amoWordBase addr) 8)
     (hread_mmio : Assumptions.NotReadableMmio (amoWordBase addr) 8 js.sail)
     (hwrite_mmio : Assumptions.NotWritableMmio (amoWordBase addr) 8 js.sail)
     (h_align : addr &&& (3 : BitVec 64) = 0)
     (hjolt_load : Assumptions.JoltRamLoadOk (amoWordBase addr) js)
-    (hjolt_store : Assumptions.JoltRamStoreOk (amoWordBase addr) js)
+    (hjolt_store : Assumptions.JoltRamStoreOk (amoWordBase addr) js (amoWordSplicedDword addr result64 (JoltISA.Mmu.ram_doubleword js.sail.mem (amoWordBase addr).toNat)) 8)
     (hresult : (Sail.BitVec.extractLsb result64 31 0 : BitVec 32) = result)
     (hmiddle :
       ∀ js_pre : SailJoltState,
         js_pre.sail = js.sail →
         js_pre.vregs (JoltISA.amoWordDwordVRegFor rd) =
           loaded_dword_at js.sail (amoWordBase addr) hbytes_base
             (amo_word_base_no_ovf addr) →
         js_pre.vregs (JoltISA.amoWordLaneVRegFor rd) = amoWordLaneMask addr →
         js_pre.vregs (JoltISA.amoWordOldVRegFor rd) = amoWordLaneOld addr
           (loaded_dword_at js.sail (amoWordBase addr) hbytes_base
             (amo_word_base_no_ovf addr)) →
         ∃ js_afterMiddle : SailJoltState,
           AmoWordMiddleStepInto
             (JoltISA.amoWordNewVRegFor rd) (JoltISA.amoWordOldVRegFor rd)
             (JoltISA.amoWordDwordVRegFor rd) (JoltISA.amoWordLaneVRegFor rd)
             (binop (.vreg (JoltISA.amoWordNewVRegFor rd))
               (.vreg (JoltISA.amoWordOldVRegFor rd)) (.xreg rs2))
             (amoWordLaneOld addr
               (loaded_dword_at js.sail (amoWordBase addr) hbytes_base
                 (amo_word_base_no_ovf addr)))
             (loaded_dword_at js.sail (amoWordBase addr) hbytes_base
               (amo_word_base_no_ovf addr))
             (amoWordLaneMask addr) result64 js_pre js_afterMiddle) :
     ∃ jsf : SailJoltState,
       (JoltISA.execProgram
         (JoltISA.amoWordBinopProgram binop rs2 rs1 rd)).run js =
         .ok RETIRE_SUCCESS jsf ∧
       jsf.sail = amoWordFinalSailState rd js.sail addr result
         (word_of_dword
           (loaded_dword_at js.sail (amoWordBase addr) hbytes_base
             (amo_word_base_no_ovf addr)) (addr &&& (7 : BitVec 64)).toNat)
```

### `amo_word_floor_store_run` (theorem)

File: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/WordLane.lean:144`.

```diff
@@ -1,11 +1,11 @@
 theorem amo_word_floor_store_run
     (rs1 : regidx) (value : JoltISA.VReg) (js : SailJoltState) (addr : BitVec 64)
     (hread : rX_bits rs1 js.sail = .ok addr js.sail)
     (halign : addr &&& (3 : BitVec 64) = 0)
     (hbase : amoWordBase addr &&& (7 : BitVec 64) = 0)
     (hram : JoltISA.RAM_START_ADDRESS ≤ (amoWordBase addr).toNat)
-    (hjolt : Assumptions.JoltRamStoreOk (amoWordBase addr) js) :
+    (hjolt : Assumptions.JoltRamStoreOk (amoWordBase addr) js (js.vregs value) 8) :
     (JoltISA.execInstr (.VirtualStoreW (.xreg rs1) (.vreg value) 0
       (ExceptionType.E_SAMO_Addr_Align ()))).run js =
       .ok RETIRE_SUCCESS
         { js with sail := state_after_dword_store js.sail (amoWordBase addr) (js.vregs value) }
```

### `amo_word_lane_merge_run` (theorem)

File: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/WordLane.lean:184`.

```diff
@@ -1,19 +1,19 @@
 theorem amo_word_lane_merge_run
     (rs1 : regidx) (dword lane : JoltISA.VReg) (source : JoltISA.Src)
     (js : SailJoltState) (addr original value : BitVec 64)
     (hread : rX_bits rs1 js.sail = .ok addr js.sail)
     (horiginal : js.vregs dword = original) (hmask : js.vregs lane = amoWordLaneMask addr)
     (hvalue : (JoltISA.readSrc source).run
       (stateAfterVRegWrite js dword (original &&& ~~~amoWordLaneMask addr)) =
       .ok value (stateAfterVRegWrite js dword (original &&& ~~~amoWordLaneMask addr)))
     (hdword : WritableVReg dword) (hlane : WritableVReg lane) (hdl : dword ≠ lane)
     (halign : addr &&& (3 : BitVec 64) = 0)
     (hbase : amoWordBase addr &&& (7 : BitVec 64) = 0)
     (hram : JoltISA.RAM_START_ADDRESS ≤ (amoWordBase addr).toNat)
-    (hjolt : Assumptions.JoltRamStoreOk (amoWordBase addr) js) :
+    (hjolt : Assumptions.JoltRamStoreOk (amoWordBase addr) js (amoWordLaneMerged addr original value) 8) :
     JoltISA.Program.Run
       (JoltISA.laneWindowMerge .word (.vreg dword) (.vreg lane) (.xreg rs1) 0 source
         (ExceptionType.E_SAMO_Addr_Align ()) (.done RETIRE_SUCCESS)) js
       { amoWordLaneMergeState js dword lane addr original value with
         sail := state_after_dword_store js.sail (amoWordBase addr)
           (amoWordLaneMerged addr original value) }
```

### `amo_word_window_program_aligned_run` (theorem)

File: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/WordProgram.lean:204`.

```diff
@@ -1,30 +1,30 @@
 theorem amo_word_window_program_aligned_run
     (middle : JoltISA.Program) (source : JoltISA.Src) (rs1 rd : regidx)
     (js : SailJoltState) (addr value : BitVec 64)
     (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
     (hbytes : MemBytesPresentAt js.sail (amoWordBase addr) 8)
     (hread : Assumptions.NotReadableMmio (amoWordBase addr) 8 js.sail)
     (hwrite : Assumptions.NotWritableMmio (amoWordBase addr) 8 js.sail)
     (halign : addr &&& (3 : BitVec 64) = 0)
     (hload : Assumptions.JoltRamLoadOk (amoWordBase addr) js)
-    (hstore : Assumptions.JoltRamStoreOk (amoWordBase addr) js)
+    (hstore : Assumptions.JoltRamStoreOk (amoWordBase addr) js (amoWordLaneMerged addr (JoltISA.Mmu.ram_doubleword js.sail.mem (amoWordBase addr).toNat) value) 8)
     (hmiddle : ∀ pre,
       pre.sail = js.sail →
       pre.vregs (JoltISA.amoWordDwordVRegFor rd) =
         loaded_dword_at js.sail (amoWordBase addr) hbytes (amo_word_base_no_ovf addr) →
       pre.vregs (JoltISA.amoWordLaneVRegFor rd) = amoWordLaneMask addr →
       pre.vregs (JoltISA.amoWordOldVRegFor rd) = sign_extend (m := 64)
         (word_of_dword
           (loaded_dword_at js.sail (amoWordBase addr) hbytes (amo_word_base_no_ovf addr))
           (addr &&& (7 : BitVec 64)).toNat) →
       ∃ after, AmoWordWindowStep rd middle source
         (word_of_dword
           (loaded_dword_at js.sail (amoWordBase addr) hbytes (amo_word_base_no_ovf addr))
           (addr &&& (7 : BitVec 64)).toNat)
         (loaded_dword_at js.sail (amoWordBase addr) hbytes (amo_word_base_no_ovf addr))
         (amoWordLaneMask addr) value pre after) :
     ∃ jsf, JoltISA.Program.Run (amoWordWindowProgram middle source rs1 rd) js jsf ∧
       jsf.sail = amoWordFinalSailState rd js.sail addr (Sail.BitVec.extractLsb value 31 0)
         (word_of_dword
           (loaded_dword_at js.sail (amoWordBase addr) hbytes (amo_word_base_no_ovf addr))
           (addr &&& (7 : BitVec 64)).toNat)
```

### `amo_word_rust_select_sd_spliced_dword_run` (theorem)

File: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/WordSelectRust.lean:370`.

```diff
@@ -1,20 +1,20 @@
 theorem amo_word_rust_select_sd_spliced_dword_run
     (js : SailJoltState) (s : SailState) (addr dwordNew old : BitVec 64)
     (hpriv : Assumptions.CurPrivilegeMachine s)
     (hmprv : Assumptions.MstatusMprvZero s)
     (hstore_pmp : Assumptions.StorePmpOk (amoWordBase addr) 8 s)
     (hwrite_mmio : Assumptions.NotWritableMmio (amoWordBase addr) 8 s)
     (h_no_ovf : (amoWordBase addr).toNat + 7 < 2 ^ 64)
     (h_sail : js.sail = s)
     (h_base : js.vregs JoltISA.amoWordSelectMaskVReg = amoWordBase addr)
     (h_dword : js.vregs JoltISA.amoWordSelectDwordVReg = dwordNew)
     (h_old : js.vregs JoltISA.amoWordSelectOldVReg = old)
-    (hjolt : Assumptions.JoltRamStoreOk (amoWordBase addr) js) :
+    (hjolt : Assumptions.JoltRamStoreOk (amoWordBase addr) js dwordNew 8) :
     ∃ js',
       js'.sail = state_after_dword_store s (amoWordBase addr) dwordNew ∧
       js'.vregs JoltISA.amoWordSelectOldVReg = old ∧
       ∀ tail,
         (JoltISA.execProgram
           (.instr (JoltISA.Encoded.SD (.vreg JoltISA.amoWordSelectMaskVReg)
             (.vreg JoltISA.amoWordSelectDwordVReg) (0 : BitVec 12)) tail)).run js =
           (JoltISA.execProgram tail).run js'
```

### `amo_word_rust_select_post64_vreg_aligned_run` (theorem)

File: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/WordSelectRust.lean:456`.

```diff
@@ -1,40 +1,40 @@
 theorem amo_word_rust_select_post64_vreg_aligned_run
     (rs1 rd : regidx)
     (js js_pre : SailJoltState)
     (hpriv : Assumptions.CurPrivilegeMachine js.sail)
     (hmprv : Assumptions.MstatusMprvZero js.sail)
     (addr newValue dword : BitVec 64) (oldWord : BitVec 32)
     (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
     (hbytes_base : MemBytesPresentAt js.sail (amoWordBase addr) 8)
     (hstore_pmp : Assumptions.StorePmpOk (amoWordBase addr) 8 js.sail)
     (hwrite_mmio : Assumptions.NotWritableMmio (amoWordBase addr) 8 js.sail)
     (h_no_ovf : (amoWordBase addr).toNat + 7 < 2 ^ 64)
     (h_align : addr &&& (3 : BitVec 64) = 0)
     (hdword :
       dword =
         loaded_dword_at js.sail (amoWordBase addr) hbytes_base h_no_ovf)
     (hpre_sail : js_pre.sail = js.sail)
     (hpre_new : js_pre.vregs JoltISA.amoWordSelectNewVReg = newValue)
     (hpre_dword :
       js_pre.vregs JoltISA.amoWordSelectDwordVReg = dword)
     (hpre_shift :
       js_pre.vregs JoltISA.amoWordSelectShiftVReg =
         shift_bits_left addr (3 : BitVec 6))
     (hpre_old :
       js_pre.vregs JoltISA.amoWordSelectOldVReg =
         amoWordShiftedOld addr dword)
     (hold :
       (Sail.BitVec.extractLsb (amoWordShiftedOld addr dword) 31 0 :
         BitVec 32) = oldWord)
-    (hjolt_store : Assumptions.JoltRamStoreOk (amoWordBase addr) js)
-    (hpre_layout : js_pre.jolt_device.memory_layout = js.jolt_device.memory_layout) :
+    (hjolt_store : Assumptions.JoltRamStoreOk (amoWordBase addr) js (amoWordSplicedDword addr newValue dword) 8)
+    (hpre_setup : JoltIOSetupFrame.SetupSame js js_pre) :
     ∃ jsf : SailJoltState,
       (JoltISA.execProgram
         (JoltISA.amoPost64ProgramWithScratch rs1 rd (.vreg JoltISA.amoWordSelectNewVReg)
           JoltISA.amoWordSelectDwordVReg JoltISA.amoWordSelectShiftVReg
           JoltISA.amoWordSelectMaskVReg JoltISA.amoWordSelectOldVReg
           JoltISA.amoWordSelectInlineTmpVReg)).run js_pre =
         .ok RETIRE_SUCCESS jsf ∧
       jsf.sail =
         amoWordFinalSailState rd js.sail addr
           (Sail.BitVec.extractLsb newValue 31 0) oldWord
```

### `amo_word_rust_select_sd_spliced_dword_run_for` (theorem)

File: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/WordSelectRust.lean:1024`.

```diff
@@ -1,22 +1,22 @@
 theorem amo_word_rust_select_sd_spliced_dword_run_for
     (rd : regidx)
     (js : SailJoltState) (s : SailState) (addr dwordNew old : BitVec 64)
     (hpriv : Assumptions.CurPrivilegeMachine s)
     (hmprv : Assumptions.MstatusMprvZero s)
     (hstore_pmp : Assumptions.StorePmpOk (amoWordBase addr) 8 s)
     (hwrite_mmio : Assumptions.NotWritableMmio (amoWordBase addr) 8 s)
     (h_no_ovf : (amoWordBase addr).toNat + 7 < 2 ^ 64)
     (h_sail : js.sail = s)
     (h_base : js.vregs (JoltISA.amoWordSelectMaskVRegFor rd) = amoWordBase addr)
     (h_dword : js.vregs (JoltISA.amoWordSelectDwordVRegFor rd) = dwordNew)
     (h_old : js.vregs (JoltISA.amoWordSelectOldVRegFor rd) = old)
-    (hjolt : Assumptions.JoltRamStoreOk (amoWordBase addr) js) :
+    (hjolt : Assumptions.JoltRamStoreOk (amoWordBase addr) js dwordNew 8) :
     ∃ js',
       js'.sail = state_after_dword_store s (amoWordBase addr) dwordNew ∧
       js'.vregs (JoltISA.amoWordSelectOldVRegFor rd) = old ∧
       ∀ tail,
         (JoltISA.execProgram
           (.instr (JoltISA.Encoded.SD (.vreg (JoltISA.amoWordSelectMaskVRegFor rd))
             (.vreg (JoltISA.amoWordSelectDwordVRegFor rd))
             (0 : BitVec 12)) tail)).run js =
           (JoltISA.execProgram tail).run js'
```

### `amo_word_rust_select_post64_vreg_aligned_run_for` (theorem)

File: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/WordSelectRust.lean:1114`.

```diff
@@ -1,43 +1,43 @@
 theorem amo_word_rust_select_post64_vreg_aligned_run_for
     (rs1 rd : regidx)
     (js js_pre : SailJoltState)
     (hpriv : Assumptions.CurPrivilegeMachine js.sail)
     (hmprv : Assumptions.MstatusMprvZero js.sail)
     (addr newValue dword : BitVec 64) (oldWord : BitVec 32)
     (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
     (hbytes_base : MemBytesPresentAt js.sail (amoWordBase addr) 8)
     (hstore_pmp : Assumptions.StorePmpOk (amoWordBase addr) 8 js.sail)
     (hwrite_mmio : Assumptions.NotWritableMmio (amoWordBase addr) 8 js.sail)
     (h_no_ovf : (amoWordBase addr).toNat + 7 < 2 ^ 64)
     (h_align : addr &&& (3 : BitVec 64) = 0)
     (hdword :
       dword =
         loaded_dword_at js.sail (amoWordBase addr) hbytes_base h_no_ovf)
     (hpre_sail : js_pre.sail = js.sail)
     (hpre_new : js_pre.vregs (JoltISA.amoWordSelectNewVRegFor rd) = newValue)
     (hpre_dword :
       js_pre.vregs (JoltISA.amoWordSelectDwordVRegFor rd) = dword)
     (hpre_shift :
       js_pre.vregs (JoltISA.amoWordSelectShiftVRegFor rd) =
         shift_bits_left addr (3 : BitVec 6))
     (hpre_old :
       js_pre.vregs (JoltISA.amoWordSelectOldVRegFor rd) =
         amoWordShiftedOld addr dword)
     (hold :
       (Sail.BitVec.extractLsb (amoWordShiftedOld addr dword) 31 0 :
         BitVec 32) = oldWord)
-    (hjolt_store : Assumptions.JoltRamStoreOk (amoWordBase addr) js)
-    (hpre_layout : js_pre.jolt_device.memory_layout = js.jolt_device.memory_layout) :
+    (hjolt_store : Assumptions.JoltRamStoreOk (amoWordBase addr) js (amoWordSplicedDword addr newValue dword) 8)
+    (hpre_setup : JoltIOSetupFrame.SetupSame js js_pre) :
     ∃ jsf : SailJoltState,
       (JoltISA.execProgram
         (JoltISA.amoPost64ProgramWithScratch rs1 rd
           (.vreg (JoltISA.amoWordSelectNewVRegFor rd))
           (JoltISA.amoWordSelectDwordVRegFor rd)
           (JoltISA.amoWordSelectShiftVRegFor rd)
           (JoltISA.amoWordSelectMaskVRegFor rd)
           (JoltISA.amoWordSelectOldVRegFor rd)
           (JoltISA.amoWordSelectInlineTmpVRegFor rd))).run js_pre =
         .ok RETIRE_SUCCESS jsf ∧
       jsf.sail =
         amoWordFinalSailState rd js.sail addr
           (Sail.BitVec.extractLsb newValue 31 0) oldWord
```

### `amo_word_rust_select_program_concrete_aligned` (theorem)

File: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/WordSelectRust.lean:3276`.

```diff
@@ -1,30 +1,30 @@
 theorem amo_word_rust_select_program_concrete_aligned
     (extend : JoltISA.Dst → JoltISA.Src → JoltISA.Instr)
     (cmp : JoltISA.Dst → JoltISA.Src → JoltISA.Src → JoltISA.Instr)
     (lhs rhs : JoltISA.Src) (rs2 rs1 rd : regidx) (js : SailJoltState)
     (addr result64 : BitVec 64) (result oldWord : BitVec 32)
     (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
     (hbytes : MemBytesPresentAt js.sail (amoWordBase addr) 8)
     (hread : Assumptions.NotReadableMmio (amoWordBase addr) 8 js.sail)
     (hwrite : Assumptions.NotWritableMmio (amoWordBase addr) 8 js.sail)
     (halign : addr &&& (3 : BitVec 64) = 0)
     (hload : Assumptions.JoltRamLoadOk (amoWordBase addr) js)
-    (hstore : Assumptions.JoltRamStoreOk (amoWordBase addr) js)
+    (hstore : Assumptions.JoltRamStoreOk (amoWordBase addr) js (amoWordSplicedDword addr result64 (JoltISA.Mmu.ram_doubleword js.sail.mem (amoWordBase addr).toNat)) 8)
     (hresult : (Sail.BitVec.extractLsb result64 31 0 : BitVec 32) = result)
     (hold : word_of_dword
       (loaded_dword_at js.sail (amoWordBase addr) hbytes (amo_word_base_no_ovf addr))
       (addr &&& (7 : BitVec 64)).toNat = oldWord)
     (hmiddle : ∀ pre,
       pre.sail = js.sail →
       pre.vregs (JoltISA.amoWordDwordVRegFor rd) =
         loaded_dword_at js.sail (amoWordBase addr) hbytes (amo_word_base_no_ovf addr) →
       pre.vregs (JoltISA.amoWordLaneVRegFor rd) = amoWordLaneMask addr →
       pre.vregs (JoltISA.amoWordOldVRegFor rd) = sign_extend (m := 64) oldWord →
       ∃ after, AmoWordWindowStep rd
         (amoWordSelectCurrentMiddleProgram extend cmp lhs rhs rs2 rd)
         (.vreg (JoltISA.amoWordNewVRegFor rd)) oldWord
         (loaded_dword_at js.sail (amoWordBase addr) hbytes (amo_word_base_no_ovf addr))
         (amoWordLaneMask addr) result64 pre after) :
     ∃ jsf, JoltISA.Program.Run
       (JoltISA.amoWordSelectRustProgram extend cmp lhs rhs rs2 rs1 rd) js jsf ∧
       jsf.sail = amoWordFinalSailState rd js.sail addr result oldWord
```

### `laneStoreProgram_run` (theorem)

File: `JoltBytecode/InstructionEquivalence/Instructions/StoreFamily/ProgramBlocks.lean:807`.

```diff
@@ -1,15 +1,18 @@
 theorem laneStoreProgram_run (width : JoltISA.AccessWidth) (imm : BitVec 12)
     (rs1 rs2 : regidx) (js : SailJoltState) (baseValue value : BitVec 64)
     (hbase : rX_bits rs1 js.sail = .ok baseValue js.sail)
     (hvalue : rX_bits rs2 js.sail = .ok value js.sail)
     (halign : load_effective_address baseValue imm &&& LoadFamily.alignmentMask width = 0)
     (haligned : AlignedDwordAccess (compute_aligned_dword_base_address baseValue imm))
     (hbytes : MemBytesPresentAt js.sail (compute_aligned_dword_base_address baseValue imm) 8)
     (hram : JoltISA.RAM_START_ADDRESS ≤ (compute_aligned_dword_base_address baseValue imm).toNat)
     (hload : Assumptions.JoltRamLoadOk (compute_aligned_dword_base_address baseValue imm) js)
-    (hstore : Assumptions.JoltRamStoreOk (compute_aligned_dword_base_address baseValue imm) js) :
+    (hstore : Assumptions.JoltRamStoreOk (compute_aligned_dword_base_address baseValue imm) js
+      (fusedSpliceValue width
+        (loaded_dword_at js.sail (compute_aligned_dword_base_address baseValue imm) hbytes haligned.no_ovf)
+        value (load_effective_address baseValue imm)) 8) :
     ∃ js', JoltISA.Program.Run (laneStoreProgram width rs1 rs2 (sign_extend (m := 64) imm)) js js' ∧
       js'.sail = state_after_dword_store js.sail (compute_aligned_dword_base_address baseValue imm)
         (fusedSpliceValue width
           (loaded_dword_at js.sail (compute_aligned_dword_base_address baseValue imm) hbytes haligned.no_ovf)
           value (load_effective_address baseValue imm))
```

### `sdWriteBlock` (theorem)

File: `JoltBytecode/InstructionEquivalence/Instructions/StoreFamily/ProgramBlocks.lean:1668`.

```diff
@@ -1,20 +1,20 @@
 theorem sdWriteBlock (rest : JoltISA.Program)
     (js_store : SailJoltState) (base dword_new : BitVec 64) (s' : SailState)
     (hbase : js_store.vregs JoltISA.inlineTmp1 = base)
     (hdword : js_store.vregs JoltISA.inlineTmp2 = dword_new)
     (h_align : base &&& (7 : BitVec 64) = 0)
     (hwrite :
       vmem_write_addr (Virtaddr base) 8 dword_new
         (Store Data) false false false js_store.sail =
       .ok (Ok true) s')
     (h_ram : JoltISA.RAM_START_ADDRESS ≤ base.toNat)
     (hpriv : Assumptions.CurPrivilegeMachine js_store.sail)
     (hmprv : Assumptions.MstatusMprvZero js_store.sail)
     (hpmp : Assumptions.StorePmpOk base 8 js_store.sail)
     (hmmio : Assumptions.NotWritableMmio base 8 js_store.sail)
-    (hjolt : Assumptions.JoltRamStoreOk base js_store) :
+    (hjolt : Assumptions.JoltRamStoreOk base js_store dword_new 8) :
     ∃ js_write : SailJoltState,
       (JoltISA.execProgram (.instr (JoltISA.Encoded.SD (.vreg JoltISA.inlineTmp1) (.vreg JoltISA.inlineTmp2) 0) rest)).run js_store =
         (JoltISA.execProgram rest).run js_write ∧
       js_write.sail = s' ∧
       js_write.vregs = js_store.vregs
```

### `sbProgramAuto_reduces_to_dword_store` (theorem)

File: `JoltBytecode/InstructionEquivalence/Instructions/StoreFamily/Sb_main.lean:51`.

```diff
@@ -1,46 +1,48 @@
 theorem sbProgramAuto_reduces_to_dword_store (imm : BitVec 12) (rs2 rs1 : regidx)
     (js : SailJoltState)
     (hpriv : Assumptions.CurPrivilegeMachine js.sail)
     (hmprv : Assumptions.MstatusMprvZero js.sail)
     (rs1_val rs2_val : BitVec 64)
     (hrs1 : rX_bits rs1 js.sail = .ok rs1_val js.sail)
     (hrs2 : rX_bits rs2 js.sail = .ok rs2_val js.sail)
     (hsetup : StoreSplice.ByteStoreFacts
       (load_effective_address rs1_val imm)
       (compute_aligned_dword_base_address rs1_val imm))
     (h_base_aligned :
       AlignedDwordAccess (compute_aligned_dword_base_address rs1_val imm))
     (hbytes :
       MemBytesPresentAt js.sail (compute_aligned_dword_base_address rs1_val imm) 8)
     (hload_pmp :
       Assumptions.LoadPmpOk (compute_aligned_dword_base_address rs1_val imm) 8 js.sail)
     (hread_mmio :
       Assumptions.NotReadableMmio (compute_aligned_dword_base_address rs1_val imm) 8 js.sail)
     (hwrite_dword :
       vmem_write_addr
         (Virtaddr (compute_aligned_dword_base_address rs1_val imm)) 8
         (sbSplicedDword imm rs1_val rs2_val
           (loaded_dword_at js.sail (compute_aligned_dword_base_address rs1_val imm)
             hbytes h_base_aligned.no_ovf))
         (Store Data) false false false js.sail =
       .ok (Ok true)
         (state_after_dword_store js.sail
           (compute_aligned_dword_base_address rs1_val imm)
           (sbSplicedDword imm rs1_val rs2_val
             (loaded_dword_at js.sail (compute_aligned_dword_base_address rs1_val imm)
               hbytes h_base_aligned.no_ovf))))
     (hstore_pmp :
       Assumptions.StorePmpOk (compute_aligned_dword_base_address rs1_val imm) 8 js.sail)
     (hwrite_mmio :
       Assumptions.NotWritableMmio (compute_aligned_dword_base_address rs1_val imm) 8 js.sail)
     (hjolt_load : Assumptions.JoltRamLoadOk (compute_aligned_dword_base_address rs1_val imm) js)
-    (hjolt_store : Assumptions.JoltRamStoreOk (compute_aligned_dword_base_address rs1_val imm) js) :
+    (hjolt_store : Assumptions.JoltRamStoreOk (compute_aligned_dword_base_address rs1_val imm) js
+      (sbSplicedDword imm rs1_val rs2_val (loaded_dword_at js.sail
+        (compute_aligned_dword_base_address rs1_val imm) hbytes h_base_aligned.no_ovf)) 8) :
     ∃ js' : SailJoltState,
       (JoltISA.execProgram (JoltISA.sbProgramAuto rs1 rs2 imm)).run js =
         .ok RETIRE_SUCCESS js' ∧
       js'.sail =
         state_after_dword_store js.sail
           (compute_aligned_dword_base_address rs1_val imm)
           (sbSplicedDword imm rs1_val rs2_val
             (loaded_dword_at js.sail (compute_aligned_dword_base_address rs1_val imm)
               hbytes h_base_aligned.no_ovf))
```

### `sbProgramAuto_concrete` (theorem)

File: `JoltBytecode/InstructionEquivalence/Instructions/StoreFamily/Sb_main.lean:176`.

```diff
@@ -1,44 +1,46 @@
 theorem sbProgramAuto_concrete (imm : BitVec 12) (rs2 rs1 : regidx)
     (js : SailJoltState)
     (hpriv : Assumptions.CurPrivilegeMachine js.sail)
     (hmprv : Assumptions.MstatusMprvZero js.sail)
     (rs1_val rs2_val : BitVec 64)
     (hrs1 : rX_bits rs1 js.sail = .ok rs1_val js.sail)
     (hrs2 : rX_bits rs2 js.sail = .ok rs2_val js.sail)
     (hsetup : StoreSplice.ByteStoreFacts
       (load_effective_address rs1_val imm)
       (compute_aligned_dword_base_address rs1_val imm))
     (h_base_aligned :
       AlignedDwordAccess (compute_aligned_dword_base_address rs1_val imm))
     (hbytes :
       MemBytesPresentAt js.sail (compute_aligned_dword_base_address rs1_val imm) 8)
     (hload_pmp :
       Assumptions.LoadPmpOk (compute_aligned_dword_base_address rs1_val imm) 8 js.sail)
     (hread_mmio :
       Assumptions.NotReadableMmio (compute_aligned_dword_base_address rs1_val imm) 8 js.sail)
     (hwrite_dword :
       vmem_write_addr
         (Virtaddr (compute_aligned_dword_base_address rs1_val imm)) 8
         (sbSplicedDword imm rs1_val rs2_val
           (loaded_dword_at js.sail (compute_aligned_dword_base_address rs1_val imm)
             hbytes h_base_aligned.no_ovf))
         (Store Data) false false false js.sail =
       .ok (Ok true)
         (state_after_dword_store js.sail
           (compute_aligned_dword_base_address rs1_val imm)
           (sbSplicedDword imm rs1_val rs2_val
             (loaded_dword_at js.sail (compute_aligned_dword_base_address rs1_val imm)
               hbytes h_base_aligned.no_ovf))))
     (hstore_pmp :
       Assumptions.StorePmpOk (compute_aligned_dword_base_address rs1_val imm) 8 js.sail)
     (hwrite_mmio :
       Assumptions.NotWritableMmio (compute_aligned_dword_base_address rs1_val imm) 8 js.sail)
     (hjolt_load : Assumptions.JoltRamLoadOk (compute_aligned_dword_base_address rs1_val imm) js)
-    (hjolt_store : Assumptions.JoltRamStoreOk (compute_aligned_dword_base_address rs1_val imm) js) :
+    (hjolt_store : Assumptions.JoltRamStoreOk (compute_aligned_dword_base_address rs1_val imm) js
+      (sbSplicedDword imm rs1_val rs2_val (loaded_dword_at js.sail
+        (compute_aligned_dword_base_address rs1_val imm) hbytes h_base_aligned.no_ovf)) 8) :
     ∃ js' : SailJoltState,
       (JoltISA.execProgram (JoltISA.sbProgramAuto rs1 rs2 imm)).run js =
         .ok RETIRE_SUCCESS js' ∧
       js'.sail =
         state_after_byte_store js.sail
           (load_effective_address rs1_val imm)
           (Sail.BitVec.extractLsb rs2_val 7 0)
```

### `sbProgramEqSailStatement` (def)

File: `JoltBytecode/InstructionEquivalence/Instructions/StoreFamily/Sb_main.lean:283`.

```diff
@@ -1,3 +1,3 @@
 def sbProgramEqSailStatement (imm : BitVec 12) (rs2 rs1 : regidx)
     (js : SailJoltState)
-    (_h : StoreProgramEqSailAssumptions imm rs2 rs1 js) : Prop
+    (_h : StoreProgramEqSailAssumptions imm rs2 rs1 js 1) : Prop
```

### `sbProgram_eq_sail` (theorem)

File: `JoltBytecode/InstructionEquivalence/Instructions/StoreFamily/Sb_main.lean:292`.

```diff
@@ -1,4 +1,4 @@
 theorem sbProgram_eq_sail (imm : BitVec 12) (rs2 rs1 : regidx)
     (js : SailJoltState)
-    (h : StoreProgramEqSailAssumptions imm rs2 rs1 js) :
+    (h : StoreProgramEqSailAssumptions imm rs2 rs1 js 1) :
     sbProgramEqSailStatement imm rs2 rs1 js h
```

### `shProgramAuto_reduces_to_dword_store` (theorem)

File: `JoltBytecode/InstructionEquivalence/Instructions/StoreFamily/Sh_main.lean:54`.

```diff
@@ -1,46 +1,48 @@
 theorem shProgramAuto_reduces_to_dword_store (imm : BitVec 12) (rs2 rs1 : regidx)
     (js : SailJoltState)
     (hpriv : Assumptions.CurPrivilegeMachine js.sail)
     (hmprv : Assumptions.MstatusMprvZero js.sail)
     (rs1_val rs2_val : BitVec 64)
     (hrs1 : rX_bits rs1 js.sail = .ok rs1_val js.sail)
     (hrs2 : rX_bits rs2 js.sail = .ok rs2_val js.sail)
     (hsetup : StoreSplice.HalfwordStoreFacts
       (load_effective_address rs1_val imm)
       (compute_aligned_dword_base_address rs1_val imm))
     (h_base_aligned :
       AlignedDwordAccess (compute_aligned_dword_base_address rs1_val imm))
     (hbytes :
       MemBytesPresentAt js.sail (compute_aligned_dword_base_address rs1_val imm) 8)
     (hload_pmp :
       Assumptions.LoadPmpOk (compute_aligned_dword_base_address rs1_val imm) 8 js.sail)
     (hread_mmio :
       Assumptions.NotReadableMmio (compute_aligned_dword_base_address rs1_val imm) 8 js.sail)
     (hwrite_dword :
       vmem_write_addr
         (Virtaddr (compute_aligned_dword_base_address rs1_val imm)) 8
         (shSplicedDword imm rs1_val rs2_val
           (loaded_dword_at js.sail (compute_aligned_dword_base_address rs1_val imm)
             hbytes h_base_aligned.no_ovf))
         (Store Data) false false false js.sail =
       .ok (Ok true)
         (state_after_dword_store js.sail
           (compute_aligned_dword_base_address rs1_val imm)
           (shSplicedDword imm rs1_val rs2_val
             (loaded_dword_at js.sail (compute_aligned_dword_base_address rs1_val imm)
               hbytes h_base_aligned.no_ovf))))
     (hstore_pmp :
       Assumptions.StorePmpOk (compute_aligned_dword_base_address rs1_val imm) 8 js.sail)
     (hwrite_mmio :
       Assumptions.NotWritableMmio (compute_aligned_dword_base_address rs1_val imm) 8 js.sail)
     (hjolt_load : Assumptions.JoltRamLoadOk (compute_aligned_dword_base_address rs1_val imm) js)
-    (hjolt_store : Assumptions.JoltRamStoreOk (compute_aligned_dword_base_address rs1_val imm) js) :
+    (hjolt_store : Assumptions.JoltRamStoreOk (compute_aligned_dword_base_address rs1_val imm) js
+      (shSplicedDword imm rs1_val rs2_val (loaded_dword_at js.sail
+        (compute_aligned_dword_base_address rs1_val imm) hbytes h_base_aligned.no_ovf)) 8) :
     ∃ js' : SailJoltState,
       (JoltISA.execProgram (JoltISA.shProgramAuto rs1 rs2 imm)).run js =
         .ok RETIRE_SUCCESS js' ∧
       js'.sail =
         state_after_dword_store js.sail
           (compute_aligned_dword_base_address rs1_val imm)
           (shSplicedDword imm rs1_val rs2_val
             (loaded_dword_at js.sail (compute_aligned_dword_base_address rs1_val imm)
               hbytes h_base_aligned.no_ovf))
```

### `shProgramAuto_concrete_aligned` (theorem)

File: `JoltBytecode/InstructionEquivalence/Instructions/StoreFamily/Sh_main.lean:176`.

```diff
@@ -1,44 +1,46 @@
 theorem shProgramAuto_concrete_aligned (imm : BitVec 12) (rs2 rs1 : regidx)
     (js : SailJoltState)
     (hpriv : Assumptions.CurPrivilegeMachine js.sail)
     (hmprv : Assumptions.MstatusMprvZero js.sail)
     (rs1_val rs2_val : BitVec 64)
     (hrs1 : rX_bits rs1 js.sail = .ok rs1_val js.sail)
     (hrs2 : rX_bits rs2 js.sail = .ok rs2_val js.sail)
     (hsetup : StoreSplice.HalfwordStoreFacts
       (load_effective_address rs1_val imm)
       (compute_aligned_dword_base_address rs1_val imm))
     (h_base_aligned :
       AlignedDwordAccess (compute_aligned_dword_base_address rs1_val imm))
     (hbytes :
       MemBytesPresentAt js.sail (compute_aligned_dword_base_address rs1_val imm) 8)
     (hload_pmp :
       Assumptions.LoadPmpOk (compute_aligned_dword_base_address rs1_val imm) 8 js.sail)
     (hread_mmio :
       Assumptions.NotReadableMmio (compute_aligned_dword_base_address rs1_val imm) 8 js.sail)
     (hwrite_dword :
       vmem_write_addr
         (Virtaddr (compute_aligned_dword_base_address rs1_val imm)) 8
         (shSplicedDword imm rs1_val rs2_val
           (loaded_dword_at js.sail (compute_aligned_dword_base_address rs1_val imm)
             hbytes h_base_aligned.no_ovf))
         (Store Data) false false false js.sail =
       .ok (Ok true)
         (state_after_dword_store js.sail
           (compute_aligned_dword_base_address rs1_val imm)
           (shSplicedDword imm rs1_val rs2_val
             (loaded_dword_at js.sail (compute_aligned_dword_base_address rs1_val imm)
               hbytes h_base_aligned.no_ovf))))
     (hstore_pmp :
       Assumptions.StorePmpOk (compute_aligned_dword_base_address rs1_val imm) 8 js.sail)
     (hwrite_mmio :
       Assumptions.NotWritableMmio (compute_aligned_dword_base_address rs1_val imm) 8 js.sail)
     (hjolt_load : Assumptions.JoltRamLoadOk (compute_aligned_dword_base_address rs1_val imm) js)
-    (hjolt_store : Assumptions.JoltRamStoreOk (compute_aligned_dword_base_address rs1_val imm) js) :
+    (hjolt_store : Assumptions.JoltRamStoreOk (compute_aligned_dword_base_address rs1_val imm) js
+      (shSplicedDword imm rs1_val rs2_val (loaded_dword_at js.sail
+        (compute_aligned_dword_base_address rs1_val imm) hbytes h_base_aligned.no_ovf)) 8) :
     ∃ js' : SailJoltState,
       (JoltISA.execProgram (JoltISA.shProgramAuto rs1 rs2 imm)).run js =
         .ok RETIRE_SUCCESS js' ∧
       js'.sail =
         state_after_halfword_store js.sail
           (load_effective_address rs1_val imm)
           (Sail.BitVec.extractLsb rs2_val 15 0)
```

### `shProgramEqSailStatement` (def)

File: `JoltBytecode/InstructionEquivalence/Instructions/StoreFamily/Sh_main.lean:328`.

```diff
@@ -1,3 +1,3 @@
 def shProgramEqSailStatement (imm : BitVec 12) (rs2 rs1 : regidx)
     (js : SailJoltState)
-    (_h : StoreProgramEqSailAssumptions imm rs2 rs1 js) : Prop
+    (_h : StoreProgramEqSailAssumptions imm rs2 rs1 js 2) : Prop
```

### `shProgram_eq_sail` (theorem)

File: `JoltBytecode/InstructionEquivalence/Instructions/StoreFamily/Sh_main.lean:337`.

```diff
@@ -1,4 +1,4 @@
 theorem shProgram_eq_sail (imm : BitVec 12) (rs2 rs1 : regidx)
     (js : SailJoltState)
-    (h : StoreProgramEqSailAssumptions imm rs2 rs1 js) :
+    (h : StoreProgramEqSailAssumptions imm rs2 rs1 js 2) :
     shProgramEqSailStatement imm rs2 rs1 js h
```

### `offset_toNat_eq_low_three` (theorem)

File: `JoltBytecode/InstructionEquivalence/Instructions/StoreFamily/Splice.lean:248`.

```diff
@@ -1,3 +1,3 @@
-private theorem offset_toNat_eq_low_three {ea base : BitVec 64}
+theorem offset_toNat_eq_low_three {ea base : BitVec 64}
     (hbase : base = ea &&& (-8 : BitVec 64)) :
     (ea - base).toNat = (ea &&& (7 : BitVec 64)).toNat
```

### `swProgramAuto_reduces_to_dword_store` (theorem)

File: `JoltBytecode/InstructionEquivalence/Instructions/StoreFamily/Sw_main.lean:62`.

```diff
@@ -1,46 +1,48 @@
 theorem swProgramAuto_reduces_to_dword_store (imm : BitVec 12) (rs2 rs1 : regidx)
     (js : SailJoltState)
     (hpriv : Assumptions.CurPrivilegeMachine js.sail)
     (hmprv : Assumptions.MstatusMprvZero js.sail)
     (rs1_val rs2_val : BitVec 64)
     (hrs1 : rX_bits rs1 js.sail = .ok rs1_val js.sail)
     (hrs2 : rX_bits rs2 js.sail = .ok rs2_val js.sail)
     (hsetup : StoreSplice.WordStoreFacts
       (load_effective_address rs1_val imm)
       (compute_aligned_dword_base_address rs1_val imm))
     (h_base_aligned :
       AlignedDwordAccess (compute_aligned_dword_base_address rs1_val imm))
     (hbytes :
       MemBytesPresentAt js.sail (compute_aligned_dword_base_address rs1_val imm) 8)
     (hload_pmp :
       Assumptions.LoadPmpOk (compute_aligned_dword_base_address rs1_val imm) 8 js.sail)
     (hread_mmio :
       Assumptions.NotReadableMmio (compute_aligned_dword_base_address rs1_val imm) 8 js.sail)
     (hwrite_dword :
       vmem_write_addr
         (Virtaddr (compute_aligned_dword_base_address rs1_val imm)) 8
         (swSplicedDword imm rs1_val rs2_val
           (loaded_dword_at js.sail (compute_aligned_dword_base_address rs1_val imm)
             hbytes h_base_aligned.no_ovf))
         (Store Data) false false false js.sail =
       .ok (Ok true)
         (state_after_dword_store js.sail
           (compute_aligned_dword_base_address rs1_val imm)
           (swSplicedDword imm rs1_val rs2_val
             (loaded_dword_at js.sail (compute_aligned_dword_base_address rs1_val imm)
               hbytes h_base_aligned.no_ovf))))
     (hstore_pmp :
       Assumptions.StorePmpOk (compute_aligned_dword_base_address rs1_val imm) 8 js.sail)
     (hwrite_mmio :
       Assumptions.NotWritableMmio (compute_aligned_dword_base_address rs1_val imm) 8 js.sail)
     (hjolt_load : Assumptions.JoltRamLoadOk (compute_aligned_dword_base_address rs1_val imm) js)
-    (hjolt_store : Assumptions.JoltRamStoreOk (compute_aligned_dword_base_address rs1_val imm) js) :
+    (hjolt_store : Assumptions.JoltRamStoreOk (compute_aligned_dword_base_address rs1_val imm) js
+      (swSplicedDword imm rs1_val rs2_val (loaded_dword_at js.sail
+        (compute_aligned_dword_base_address rs1_val imm) hbytes h_base_aligned.no_ovf)) 8) :
     ∃ js' : SailJoltState,
       (JoltISA.execProgram (JoltISA.swProgramAuto rs1 rs2 imm)).run js =
         .ok RETIRE_SUCCESS js' ∧
       js'.sail =
         state_after_dword_store js.sail
           (compute_aligned_dword_base_address rs1_val imm)
           (swSplicedDword imm rs1_val rs2_val
             (loaded_dword_at js.sail (compute_aligned_dword_base_address rs1_val imm)
               hbytes h_base_aligned.no_ovf))
```

### `swProgramAuto_concrete_aligned` (theorem)

File: `JoltBytecode/InstructionEquivalence/Instructions/StoreFamily/Sw_main.lean:190`.

```diff
@@ -1,44 +1,46 @@
 theorem swProgramAuto_concrete_aligned (imm : BitVec 12) (rs2 rs1 : regidx)
     (js : SailJoltState)
     (hpriv : Assumptions.CurPrivilegeMachine js.sail)
     (hmprv : Assumptions.MstatusMprvZero js.sail)
     (rs1_val rs2_val : BitVec 64)
     (hrs1 : rX_bits rs1 js.sail = .ok rs1_val js.sail)
     (hrs2 : rX_bits rs2 js.sail = .ok rs2_val js.sail)
     (hsetup : StoreSplice.WordStoreFacts
       (load_effective_address rs1_val imm)
       (compute_aligned_dword_base_address rs1_val imm))
     (h_base_aligned :
       AlignedDwordAccess (compute_aligned_dword_base_address rs1_val imm))
     (hbytes :
       MemBytesPresentAt js.sail (compute_aligned_dword_base_address rs1_val imm) 8)
     (hload_pmp :
       Assumptions.LoadPmpOk (compute_aligned_dword_base_address rs1_val imm) 8 js.sail)
     (hread_mmio :
       Assumptions.NotReadableMmio (compute_aligned_dword_base_address rs1_val imm) 8 js.sail)
     (hwrite_dword :
       vmem_write_addr
         (Virtaddr (compute_aligned_dword_base_address rs1_val imm)) 8
         (swSplicedDword imm rs1_val rs2_val
           (loaded_dword_at js.sail (compute_aligned_dword_base_address rs1_val imm)
             hbytes h_base_aligned.no_ovf))
         (Store Data) false false false js.sail =
       .ok (Ok true)
         (state_after_dword_store js.sail
           (compute_aligned_dword_base_address rs1_val imm)
           (swSplicedDword imm rs1_val rs2_val
             (loaded_dword_at js.sail (compute_aligned_dword_base_address rs1_val imm)
               hbytes h_base_aligned.no_ovf))))
     (hstore_pmp :
       Assumptions.StorePmpOk (compute_aligned_dword_base_address rs1_val imm) 8 js.sail)
     (hwrite_mmio :
       Assumptions.NotWritableMmio (compute_aligned_dword_base_address rs1_val imm) 8 js.sail)
     (hjolt_load : Assumptions.JoltRamLoadOk (compute_aligned_dword_base_address rs1_val imm) js)
-    (hjolt_store : Assumptions.JoltRamStoreOk (compute_aligned_dword_base_address rs1_val imm) js) :
+    (hjolt_store : Assumptions.JoltRamStoreOk (compute_aligned_dword_base_address rs1_val imm) js
+      (swSplicedDword imm rs1_val rs2_val (loaded_dword_at js.sail
+        (compute_aligned_dword_base_address rs1_val imm) hbytes h_base_aligned.no_ovf)) 8) :
     ∃ js' : SailJoltState,
       (JoltISA.execProgram (JoltISA.swProgramAuto rs1 rs2 imm)).run js =
         .ok RETIRE_SUCCESS js' ∧
       js'.sail =
         state_after_word_store js.sail
           (load_effective_address rs1_val imm)
           (Sail.BitVec.extractLsb rs2_val 31 0)
```

### `swProgramEqSailStatement` (def)

File: `JoltBytecode/InstructionEquivalence/Instructions/StoreFamily/Sw_main.lean:348`.

```diff
@@ -1,3 +1,3 @@
 def swProgramEqSailStatement (imm : BitVec 12) (rs2 rs1 : regidx)
     (js : SailJoltState)
-    (_h : StoreProgramEqSailAssumptions imm rs2 rs1 js) : Prop
+    (_h : StoreProgramEqSailAssumptions imm rs2 rs1 js 4) : Prop
```

### `swProgram_eq_sail` (theorem)

File: `JoltBytecode/InstructionEquivalence/Instructions/StoreFamily/Sw_main.lean:357`.

```diff
@@ -1,4 +1,4 @@
 theorem swProgram_eq_sail (imm : BitVec 12) (rs2 rs1 : regidx)
     (js : SailJoltState)
-    (h : StoreProgramEqSailAssumptions imm rs2 rs1 js) :
+    (h : StoreProgramEqSailAssumptions imm rs2 rs1 js 4) :
     swProgramEqSailStatement imm rs2 rs1 js h
```

### `ReservationStoreEqAssumptions` (structure)

File: `JoltBytecode/InstructionEquivalence/Instructions/System/Sc.lean:23`.

```diff
@@ -1,8 +1,9 @@
 structure ReservationStoreEqAssumptions (double : Bool) (rs2 rs1 : regidx)
     (js : SailJoltState) : Type extends BinarySourceReadWithLinkedCSRs rs2 rs1 js,
       ReservationWindow double rs1_val js where
   not_writable_mmio : Assumptions.NotWritableMmioWindow (reservationBase double rs1_val) 8 js.sail
   jolt_ram_store : Assumptions.JoltRamStoreOk (reservationBase double rs1_val) js
+    (scStoreValue double js rs1_val rs2_val) 8
   conditional_access : phys_access_check (StoreConditional Data) Privilege.Machine
     (physaddr.Physaddr rs1_val) (if double then 8 else 4) true js.sail = .ok none js.sail
   reservation_pair : js.vregs 33#7 = 0#64 ∨ js.vregs 33#7 = js.vregs 32#7
```

### `scdProgram_spec` (theorem)

File: `JoltBytecode/InstructionEquivalence/Instructions/System/ScDword.lean:25`.

```diff
@@ -1,12 +1,13 @@
 theorem scdProgram_spec (rd rs1 rs2 : regidx) (js : SailJoltState) (addr src : BitVec 64)
     (hr1 : rX_bits rs1 js.sail = .ok addr js.sail)
     (hr2 : rX_bits rs2 js.sail = .ok src js.sail)
     (ha : addr &&& 7#64 = 0#64) (hram : JoltISA.RAM_START_ADDRESS ≤ addr.toNat)
     (hl : JoltISA.Mmu.effective_address_ok js.jolt_device addr.toNat false = true)
-    (hs : JoltISA.Mmu.effective_address_ok js.jolt_device addr.toNat true = true) :
+    (hs : Assumptions.JoltRamStoreOk addr js
+      (if addr == js.vregs 33#7 then src else JoltISA.Mmu.ram_doubleword js.sail.mem addr.toNat) 8) :
     System.systemProjectResult (JoltISA.execProgram (JoltISA.scdProgramAuto rd rs1 rs2) js) =
       .ok RETIRE_SUCCESS (stateAfterWrite
         (System.systemProject (withReservation
           { js with sail := (state_after_dword_store js.sail addr
             (if addr == js.vregs 33#7 then src else JoltISA.Mmu.ram_doubleword js.sail.mem addr.toNat)) }
           0#64 0#64)) rd (if addr == js.vregs 33#7 then 0#64 else 1#64))
```

### `scwProgram_spec` (theorem)

File: `JoltBytecode/InstructionEquivalence/Instructions/System/ScWord.lean:84`.

```diff
@@ -1,14 +1,18 @@
 theorem scwProgram_spec (rd rs1 rs2 : regidx) (js : SailJoltState) (addr src : BitVec 64)
     (hr1 : rX_bits rs1 js.sail = .ok addr js.sail)
     (hr2 : rX_bits rs2 js.sail = .ok src js.sail)
     (ha : addr &&& 3#64 = 0#64) (hram : JoltISA.RAM_START_ADDRESS ≤ addr.toNat)
     (hbase : JoltISA.RAM_START_ADDRESS ≤ (amoWordBase addr).toNat)
     (hl : JoltISA.Mmu.effective_address_ok js.jolt_device (amoWordBase addr).toNat false = true)
-    (hs : Assumptions.JoltRamStoreOk (amoWordBase addr) js) :
+    (hs : Assumptions.JoltRamStoreOk (amoWordBase addr) js
+      (AtomicFamily.amoWordLaneMerged addr
+        (JoltISA.Mmu.ram_doubleword js.sail.mem (amoWordBase addr).toNat)
+        (if addr == js.vregs 32#7 then src else AtomicFamily.amoWordLaneOld addr
+          (JoltISA.Mmu.ram_doubleword js.sail.mem (amoWordBase addr).toNat))) 8) :
     System.systemProjectResult (JoltISA.execProgram (JoltISA.scwProgramAuto rd rs1 rs2) js) =
       .ok RETIRE_SUCCESS (stateAfterWrite (System.systemProject (withReservation
         { js with sail := (state_after_dword_store js.sail (amoWordBase addr)
           (AtomicFamily.amoWordLaneMerged addr (JoltISA.Mmu.ram_doubleword js.sail.mem (amoWordBase addr).toNat)
             (if addr == js.vregs 32#7 then src else AtomicFamily.amoWordLaneOld addr
               (JoltISA.Mmu.ram_doubleword js.sail.mem (amoWordBase addr).toNat)))) }
         0#64 0#64)) rd (if addr == js.vregs 32#7 then 0#64 else 1#64))
```

### `InstrWritesNoProtectedVReg` (def)

File: `JoltBytecode/InstructionEquivalence/ProofSupport/Basic.lean:178`.

```diff
@@ -1,92 +1,93 @@
 def InstrWritesNoProtectedVReg : Instr → Prop
   | .ADDI dst _ _ => DstWritesNoProtectedVReg dst
   | .ADDIW dst _ _ => DstWritesNoProtectedVReg dst
   | .ANDI dst _ _ => DstWritesNoProtectedVReg dst
   | .ORI dst _ _ => DstWritesNoProtectedVReg dst
   | .XORI dst _ _ => DstWritesNoProtectedVReg dst
   | .SLTI _ _ _ => False
   | .SLTIU _ _ _ => False
   | .LUI dst _ => DstWritesNoProtectedVReg dst
   | .AUIPC _ _ => False
   | .JAL _ _ => False
   | .JALR _ _ _ => False
   | .BEQ _ _ _ => False
   | .BNE _ _ _ => False
   | .BLT _ _ _ => False
   | .BGE _ _ _ => False
   | .BLTU _ _ _ => False
   | .BGEU _ _ _ => False
+  | .JoltSuccess _ | .Panic _ => False
   | .FENCE => False
   | .ADD dst _ _ => DstWritesNoProtectedVReg dst
   | .ADDW dst _ _ => DstWritesNoProtectedVReg dst
   | .SUB dst _ _ => DstWritesNoProtectedVReg dst
   | .SUBW dst _ _ => DstWritesNoProtectedVReg dst
   | .MUL dst _ _ => DstWritesNoProtectedVReg dst
   | .MULW dst _ _ => DstWritesNoProtectedVReg dst
   | .MULHU dst _ _ => DstWritesNoProtectedVReg dst
   | .ANDN dst _ _ => DstWritesNoProtectedVReg dst
   | .OR dst _ _ => DstWritesNoProtectedVReg dst
   | .XOR dst _ _ => DstWritesNoProtectedVReg dst
   | .AND dst _ _ => DstWritesNoProtectedVReg dst
   | .SLT dst _ _ => DstWritesNoProtectedVReg dst
   | .SLTU dst _ _ => DstWritesNoProtectedVReg dst
   | .VirtualMULI dst _ _ => DstWritesNoProtectedVReg dst
   | .VirtualMULIW dst _ _ => DstWritesNoProtectedVReg dst
   | .VirtualPow2 dst _ _ => DstWritesNoProtectedVReg dst
   | .VirtualPow2W dst _ _ => DstWritesNoProtectedVReg dst
   | .VirtualPow2I _ _ => False
   | .VirtualPow2IW _ _ => False
   | .VirtualShiftRightBitmask dst _ _ => DstWritesNoProtectedVReg dst
   | .VirtualShiftRightBitmaskI _ _ => False
   | .VirtualShiftRightBitmaskW dst _ _ => DstWritesNoProtectedVReg dst
   | .VirtualSRLI dst _ _ => DstWritesNoProtectedVReg dst
   | .VirtualSRAI dst _ _ => DstWritesNoProtectedVReg dst
   | .VirtualSRLIW dst _ _ => DstWritesNoProtectedVReg dst
   | .VirtualSRAIW dst _ _ => DstWritesNoProtectedVReg dst
   | .VirtualSRL dst _ _ => DstWritesNoProtectedVReg dst
   | .VirtualSRA dst _ _ => DstWritesNoProtectedVReg dst
   | .VirtualSRLW dst _ _ => DstWritesNoProtectedVReg dst
   | .VirtualSRAW dst _ _ => DstWritesNoProtectedVReg dst
   | .VirtualROTRI _ _ _ => False
   | .VirtualROTRIW _ _ _ => False
   | .VirtualRev8W _ _ _ => False
   | .VirtualXORROT32 _ _ _ => False
   | .VirtualXORROT24 _ _ _ => False
   | .VirtualXORROT16 _ _ _ => False
   | .VirtualXORROT63 _ _ _ => False
   | .VirtualXORROTL1 dst _ _ => DstWritesNoProtectedVReg dst
   | .VirtualXORROTW16 _ _ _ => False
   | .VirtualXORROTW12 _ _ _ => False
   | .VirtualXORROTW8 _ _ _ => False
   | .VirtualXORROTW7 _ _ _ => False
   | .VirtualXORROTW22 _ _ _ => False
   | .VirtualXORROTW19 _ _ _ => False
   | .VirtualXORROTW6 _ _ _ => False
   | .VirtualWindowMaskB dst _ _ => DstWritesNoProtectedVReg dst
   | .VirtualWindowMaskH dst _ _ => DstWritesNoProtectedVReg dst
   | .VirtualWindowMaskW dst _ _ => DstWritesNoProtectedVReg dst
   | .VirtualShiftDataB dst _ _ _ => DstWritesNoProtectedVReg dst
   | .VirtualShiftDataH dst _ _ _ => DstWritesNoProtectedVReg dst
   | .VirtualShiftDataW dst _ _ _ => DstWritesNoProtectedVReg dst
   | .VirtualPext dst _ _ => DstWritesNoProtectedVReg dst
   | .VirtualPextSigned dst _ _ => DstWritesNoProtectedVReg dst
   | .VirtualSignExtendWord dst _ _ => DstWritesNoProtectedVReg dst
   | .VirtualZeroExtendWord dst _ _ => DstWritesNoProtectedVReg dst
   | .VirtualMovsign dst _ _ => DstWritesNoProtectedVReg dst
   | .LD _ dst _ _ => DstWritesNoProtectedVReg dst
   | .VirtualLoadB _ dst _ _ _ => DstWritesNoProtectedVReg dst
   | .VirtualLoadH _ dst _ _ _ => DstWritesNoProtectedVReg dst
   | .VirtualLoadW _ dst _ _ _ => DstWritesNoProtectedVReg dst
   | .SD _ _ _ => True
   | .VirtualStoreB _ _ _ _ => True
   | .VirtualStoreH _ _ _ _ => True
   | .VirtualStoreW _ _ _ _ => True
   | .VirtualAdvice dst _ _ => DstWritesNoProtectedVReg dst
   | .VirtualAdviceLoad dst _ => DstWritesNoProtectedVReg dst
   | .VirtualHostIO => False
   | .VirtualAssertEQ _ _ _ => True
   | .VirtualAssertValidDiv0 _ _ _ => True
   | .VirtualNegateIf dst _ _ => DstWritesNoProtectedVReg dst
   | .VirtualAssertValidUnsignedRemainder _ _ _ => True
   | .VirtualAssertMulUNoOverflow _ _ _ => True
   | .VirtualAssertLTE _ _ _ => True
```

### `StoreDwordWindowFacts` (structure)

File: `JoltBytecode/InstructionEquivalence/ProofSupport/BundleLemmas.lean:60`.

```diff
@@ -1,19 +1,19 @@
 structure StoreDwordWindowFacts
-    (imm : BitVec 12) (rs2 rs1 : regidx) (js : SailJoltState)
-    (h : StoreProgramEqSailAssumptions imm rs2 rs1 js) : Prop where
+    (imm : BitVec 12) (rs2 rs1 : regidx) (js : SailJoltState) {storeWidth : Nat}
+    (h : StoreProgramEqSailAssumptions imm rs2 rs1 js storeWidth) : Prop where
   aligned :
     AlignedDwordAccess (compute_aligned_dword_base_address h.rs1_val imm)
   bytes :
     MemBytesPresentAt js.sail (compute_aligned_dword_base_address h.rs1_val imm) 8
   load_pmp :
     Assumptions.LoadPmpOk
       (compute_aligned_dword_base_address h.rs1_val imm) 8 js.sail
   read_mmio :
     Assumptions.NotReadableMmio
       (compute_aligned_dword_base_address h.rs1_val imm) 8 js.sail
   store_pmp :
     Assumptions.StorePmpOk
       (compute_aligned_dword_base_address h.rs1_val imm) 8 js.sail
   write_mmio :
     Assumptions.NotWritableMmio
       (compute_aligned_dword_base_address h.rs1_val imm) 8 js.sail
```

### `StoreProgramEqSailAssumptions.dwordWindowFacts` (theorem)

File: `JoltBytecode/InstructionEquivalence/ProofSupport/BundleLemmas.lean:80`.

```diff
@@ -1,4 +1,4 @@
 theorem StoreProgramEqSailAssumptions.dwordWindowFacts
-    {imm : BitVec 12} {rs2 rs1 : regidx} {js : SailJoltState}
-    (h : StoreProgramEqSailAssumptions imm rs2 rs1 js) :
+    {imm : BitVec 12} {rs2 rs1 : regidx} {js : SailJoltState} {storeWidth : Nat}
+    (h : StoreProgramEqSailAssumptions imm rs2 rs1 js storeWidth) :
     StoreDwordWindowFacts imm rs2 rs1 js h
```

### `StoreAccessFacts` (structure)

File: `JoltBytecode/InstructionEquivalence/ProofSupport/BundleLemmas.lean:117`.

```diff
@@ -1,8 +1,8 @@
 structure StoreAccessFacts
-    (imm : BitVec 12) (rs2 rs1 : regidx) (js : SailJoltState)
-    (h : StoreProgramEqSailAssumptions imm rs2 rs1 js)
+    (imm : BitVec 12) (rs2 rs1 : regidx) (js : SailJoltState) {storeWidth : Nat}
+    (h : StoreProgramEqSailAssumptions imm rs2 rs1 js storeWidth)
     (width : Nat) : Prop where
   store_pmp :
     Assumptions.StorePmpOk (load_effective_address h.rs1_val imm) width js.sail
   write_mmio :
     Assumptions.NotWritableMmio (load_effective_address h.rs1_val imm) width js.sail
```

### `StoreProgramEqSailAssumptions.storeAccessFacts` (theorem)

File: `JoltBytecode/InstructionEquivalence/ProofSupport/BundleLemmas.lean:126`.

```diff
@@ -1,9 +1,9 @@
 theorem StoreProgramEqSailAssumptions.storeAccessFacts
-    {imm : BitVec 12} {rs2 rs1 : regidx} {js : SailJoltState}
-    (h : StoreProgramEqSailAssumptions imm rs2 rs1 js)
+    {imm : BitVec 12} {rs2 rs1 : regidx} {js : SailJoltState} {storeWidth : Nat}
+    (h : StoreProgramEqSailAssumptions imm rs2 rs1 js storeWidth)
     (width : Nat)
     (hpositive : 0 < width)
     (hfits :
       (load_effective_address h.rs1_val imm &&& (7 : BitVec 64)).toNat +
         width ≤ 8) :
     StoreAccessFacts imm rs2 rs1 js h width
```

### `Same` (structure)

File: `JoltBytecode/InstructionEquivalence/ProofSupport/DeviceFrame.lean:15`.

```diff
@@ -1 +1,2 @@
-def Same (a b : JoltDevice) : Prop
+structure Same (a b : JoltDevice) : Prop where
+  layout : b.memory_layout = a.memory_layout
```

### `Rules` (structure)

File: `JoltBytecode/InstructionEquivalence/ProofSupport/InstructionFrame.lean:28`.

```diff
@@ -1,13 +1,13 @@
 structure Rules (relation : SailJoltState → SailJoltState → Prop) : Prop where
   refl : ∀ state, relation state state
   trans : ∀ before middle after, relation before middle → relation middle after →
     relation before after
-  sail : ∀ state after, relation state { state with sail := after }
+  sail : ∀ (state : SailJoltState) (after : SailState), after.mem = state.sail.mem → relation state { state with sail := after }
   vreg : ∀ state vr value, relation state
     { state with vregs := fun r => if r = vr then value else state.vregs r }
-  store : ∀ state device address value,
-    JoltDevice.store? state.jolt_device address value = some device →
-    relation state { state with jolt_device := device }
+  store : ∀ address value,
+    StatePreservation.Preserves relation (Mmu.store_doubleword address value)
+  halt : ∀ state kind, relation state (recordHalt kind state)
   append : ∀ state bytes, relation state
     { state with adviceTape :=
       { state.adviceTape with bytes := state.adviceTape.bytes ++ bytes } }
```

### `NonStoreRules` (structure)

File: `JoltBytecode/InstructionEquivalence/ProofSupport/InstructionFrame.lean:46`.

```diff
@@ -1,10 +1,11 @@
 structure NonStoreRules (relation : SailJoltState → SailJoltState → Prop) : Prop where
   refl : ∀ state, relation state state
   trans : ∀ before middle after, relation before middle → relation middle after →
     relation before after
-  sail : ∀ state after, relation state { state with sail := after }
+  sail : ∀ (state : SailJoltState) (after : SailState), after.mem = state.sail.mem → relation state { state with sail := after }
   vreg : ∀ state vr value, relation state
     { state with vregs := fun r => if r = vr then value else state.vregs r }
+  halt : ∀ state kind, relation state (recordHalt kind state)
   append : ∀ state bytes, relation state
     { state with adviceTape :=
       { state.adviceTape with bytes := state.adviceTape.bytes ++ bytes } }
```

### `NonStoreRules.withStore` (theorem)

File: `JoltBytecode/InstructionEquivalence/ProofSupport/InstructionFrame.lean:62`.

```diff
@@ -1,5 +1,4 @@
 private theorem NonStoreRules.withStore {relation : SailJoltState → SailJoltState → Prop}
     (rules : NonStoreRules relation)
-    (store : ∀ state device address value,
-      JoltDevice.store? state.jolt_device address value = some device →
-      relation state { state with jolt_device := device }) : Rules relation
+    (store : ∀ address value,
+      StatePreservation.Preserves relation (Mmu.store_doubleword address value)) : Rules relation
```

### `writeDst_rule` (theorem)

File: `JoltBytecode/InstructionEquivalence/ProofSupport/InstructionFrame.lean:72`.

```diff
@@ -1,6 +1,6 @@
 theorem writeDst_rule (relation : SailJoltState → SailJoltState → Prop)
-    (sail : ∀ state after, relation state { state with sail := after })
+    (sail : ∀ (state : SailJoltState) (after : SailState), after.mem = state.sail.mem → relation state { state with sail := after })
     (vreg : ∀ state vr value, relation state
       { state with vregs := fun r => if r = vr then value else state.vregs r })
     (dst : Dst) (value : BitVec 64) :
     StatePreservation.Preserves relation (writeDst dst value)
```

### `lift_rule` (theorem)

File: `JoltBytecode/InstructionEquivalence/ProofSupport/InstructionFrame.lean:188`.

```diff
@@ -1,2 +1,2 @@
-private theorem lift_rule (rules : NonStoreRules relation) {α : Type} (step : SailM α) :
-    StatePreservation.Preserves relation (liftSail step)
+private theorem lift_rule (rules : NonStoreRules relation) {α : Type} (step : SailM α)
+    (hmem : SailMemory step) : StatePreservation.Preserves relation (liftSail step)
```

### `storeRaw_rule` (theorem)

File: `JoltBytecode/InstructionEquivalence/ProofSupport/InstructionFrame.lean:209`.

```diff
@@ -1,8 +1,8 @@
 theorem storeRaw_rule
     (sail : ∀ state after, relation state { state with sail := after })
     (store : ∀ state device address value,
-      JoltDevice.store? state.jolt_device address value = some device →
-      relation state { state with jolt_device := device })
+      JoltDevice.store? state.jolt_device state.sail.mem address value = some device →
+      relation state { state with sail := { state.sail with mem := device } })
     (s s' : SailJoltState)
     (address : Nat) (value : BitVec 8)
     (stored : Mmu.store_raw? s address value = some s') : relation s s'
```

### `execInstr_rule_of_store` (theorem)

File: `JoltBytecode/InstructionEquivalence/ProofSupport/InstructionFrame.lean:314`.

```diff
@@ -1,16 +1,12 @@
 theorem execInstr_rule_of_store (rules : NonStoreRules relation) (instr : Instr)
     (store : ∀ base source imm, instr = .SD base source imm →
-      ∀ state device address value,
-        JoltDevice.store? state.jolt_device address value = some device →
-        relation state { state with jolt_device := device })
+      ∀ address value, StatePreservation.Preserves relation (Mmu.store_doubleword address value))
     (floorStore : ∀ base source imm fault,
       (instr = .VirtualStoreB base source imm fault ∨
        instr = .VirtualStoreH base source imm fault ∨
        instr = .VirtualStoreW base source imm fault) →
-      ∀ state device address value,
-        JoltDevice.store? state.jolt_device address value = some device →
-        relation state { state with jolt_device := device })
+      ∀ address value, StatePreservation.Preserves relation (Mmu.store_doubleword address value))
     (read : ∀ dst width, instr = .VirtualAdviceLoad dst width →
       ∀ state value tape, readAdviceTape state.adviceTape width = some (value, tape) →
         relation state { state with adviceTape := tape }) :
     StatePreservation.Preserves relation (execInstr instr)
```

### `execInstr_sd_vreg_run` (theorem)

File: `JoltBytecode/InstructionEquivalence/ProofSupport/InstructionLemmas/SD.lean:22`.

```diff
@@ -1,13 +1,15 @@
 theorem execInstr_sd_vreg_run (base value : VReg) (imm : BitVec 12)
     (js : SailJoltState)
     (h_align :
       (js.vregs base + sign_extend (m := 64) imm) &&& (7 : BitVec 64) = 0)
     (h_ram : RAM_START_ADDRESS ≤ (js.vregs base + sign_extend (m := 64) imm).toNat)
     (h_legal : Mmu.effective_address_ok js.jolt_device
-      (js.vregs base + sign_extend (m := 64) imm).toNat true = true) :
+      (js.vregs base + sign_extend (m := 64) imm).toNat true = true)
+    (h_protected : Mmu.protected_store_ok js
+      (js.vregs base + sign_extend (m := 64) imm).toNat (js.vregs value) 8 = true) :
     (execInstr (JoltISA.Encoded.SD (.vreg base) (.vreg value) imm)).run js =
       .ok RETIRE_SUCCESS
         { js with
           sail := { js.sail with
             mem := Mmu.write_ram_doubleword js.sail.mem
               (js.vregs base + sign_extend (m := 64) imm).toNat (js.vregs value) } }
```

### `execInstr_sd_xreg_xreg_run` (theorem)

File: `JoltBytecode/InstructionEquivalence/ProofSupport/InstructionLemmas/SD.lean:44`.

```diff
@@ -1,16 +1,18 @@
 theorem execInstr_sd_xreg_xreg_run
     (base value : regidx) (imm : BitVec 12)
     (js : SailJoltState) (baseValue stored : BitVec 64)
     (hbase : rX_bits base js.sail = .ok baseValue js.sail)
     (hvalue : rX_bits value js.sail = .ok stored js.sail)
     (h_align :
       (baseValue + sign_extend (m := 64) imm) &&& (7 : BitVec 64) = 0)
     (h_ram : RAM_START_ADDRESS ≤ (baseValue + sign_extend (m := 64) imm).toNat)
     (h_legal : Mmu.effective_address_ok js.jolt_device
-      (baseValue + sign_extend (m := 64) imm).toNat true = true) :
+      (baseValue + sign_extend (m := 64) imm).toNat true = true)
+    (h_protected : Mmu.protected_store_ok js
+      (baseValue + sign_extend (m := 64) imm).toNat stored 8 = true) :
     (execInstr (JoltISA.Encoded.SD (.xreg base) (.xreg value) imm)).run js =
       .ok RETIRE_SUCCESS
         { js with
           sail := { js.sail with
             mem := Mmu.write_ram_doubleword js.sail.mem
               (baseValue + sign_extend (m := 64) imm).toNat stored } }
```

### `effective_address_ok_of_store` (theorem)

File: `JoltBytecode/InstructionEquivalence/ProofSupport/Memory/MmuJolt.lean:33`.

```diff
@@ -1,3 +1,3 @@
-theorem effective_address_ok_of_store {js : SailJoltState} {addr : BitVec 64}
-    (hram : RAM_START_ADDRESS ≤ addr.toNat) (h : Assumptions.JoltRamStoreOk addr js) :
+theorem effective_address_ok_of_store {js : SailJoltState} {addr value : BitVec 64} {width : Nat}
+    (hram : RAM_START_ADDRESS ≤ addr.toNat) (h : Assumptions.JoltRamStoreOk addr js value width) :
     effective_address_ok js.jolt_device addr.toNat true = true
```

### `store_doubleword_ram` (theorem)

File: `JoltBytecode/InstructionEquivalence/ProofSupport/Memory/MmuJolt.lean:209`.

```diff
@@ -1,6 +1,7 @@
 theorem store_doubleword_ram (js : SailJoltState) (addr value : BitVec 64)
     (halign : addr &&& 7 = 0) (hram : RAM_START_ADDRESS ≤ addr.toNat)
-    (hlegal : effective_address_ok js.jolt_device addr.toNat true = true) :
+    (hlegal : effective_address_ok js.jolt_device addr.toNat true = true)
+    (hprotected : protected_store_ok js addr.toNat value 8 = true) :
     store_doubleword addr value js =
       .ok (.Ok true)
         { js with sail := { js.sail with mem := write_ram_doubleword js.sail.mem addr.toNat value } }
```

### `JoltISA.Mmu.store_doubleword_eq_sail` (theorem)

File: `JoltBytecode/InstructionEquivalence/ProofSupport/Memory/Write.lean:265`.

```diff
@@ -1,9 +1,10 @@
 theorem JoltISA.Mmu.store_doubleword_eq_sail (js : SailJoltState) (addr value : BitVec 64)
     (hpriv : Assumptions.CurPrivilegeMachine js.sail)
     (hmprv : Assumptions.MstatusMprvZero js.sail)
     (hda : AlignedDwordAccess addr)
     (hpmp : Assumptions.StorePmpOk addr 8 js.sail)
     (hmmio : Assumptions.NotWritableMmio addr 8 js.sail)
-    (hlegal : JoltISA.Mmu.effective_address_ok js.jolt_device addr.toNat true = true) :
+    (hlegal : JoltISA.Mmu.effective_address_ok js.jolt_device addr.toNat true = true)
+    (hprotected : JoltISA.Mmu.protected_store_ok js addr.toNat value 8 = true) :
     JoltISA.Mmu.store_doubleword addr value js =
       liftSail (vmem_write_addr (Virtaddr addr) 8 value (Store Data) false false false) js
```

### `execInstr_sd_vreg_run_of_write` (theorem)

File: `JoltBytecode/InstructionEquivalence/ProofSupport/Memory/Write.lean:284`.

```diff
@@ -1,16 +1,16 @@
 theorem execInstr_sd_vreg_run_of_write (base value : VReg) (imm : BitVec 12)
     (js : SailJoltState) (s' : SailState)
     (h_align :
       (js.vregs base + sign_extend (m := 64) imm) &&& (7 : BitVec 64) = 0)
     (h :
       vmem_write_addr (Virtaddr (js.vregs base + sign_extend (m := 64) imm)) 8
         (js.vregs value) (Store Data) false false false js.sail =
         .ok (Ok true) s')
     (h_ram : RAM_START_ADDRESS ≤ (js.vregs base + sign_extend (m := 64) imm).toNat)
     (hpriv : Assumptions.CurPrivilegeMachine js.sail)
     (hmprv : Assumptions.MstatusMprvZero js.sail)
     (hpmp : Assumptions.StorePmpOk (js.vregs base + sign_extend (m := 64) imm) 8 js.sail)
     (hmmio : Assumptions.NotWritableMmio (js.vregs base + sign_extend (m := 64) imm) 8 js.sail)
-    (hjolt : Assumptions.JoltRamStoreOk (js.vregs base + sign_extend (m := 64) imm) js) :
+    (hjolt : Assumptions.JoltRamStoreOk (js.vregs base + sign_extend (m := 64) imm) js (js.vregs value) 8) :
     (execInstr (JoltISA.Encoded.SD (.vreg base) (.vreg value) imm)).run js =
       .ok RETIRE_SUCCESS { js with sail := s' }
```

### `execInstr_sd_xreg_xreg_run_of_write` (theorem)

File: `JoltBytecode/InstructionEquivalence/ProofSupport/Memory/Write.lean:307`.

```diff
@@ -1,19 +1,19 @@
 theorem execInstr_sd_xreg_xreg_run_of_write
     (base value : regidx) (imm : BitVec 12)
     (js : SailJoltState) (baseValue stored : BitVec 64) (s' : SailState)
     (hbase : rX_bits base js.sail = .ok baseValue js.sail)
     (hvalue : rX_bits value js.sail = .ok stored js.sail)
     (h_align :
       (baseValue + sign_extend (m := 64) imm) &&& (7 : BitVec 64) = 0)
     (hwrite :
       vmem_write_addr (Virtaddr (baseValue + sign_extend (m := 64) imm)) 8
         stored (Store Data) false false false js.sail =
         .ok (Ok true) s')
     (h_ram : RAM_START_ADDRESS ≤ (baseValue + sign_extend (m := 64) imm).toNat)
     (hpriv : Assumptions.CurPrivilegeMachine js.sail)
     (hmprv : Assumptions.MstatusMprvZero js.sail)
     (hpmp : Assumptions.StorePmpOk (baseValue + sign_extend (m := 64) imm) 8 js.sail)
     (hmmio : Assumptions.NotWritableMmio (baseValue + sign_extend (m := 64) imm) 8 js.sail)
-    (hjolt : Assumptions.JoltRamStoreOk (baseValue + sign_extend (m := 64) imm) js) :
+    (hjolt : Assumptions.JoltRamStoreOk (baseValue + sign_extend (m := 64) imm) js stored 8) :
     (execInstr (JoltISA.Encoded.SD (.xreg base) (.xreg value) imm)).run js =
       .ok RETIRE_SUCCESS { js with sail := s' }
```

### `Instr.WritesProtectedVReg` (def)

File: `JoltBytecode/InstructionEquivalence/ProofSupport/ProtectedVRegWrites.lean:29`.

```diff
@@ -1,92 +1,94 @@
 def Instr.WritesProtectedVReg : Instr → Prop
+  | .JoltSuccess dst
+  | .Panic dst
   | .ADDI dst _ _
   | .ADDIW dst _ _
   | .ANDI dst _ _
   | .ORI dst _ _
   | .XORI dst _ _
   | .SLTI dst _ _
   | .SLTIU dst _ _
   | .LUI dst _
   | .AUIPC dst _
   | .JAL dst _
   | .JALR dst _ _
   | .ADD dst _ _
   | .ADDW dst _ _
   | .SUB dst _ _
   | .SUBW dst _ _
   | .MUL dst _ _
   | .MULW dst _ _
   | .MULHU dst _ _
   | .ANDN dst _ _
   | .VirtualMULI dst _ _
   | .VirtualMULIW dst _ _
   | .VirtualPow2 dst _ _
   | .VirtualPow2W dst _ _
   | .VirtualPow2I dst _
   | .VirtualPow2IW dst _
   | .VirtualShiftRightBitmask dst _ _
   | .VirtualShiftRightBitmaskI dst _
   | .VirtualShiftRightBitmaskW dst _ _
   | .VirtualSRLI dst _ _
   | .VirtualSRAI dst _ _
   | .VirtualSRLIW dst _ _
   | .VirtualSRAIW dst _ _
   | .VirtualSRL dst _ _
   | .VirtualSRA dst _ _
   | .VirtualSRLW dst _ _
   | .VirtualSRAW dst _ _
   | .VirtualROTRI dst _ _
   | .VirtualROTRIW dst _ _
   | .VirtualRev8W dst _ _
   | .VirtualXORROT32 dst _ _
   | .VirtualXORROT24 dst _ _
   | .VirtualXORROT16 dst _ _
   | .VirtualXORROT63 dst _ _
   | .VirtualXORROTL1 dst _ _
   | .VirtualXORROTW16 dst _ _
   | .VirtualXORROTW12 dst _ _
   | .VirtualXORROTW8 dst _ _
   | .VirtualXORROTW7 dst _ _
   | .VirtualXORROTW22 dst _ _
   | .VirtualXORROTW19 dst _ _
   | .VirtualXORROTW6 dst _ _
   | .OR dst _ _
   | .XOR dst _ _
   | .AND dst _ _
   | .SLT dst _ _
   | .SLTU dst _ _
   | .VirtualWindowMaskB dst _ _
   | .VirtualWindowMaskH dst _ _
   | .VirtualWindowMaskW dst _ _
   | .VirtualPext dst _ _
   | .VirtualPextSigned dst _ _
   | .VirtualShiftDataB dst _ _ _
   | .VirtualShiftDataH dst _ _ _
   | .VirtualShiftDataW dst _ _ _
   | .VirtualSignExtendWord dst _ _
   | .VirtualZeroExtendWord dst _ _
   | .VirtualMovsign dst _ _
   | .VirtualAdvice dst _ _
   | .VirtualAdviceLoad dst _
   | .VirtualNegateIf dst _ _ => dst.WritesProtectedVReg
   | .LD _ dst _ _
   | .VirtualLoadB _ dst _ _ _
   | .VirtualLoadH _ dst _ _ _
   | .VirtualLoadW _ dst _ _ _ => dst.WritesProtectedVReg
   | .BEQ _ _ _
   | .BNE _ _ _
   | .BLT _ _ _
   | .BGE _ _ _
   | .BLTU _ _ _
   | .BGEU _ _ _
   | .FENCE
   | .SD _ _ _
   | .VirtualStoreB _ _ _ _
   | .VirtualStoreH _ _ _ _
   | .VirtualStoreW _ _ _ _
   | .VirtualHostIO
   | .VirtualAssertEQ _ _ _
   | .VirtualAssertValidDiv0 _ _ _
   | .VirtualAssertValidUnsignedRemainder _ _ _
   | .VirtualAssertMulUNoOverflow _ _ _
   | .VirtualAssertLTE _ _ _ => False
```

### `SailJoltState` (structure)

File: `JoltBytecode/JoltISA/Core.lean:60`.

```diff
@@ -1,7 +1,12 @@
 structure SailJoltState where
   sail : SailState
   vregs : BitVec 7 → BitVec 64 := fun _ => 0
   -- Rust: jolt/tracer/src/emulator/mmu.rs:25 (Mmu.jolt_device)
   jolt_device : JoltDevice
   adviceTape : JoltAdviceTape
   hostIO : JoltHostIOConfig := {}
+  /-- Code-word indices from the lowest mapped address, as `CodeGuard::region`.
+  For example, `(2, 4)` protects exactly domain words two and three. -/
+  codeRegion : Nat × Nat := (0, 0)
+  /-- A recorded halt; for example, `some .success` makes later ticks no-ops. -/
+  halted : Option JoltHaltKind := none
```

### `effective_address_ok` (def)

File: `JoltBytecode/JoltISA/DeviceMemory.lean:41`.

```diff
@@ -1 +1 @@
-def effective_address_ok (device : JoltDevice) (ea : Nat) (is_write : Bool) : Bool
+def effective_address_ok (device : JoltDevice) (ea : Nat) (_is_write : Bool) : Bool
```

### `Instr` (inductive)

File: `JoltBytecode/JoltISA/Instruction.lean:66`.

```diff
@@ -1,113 +1,117 @@
 inductive Instr where
   | ADDI (dst : Dst) (src : Src) (imm : BitVec 64)
   | ADDIW (dst : Dst) (src : Src) (imm : BitVec 64)
   | ANDI (dst : Dst) (src : Src) (imm : BitVec 64)
   | ORI  (dst : Dst) (src : Src) (imm : BitVec 64)
   | XORI (dst : Dst) (src : Src) (imm : BitVec 64)
   | SLTI (dst : Dst) (src : Src) (imm : BitVec 64)
   | SLTIU (dst : Dst) (src : Src) (imm : BitVec 64)
   | LUI  (dst : Dst) (imm : BitVec 64)
   | AUIPC (dst : Dst) (imm : BitVec 64)
   | JAL (dst : Dst) (imm : BitVec 64)
   | JALR (dst : Dst) (base : Src) (imm : BitVec 64)
   | BEQ (lhs rhs : Src) (imm : BitVec 128)
   | BNE (lhs rhs : Src) (imm : BitVec 128)
   | BLT (lhs rhs : Src) (imm : BitVec 128)
   | BGE (lhs rhs : Src) (imm : BitVec 128)
   | BLTU (lhs rhs : Src) (imm : BitVec 128)
   | BGEU (lhs rhs : Src) (imm : BitVec 128)
   | FENCE
+  /-- Success halt row; for example, decoded jolt.success uses x0 as link destination. -/
+  | JoltSuccess (dst : Dst)
+  /-- Failure halt row; for example, EBREAK lowers to this row with scratch v40. -/
+  | Panic (dst : Dst)
   | ADD  (dst : Dst) (lhs rhs : Src)
   | ADDW (dst : Dst) (lhs rhs : Src)
   | SUB  (dst : Dst) (lhs rhs : Src)
   | SUBW (dst : Dst) (lhs rhs : Src)
   | MUL  (dst : Dst) (lhs rhs : Src)
   | MULW (dst : Dst) (lhs rhs : Src)
   | MULHU (dst : Dst) (lhs rhs : Src)
   | ANDN (dst : Dst) (lhs rhs : Src)
   | VirtualMULI (dst : Dst) (src : Src) (imm : BitVec 64)
   | VirtualMULIW (dst : Dst) (src : Src) (imm : BitVec 64)
   | VirtualPow2 (dst : Dst) (src : Src) (imm : BitVec 64)
   | VirtualPow2W (dst : Dst) (src : Src) (imm : BitVec 64 := 0)
   | VirtualPow2I (dst : Dst) (imm : Nat)
   | VirtualPow2IW (dst : Dst) (imm : Nat)
   | VirtualShiftRightBitmask (dst : Dst) (src : Src) (imm : BitVec 64 := 0)
   | VirtualShiftRightBitmaskI (dst : Dst) (imm : Nat)
   | VirtualShiftRightBitmaskW (dst : Dst) (src : Src) (imm : BitVec 64 := 0)
   | VirtualSRLI (dst : Dst) (src : Src) (bitmask : Nat)
   | VirtualSRAI (dst : Dst) (src : Src) (bitmask : Nat)
   | VirtualSRLIW (dst : Dst) (src : Src) (bitmask : Nat)
   | VirtualSRAIW (dst : Dst) (src : Src) (bitmask : Nat)
   | VirtualSRL (dst : Dst) (value bitmask : Src)
   | VirtualSRA (dst : Dst) (value bitmask : Src)
   | VirtualSRLW (dst : Dst) (value bitmask : Src)
   | VirtualSRAW (dst : Dst) (value bitmask : Src)
   | VirtualROTRI (dst : Dst) (src : Src) (bitmask : Nat)
   | VirtualROTRIW (dst : Dst) (src : Src) (bitmask : Nat)
   | VirtualRev8W (dst : Dst) (src : Src) (imm : BitVec 64 := 0)
   | VirtualXORROT32 (dst : Dst) (lhs rhs : Src)
   | VirtualXORROT24 (dst : Dst) (lhs rhs : Src)
   | VirtualXORROT16 (dst : Dst) (lhs rhs : Src)
   | VirtualXORROT63 (dst : Dst) (lhs rhs : Src)
   | VirtualXORROTL1 (dst : Dst) (lhs rhs : Src)
   | VirtualXORROTW16 (dst : Dst) (lhs rhs : Src)
   | VirtualXORROTW12 (dst : Dst) (lhs rhs : Src)
   | VirtualXORROTW8 (dst : Dst) (lhs rhs : Src)
   | VirtualXORROTW7 (dst : Dst) (lhs rhs : Src)
   | VirtualXORROTW22 (dst : Dst) (lhs rhs : Src)
   | VirtualXORROTW19 (dst : Dst) (lhs rhs : Src)
   | VirtualXORROTW6 (dst : Dst) (lhs rhs : Src)
   | OR   (dst : Dst) (lhs rhs : Src)
   | XOR  (dst : Dst) (lhs rhs : Src)
   | AND  (dst : Dst) (lhs rhs : Src)
   | SLT  (dst : Dst) (lhs rhs : Src)
   | SLTU (dst : Dst) (lhs rhs : Src)
   | VirtualWindowMaskB (dst : Dst) (base : Src) (imm : BitVec 64)
   | VirtualWindowMaskH (dst : Dst) (base : Src) (imm : BitVec 64)
   | VirtualWindowMaskW (dst : Dst) (base : Src) (imm : BitVec 64)
   | VirtualPext (dst : Dst) (value mask : Src)
   | VirtualPextSigned (dst : Dst) (value mask : Src)
   /-- Byte store-data shifter. `value` is the stored register, `address` the
   base register, and `imm` the store offset. The lane is chosen from
   `ea = address + imm`, so `(value & 0xFF) << (8 * (ea mod 8))` is the byte in
   its lane. Rust: `crates/jolt-riscv/src/instructions/virt/shift_data_b.rs`. -/
   | VirtualShiftDataB (dst : Dst) (value address : Src) (imm : BitVec 64)
   | VirtualShiftDataH (dst : Dst) (value address : Src) (imm : BitVec 64)
   | VirtualShiftDataW (dst : Dst) (value address : Src) (imm : BitVec 64)
   | VirtualSignExtendWord (dst : Dst) (src : Src) (imm : BitVec 64 := 0)
   | VirtualZeroExtendWord (dst : Dst) (src : Src) (imm : BitVec 64 := 0)
   | VirtualMovsign (dst : Dst) (src : Src) (imm : BitVec 64 := 0)
   /-- Floor-addressed doubleword load for byte accesses. `dst` receives the
   doubleword containing `ea = base + imm`, that is the word at `ea & ~7`.
   Example: with `base = 0x80000003` and `imm = 0`, the row loads the word at
   `0x80000000`. Rust: `crates/jolt-riscv/src/instructions/virt/load_b.rs` and
   `tracer/src/instruction/floor_access.rs` (`load`). The halfword and word rows
   (`VirtualLoadH`, `VirtualLoadW`) raise `fault` when `ea` is not a multiple of 2
   or 4 in the Lean model; Jolt's tracer panics there instead, so an honest trace
   has no such row. -/
   | VirtualLoadB (faultClass : LoadFaultClass) (dst : Dst) (base : Src) (imm : BitVec 64) (fault : ExceptionType)
   | VirtualLoadH (faultClass : LoadFaultClass) (dst : Dst) (base : Src) (imm : BitVec 64) (fault : ExceptionType)
   | VirtualLoadW (faultClass : LoadFaultClass) (dst : Dst) (base : Src) (imm : BitVec 64) (fault : ExceptionType)
   /-- Floor-addressed doubleword store, the write side of `VirtualLoadB`. `value`
   is written to the doubleword containing `ea = base + imm`. Rust:
   `crates/jolt-riscv/src/instructions/virt/store_b.rs` and
   `tracer/src/instruction/floor_access.rs` (`store`). -/
   | VirtualStoreB (base value : Src) (imm : BitVec 64) (fault : ExceptionType)
   | VirtualStoreH (base value : Src) (imm : BitVec 64) (fault : ExceptionType)
   | VirtualStoreW (base value : Src) (imm : BitVec 64) (fault : ExceptionType)
   | LD (faultClass : LoadFaultClass) (dst : Dst) (base : Src) (imm : BitVec 64)
   | SD (base value : Src) (imm : BitVec 64)
   | VirtualAdvice (dst : Dst) (value : BitVec 64) (imm : BitVec 64 := 0)
   | VirtualAdviceLoad (dst : Dst) (byteCount : BitVec 64)
   /-- A host call with no normalized register operands or immediate.
   For example, an advice-write call reads x10–x12 implicitly and writes no register.
   See jolt/tracer/src/instruction/virtual_host_io.rs:9-38 and
   jolt/tracer/src/instruction/format/format_no_operands.rs:6-29 at 5def437f. -/
   | VirtualHostIO
   | VirtualAssertEQ (lhs rhs : Src) (imm: BitVec 128)
   | VirtualAssertValidDiv0 (divisor quotient : Src) (imm : BitVec 128 := 0)
   | VirtualNegateIf (dst : Dst) (signSource value : Src)
   | VirtualAssertValidUnsignedRemainder (remainder divisor : Src) (imm : BitVec 128 := 0)
   | VirtualAssertMulUNoOverflow (lhs rhs : Src) (imm : BitVec 128 := 0)
   | VirtualAssertLTE (lhs rhs : Src) (imm : BitVec 128 := 0)
   deriving Repr
```

### `Instr.destination?` (def)

File: `JoltBytecode/JoltISA/Instruction.lean:459`.

```diff
@@ -1,32 +1,32 @@
 def Instr.destination? : Instr → Option Dst
-  | .ADDI dst _ _ | .ADDIW dst _ _ | .ANDI dst _ _ | .ORI dst _ _ | .XORI dst _ _
+  | .JoltSuccess dst | .Panic dst | .ADDI dst _ _ | .ADDIW dst _ _ | .ANDI dst _ _ | .ORI dst _ _ | .XORI dst _ _
   | .SLTI dst _ _ | .SLTIU dst _ _ | .LUI dst _ | .AUIPC dst _ | .JAL dst _ | .JALR dst _ _
   | .ADD dst _ _ | .ADDW dst _ _ | .SUB dst _ _ | .SUBW dst _ _ | .MUL dst _ _
   | .MULW dst _ _ | .MULHU dst _ _ | .ANDN dst _ _ | .VirtualMULI dst _ _
   | .VirtualMULIW dst _ _ | .VirtualPow2 dst _ _ | .VirtualPow2W dst _ _
   | .VirtualPow2I dst _ | .VirtualPow2IW dst _
   | .VirtualShiftRightBitmask dst _ _ | .VirtualShiftRightBitmaskI dst _
   | .VirtualShiftRightBitmaskW dst _ _ | .VirtualSRLI dst _ _ | .VirtualSRAI dst _ _
   | .VirtualSRLIW dst _ _ | .VirtualSRAIW dst _ _ | .VirtualSRL dst _ _
   | .VirtualSRA dst _ _ | .VirtualSRLW dst _ _ | .VirtualSRAW dst _ _
   | .VirtualROTRI dst _ _ | .VirtualROTRIW dst _ _ | .VirtualRev8W dst _ _
   | .VirtualXORROT32 dst _ _ | .VirtualXORROT24 dst _ _ | .VirtualXORROT16 dst _ _
   | .VirtualXORROT63 dst _ _ | .VirtualXORROTL1 dst _ _
   | .VirtualXORROTW16 dst _ _ | .VirtualXORROTW12 dst _ _ | .VirtualXORROTW8 dst _ _
   | .VirtualXORROTW7 dst _ _ | .VirtualXORROTW22 dst _ _ | .VirtualXORROTW19 dst _ _
   | .VirtualXORROTW6 dst _ _ | .OR dst _ _ | .XOR dst _ _ | .AND dst _ _
   | .SLT dst _ _ | .SLTU dst _ _
   | .VirtualWindowMaskB dst _ _ | .VirtualWindowMaskH dst _ _
   | .VirtualWindowMaskW dst _ _ | .VirtualPext dst _ _ | .VirtualPextSigned dst _ _
   | .VirtualShiftDataB dst _ _ _ | .VirtualShiftDataH dst _ _ _ | .VirtualShiftDataW dst _ _ _
   | .VirtualSignExtendWord dst _ _ | .VirtualZeroExtendWord dst _ _
   | .VirtualMovsign dst _ _ | .VirtualAdvice dst _ _ | .VirtualAdviceLoad dst _
   | .VirtualNegateIf dst _ _ =>
       some dst
   | .LD _ dst _ _ | .VirtualLoadB _ dst _ _ _ | .VirtualLoadH _ dst _ _ _
   | .VirtualLoadW _ dst _ _ _ => some dst
   | .BEQ _ _ _ | .BNE _ _ _ | .BLT _ _ _ | .BGE _ _ _ | .BLTU _ _ _
   | .BGEU _ _ _ | .FENCE | .VirtualHostIO | .SD _ _ _ | .VirtualAssertEQ _ _ _
   | .VirtualStoreB _ _ _ _ | .VirtualStoreH _ _ _ _ | .VirtualStoreW _ _ _ _
   | .VirtualAssertValidDiv0 _ _ _ | .VirtualAssertValidUnsignedRemainder _ _ _
   | .VirtualAssertMulUNoOverflow _ _ _ | .VirtualAssertLTE _ _ _ => none
```

### `MemoryLayout` (structure)

File: `JoltBytecode/JoltISA/JoltDevice.lean:32`.

```diff
@@ -1,22 +1,20 @@
 structure MemoryLayout where
   program_size : BitVec 64
   max_trusted_advice_size : BitVec 64
   trusted_advice_start : BitVec 64
   trusted_advice_end : BitVec 64
   max_untrusted_advice_size : BitVec 64
   untrusted_advice_start : BitVec 64
   untrusted_advice_end : BitVec 64
   max_input_size : BitVec 64
   max_output_size : BitVec 64
   input_start : BitVec 64
   input_end : BitVec 64
   output_start : BitVec 64
   output_end : BitVec 64
   stack_size : BitVec 64
   stack_end : BitVec 64
   heap_size : BitVec 64
   heap_end : BitVec 64
-  panic : BitVec 64
-  termination : BitVec 64
   io_end : BitVec 64
   deriving DecidableEq
```

### `JoltDevice` (structure)

File: `JoltBytecode/JoltISA/JoltDevice.lean:206`.

```diff
@@ -1,7 +1,3 @@
 structure JoltDevice where
-  inputs : Array (BitVec 8)
-  trusted_advice : Array (BitVec 8)
-  untrusted_advice : Array (BitVec 8)
-  outputs : Array (BitVec 8)
   panic : Bool
   memory_layout : MemoryLayout
```

### `load?` (def)

File: `JoltBytecode/JoltISA/JoltDevice.lean:242`.

```diff
@@ -1 +1,2 @@
-def load? (device : JoltDevice) (address : Nat) : Option (BitVec 8)
+def load? (device : JoltDevice) (mem : Std.ExtHashMap Nat (BitVec 8))
+    (address : Nat) : Option (BitVec 8)
```

### `store?` (def)

File: `JoltBytecode/JoltISA/JoltDevice.lean:248`.

```diff
@@ -1,2 +1,2 @@
-def store? (device : JoltDevice) (address : Nat) (value : BitVec 8) :
-    Option JoltDevice
+def store? (device : JoltDevice) (mem : Std.ExtHashMap Nat (BitVec 8))
+    (address : Nat) (value : BitVec 8) : Option (Std.ExtHashMap Nat (BitVec 8))
```

### `execInstr` (def)

File: `JoltBytecode/JoltISA/Semantics.lean:70`.

```diff
@@ -1,24 +1,26 @@
 def execInstr : Instr → JoltMonad ExecutionResult
+  | .JoltSuccess dst => execHalt .success dst
+  | .Panic dst => execHalt .panic dst
   | .ADDI dst src imm => do
       let x ← readSrc src
       writeDst dst (BitVec.ofNat 64 (addWide x imm))
       pure RETIRE_SUCCESS
   | .ADDIW dst src imm => do
       let x ← readSrc src
       writeDst dst (jolt_addiw_value64 x imm)
       pure RETIRE_SUCCESS
   | .ANDI dst src imm => do
       let x ← readSrc src
       writeDst dst (Riscv.andi x imm)
       pure RETIRE_SUCCESS
   | .ORI dst src imm => do
       let x ← readSrc src
       writeDst dst (Riscv.ori x imm)
       pure RETIRE_SUCCESS
   | .XORI dst src imm => do
       let x ← readSrc src
       writeDst dst (jolt_xor_value x imm)
       pure RETIRE_SUCCESS
   | .SLTI dst src imm => do
       let x ← readSrc src
       let y
```

## Bundled and aliased premise users

All declarations below use the changed acceptance or load-bound bundles directly or through a statement alias.
For every listed declaration, the old and new premise meanings are specified above and in the direct bundle diffs.
Their remaining hypotheses and conclusions are unchanged unless a direct diff above says otherwise.
`RiscvInstruction.equivAssumptions` now selects widths 1, 2 and 4 for SB, SH and SW; SD keeps its default width 8.
Consequently, generic dispatch and step theorems that take `equivAssumptions` use the corresponding value-dependent store or padded-load premise for their memory cases.

- `JoltRamLoadOk`: `JoltBytecode/Assumptions.lean:202`.
- `JoltRamStoreOk`: `JoltBytecode/Assumptions.lean:210`.
- `LoadProgramEqSailAssumptions`: `JoltBytecode/Bundles.lean:212`.
- `LoadProgramEqSailAssumptions.linkedCSRs`: `JoltBytecode/Bundles.lean:221`.
- `StoreProgramEqSailAssumptions`: `JoltBytecode/Bundles.lean:234`.
- `StoreProgramEqSailAssumptions.linkedCSRs`: `JoltBytecode/Bundles.lean:246`.
- `AmoDwordProgramEqSailAssumptions`: `JoltBytecode/Bundles.lean:279`.
- `AmoDwordProgramEqSailAssumptions.rdReadable`: `JoltBytecode/Bundles.lean:289`.
- `AmoDwordProgramEqSailAssumptions.linkedCSRs`: `JoltBytecode/Bundles.lean:296`.
- `AmoWordProgramEqSailAssumptions`: `JoltBytecode/Bundles.lean:303`.
- `AmoWordProgramEqSailAssumptions.rdReadable`: `JoltBytecode/Bundles.lean:314`.
- `AmoWordProgramEqSailAssumptions.linkedCSRs`: `JoltBytecode/Bundles.lean:321`.
- `amoadddProgram_core_eq_sail`: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/Amoaddd.lean:63`.
- `amoadddProgramEqSailStatement`: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/Amoaddd.lean:113`.
- `amoadddProgram_eq_sail`: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/Amoaddd.lean:121`.
- `amoaddwProgram_core_eq_sail`: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/Amoaddw.lean:65`.
- `amoaddwProgramEqSailStatement`: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/Amoaddw.lean:81`.
- `amoaddwProgram_eq_sail`: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/Amoaddw.lean:89`.
- `amoanddProgram_core_eq_sail`: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/Amoandd.lean:65`.
- `amoanddProgramEqSailStatement`: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/Amoandd.lean:112`.
- `amoanddProgram_eq_sail`: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/Amoandd.lean:120`.
- `amoandwProgram_core_eq_sail`: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/Amoandw.lean:65`.
- `amoandwProgramEqSailStatement`: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/Amoandw.lean:81`.
- `amoandwProgram_eq_sail`: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/Amoandw.lean:89`.
- `amomaxdProgram_core_eq_sail`: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/Amomaxd.lean:60`.
- `amomaxdProgramEqSailStatement`: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/Amomaxd.lean:116`.
- `amomaxdProgram_eq_sail`: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/Amomaxd.lean:124`.
- `amomaxudProgram_core_eq_sail`: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/Amomaxud.lean:60`.
- `amomaxudProgramEqSailStatement`: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/Amomaxud.lean:116`.
- `amomaxudProgram_eq_sail`: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/Amomaxud.lean:124`.
- `amomaxuwProgram_core_eq_sail`: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/Amomaxuw.lean:78`.
- `amomaxuwProgramEqSailStatement`: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/Amomaxuw.lean:101`.
- `amomaxuwProgram_eq_sail`: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/Amomaxuw.lean:109`.
- `amomaxwProgram_core_eq_sail`: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/Amomaxw.lean:78`.
- `amomaxwProgramEqSailStatement`: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/Amomaxw.lean:101`.
- `amomaxwProgram_eq_sail`: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/Amomaxw.lean:109`.
- `amomindProgram_core_eq_sail`: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/Amomind.lean:60`.
- `amomindProgramEqSailStatement`: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/Amomind.lean:116`.
- `amomindProgram_eq_sail`: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/Amomind.lean:124`.
- `amominudProgram_core_eq_sail`: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/Amominud.lean:60`.
- `amominudProgramEqSailStatement`: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/Amominud.lean:116`.
- `amominudProgram_eq_sail`: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/Amominud.lean:124`.
- `amominuwProgram_core_eq_sail`: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/Amominuw.lean:78`.
- `amominuwProgramEqSailStatement`: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/Amominuw.lean:100`.
- `amominuwProgram_eq_sail`: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/Amominuw.lean:108`.
- `amominwProgram_core_eq_sail`: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/Amominw.lean:78`.
- `amominwProgramEqSailStatement`: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/Amominw.lean:101`.
- `amominwProgram_eq_sail`: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/Amominw.lean:109`.
- `amoordProgram_core_eq_sail`: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/Amoord.lean:65`.
- `amoordProgramEqSailStatement`: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/Amoord.lean:112`.
- `amoordProgram_eq_sail`: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/Amoord.lean:120`.
- `amoorwProgram_core_eq_sail`: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/Amoorw.lean:65`.
- `amoorwProgramEqSailStatement`: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/Amoorw.lean:81`.
- `amoorwProgram_eq_sail`: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/Amoorw.lean:89`.
- `amoswapdProgramAuto_eq_sail`: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/Amoswapd.lean:34`.
- `amoswapdProgramEqSailStatement`: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/Amoswapd.lean:155`.
- `amoswapdProgram_eq_sail`: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/Amoswapd.lean:163`.
- `amo_word_swap_pre64_aligned_run_for`: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/Amoswapw.lean:32`.
- `amo_word_swap_sd_spliced_dword_run`: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/Amoswapw.lean:764`.
- `amo_word_swap_sd_spliced_dword_run_for`: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/Amoswapw.lean:827`.
- `amo_word_swap_post64_amoswap_aligned_run`: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/Amoswapw.lean:937`.
- `amo_word_swap_post64_amoswap_aligned_run_for`: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/Amoswapw.lean:1062`.
- `amoswapwProgram_concrete_aligned`: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/Amoswapw.lean:1204`.
- `amoswapwProgramAuto_eq_sail`: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/Amoswapw.lean:1259`.
- `amoswapwProgramEqSailStatement`: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/Amoswapw.lean:1287`.
- `amoswapwProgram_eq_sail`: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/Amoswapw.lean:1295`.
- `amoxordProgram_core_eq_sail`: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/Amoxord.lean:65`.
- `amoxordProgramEqSailStatement`: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/Amoxord.lean:112`.
- `amoxordProgram_eq_sail`: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/Amoxord.lean:120`.
- `amoxorwProgram_core_eq_sail`: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/Amoxorw.lean:65`.
- `amoxorwProgramEqSailStatement`: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/Amoxorw.lean:81`.
- `amoxorwProgram_eq_sail`: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/Amoxorw.lean:89`.
- `amo_dword_ld_old_run_into`: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/Dword.lean:149`.
- `amo_dword_ld_old_run`: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/Dword.lean:206`.
- `amo_dword_sd_result_run`: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/Dword.lean:232`.
- `amo_dword_sd_xreg_vreg_run_of_write`: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/Dword.lean:290`.
- `amo_dword_sd_vreg_result_run`: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/Dword.lean:323`.
- `amo_dword_load_old_aligned_run_into`: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/Dword.lean:447`.
- `amo_dword_load_old_aligned_run`: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/Dword.lean:484`.
- `amo_dword_store_xreg_result_after_load_aligned_run`: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/Dword.lean:510`.
- `amo_dword_store_vreg_result_after_middle_aligned_run_from`: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/Dword.lean:2577`.
- `amo_dword_store_vreg_result_after_middle_aligned_run`: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/Dword.lean:2627`.
- `amo_dword_double_binop_program_concrete_aligned`: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/Dword.lean:2698`.
- `amo_dword_bundle_store_ok`: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/Dword.lean:3076`.
- `amo_dword_double_binop_program_eq_sail_aligned`: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/Dword.lean:3246`.
- `amo_dword_double_binop_program_project_eq_sail`: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/Dword.lean:3376`.
- `amo_dword_double_select_program_concrete_aligned`: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/Dword.lean:3440`.
- `amo_dword_double_select_program_eq_sail_aligned`: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/Dword.lean:3592`.
- `amo_dword_double_select_program_project_eq_sail`: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/Dword.lean:3692`.
- `amo_word_pre64_aligned_run_with`: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/Word.lean:1051`.
- `amo_word_pre64_aligned_run_for`: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/Word.lean:1095`.
- `amo_word_sd_spliced_dword_run`: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/Word.lean:2689`.
- `amo_word_sd_spliced_dword_run_for`: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/Word.lean:2753`.
- `amo_word_post64_vreg_aligned_run`: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/Word.lean:2912`.
- `amo_word_post64_vreg_aligned_run_for`: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/Word.lean:3033`.
- `amo_word_merge_program_aligned_run`: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/Word.lean:3217`.
- `amo_word_binop_program_concrete_aligned`: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/Word.lean:3261`.
- `amo_word_floor_store_run`: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/WordLane.lean:144`.
- `amo_word_lane_merge_run`: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/WordLane.lean:184`.
- `amoWordBundleOld`: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/WordProgram.lean:13`.
- `amo_word_bundle_store_spliced_ok`: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/WordProgram.lean:23`.
- `amo_word_bundle_store_lane_ok`: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/WordProgram.lean:65`.
- `amo_word_program_eq_sail`: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/WordProgram.lean:80`.
- `amo_word_window_program_aligned_run`: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/WordProgram.lean:204`.
- `amo_word_binop_eq_sail`: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/WordProgram.lean:271`.
- `amo_word_select_eq_sail`: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/WordSelectLane.lean:156`.
- `amo_word_rust_select_sd_spliced_dword_run`: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/WordSelectRust.lean:370`.
- `amo_word_rust_select_post64_vreg_aligned_run`: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/WordSelectRust.lean:456`.
- `amo_word_rust_select_sd_spliced_dword_run_for`: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/WordSelectRust.lean:1024`.
- `amo_word_rust_select_post64_vreg_aligned_run_for`: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/WordSelectRust.lean:1114`.
- `amo_word_rust_select_program_concrete_aligned`: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/WordSelectRust.lean:3276`.
- `floorLoad_of_assumptions`: `JoltBytecode/InstructionEquivalence/Instructions/LoadFamily/FloorLoad.lean:63`.
- `lbuProgramEqSailStatement`: `JoltBytecode/InstructionEquivalence/Instructions/LoadFamily/LBU_main.lean:22`.
- `lbu_virtual_pext_rd_run`: `JoltBytecode/InstructionEquivalence/Instructions/LoadFamily/LBU_main.lean:49`.
- `lbu_virtual_pext_v40_run`: `JoltBytecode/InstructionEquivalence/Instructions/LoadFamily/LBU_main.lean:76`.
- `lbuProgramAuto_nonzero_run`: `JoltBytecode/InstructionEquivalence/Instructions/LoadFamily/LBU_main.lean:146`.
- `lbuProgram_eq_sail_nonzero`: `JoltBytecode/InstructionEquivalence/Instructions/LoadFamily/LBU_main.lean:175`.
- `lbuProgramAuto_x0_run`: `JoltBytecode/InstructionEquivalence/Instructions/LoadFamily/LBU_main.lean:239`.
- `lbuProgram_eq_sail_x0`: `JoltBytecode/InstructionEquivalence/Instructions/LoadFamily/LBU_main.lean:267`.
- `lbuProgram_eq_sail`: `JoltBytecode/InstructionEquivalence/Instructions/LoadFamily/LBU_main.lean:335`.
- `byte_subaccess_no_overflow`: `JoltBytecode/InstructionEquivalence/Instructions/LoadFamily/LB_SailSide.lean:40`.
- `byte_mem_present`: `JoltBytecode/InstructionEquivalence/Instructions/LoadFamily/LB_SailSide.lean:51`.
- `byte_load_pmp_ok`: `JoltBytecode/InstructionEquivalence/Instructions/LoadFamily/LB_SailSide.lean:68`.
- `byte_not_readable_mmio`: `JoltBytecode/InstructionEquivalence/Instructions/LoadFamily/LB_SailSide.lean:81`.
- `byte_present`: `JoltBytecode/InstructionEquivalence/Instructions/LoadFamily/LB_SailSide.lean:94`.
- `writeValue`: `JoltBytecode/InstructionEquivalence/Instructions/LoadFamily/LB_SailSide.lean:102`.
- `writeValueUnsigned`: `JoltBytecode/InstructionEquivalence/Instructions/LoadFamily/LB_SailSide.lean:111`.
- `stateAfterWrite_writeValue_eq_dword_byte`: `JoltBytecode/InstructionEquivalence/Instructions/LoadFamily/LB_SailSide.lean:123`.
- `stateAfterWrite_writeValueUnsigned_eq_dword_byte`: `JoltBytecode/InstructionEquivalence/Instructions/LoadFamily/LB_SailSide.lean:151`.
- `execute_LB_reduces`: `JoltBytecode/InstructionEquivalence/Instructions/LoadFamily/LB_SailSide.lean:179`.
- `execute_LBU_reduces`: `JoltBytecode/InstructionEquivalence/Instructions/LoadFamily/LB_SailSide.lean:224`.
- `lbProgramEqSailStatement`: `JoltBytecode/InstructionEquivalence/Instructions/LoadFamily/LB_main.lean:34`.
- `lb_ld_run`: `JoltBytecode/InstructionEquivalence/Instructions/LoadFamily/LB_main.lean:73`.
- `lb_virtual_window_mask_b_run`: `JoltBytecode/InstructionEquivalence/Instructions/LoadFamily/LB_main.lean:104`.
- `lb_virtual_pext_signed_rd_run`: `JoltBytecode/InstructionEquivalence/Instructions/LoadFamily/LB_main.lean:125`.
- `lb_virtual_pext_signed_v40_run`: `JoltBytecode/InstructionEquivalence/Instructions/LoadFamily/LB_main.lean:151`.
- `lbProgramAuto_nonzero_run`: `JoltBytecode/InstructionEquivalence/Instructions/LoadFamily/LB_main.lean:220`.
- `lbProgram_eq_sail_nonzero`: `JoltBytecode/InstructionEquivalence/Instructions/LoadFamily/LB_main.lean:249`.
- `lbProgramAuto_x0_run`: `JoltBytecode/InstructionEquivalence/Instructions/LoadFamily/LB_main.lean:316`.
- `lbProgram_eq_sail_x0`: `JoltBytecode/InstructionEquivalence/Instructions/LoadFamily/LB_main.lean:344`.
- `lbProgram_eq_sail`: `JoltBytecode/InstructionEquivalence/Instructions/LoadFamily/LB_main.lean:415`.
- `lhuProgramEqSailStatement`: `JoltBytecode/InstructionEquivalence/Instructions/LoadFamily/LHU_main.lean:22`.
- `lhu_virtual_pext_rd_run`: `JoltBytecode/InstructionEquivalence/Instructions/LoadFamily/LHU_main.lean:52`.
- `lhu_virtual_pext_v40_run`: `JoltBytecode/InstructionEquivalence/Instructions/LoadFamily/LHU_main.lean:79`.
- `lhuProgramAuto_nonzero_run`: `JoltBytecode/InstructionEquivalence/Instructions/LoadFamily/LHU_main.lean:150`.
- `lhuProgram_eq_sail_nonzero_aligned`: `JoltBytecode/InstructionEquivalence/Instructions/LoadFamily/LHU_main.lean:181`.
- `lhuProgramAuto_misaligned_run`: `JoltBytecode/InstructionEquivalence/Instructions/LoadFamily/LHU_main.lean:251`.
- `lhuProgram_eq_sail_misaligned`: `JoltBytecode/InstructionEquivalence/Instructions/LoadFamily/LHU_main.lean:266`.
- `lhuProgram_eq_sail_nonzero`: `JoltBytecode/InstructionEquivalence/Instructions/LoadFamily/LHU_main.lean:296`.
- `lhuProgramAuto_x0_run`: `JoltBytecode/InstructionEquivalence/Instructions/LoadFamily/LHU_main.lean:321`.
- `lhuProgram_eq_sail_x0_aligned`: `JoltBytecode/InstructionEquivalence/Instructions/LoadFamily/LHU_main.lean:351`.
- `lhuProgram_eq_sail_x0`: `JoltBytecode/InstructionEquivalence/Instructions/LoadFamily/LHU_main.lean:424`.
- `lhuProgram_eq_sail`: `JoltBytecode/InstructionEquivalence/Instructions/LoadFamily/LHU_main.lean:449`.
- `halfword_subaccess_no_overflow`: `JoltBytecode/InstructionEquivalence/Instructions/LoadFamily/LH_SailSide.lean:45`.
- `halfword_mem_present`: `JoltBytecode/InstructionEquivalence/Instructions/LoadFamily/LH_SailSide.lean:58`.
- `halfword_load_pmp_ok`: `JoltBytecode/InstructionEquivalence/Instructions/LoadFamily/LH_SailSide.lean:78`.
- `halfword_not_readable_mmio`: `JoltBytecode/InstructionEquivalence/Instructions/LoadFamily/LH_SailSide.lean:94`.
- `halfword_no_overflow`: `JoltBytecode/InstructionEquivalence/Instructions/LoadFamily/LH_SailSide.lean:109`.
- `aligned_access`: `JoltBytecode/InstructionEquivalence/Instructions/LoadFamily/LH_SailSide.lean:119`.
- `writeValue`: `JoltBytecode/InstructionEquivalence/Instructions/LoadFamily/LH_SailSide.lean:134`.
- `writeValueUnsigned`: `JoltBytecode/InstructionEquivalence/Instructions/LoadFamily/LH_SailSide.lean:147`.
- `stateAfterWrite_writeValue_eq_dword_halfword`: `JoltBytecode/InstructionEquivalence/Instructions/LoadFamily/LH_SailSide.lean:161`.
- `stateAfterWrite_writeValueUnsigned_eq_dword_halfword`: `JoltBytecode/InstructionEquivalence/Instructions/LoadFamily/LH_SailSide.lean:194`.
- `execute_LH_reduces`: `JoltBytecode/InstructionEquivalence/Instructions/LoadFamily/LH_SailSide.lean:227`.
- `execute_LHU_reduces`: `JoltBytecode/InstructionEquivalence/Instructions/LoadFamily/LH_SailSide.lean:274`.
- `execute_LH_misaligned`: `JoltBytecode/InstructionEquivalence/Instructions/LoadFamily/LH_SailSide.lean:321`.
- `execute_LHU_misaligned`: `JoltBytecode/InstructionEquivalence/Instructions/LoadFamily/LH_SailSide.lean:350`.
- `lhProgramEqSailStatement`: `JoltBytecode/InstructionEquivalence/Instructions/LoadFamily/LH_main.lean:23`.
- `lh_virtual_window_mask_h_run`: `JoltBytecode/InstructionEquivalence/Instructions/LoadFamily/LH_main.lean:53`.
- `lh_virtual_pext_signed_rd_run`: `JoltBytecode/InstructionEquivalence/Instructions/LoadFamily/LH_main.lean:74`.
- `lh_virtual_pext_signed_v40_run`: `JoltBytecode/InstructionEquivalence/Instructions/LoadFamily/LH_main.lean:101`.
- `lhProgramAuto_nonzero_run`: `JoltBytecode/InstructionEquivalence/Instructions/LoadFamily/LH_main.lean:172`.
- `lhProgram_eq_sail_nonzero_aligned`: `JoltBytecode/InstructionEquivalence/Instructions/LoadFamily/LH_main.lean:203`.
- `lhProgramAuto_misaligned_run`: `JoltBytecode/InstructionEquivalence/Instructions/LoadFamily/LH_main.lean:273`.
- `lhProgram_eq_sail_misaligned`: `JoltBytecode/InstructionEquivalence/Instructions/LoadFamily/LH_main.lean:288`.
- `lhProgram_eq_sail_nonzero`: `JoltBytecode/InstructionEquivalence/Instructions/LoadFamily/LH_main.lean:318`.
- `lhProgramAuto_x0_run`: `JoltBytecode/InstructionEquivalence/Instructions/LoadFamily/LH_main.lean:343`.
- `lhProgram_eq_sail_x0_aligned`: `JoltBytecode/InstructionEquivalence/Instructions/LoadFamily/LH_main.lean:373`.
- `lhProgram_eq_sail_x0`: `JoltBytecode/InstructionEquivalence/Instructions/LoadFamily/LH_main.lean:446`.
- `lhProgram_eq_sail`: `JoltBytecode/InstructionEquivalence/Instructions/LoadFamily/LH_main.lean:471`.
- `lwuProgramEqSailStatement`: `JoltBytecode/InstructionEquivalence/Instructions/LoadFamily/LWU_main.lean:22`.
- `lwu_virtual_pext_rd_run`: `JoltBytecode/InstructionEquivalence/Instructions/LoadFamily/LWU_main.lean:52`.
- `lwu_virtual_pext_v40_run`: `JoltBytecode/InstructionEquivalence/Instructions/LoadFamily/LWU_main.lean:79`.
- `lwuProgramAuto_nonzero_run`: `JoltBytecode/InstructionEquivalence/Instructions/LoadFamily/LWU_main.lean:149`.
- `lwuProgram_eq_sail_nonzero_aligned`: `JoltBytecode/InstructionEquivalence/Instructions/LoadFamily/LWU_main.lean:180`.
- `lwuProgramAuto_misaligned_run`: `JoltBytecode/InstructionEquivalence/Instructions/LoadFamily/LWU_main.lean:250`.
- `lwuProgram_eq_sail_misaligned`: `JoltBytecode/InstructionEquivalence/Instructions/LoadFamily/LWU_main.lean:265`.
- `lwuProgram_eq_sail_nonzero`: `JoltBytecode/InstructionEquivalence/Instructions/LoadFamily/LWU_main.lean:295`.
- `lwuProgramAuto_x0_run`: `JoltBytecode/InstructionEquivalence/Instructions/LoadFamily/LWU_main.lean:320`.
- `lwuProgram_eq_sail_x0_aligned`: `JoltBytecode/InstructionEquivalence/Instructions/LoadFamily/LWU_main.lean:350`.
- `lwuProgram_eq_sail_x0`: `JoltBytecode/InstructionEquivalence/Instructions/LoadFamily/LWU_main.lean:423`.
- `lwuProgram_eq_sail`: `JoltBytecode/InstructionEquivalence/Instructions/LoadFamily/LWU_main.lean:448`.
- `word_subaccess_no_overflow`: `JoltBytecode/InstructionEquivalence/Instructions/LoadFamily/LW_SailSide.lean:43`.
- `word_mem_present`: `JoltBytecode/InstructionEquivalence/Instructions/LoadFamily/LW_SailSide.lean:56`.
- `word_load_pmp_ok`: `JoltBytecode/InstructionEquivalence/Instructions/LoadFamily/LW_SailSide.lean:75`.
- `word_not_readable_mmio`: `JoltBytecode/InstructionEquivalence/Instructions/LoadFamily/LW_SailSide.lean:90`.
- `word_no_overflow`: `JoltBytecode/InstructionEquivalence/Instructions/LoadFamily/LW_SailSide.lean:105`.
- `aligned_access`: `JoltBytecode/InstructionEquivalence/Instructions/LoadFamily/LW_SailSide.lean:115`.
- `writeValue`: `JoltBytecode/InstructionEquivalence/Instructions/LoadFamily/LW_SailSide.lean:130`.
- `writeValueUnsigned`: `JoltBytecode/InstructionEquivalence/Instructions/LoadFamily/LW_SailSide.lean:143`.
- `stateAfterWrite_writeValue_eq_dword_word`: `JoltBytecode/InstructionEquivalence/Instructions/LoadFamily/LW_SailSide.lean:157`.
- `stateAfterWrite_writeValueUnsigned_eq_dword_word`: `JoltBytecode/InstructionEquivalence/Instructions/LoadFamily/LW_SailSide.lean:189`.
- `execute_LW_reduces`: `JoltBytecode/InstructionEquivalence/Instructions/LoadFamily/LW_SailSide.lean:221`.
- `execute_LWU_reduces`: `JoltBytecode/InstructionEquivalence/Instructions/LoadFamily/LW_SailSide.lean:268`.
- `execute_LW_misaligned`: `JoltBytecode/InstructionEquivalence/Instructions/LoadFamily/LW_SailSide.lean:315`.
- `execute_LWU_misaligned`: `JoltBytecode/InstructionEquivalence/Instructions/LoadFamily/LW_SailSide.lean:344`.
- `lwProgramEqSailStatement`: `JoltBytecode/InstructionEquivalence/Instructions/LoadFamily/LW_main.lean:33`.
- `lw_ld_run`: `JoltBytecode/InstructionEquivalence/Instructions/LoadFamily/LW_main.lean:61`.
- `lw_virtual_window_mask_w_run`: `JoltBytecode/InstructionEquivalence/Instructions/LoadFamily/LW_main.lean:92`.
- `lw_virtual_pext_signed_rd_run`: `JoltBytecode/InstructionEquivalence/Instructions/LoadFamily/LW_main.lean:113`.
- `lw_virtual_pext_signed_v40_run`: `JoltBytecode/InstructionEquivalence/Instructions/LoadFamily/LW_main.lean:139`.
- `lwProgramAuto_nonzero_run`: `JoltBytecode/InstructionEquivalence/Instructions/LoadFamily/LW_main.lean:208`.
- `lwProgram_eq_sail_nonzero_aligned`: `JoltBytecode/InstructionEquivalence/Instructions/LoadFamily/LW_main.lean:240`.
- `lwProgramAuto_misaligned_run`: `JoltBytecode/InstructionEquivalence/Instructions/LoadFamily/LW_main.lean:310`.
- `lwProgram_eq_sail_nonzero_misaligned`: `JoltBytecode/InstructionEquivalence/Instructions/LoadFamily/LW_main.lean:326`.
- `lwProgram_eq_sail_nonzero`: `JoltBytecode/InstructionEquivalence/Instructions/LoadFamily/LW_main.lean:357`.
- `lwProgramAuto_x0_run`: `JoltBytecode/InstructionEquivalence/Instructions/LoadFamily/LW_main.lean:383`.
- `lwProgram_eq_sail_x0_aligned`: `JoltBytecode/InstructionEquivalence/Instructions/LoadFamily/LW_main.lean:413`.
- `lwProgram_eq_sail_x0_misaligned`: `JoltBytecode/InstructionEquivalence/Instructions/LoadFamily/LW_main.lean:487`.
- `lwProgram_eq_sail_x0`: `JoltBytecode/InstructionEquivalence/Instructions/LoadFamily/LW_main.lean:518`.
- `lwProgram_eq_sail`: `JoltBytecode/InstructionEquivalence/Instructions/LoadFamily/LW_main.lean:544`.
- `ldNative_x0_run_from_memory_read`: `JoltBytecode/InstructionEquivalence/Instructions/Natives/Ld.lean:23`.
- `ldJolt_aligned_reduces`: `JoltBytecode/InstructionEquivalence/Instructions/Natives/Ld.lean:143`.
- `ldInstrEqSailStatement`: `JoltBytecode/InstructionEquivalence/Instructions/Natives/Ld.lean:245`.
- `ldInstr_eq_sail`: `JoltBytecode/InstructionEquivalence/Instructions/Natives/Ld.lean:254`.
- `sdInstrEqSailStatement`: `JoltBytecode/InstructionEquivalence/Instructions/Natives/Sd.lean:19`.
- `sdJolt_reduces_to_vmem_write_addr`: `JoltBytecode/InstructionEquivalence/Instructions/Natives/Sd.lean:29`.
- `sdSail_reduces_to_vmem_write_addr`: `JoltBytecode/InstructionEquivalence/Instructions/Natives/Sd.lean:130`.
- `sdInstr_eq_sail`: `JoltBytecode/InstructionEquivalence/Instructions/Natives/Sd.lean:174`.
- `setupBlock`: `JoltBytecode/InstructionEquivalence/Instructions/StoreFamily/ProgramBlocks.lean:519`.
- `laneStoreProgram_run`: `JoltBytecode/InstructionEquivalence/Instructions/StoreFamily/ProgramBlocks.lean:807`.
- `sdWriteBlock`: `JoltBytecode/InstructionEquivalence/Instructions/StoreFamily/ProgramBlocks.lean:1668`.
- `sbProgramAuto_reduces_to_dword_store`: `JoltBytecode/InstructionEquivalence/Instructions/StoreFamily/Sb_main.lean:51`.
- `sbProgramAuto_concrete`: `JoltBytecode/InstructionEquivalence/Instructions/StoreFamily/Sb_main.lean:176`.
- `sbProgramEqSailStatement`: `JoltBytecode/InstructionEquivalence/Instructions/StoreFamily/Sb_main.lean:283`.
- `sbProgram_eq_sail`: `JoltBytecode/InstructionEquivalence/Instructions/StoreFamily/Sb_main.lean:292`.
- `shProgramAuto_reduces_to_dword_store`: `JoltBytecode/InstructionEquivalence/Instructions/StoreFamily/Sh_main.lean:54`.
- `shProgramAuto_concrete_aligned`: `JoltBytecode/InstructionEquivalence/Instructions/StoreFamily/Sh_main.lean:176`.
- `shProgramEqSailStatement`: `JoltBytecode/InstructionEquivalence/Instructions/StoreFamily/Sh_main.lean:328`.
- `shProgram_eq_sail`: `JoltBytecode/InstructionEquivalence/Instructions/StoreFamily/Sh_main.lean:337`.
- `swProgramAuto_reduces_to_dword_store`: `JoltBytecode/InstructionEquivalence/Instructions/StoreFamily/Sw_main.lean:62`.
- `swProgramAuto_concrete_aligned`: `JoltBytecode/InstructionEquivalence/Instructions/StoreFamily/Sw_main.lean:190`.
- `swProgramEqSailStatement`: `JoltBytecode/InstructionEquivalence/Instructions/StoreFamily/Sw_main.lean:348`.
- `swProgram_eq_sail`: `JoltBytecode/InstructionEquivalence/Instructions/StoreFamily/Sw_main.lean:357`.
- `ReservationWindow`: `JoltBytecode/InstructionEquivalence/Instructions/System/Reservation.lean:13`.
- `ReservationReadEqAssumptions`: `JoltBytecode/InstructionEquivalence/Instructions/System/Reservation.lean:24`.
- `ReservationReadEqAssumptions.linkedCSRs`: `JoltBytecode/InstructionEquivalence/Instructions/System/Reservation.lean:32`.
- `lrRows_eq_execute`: `JoltBytecode/InstructionEquivalence/Instructions/System/Reservation.lean:103`.
- `ReservationStoreEqAssumptions`: `JoltBytecode/InstructionEquivalence/Instructions/System/Sc.lean:23`.
- `ReservationStoreEqAssumptions.linkedCSRs`: `JoltBytecode/InstructionEquivalence/Instructions/System/Sc.lean:35`.
- `scRows_spec`: `JoltBytecode/InstructionEquivalence/Instructions/System/Sc.lean:154`.
- `scRows_eq_execute`: `JoltBytecode/InstructionEquivalence/Instructions/System/Sc.lean:184`.
- `scdProgram_spec`: `JoltBytecode/InstructionEquivalence/Instructions/System/ScDword.lean:25`.
- `scwProgram_spec`: `JoltBytecode/InstructionEquivalence/Instructions/System/ScWord.lean:84`.
- `LoadDwordWindowFacts`: `JoltBytecode/InstructionEquivalence/ProofSupport/BundleLemmas.lean:26`.
- `LoadProgramEqSailAssumptions.dwordWindowFacts`: `JoltBytecode/InstructionEquivalence/ProofSupport/BundleLemmas.lean:40`.
- `StoreDwordWindowFacts`: `JoltBytecode/InstructionEquivalence/ProofSupport/BundleLemmas.lean:60`.
- `StoreProgramEqSailAssumptions.dwordWindowFacts`: `JoltBytecode/InstructionEquivalence/ProofSupport/BundleLemmas.lean:80`.
- `StoreProgramEqSailAssumptions.storeOk`: `JoltBytecode/InstructionEquivalence/ProofSupport/BundleLemmas.lean:103`.
- `StoreAccessFacts`: `JoltBytecode/InstructionEquivalence/ProofSupport/BundleLemmas.lean:117`.
- `StoreProgramEqSailAssumptions.storeAccessFacts`: `JoltBytecode/InstructionEquivalence/ProofSupport/BundleLemmas.lean:126`.
- `effective_address_ok_of_load`: `JoltBytecode/InstructionEquivalence/ProofSupport/Memory/MmuJolt.lean:27`.
- `effective_address_ok_of_store`: `JoltBytecode/InstructionEquivalence/ProofSupport/Memory/MmuJolt.lean:33`.
- `Assumptions.JoltRamStoreOk.transfer`: `JoltBytecode/InstructionEquivalence/ProofSupport/Memory/MmuJolt.lean:286`.
- `ld_run_vreg_vreg_from_memory_read`: `JoltBytecode/InstructionEquivalence/ProofSupport/Memory/Read.lean:471`.
- `ld_run_vreg_xreg_from_memory_read`: `JoltBytecode/InstructionEquivalence/ProofSupport/Memory/Read.lean:500`.
- `vreg_LD_run_of_aligned_dword_phys`: `JoltBytecode/InstructionEquivalence/ProofSupport/Memory/Read.lean:590`.
- `execInstr_sd_vreg_run_of_write`: `JoltBytecode/InstructionEquivalence/ProofSupport/Memory/Write.lean:284`.
- `execInstr_sd_xreg_xreg_run_of_write`: `JoltBytecode/InstructionEquivalence/ProofSupport/Memory/Write.lean:307`.
- `AdviceHonest`: `JoltBytecode/Step/Instructions.lean:244`.
- `joltRun_eq_execute`: `JoltBytecode/Step/Instructions.lean:259`.
- `joltStep_eq_try_step_base`: `JoltBytecode/Step/Instructions.lean:720`.
- `joltStep_eq_try_step_compressed`: `JoltBytecode/Step/Instructions.lean:741`.
- `joltStep_stepInvariant`: `JoltBytecode/Step/Instructions.lean:771`.
- `joltStep_stepInvariant`: `JoltBytecode/Step/Invariant.lean:211`.

## Replaced or removed device-array interfaces

The former device-returning store API and arrays no longer exist.
`storeDeviceByte_same` is replaced by `store_raw_same` and the setup frame over CPU/MMU state.
`storeDeviceByte_outputs_fit` is replaced by `JoltDevice.outputsOf_size`, which proves exact extraction capacity instead of bounding an independently stored output array.
The generic device-only wrappers below were unused and do not express protected shared-memory preservation; the shared `InstructionFrame` and `execInstr_memory`/`execProgram_memory` provide the replacement.
The private `storeFold_rule` became unnecessary once the frame delegates checked stores to the MMU preservation theorem.

- `storeDeviceByte_same`: baseline `JoltBytecode/InstructionEquivalence/ProofSupport/DeviceFrame.lean:35`.
- `storeDeviceByte_outputs_fit`: baseline `JoltBytecode/InstructionEquivalence/ProofSupport/DeviceFrame.lean:42`.
- `writeDst_rule_of_device_relation`: baseline `JoltBytecode/InstructionEquivalence/ProofSupport/DeviceFrame.lean:76`.
- `execInstr_rule_of_device_relation_for_store`: baseline `JoltBytecode/InstructionEquivalence/ProofSupport/DeviceFrame.lean:92`.
- `execInstr_rule_of_device_relation`: baseline `JoltBytecode/InstructionEquivalence/ProofSupport/DeviceFrame.lean:125`.
- `storeFold_rule`: baseline `JoltBytecode/InstructionEquivalence/ProofSupport/InstructionFrame.lean:153`.

## Added theorem interfaces

These include the new shared-memory, setup, decoder and halt contracts and their proof helpers.

- `SourceInstruction.tick_halted`: `JoltBytecode/Decode/Execute.lean:477`.
- `decodeJoltSuccess_some_iff`: `JoltBytecode/Decode/Jolt.lean:211`.
- `amo_dword_bundle_store_ok`: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/Dword.lean:3076`.
- `amo_word_lane_merged_eq_spliced`: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/Word.lean:3159`.
- `amo_word_bundle_store_spliced_ok`: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/WordProgram.lean:23`.
- `amo_word_bundle_store_lane_ok`: `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/WordProgram.lean:65`.
- `StoreProgramEqSailAssumptions.storeOk`: `JoltBytecode/InstructionEquivalence/ProofSupport/BundleLemmas.lean:103`.
- `SetupSame.trans`: `JoltBytecode/InstructionEquivalence/ProofSupport/DeviceFrame.lean:44`.
- `setup_refl`: `JoltBytecode/InstructionEquivalence/ProofSupport/DeviceFrame.lean:48`.
- `setup_trans`: `JoltBytecode/InstructionEquivalence/ProofSupport/DeviceFrame.lean:49`.
- `execInstr_setup`: `JoltBytecode/InstructionEquivalence/ProofSupport/DeviceFrame.lean:54`.
- `execProgram_setup`: `JoltBytecode/InstructionEquivalence/ProofSupport/DeviceFrame.lean:68`.
- `execInstr_memory`: `JoltBytecode/InstructionEquivalence/ProofSupport/DeviceFrame.lean:81`.
- `execProgram_memory`: `JoltBytecode/InstructionEquivalence/ProofSupport/DeviceFrame.lean:95`.
- `codeRegion_of_instr_run`: `JoltBytecode/InstructionEquivalence/ProofSupport/DeviceFrame.lean:116`.
- `codeRegion_of_program_run`: `JoltBytecode/InstructionEquivalence/ProofSupport/DeviceFrame.lean:121`.
- `setup_of_tail_run`: `JoltBytecode/InstructionEquivalence/ProofSupport/DeviceFrame.lean:127`.
- `execHalt_vreg_run`: `JoltBytecode/InstructionEquivalence/ProofSupport/DeviceFrame.lean:151`.
- `mem_pure`: `JoltBytecode/InstructionEquivalence/ProofSupport/InstructionFrame.lean:98`.
- `mem_bind`: `JoltBytecode/InstructionEquivalence/ProofSupport/InstructionFrame.lean:102`.
- `mem_read`: `JoltBytecode/InstructionEquivalence/ProofSupport/InstructionFrame.lean:106`.
- `mem_write`: `JoltBytecode/InstructionEquivalence/ProofSupport/InstructionFrame.lean:110`.
- `mem_and`: `JoltBytecode/InstructionEquivalence/ProofSupport/InstructionFrame.lean:118`.
- `mem_liftE`: `JoltBytecode/InstructionEquivalence/ProofSupport/InstructionFrame.lean:126`.
- `mem_bindE`: `JoltBytecode/InstructionEquivalence/ProofSupport/InstructionFrame.lean:138`.
- `mem_andE`: `JoltBytecode/InstructionEquivalence/ProofSupport/InstructionFrame.lean:147`.
- `mem_runE`: `JoltBytecode/InstructionEquivalence/ProofSupport/InstructionFrame.lean:156`.
- `mem_jump`: `JoltBytecode/InstructionEquivalence/ProofSupport/InstructionFrame.lean:167`.
- `protected_store_ok_congr`: `JoltBytecode/InstructionEquivalence/ProofSupport/Memory/MmuJolt.lean:41`.
- `protected_byte_congr`: `JoltBytecode/InstructionEquivalence/ProofSupport/Memory/MmuJolt.lean:51`.
- `ProtectedMemory.refl`: `JoltBytecode/InstructionEquivalence/ProofSupport/Memory/MmuJolt.lean:68`.
- `ProtectedMemory.trans`: `JoltBytecode/InstructionEquivalence/ProofSupport/Memory/MmuJolt.lean:73`.
- `insert_keeps_protected`: `JoltBytecode/InstructionEquivalence/ProofSupport/Memory/MmuJolt.lean:81`.
- `protected_store_byte_iff`: `JoltBytecode/InstructionEquivalence/ProofSupport/Memory/MmuJolt.lean:97`.
- `store_raw_existing`: `JoltBytecode/InstructionEquivalence/ProofSupport/Memory/MmuJolt.lean:107`.
- `store_raw_protected`: `JoltBytecode/InstructionEquivalence/ProofSupport/Memory/MmuJolt.lean:124`.
- `write_doubleword_keeps_protected`: `JoltBytecode/InstructionEquivalence/ProofSupport/Memory/MmuJolt.lean:136`.
- `store_doubleword_protected`: `JoltBytecode/InstructionEquivalence/ProofSupport/Memory/MmuJolt.lean:151`.
- `Assumptions.JoltRamStoreOk.transfer`: `JoltBytecode/InstructionEquivalence/ProofSupport/Memory/MmuJolt.lean:286`.
- `outputsOf_size`: `JoltBytecode/JoltISA/JoltDevice.lean:275`.
