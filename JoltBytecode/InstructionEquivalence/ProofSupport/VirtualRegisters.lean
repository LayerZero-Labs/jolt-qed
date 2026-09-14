import JoltBytecode.JoltISA.VirtualRegisters

/-!
# Proof-side facts about the Jolt virtual-register layout

These are the proof hammers built on top of `JoltBytecode/JoltISA/VirtualRegisters.lean`:

* `rfl`-projection `@[simp]`s that expose the reserved-CSR ↔ Sail register /
  CSR-address mapping;
* the small worked allocator decide-theorems for `allocate()` / drop;
* the `inlineTmpN_not_protected` chain plus `protected_ne_inlineTmpN`
  side-condition discharge lemmas;
* the full `inlineTmp0..7` distinctness matrix.

The data layer (`VReg`, `joltRegisterSlot`, `IsProtectedJoltRegister`, the
allocator model, the `inlineTmpN` aliases) lives in `VirtualRegisters.lean`.
-/

namespace JoltISA

/-!
The reserved CSR entries below are Jolt ISA layout facts.  They reduce by
`rfl`; later proofs should not re-assume this mapping.
-/

@[simp] theorem joltRegisterSailTarget_trapHandlerVReg :
    joltRegisterSailTarget? trapHandlerVReg = some Register.mtvec := rfl

@[simp] theorem joltRegisterSailTarget_mscratchVReg :
    joltRegisterSailTarget? mscratchVReg = some Register.mscratch := rfl

@[simp] theorem joltRegisterSailTarget_mepcVReg :
    joltRegisterSailTarget? mepcVReg = some Register.mepc := rfl

@[simp] theorem joltRegisterSailTarget_mcauseVReg :
    joltRegisterSailTarget? mcauseVReg = some Register.mcause := rfl

@[simp] theorem joltRegisterSailTarget_mtvalVReg :
    joltRegisterSailTarget? mtvalVReg = some Register.mtval := rfl

@[simp] theorem joltRegisterSailTarget_mstatusVReg :
    joltRegisterSailTarget? mstatusVReg = some Register.mstatus := rfl

@[simp] theorem joltRegisterCsrAddress_trapHandlerVReg :
    joltRegisterCsrAddress? trapHandlerVReg = some 0x305#12 := rfl

@[simp] theorem joltRegisterCsrAddress_mscratchVReg :
    joltRegisterCsrAddress? mscratchVReg = some 0x340#12 := rfl

@[simp] theorem joltRegisterCsrAddress_mepcVReg :
    joltRegisterCsrAddress? mepcVReg = some 0x341#12 := rfl

@[simp] theorem joltRegisterCsrAddress_mcauseVReg :
    joltRegisterCsrAddress? mcauseVReg = some 0x342#12 := rfl

@[simp] theorem joltRegisterCsrAddress_mtvalVReg :
    joltRegisterCsrAddress? mtvalVReg = some 0x343#12 := rfl

@[simp] theorem joltRegisterCsrAddress_mstatusVReg :
    joltRegisterCsrAddress? mstatusVReg = some 0x300#12 := rfl

/-! ## Allocator worked examples -/

/-- With no live temporaries, Rust `allocate()` returns register 40. -/
theorem allocateInstructionRegister_nil :
    allocateInstructionRegister [] = some (inlineTmp 0, [0]) := by
  decide

/-- With `v0` live, Rust `allocate()` returns register 41. -/
theorem allocateInstructionRegister_live_0 :
    allocateInstructionRegister [0] = some (inlineTmp 1, [1, 0]) := by
  decide

/-- With `v0,v1` live, Rust `allocate()` returns register 42. -/
theorem allocateInstructionRegister_live_0_1 :
    allocateInstructionRegister [0, 1] = some (inlineTmp 2, [2, 0, 1]) := by
  decide

/-- With `v0..v2` live, Rust `allocate()` returns register 43. -/
theorem allocateInstructionRegister_live_0_1_2 :
    allocateInstructionRegister [0, 1, 2] =
      some (inlineTmp 3, [3, 0, 1, 2]) := by
  decide

/-- With `v0..v3` live, Rust `allocate()` returns register 44. -/
theorem allocateInstructionRegister_live_0_1_2_3 :
    allocateInstructionRegister [0, 1, 2, 3] =
      some (inlineTmp 4, [4, 0, 1, 2, 3]) := by
  decide

/-- With `v0..v4` live, Rust `allocate()` returns register 45. -/
theorem allocateInstructionRegister_live_0_1_2_3_4 :
    allocateInstructionRegister [0, 1, 2, 3, 4] =
      some (inlineTmp 5, [5, 0, 1, 2, 3, 4]) := by
  decide

/-- Dropping the nested scratch from a live `v0..v4,v5` set exposes `v5`
for the next recursive inline expansion. -/
theorem dropInstructionRegister_5_after_live_0_to_5 :
    dropInstructionRegister 5 [5, 0, 1, 2, 3, 4] =
      [0, 1, 2, 3, 4] := by
  decide

/-! ## Protection / distinctness -/

/-- Any Jolt register classified as instruction-local scratch is not
protected. -/
theorem not_protected_of_instructionTmp {r : VReg} {n : Nat}
    (h : joltRegisterSlot r = .instructionTmp n) :
    ¬ IsProtectedJoltRegister r := by
  unfold IsProtectedJoltRegister
  rw [h]
  simp [JoltRegisterSlot.isProtected]

/-- A protected Jolt register cannot be an unprotected scratch register. -/
theorem protected_ne_of_not_protected {r scratch : VReg}
    (hprotected : IsProtectedJoltRegister r)
    (hscratch : ¬ IsProtectedJoltRegister scratch) :
    r ≠ scratch := by
  intro hEq
  rw [hEq] at hprotected
  exact hscratch hprotected

/-- Rust's first instruction-local scratch register is not protected. -/
@[simp] theorem inlineTmp0_not_protected : ¬ IsProtectedJoltRegister inlineTmp0 :=
  not_protected_of_instructionTmp (r := inlineTmp0) (n := 0) rfl

/-- Any protected Jolt register address is distinct from Rust's first
instruction-local scratch register. -/
theorem protected_ne_inlineTmp0 {r : VReg}
    (h : IsProtectedJoltRegister r) :
    r ≠ inlineTmp0 := by
  exact protected_ne_of_not_protected h inlineTmp0_not_protected

/-- Rust's second instruction-local scratch register is not protected. -/
@[simp] theorem inlineTmp1_not_protected : ¬ IsProtectedJoltRegister inlineTmp1 :=
  not_protected_of_instructionTmp (r := inlineTmp1) (n := 1) rfl

/-- Any protected Jolt register address is distinct from Rust's second
instruction-local scratch register. -/
theorem protected_ne_inlineTmp1 {r : VReg}
    (h : IsProtectedJoltRegister r) :
    r ≠ inlineTmp1 := by
  exact protected_ne_of_not_protected h inlineTmp1_not_protected

/-- Rust's third instruction-local scratch register is not protected. -/
@[simp] theorem inlineTmp2_not_protected : ¬ IsProtectedJoltRegister inlineTmp2 :=
  not_protected_of_instructionTmp (r := inlineTmp2) (n := 2) rfl

/-- Any protected Jolt register address is distinct from Rust's third
instruction-local scratch register. -/
theorem protected_ne_inlineTmp2 {r : VReg}
    (h : IsProtectedJoltRegister r) :
    r ≠ inlineTmp2 := by
  exact protected_ne_of_not_protected h inlineTmp2_not_protected

/-- Rust's fourth instruction-local scratch register is not protected. -/
@[simp] theorem inlineTmp3_not_protected : ¬ IsProtectedJoltRegister inlineTmp3 :=
  not_protected_of_instructionTmp (r := inlineTmp3) (n := 3) rfl

/-- Any protected Jolt register address is distinct from Rust's fourth
instruction-local scratch register. -/
theorem protected_ne_inlineTmp3 {r : VReg}
    (h : IsProtectedJoltRegister r) :
    r ≠ inlineTmp3 := by
  exact protected_ne_of_not_protected h inlineTmp3_not_protected

/-- Rust's fifth instruction-local scratch register is not protected. -/
@[simp] theorem inlineTmp4_not_protected : ¬ IsProtectedJoltRegister inlineTmp4 :=
  not_protected_of_instructionTmp (r := inlineTmp4) (n := 4) rfl

/-- Any protected Jolt register address is distinct from Rust's fifth
instruction-local scratch register. -/
theorem protected_ne_inlineTmp4 {r : VReg}
    (h : IsProtectedJoltRegister r) :
    r ≠ inlineTmp4 := by
  exact protected_ne_of_not_protected h inlineTmp4_not_protected

/-- Rust's sixth instruction-local scratch register is not protected. -/
@[simp] theorem inlineTmp5_not_protected : ¬ IsProtectedJoltRegister inlineTmp5 :=
  not_protected_of_instructionTmp (r := inlineTmp5) (n := 5) rfl

/-- Any protected Jolt register address is distinct from Rust's sixth
instruction-local scratch register. -/
theorem protected_ne_inlineTmp5 {r : VReg}
    (h : IsProtectedJoltRegister r) :
    r ≠ inlineTmp5 := by
  exact protected_ne_of_not_protected h inlineTmp5_not_protected

/-- Rust's seventh instruction-local scratch register is not protected. -/
@[simp] theorem inlineTmp6_not_protected : ¬ IsProtectedJoltRegister inlineTmp6 :=
  not_protected_of_instructionTmp (r := inlineTmp6) (n := 6) rfl

/-- Rust's eighth instruction-local scratch register is not protected. -/
@[simp] theorem inlineTmp7_not_protected : ¬ IsProtectedJoltRegister inlineTmp7 :=
  not_protected_of_instructionTmp (r := inlineTmp7) (n := 7) rfl

/- The Rust `allocate()` scratch aliases denote distinct physical virtual
registers.  These small facts let proof code talk in names instead of raw
numbers while still discharging preservation side conditions directly. -/
@[simp] theorem inlineTmp0_ne_inlineTmp1 : inlineTmp0 ≠ inlineTmp1 := by decide
@[simp] theorem inlineTmp1_ne_inlineTmp0 : inlineTmp1 ≠ inlineTmp0 := by decide
@[simp] theorem inlineTmp0_ne_inlineTmp2 : inlineTmp0 ≠ inlineTmp2 := by decide
@[simp] theorem inlineTmp2_ne_inlineTmp0 : inlineTmp2 ≠ inlineTmp0 := by decide
@[simp] theorem inlineTmp0_ne_inlineTmp3 : inlineTmp0 ≠ inlineTmp3 := by decide
@[simp] theorem inlineTmp3_ne_inlineTmp0 : inlineTmp3 ≠ inlineTmp0 := by decide
@[simp] theorem inlineTmp0_ne_inlineTmp4 : inlineTmp0 ≠ inlineTmp4 := by decide
@[simp] theorem inlineTmp4_ne_inlineTmp0 : inlineTmp4 ≠ inlineTmp0 := by decide
@[simp] theorem inlineTmp0_ne_inlineTmp5 : inlineTmp0 ≠ inlineTmp5 := by decide
@[simp] theorem inlineTmp5_ne_inlineTmp0 : inlineTmp5 ≠ inlineTmp0 := by decide
@[simp] theorem inlineTmp0_ne_inlineTmp6 : inlineTmp0 ≠ inlineTmp6 := by decide
@[simp] theorem inlineTmp6_ne_inlineTmp0 : inlineTmp6 ≠ inlineTmp0 := by decide
@[simp] theorem inlineTmp0_ne_inlineTmp7 : inlineTmp0 ≠ inlineTmp7 := by decide
@[simp] theorem inlineTmp7_ne_inlineTmp0 : inlineTmp7 ≠ inlineTmp0 := by decide

@[simp] theorem inlineTmp1_ne_inlineTmp2 : inlineTmp1 ≠ inlineTmp2 := by decide
@[simp] theorem inlineTmp2_ne_inlineTmp1 : inlineTmp2 ≠ inlineTmp1 := by decide
@[simp] theorem inlineTmp1_ne_inlineTmp3 : inlineTmp1 ≠ inlineTmp3 := by decide
@[simp] theorem inlineTmp3_ne_inlineTmp1 : inlineTmp3 ≠ inlineTmp1 := by decide
@[simp] theorem inlineTmp1_ne_inlineTmp4 : inlineTmp1 ≠ inlineTmp4 := by decide
@[simp] theorem inlineTmp4_ne_inlineTmp1 : inlineTmp4 ≠ inlineTmp1 := by decide
@[simp] theorem inlineTmp1_ne_inlineTmp5 : inlineTmp1 ≠ inlineTmp5 := by decide
@[simp] theorem inlineTmp5_ne_inlineTmp1 : inlineTmp5 ≠ inlineTmp1 := by decide
@[simp] theorem inlineTmp1_ne_inlineTmp6 : inlineTmp1 ≠ inlineTmp6 := by decide
@[simp] theorem inlineTmp6_ne_inlineTmp1 : inlineTmp6 ≠ inlineTmp1 := by decide
@[simp] theorem inlineTmp1_ne_inlineTmp7 : inlineTmp1 ≠ inlineTmp7 := by decide
@[simp] theorem inlineTmp7_ne_inlineTmp1 : inlineTmp7 ≠ inlineTmp1 := by decide

@[simp] theorem inlineTmp2_ne_inlineTmp3 : inlineTmp2 ≠ inlineTmp3 := by decide
@[simp] theorem inlineTmp3_ne_inlineTmp2 : inlineTmp3 ≠ inlineTmp2 := by decide
@[simp] theorem inlineTmp2_ne_inlineTmp4 : inlineTmp2 ≠ inlineTmp4 := by decide
@[simp] theorem inlineTmp4_ne_inlineTmp2 : inlineTmp4 ≠ inlineTmp2 := by decide
@[simp] theorem inlineTmp2_ne_inlineTmp5 : inlineTmp2 ≠ inlineTmp5 := by decide
@[simp] theorem inlineTmp5_ne_inlineTmp2 : inlineTmp5 ≠ inlineTmp2 := by decide
@[simp] theorem inlineTmp2_ne_inlineTmp6 : inlineTmp2 ≠ inlineTmp6 := by decide
@[simp] theorem inlineTmp6_ne_inlineTmp2 : inlineTmp6 ≠ inlineTmp2 := by decide
@[simp] theorem inlineTmp2_ne_inlineTmp7 : inlineTmp2 ≠ inlineTmp7 := by decide
@[simp] theorem inlineTmp7_ne_inlineTmp2 : inlineTmp7 ≠ inlineTmp2 := by decide

@[simp] theorem inlineTmp3_ne_inlineTmp4 : inlineTmp3 ≠ inlineTmp4 := by decide
@[simp] theorem inlineTmp4_ne_inlineTmp3 : inlineTmp4 ≠ inlineTmp3 := by decide
@[simp] theorem inlineTmp3_ne_inlineTmp5 : inlineTmp3 ≠ inlineTmp5 := by decide
@[simp] theorem inlineTmp5_ne_inlineTmp3 : inlineTmp5 ≠ inlineTmp3 := by decide
@[simp] theorem inlineTmp3_ne_inlineTmp6 : inlineTmp3 ≠ inlineTmp6 := by decide
@[simp] theorem inlineTmp6_ne_inlineTmp3 : inlineTmp6 ≠ inlineTmp3 := by decide
@[simp] theorem inlineTmp3_ne_inlineTmp7 : inlineTmp3 ≠ inlineTmp7 := by decide
@[simp] theorem inlineTmp7_ne_inlineTmp3 : inlineTmp7 ≠ inlineTmp3 := by decide

@[simp] theorem inlineTmp4_ne_inlineTmp5 : inlineTmp4 ≠ inlineTmp5 := by decide
@[simp] theorem inlineTmp5_ne_inlineTmp4 : inlineTmp5 ≠ inlineTmp4 := by decide
@[simp] theorem inlineTmp4_ne_inlineTmp6 : inlineTmp4 ≠ inlineTmp6 := by decide
@[simp] theorem inlineTmp6_ne_inlineTmp4 : inlineTmp6 ≠ inlineTmp4 := by decide
@[simp] theorem inlineTmp4_ne_inlineTmp7 : inlineTmp4 ≠ inlineTmp7 := by decide
@[simp] theorem inlineTmp7_ne_inlineTmp4 : inlineTmp7 ≠ inlineTmp4 := by decide

@[simp] theorem inlineTmp5_ne_inlineTmp6 : inlineTmp5 ≠ inlineTmp6 := by decide
@[simp] theorem inlineTmp6_ne_inlineTmp5 : inlineTmp6 ≠ inlineTmp5 := by decide
@[simp] theorem inlineTmp5_ne_inlineTmp7 : inlineTmp5 ≠ inlineTmp7 := by decide
@[simp] theorem inlineTmp7_ne_inlineTmp5 : inlineTmp7 ≠ inlineTmp5 := by decide

@[simp] theorem inlineTmp6_ne_inlineTmp7 : inlineTmp6 ≠ inlineTmp7 := by decide
@[simp] theorem inlineTmp7_ne_inlineTmp6 : inlineTmp7 ≠ inlineTmp6 := by decide

end JoltISA
