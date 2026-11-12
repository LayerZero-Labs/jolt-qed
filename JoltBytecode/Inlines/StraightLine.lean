import JoltBytecode.Inlines.Frame
import JoltBytecode.InstructionEquivalence.ProofSupport.ValueLemmas

/-!
# A program logic for straight-line inline rows

The per-inline theorems of `docs/inline-precompiles.md` (sections 5.4 and 5.5) reason about
runs of long straight-line row lists. This module gives the generic tools, shared by every
inline:

* `regRun`: a pure evaluator for the *register rows* (`ADD`, `MUL`, `MULHU`, `SLTU`, `LUI`,
  `VirtualAdvice` and `ADDI` from `x0`, all on virtual registers). A successful run of
  `l ++ rest` whose prefix `l` is register rows is a run of `rest` from the evaluated register
  file (`run_append_of_regRun`), so a proof never unfolds `execInstr` on those rows.
* `run_instr_iff` and `seq_cons`, which peel one row off a run.
* `run_assertEq_iff` and `run_assertLTE_iff`: what a successful run of
  `VirtualAssertEQ :: rest` or `VirtualAssertLTE :: rest` means, in both directions.

The rows that touch memory or architectural registers (`LD` and `SD` through an architectural
base, the value `loadDword?` an `LD` reads, and the read-after-write facts for stores to RAM)
are in `StraightLineMemory`, which imports this module.

Every lemma is proved; the module has no `sorry`.
-/

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail LeanRV64D
  LeanRV64D.Functions

set_option autoImplicit false

noncomputable section

namespace JoltISA.Inlines

/-! ## Register files -/

/-- The register file `f` with virtual register `d` set to `v`. This is the update that
`writeVReg` performs.
Example: `setV f vr48 7 vr48 = 7`, and `setV f vr48 7 vr49 = f vr49`. -/
def setV (f : VReg → BitVec 64) (d : VReg) (v : BitVec 64) : VReg → BitVec 64 :=
  fun r => if r = d then v else f r

/-- Reading the register just set. Example: `setV f vr48 7 vr48 = 7`. -/
@[simp] theorem setV_same (f : VReg → BitVec 64) (d : VReg) (v : BitVec 64) :
    setV f d v d = v := by simp [setV]

/-! ## Register rows -/

/-- The register rows: rows that read only virtual registers (or `x0`) and write one virtual
register. The result is the destination and the value as a function of the register file.
`ADDI` counts only with source `x0`, which is how Jolt resets pool registers, and `SUB` counts
with a virtual or an `x0` first source (BLAKE2 negates its final-block flag with
`SUB vr62, x0, vr62`).
Example: `(ADD (.vreg vr62) (.vreg vr62) (.vreg vr61)).regRow?` is
`some (vr62, fun f => f vr62 + f vr61)`. -/
def _root_.JoltISA.Instr.regRow? : Instr → Option (VReg × ((VReg → BitVec 64) → BitVec 64))
  | .ADD (.vreg d) (.vreg x) (.vreg y) => some (d, fun f => f x + f y)
  | .MUL (.vreg d) (.vreg x) (.vreg y) => some (d, fun f => f x * f y)
  | .MULHU (.vreg d) (.vreg x) (.vreg y) => some (d, fun f => jolt_mulhu_value (f x) (f y))
  | .SLTU (.vreg d) (.vreg x) (.vreg y) => some (d, fun f => jolt_sltu_value (f x) (f y))
  | .LUI (.vreg d) imm => some (d, fun _ => imm)
  | .VirtualAdvice (.vreg d) v _ => some (d, fun _ => v)
  | .SUB (.vreg d) (.vreg x) (.vreg y) => some (d, fun f => f x - f y)
  | .XOR (.vreg d) (.vreg x) (.vreg y) => some (d, fun f => jolt_xor_value (f x) (f y))
  | .XORI (.vreg d) (.vreg x) imm => some (d, fun f => jolt_xor_value (f x) imm)
  | .VirtualXORROT32 (.vreg d) (.vreg x) (.vreg y) =>
    some (d, fun f => jolt_virtual_xorrot_value 32 (f x) (f y))
  | .VirtualXORROT24 (.vreg d) (.vreg x) (.vreg y) =>
    some (d, fun f => jolt_virtual_xorrot_value 24 (f x) (f y))
  | .VirtualXORROT16 (.vreg d) (.vreg x) (.vreg y) =>
    some (d, fun f => jolt_virtual_xorrot_value 16 (f x) (f y))
  | .VirtualXORROT63 (.vreg d) (.vreg x) (.vreg y) =>
    some (d, fun f => jolt_virtual_xorrot_value 63 (f x) (f y))
  | .ADDI (.vreg d) (.xreg r) imm => if isX0 r then some (d, fun _ => 0 + imm) else none
  | .SUB (.vreg d) (.xreg r) (.vreg y) => if isX0 r then some (d, fun f => 0 - f y) else none
  | _ => none

private theorem readSrc_x0 {r : regidx} (h : isX0 r = true) (s : SailJoltState) :
    readSrc (.xreg r) s = .ok 0 s := by
  obtain ⟨b⟩ := r
  simp only [isX0, decide_eq_true_eq] at h
  have hb : b = 0 := BitVec.eq_of_toNat_eq (by simpa using h)
  subst hb
  apply readSrc_xreg_run_of_read
  exact rX_bits_regidx_zero s.sail

/-- A register row with a writable destination retires and sets its destination.
Example: `ADD vr62 vr62 vr61` from `s` ends in `s` with `vr62 := s.vregs vr62 + s.vregs vr61`. -/
theorem execInstr_of_regRow {i : Instr} {d : VReg} {g : (VReg → BitVec 64) → BitVec 64}
    (h : i.regRow? = some (d, g)) (hd : 32 ≤ d.toNat) (s : SailJoltState) :
    (execInstr i).run s = .ok RETIRE_SUCCESS { s with vregs := setV s.vregs d (g s.vregs) } := by
  have hw : WritableVReg d := by unfold WritableVReg; omega
  unfold Instr.regRow? at h
  split at h
  all_goals
    try first
    | (simp only [Option.some.injEq, Prod.mk.injEq] at h
       obtain ⟨rfl, rfl⟩ := h
       simp only [execInstr, EStateM.run, readSrc_vreg, readVReg_run, writeDst_vreg, bind,
         EStateM.bind, addWide_low, subWide_low, mulWide_low]
       exact writeVReg_retire_run_of_writable _ _ s hw)
    | cases h
  -- `ADDI` and `SUB` from `x0`
  all_goals
    split at h
    · rename_i hx
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [execInstr, EStateM.run, bind, EStateM.bind, readSrc_x0 hx s, readSrc_vreg,
        readVReg_run, writeDst_vreg, addWide_low, subWide_low]
      exact writeVReg_retire_run_of_writable _ _ s hw
    · cases h

/-! ## Running programs row by row -/

/-- `Program.seq` of a cons is the row followed by the rest.
Example: `Program.seq [LUI vr60 5, ADD vr62 vr60 vr60]` is
`.instr (LUI vr60 5) (Program.seq [ADD vr62 vr60 vr60])`. -/
@[simp] theorem seq_cons (i : Instr) (l : List Instr) :
    Program.seq (i :: l) = .instr i (Program.seq l) := rfl

/-- A row that retires from `s` to `t` can be peeled off a run.
Example: if `ADDI vr48, x0, 5` retires from `s` to `t`, a run of
`[ADDI vr48, x0, 5; SD x12, vr48, 0]` from `s` is a run of `[SD x12, vr48, 0]` from `t`. -/
theorem run_instr_iff {i : Instr} {s t : SailJoltState}
    (h : (execInstr i).run s = .ok RETIRE_SUCCESS t) (p : Program) (s' : SailJoltState) :
    Program.Run (.instr i p) s s' ↔ Program.Run p t s' := by
  constructor
  · intro hr
    obtain ⟨t', ht', hrest⟩ := execProgram_instr_run_retire_inv i p s s' hr
    rw [h] at ht'
    cases ht'
    exact hrest
  · intro hr
    unfold Program.Run
    rw [execProgram_instr_run_retire i p s t h]
    exact hr

/-- A row that throws ends every run.
Example: `VirtualAssertEQ vr62, vr56` from a state with `vr62 = 1` and `vr56 = 2` throws, so
no run of `[VirtualAssertEQ vr62, vr56; …]` starts there. -/
theorem not_run_of_error {i : Instr} {s t : SailJoltState} {e : Error exception}
    (h : (execInstr i).run s = .error e t) (p : Program) (s' : SailJoltState) :
    ¬ Program.Run (.instr i p) s s' := by
  intro hr
  obtain ⟨t', ht', _⟩ := execProgram_instr_run_retire_inv i p s s' hr
  rw [h] at ht'
  cases ht'

/-- The pure evaluator for register rows: `none` as soon as a row is not a register row or
writes a register below `vr32`.
Example: `regRun [LUI vr60 5, ADD vr62 vr60 vr60] f = some (setV (setV f vr60 5) vr62 10)`. -/
def regRun : List Instr → (VReg → BitVec 64) → Option (VReg → BitVec 64)
  | [], f => some f
  | i :: l, f =>
    match i.regRow? with
    | some (d, g) => if 32 ≤ d.toNat then regRun l (setV f d (g f)) else none
    | none => none

/-- **Register rows run as evaluated.** If the register rows `l` evaluate to `f` from the
register file of `s`, a run of `l ++ rest` from `s` is a run of `rest` from `s` with register
file `f`. Nothing else in the state changes.
Example: `regRun [LUI vr60 5] s.vregs = some (setV s.vregs vr60 5)`, so a run of
`[LUI vr60 5; SD x12, vr60, 0]` from `s` is a run of `[SD x12, vr60, 0]` from `s` with
`vr60 = 5`. -/
theorem run_append_of_regRun {l : List Instr} {s : SailJoltState} {f : VReg → BitVec 64}
    (h : regRun l s.vregs = some f) (rest : List Instr) (s' : SailJoltState) :
    (Program.seq (l ++ rest)).Run s s' ↔ (Program.seq rest).Run { s with vregs := f } s' := by
  induction l generalizing s with
  | nil =>
    simp only [regRun, Option.some.injEq] at h
    subst h
    rfl
  | cons i l ih =>
    simp only [regRun] at h
    split at h
    · rename_i d g hi
      split at h
      · rename_i hd
        rw [List.cons_append, seq_cons, run_instr_iff (execInstr_of_regRow hi hd s)]
        exact ih (s := { s with vregs := setV s.vregs d (g s.vregs) }) h
      · cases h
    · cases h

/-! ## Assertions -/

/-- A run through `VirtualAssertEQ x y 0` is a run of the rest in which `x = y` held.
Example: from a state with `vr62 = vr56 = 1`, a run of `[VirtualAssertEQ vr62, vr56; rest]` is a
run of `rest`; with `vr62 = 1`, `vr56 = 2` there is none. -/
theorem run_assertEq_iff (x y : VReg) (rest : List Instr) (s s' : SailJoltState) :
    (Program.seq (.VirtualAssertEQ (.vreg x) (.vreg y) 0 :: rest)).Run s s' ↔
      s.vregs x = s.vregs y ∧ (Program.seq rest).Run s s' := by
  by_cases hxy : s.vregs x = s.vregs y
  · have h : (execInstr (.VirtualAssertEQ (.vreg x) (.vreg y) 0)).run s = .ok RETIRE_SUCCESS s := by
      simp [execInstr, EStateM.run, bind, EStateM.bind, hxy, pure, EStateM.pure]
    rw [seq_cons, run_instr_iff h]
    exact ⟨fun hr => ⟨hxy, hr⟩, fun hr => hr.2⟩
  · have h : (execInstr (.VirtualAssertEQ (.vreg x) (.vreg y) 0)).run s =
        .error (Error.Assertion "VirtualAssertEQ") s := by
      simp [execInstr, EStateM.run, bind, EStateM.bind, hxy, throw, throwThe,
        MonadExceptOf.throw, EStateM.throw]
    rw [seq_cons]
    exact ⟨fun hr => absurd hr (not_run_of_error h _ _), fun hr => absurd hr.1 hxy⟩

/-- A run through `VirtualAssertLTE x y 0` is a run of the rest in which `x ≤ y` held as
unsigned 64-bit values.
Example: from a state with `vr61 = 1` and `vr63 = 2`, a run of `[VirtualAssertLTE vr61, vr63; rest]`
is a run of `rest`; with `vr61 = 3` there is none. -/
theorem run_assertLTE_iff (x y : VReg) (rest : List Instr) (s s' : SailJoltState) :
    (Program.seq (.VirtualAssertLTE (.vreg x) (.vreg y) 0 :: rest)).Run s s' ↔
      (s.vregs x).toNat ≤ (s.vregs y).toNat ∧ (Program.seq rest).Run s s' := by
  by_cases hxy : (s.vregs x).toNat ≤ (s.vregs y).toNat
  · have h : (execInstr (.VirtualAssertLTE (.vreg x) (.vreg y) 0)).run s =
        .ok RETIRE_SUCCESS s := by
      simp [execInstr, EStateM.run, bind, EStateM.bind, hxy, pure, EStateM.pure]
    rw [seq_cons, run_instr_iff h]
    exact ⟨fun hr => ⟨hxy, hr⟩, fun hr => hr.2⟩
  · have h : (execInstr (.VirtualAssertLTE (.vreg x) (.vreg y) 0)).run s =
        .error (Error.Assertion "VirtualAssertLTE") s := by
      simp [execInstr, EStateM.run, bind, EStateM.bind, hxy, throw, throwThe,
        MonadExceptOf.throw, EStateM.throw]
    rw [seq_cons]
    exact ⟨fun hr => absurd hr (not_run_of_error h _ _), fun hr => absurd hr.1 hxy⟩

end JoltISA.Inlines
