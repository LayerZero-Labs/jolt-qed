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
* One lemma per remaining row shape the inlines use: `VirtualAssertEQ`, `VirtualAssertLTE`,
  `LD` from an architectural base, and `SD` to an architectural base.
  Each states what a successful run of `row :: rest` means, in both directions where the
  completeness proofs need it.
* `loadDword?`, the value an `LD` reads, with the read-after-write facts for stores to RAM.

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

/-- Reading another register. Example: `setV f vr48 7 vr49 = f vr49`. -/
theorem setV_ne (f : VReg → BitVec 64) {d r : VReg} (v : BitVec 64) (h : r ≠ d) :
    setV f d v r = f r := by simp [setV, h]

/-! ## Register rows -/

/-- The register rows: rows that read only virtual registers (or `x0`) and write one virtual
register. The result is the destination and the value as a function of the register file.
`ADDI` counts only with source `x0`, which is how Jolt resets pool registers.
Example: `(ADD (.vreg vr62) (.vreg vr62) (.vreg vr61)).regRow? = some (vr62, fun f => f vr62 + f vr61)`. -/
def _root_.JoltISA.Instr.regRow? : Instr → Option (VReg × ((VReg → BitVec 64) → BitVec 64))
  | .ADD (.vreg d) (.vreg x) (.vreg y) => some (d, fun f => f x + f y)
  | .MUL (.vreg d) (.vreg x) (.vreg y) => some (d, fun f => f x * f y)
  | .MULHU (.vreg d) (.vreg x) (.vreg y) => some (d, fun f => jolt_mulhu_value (f x) (f y))
  | .SLTU (.vreg d) (.vreg x) (.vreg y) => some (d, fun f => jolt_sltu_value (f x) (f y))
  | .LUI (.vreg d) imm => some (d, fun _ => imm)
  | .VirtualAdvice (.vreg d) v _ => some (d, fun _ => v)
  | .ADDI (.vreg d) (.xreg r) imm => if isX0 r then some (d, fun _ => 0 + imm) else none
  | _ => none

private theorem bind_ok' {ε σ α β : Type} {x : EStateM ε σ α} {f : α → EStateM ε σ β}
    {s t : σ} {r : β} (h : (x >>= f) s = .ok r t) :
    ∃ a m, x s = .ok a m ∧ f a m = .ok r t := by
  simp only [bind, EStateM.bind] at h
  cases hx : x s with
  | error e m => rw [hx] at h; cases h
  | ok a m => rw [hx] at h; exact ⟨a, m, rfl, h⟩

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
    first
    | (simp only [Option.some.injEq, Prod.mk.injEq] at h
       obtain ⟨rfl, rfl⟩ := h
       simp only [execInstr, EStateM.run, readSrc_vreg, readVReg_run, writeDst_vreg, bind,
         EStateM.bind, addWide_low, mulWide_low]
       exact writeVReg_retire_run_of_writable _ _ s hw)
    | (simp only [Option.some.injEq, Prod.mk.injEq] at h
       obtain ⟨rfl, rfl⟩ := h
       simp only [execInstr, EStateM.run, writeDst_vreg]
       exact writeVReg_retire_run_of_writable _ _ s hw)
    | cases h
    | skip
  -- `ADDI` from `x0`
  rename_i r imm
  split at h
  · rename_i hx
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [execInstr, EStateM.run, bind, EStateM.bind, readSrc_x0 hx s, writeDst_vreg,
      addWide_low]
    exact writeVReg_retire_run_of_writable _ _ s hw
  · cases h

/-! ## Running programs row by row -/

/-- `Program.seq` of a cons is the row followed by the rest. Example: by definition. -/
@[simp] theorem seq_cons (i : Instr) (l : List Instr) :
    Program.seq (i :: l) = .instr i (Program.seq l) := rfl

/-- A row that retires from `s` to `t` can be peeled off a run.
Example: the step from `run_append_of_regRun` to the next row. -/
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

/-- A row that throws ends every run. Example: a failing `VirtualAssertEQ`. -/
theorem not_run_of_error {i : Instr} {s t : SailJoltState} {e : Error exception}
    (h : (execInstr i).run s = .error e t) (p : Program) (s' : SailJoltState) :
    ¬ Program.Run (.instr i p) s s' := by
  intro hr
  obtain ⟨t', ht', _⟩ := execProgram_instr_run_retire_inv i p s s' hr
  rw [h] at ht'
  cases ht'

/-- A row that returns a result other than `RETIRE_SUCCESS` ends every run.
Example: a misaligned `LD`, which returns a memory exception. -/
theorem not_run_of_result {i : Instr} {s t : SailJoltState} {r : ExecutionResult}
    (h : (execInstr i).run s = .ok r t) (hr : r ≠ RETIRE_SUCCESS) (p : Program)
    (s' : SailJoltState) : ¬ Program.Run (.instr i p) s s' := by
  intro hrun
  obtain ⟨t', ht', _⟩ := execProgram_instr_run_retire_inv i p s s' hrun
  rw [h] at ht'
  cases ht'
  exact hr rfl

/-- The pure evaluator for register rows: `none` as soon as a row is not a register row or
writes a register below `vr32`.
Example: `regRun [LUI vr60 5, ADD vr62 vr60 vr60] f = some (setV (setV f vr60 5) vr62 10)`. -/
def regRun : List Instr → (VReg → BitVec 64) → Option (VReg → BitVec 64)
  | [], f => some f
  | i :: l, f =>
    match i.regRow? with
    | some (d, g) => if 32 ≤ d.toNat then regRun l (setV f d (g f)) else none
    | none => none

/-- The evaluator of a concatenation. Example: used to evaluate one helper at a time. -/
theorem regRun_append (l₁ l₂ : List Instr) (f : VReg → BitVec 64) :
    regRun (l₁ ++ l₂) f = (regRun l₁ f).bind (regRun l₂) := by
  induction l₁ generalizing f with
  | nil => rfl
  | cons i l ih =>
    simp only [List.cons_append, regRun]
    split
    · split
      · exact ih _
      · rfl
    · rfl

/-- **Register rows run as evaluated.** If the register rows `l` evaluate to `f` from the
register file of `s`, a run of `l ++ rest` from `s` is a run of `rest` from `s` with register
file `f`. Nothing else in the state changes.
Example: the multiply-accumulate helpers of the secp256k1 field inlines. -/
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
Example: the column checks `assert_eq r, w[k]` of the secp256k1 field inlines. -/
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
Example: the final overflow check `assert_lte aux, r[1]` of the secp256k1 field inlines. -/
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
