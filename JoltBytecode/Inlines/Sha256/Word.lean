import JoltBytecode.Inlines.Blake2b.Compress
import JoltBytecode.Inlines.Sha256.Rows
import JoltBytecode.InstructionEquivalence.ProofSupport.ValueLemmas

/-!
# The rounds of SHA-256 on 32-bit words

SHA-256 keeps each 32-bit word in the low half of a 64-bit register and never cleans the high
half: `ADD`, `AND`, `XOR` and their immediate forms leave junk above bit 31, and the 32-bit
rows (`VirtualROTRIW`, `VirtualXORROTW*`, `VirtualSRLIW`) read only the low half. So the round
rows are best read on the low words alone. This module sets that up:

* `lo f` is the low-word view of a register file, and `row32?` gives the low word that a round
  row writes as a function of the low words it reads. `regRun_of_run32` lifts a run of the
  32-bit evaluator `run32` to a run of `regRun` with the same low words.
* `Runs l L L' W` says that the rows `l` take the low-word file `L` to `L'` and write only
  registers in `W`.
* `add_spec`, `xor_spec`, `and_spec`, `bigSigma1_spec`, `bigSigma0_spec`, `ch_spec`, `maj_spec`
  and `updateRows_spec` give the value and the written registers of each block of
  `Sha256.Rows`, for registers and for folded constants alike.
-/

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail LeanRV64D
  LeanRV64D.Functions

set_option autoImplicit false

namespace JoltISA.Inlines.Sha256

open JoltSpec.Sha256

/-! ## Words -/

/-- Sail's `extractLsb x 31 0` is the low word.
Example: `extractLsb 0x1_0000_0002#64 31 0 = 2#32`. -/
theorem extractLsb_lo (x : BitVec 64) : Sail.BitVec.extractLsb x 31 0 = x.setWidth 32 := by
  unfold Sail.BitVec.extractLsb
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_extractLsb]
  simp

/-- Zero-extending a word and taking the low word gives the word back.
Example: `(zero_extend (m := 64) 5#32).setWidth 32 = 5#32`. -/
theorem zero_extend_lo (v : BitVec 32) : (zero_extend (m := 64) v).setWidth 32 = v := by
  unfold zero_extend Sail.BitVec.zeroExtend
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [hi]

/-- Sign-extending a word and taking the low word gives the word back.
Example: `((-1#32).signExtend 64).setWidth 32 = -1#32`. -/
theorem signExtend_lo (v : BitVec 32) : (v.signExtend 64).setWidth 32 = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_signExtend, hi, decide_true,
    Bool.true_and, show i < 64 by omega, ↓reduceIte]

/-- Bit `i` of a word rotated right by `r` is bit `(i + r) mod 32`.
Example: bit 0 of `x.rotateRight 6` is bit 6 of `x`. -/
theorem getLsbD_rotr (x : BitVec 32) (r i : Nat) (hi : i < 32) :
    (x.rotateRight r).getLsbD i = x.getLsbD ((i + r) % 32) := by
  rw [BitVec.getLsbD_rotateRight]
  split
  · congr 1; omega
  · simp only [hi, decide_true, Bool.true_and]; congr 1; omega

/-- Rotation distributes over XOR.
Example: `(x ^^^ y).rotateRight 6 = x.rotateRight 6 ^^^ y.rotateRight 6`. -/
theorem rotr_xor (x y : BitVec 32) (r : Nat) :
    (x ^^^ y).rotateRight r = x.rotateRight r ^^^ y.rotateRight r := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [getLsbD_rotr _ _ _ hi, BitVec.getLsbD_xor]

/-- Two rotations are one rotation by the sum.
Example: `(x.rotateRight 18).rotateRight 19 = x.rotateRight 37`. -/
theorem rotr_rotr (x : BitVec 32) (a b : Nat) :
    (x.rotateRight a).rotateRight b = x.rotateRight (a + b) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_rotr _ _ _ hi, getLsbD_rotr _ _ _ (Nat.mod_lt _ (by decide)), getLsbD_rotr _ _ _ hi]
  congr 1
  omega

/-- A rotation by `r ≥ 32` is a rotation by `r - 32`.
Example: `x.rotateRight 43 = x.rotateRight 11`. -/
theorem rotr_sub (x : BitVec 32) (r : Nat) (hr : 32 ≤ r) :
    x.rotateRight r = x.rotateRight (r - 32) := by
  rw [← BitVec.rotateRight_mod_eq_rotateRight (r := r),
    ← BitVec.rotateRight_mod_eq_rotateRight (r := r - 32)]
  congr 1
  omega

/-- The trailing-zero count of `wordMask k` is `k`.
Example: `ctz (wordMask 18) = 18`. -/
theorem ctz_wordMask (k : Nat) (hk : k < 32) : ctz (wordMask k) = k := by
  have := ctz_word_shift_bitmask k hk
  simpa only [wordMask, Nat.shiftLeft_eq, one_mul] using this

/-- `wordMask k` is not zero.
Example: `wordMask 3 = 4294967288`. -/
theorem wordMask_ne_zero (k : Nat) (hk : k < 32) : wordMask k ≠ 0 := by
  unfold wordMask
  have : 2 ^ k < 2 ^ 32 := Nat.pow_lt_pow_right (by decide) hk
  omega

/-- The rows of Σ1 compute `Spec.large1`. -/
theorem large1_rows (x : BitVec 32) :
    (x ^^^ (x ^^^ x.rotateRight 18).rotateRight 19).rotateRight 6 = Spec.large1 x := by
  simp only [rotr_xor, rotr_rotr, Nat.reduceAdd, Spec.large1]
  rw [rotr_sub x 43 (by decide)]
  simp only [Nat.reduceSub]
  ac_rfl

/-- The rows of Σ0 compute `Spec.large0`. -/
theorem large0_rows (x : BitVec 32) :
    (x ^^^ (x ^^^ x.rotateRight 11).rotateRight 12).rotateRight 22 = Spec.large0 x := by
  simp only [rotr_xor, rotr_rotr, Nat.reduceAdd, Spec.large0]
  rw [rotr_sub x 34 (by decide), rotr_sub x 45 (by decide)]
  simp only [Nat.reduceSub]
  ac_rfl

/-- The rows of σ0 compute `Spec.small0`. -/
theorem small0_rows (x : BitVec 32) :
    (x ^^^ x.rotateRight 11).rotateRight 7 ^^^ x >>> 3 = Spec.small0 x := by
  simp only [rotr_xor, rotr_rotr, Nat.reduceAdd, Spec.small0]

/-- The rows of σ1 compute `Spec.small1`. -/
theorem small1_rows (x : BitVec 32) :
    (x ^^^ x.rotateRight 30).rotateRight 19 ^^^ x >>> 10 = Spec.small1 x := by
  simp only [rotr_xor, rotr_rotr, Nat.reduceAdd, Spec.small1]
  rw [rotr_sub x 49 (by decide)]
  simp only [Nat.reduceSub]
  ac_rfl

/-! ## The low-word view -/

/-- The low words of a register file.
Example: if `f vr48 = 0x1_0000_0002`, then `lo f vr48 = 2`. -/
def lo (f : VReg → BitVec 64) : VReg → BitVec 32 := fun r => (f r).setWidth 32

/-- The low-word file `L` with register `d` set to `v`.
Example: `set32 L vr48 7 vr48 = 7`. -/
def set32 (L : VReg → BitVec 32) (d : VReg) (v : BitVec 32) : VReg → BitVec 32 :=
  fun r => if r = d then v else L r

/-- Setting a register and taking low words commute.
Example: `lo (setV f vr48 0x1_0000_0002) = set32 (lo f) vr48 2`. -/
theorem lo_setV (f : VReg → BitVec 64) (d : VReg) (v : BitVec 64) :
    lo (setV f d v) = set32 (lo f) d (v.setWidth 32) := by
  funext r
  simp only [lo, setV, set32]
  split <;> rfl

/-- The round rows read as functions of low words: the destination and the low word written.
Example: `row32? (ADDI vr80 vr79 0x428a2f98) = some (vr80, fun L => L vr79 + 0x428a2f98)`. -/
def row32? : Instr → Option (VReg × ((VReg → BitVec 32) → BitVec 32))
  | .ADD (.vreg d) (.vreg x) (.vreg y) => some (d, fun L => L x + L y)
  | .ADDI (.vreg d) (.vreg x) imm => some (d, fun L => L x + w32 imm)
  | .AND (.vreg d) (.vreg x) (.vreg y) => some (d, fun L => L x &&& L y)
  | .ANDI (.vreg d) (.vreg x) imm => some (d, fun L => L x &&& w32 imm)
  | .XOR (.vreg d) (.vreg x) (.vreg y) => some (d, fun L => L x ^^^ L y)
  | .XORI (.vreg d) (.vreg x) imm => some (d, fun L => L x ^^^ w32 imm)
  | .ANDN (.vreg d) (.vreg x) (.vreg y) => some (d, fun L => L x &&& ~~~L y)
  | .VirtualROTRIW (.vreg d) (.vreg x) m => some (d, fun L => rotater (L x) (min (ctz m) 32))
  | .VirtualSRLIW (.vreg d) (.vreg x) m => some (d, fun L => if m = 0 then 0 else L x >>> ctz m)
  | .VirtualXORROTW22 (.vreg d) (.vreg x) (.vreg y) => some (d, fun L => rotater (L x ^^^ L y) 22)
  | .VirtualXORROTW19 (.vreg d) (.vreg x) (.vreg y) => some (d, fun L => rotater (L x ^^^ L y) 19)
  | .VirtualXORROTW12 (.vreg d) (.vreg x) (.vreg y) => some (d, fun L => rotater (L x ^^^ L y) 12)
  | .VirtualXORROTW7 (.vreg d) (.vreg x) (.vreg y) => some (d, fun L => rotater (L x ^^^ L y) 7)
  | .VirtualXORROTW6 (.vreg d) (.vreg x) (.vreg y) => some (d, fun L => rotater (L x ^^^ L y) 6)
  | _ => none

/-- **A round row writes a low word that depends only on low words.** It is a register row whose
value has, as low word, the `row32?` value of the low words.
Example: `ANDN` writes `x &&& ~~~y`, whose low word is `lo x &&& ~~~lo y`. -/
theorem regRow_of_row32 {i : Instr} {d : VReg} {g : (VReg → BitVec 32) → BitVec 32}
    (h : row32? i = some (d, g)) :
    ∃ g64, i.regRow? = some (d, g64) ∧ ∀ f, (g64 f).setWidth 32 = g (lo f) := by
  unfold row32? at h
  split at h
  all_goals
    try simp only [Option.some.injEq, Prod.mk.injEq] at h
    try obtain ⟨rfl, rfl⟩ := h
    try refine ⟨_, rfl, fun f => ?_⟩
  all_goals
    try simp only [lo, BitVec.setWidth_add _ _ (by decide : 32 ≤ 64), Riscv.andi,
      BitVec.setWidth_and, BitVec.setWidth_xor, BitVec.setWidth_not (by decide : 32 ≤ 64),
      jolt_xor_value, jolt_andn_value, w32]
  · simp only [jolt_virtual_rotriw_value, zero_extend_lo, extractLsb_lo]
  · simp only [jolt_virtual_srliw_value]
    split
    · rfl
    · exact signExtend_lo _
  all_goals
    try simp only [jolt_virtual_xorrotw_value, zero_extend_lo, extractLsb_lo]

/-- The 32-bit evaluator of round rows: `none` as soon as a row is not a round row or writes a
register below `vr32`.
Example: `run32 [ADD vr80 vr80 vr82] L = some (set32 L vr80 (L vr80 + L vr82))`. -/
def run32 : List Instr → (VReg → BitVec 32) → Option (VReg → BitVec 32)
  | [], L => some L
  | i :: l, L =>
    match row32? i with
    | some (d, g) => if 32 ≤ d.toNat then run32 l (set32 L d (g L)) else none
    | none => none

/-- Evaluating a concatenation evaluates the first part, then the second.
Example: `run32 (l₁ ++ []) L = run32 l₁ L`. -/
theorem run32_append (l₁ l₂ : List Instr) (L : VReg → BitVec 32) :
    run32 (l₁ ++ l₂) L = (run32 l₁ L).bind (run32 l₂) := by
  induction l₁ generalizing L with
  | nil => rfl
  | cons i l ih =>
    rw [List.cons_append]
    cases h : row32? i with
    | none => simp only [run32, h, Option.bind_none]
    | some p =>
      obtain ⟨d, g⟩ := p
      by_cases hd : 32 ≤ d.toNat
      · simp only [run32, h, hd, ↓reduceIte, ih]
      · simp only [run32, h, hd, ↓reduceIte, Option.bind_none]

/-- **The 32-bit evaluator runs the rows.** If `run32` takes the low words of `f` to `L'`, then
`regRun` runs the same rows from `f` to a file whose low words are `L'`.
Example: from `run32 [ADD vr80 vr80 vr82] (lo f) = some L'`, `regRun` gives
`setV f vr80 (f vr80 + f vr82)`, whose low words are `L'`. -/
theorem regRun_of_run32 {l : List Instr} {f : VReg → BitVec 64} {L' : VReg → BitVec 32}
    (h : run32 l (lo f) = some L') : ∃ f', regRun l f = some f' ∧ lo f' = L' := by
  induction l generalizing f with
  | nil =>
    simp only [run32, Option.some.injEq] at h
    exact ⟨f, rfl, h⟩
  | cons i l ih =>
    simp only [run32] at h
    split at h
    · rename_i d g hrow
      split at h
      · rename_i hd
        obtain ⟨g64, hrow64, hg⟩ := regRow_of_row32 hrow
        rw [← hg, ← lo_setV] at h
        obtain ⟨f', h1, h2⟩ := ih h
        exact ⟨f', by rw [regRun_cons_of hrow64 hd]; exact h1, h2⟩
      · cases h
    · cases h

/-! ## Runs that write a set of registers -/

/-- The rows `l` take the low-word file `L` to `L'`, and every row writes a register in `W`.
Example: `Runs [ADD vr80 vr80 vr82] L (set32 L vr80 (L vr80 + L vr82)) (· = vr80)`. -/
def Runs (l : List Instr) (L L' : VReg → BitVec 32) (W : VReg → Prop) : Prop :=
  run32 l L = some L' ∧ ∀ i ∈ l, ∀ d g, row32? i = some (d, g) → W d

/-- No rows: nothing changes. -/
theorem Runs.nil (L : VReg → BitVec 32) (W : VReg → Prop) : Runs [] L L W :=
  ⟨rfl, by simp⟩

/-- One round row with a writable destination. -/
theorem Runs.single {i : Instr} {d : VReg} {g : (VReg → BitVec 32) → BitVec 32}
    (h : row32? i = some (d, g)) (hd : 32 ≤ d.toNat) (L : VReg → BitVec 32) :
    Runs [i] L (set32 L d (g L)) (· = d) := by
  refine ⟨by simp only [run32, h, hd, ↓reduceIte], ?_⟩
  intro j hj d' g' h'
  simp only [List.mem_singleton] at hj
  subst hj
  rw [h] at h'
  cases h'
  rfl

/-- Runs compose. -/
theorem Runs.append {l₁ l₂ : List Instr} {L L₁ L₂ : VReg → BitVec 32} {W₁ W₂ : VReg → Prop}
    (h₁ : Runs l₁ L L₁ W₁) (h₂ : Runs l₂ L₁ L₂ W₂) :
    Runs (l₁ ++ l₂) L L₂ (fun r => W₁ r ∨ W₂ r) := by
  refine ⟨by rw [run32_append, h₁.1, Option.bind_some, h₂.1], ?_⟩
  intro i hi d g h
  rcases List.mem_append.1 hi with hi | hi
  · exact Or.inl (h₁.2 i hi d g h)
  · exact Or.inr (h₂.2 i hi d g h)

/-- A run that writes in `W` writes in any larger set. -/
theorem Runs.mono {l : List Instr} {L L' : VReg → BitVec 32} {W W' : VReg → Prop}
    (h : Runs l L L' W) (hW : ∀ r, W r → W' r) : Runs l L L' W' :=
  ⟨h.1, fun i hi d g hg => hW d (h.2 i hi d g hg)⟩

/-- **A run changes only the registers it writes.** -/
theorem Runs.frame {l : List Instr} {L L' : VReg → BitVec 32} {W : VReg → Prop}
    (h : Runs l L L' W) (r : VReg) (hr : ¬ W r) : L' r = L r := by
  obtain ⟨hrun, hW⟩ := h
  induction l generalizing L with
  | nil =>
    simp only [run32, Option.some.injEq] at hrun
    rw [hrun]
  | cons i l ih =>
    simp only [run32] at hrun
    split at hrun
    · rename_i d g hrow
      split at hrun
      · have h1 := ih hrun (fun j hj => hW j (List.mem_cons_of_mem _ hj))
        rw [h1]
        have hd : d ≠ r := fun e => hr (e ▸ hW i List.mem_cons_self d g hrow)
        simp only [set32, Ne.symm hd, ↓reduceIte]
      · cases hrun
    · cases hrun

/-- **A low-word run is a register run.** If the rows `l` take the low words of `f` to `L'` and
write only registers in `W`, then `regRun` runs them from `f` to a file whose low words are `L'`
and that keeps every register outside `W` whole.
Example: `Runs [ADD vr80 vr80 vr82] (lo f) L' (· = vr80)` gives a file equal to `f` except at
`vr80`. -/
theorem Runs.lift {l : List Instr} {f : VReg → BitVec 64} {L' : VReg → BitVec 32}
    {W : VReg → Prop} (h : Runs l (lo f) L' W) :
    ∃ f', regRun l f = some f' ∧ lo f' = L' ∧ ∀ r, ¬ W r → f' r = f r := by
  obtain ⟨hrun, hW⟩ := h
  induction l generalizing f with
  | nil =>
    simp only [run32, Option.some.injEq] at hrun
    exact ⟨f, rfl, hrun, fun _ _ => rfl⟩
  | cons i l ih =>
    simp only [run32] at hrun
    split at hrun
    · rename_i d g hrow
      split at hrun
      · rename_i hd
        obtain ⟨g64, hrow64, hg⟩ := regRow_of_row32 hrow
        rw [← hg, ← lo_setV] at hrun
        obtain ⟨f', h1, h2, h3⟩ := ih hrun (fun j hj => hW j (List.mem_cons_of_mem _ hj))
        refine ⟨f', by rw [regRun_cons_of hrow64 hd]; exact h1, h2, fun r hr => ?_⟩
        have hrd : r ≠ d := fun e => hr (e ▸ hW i List.mem_cons_self d g hrow)
        rw [h3 r hr]
        simp only [setV, hrd, ↓reduceIte]
      · cases hrun
    · cases hrun

/-! ## Values -/

/-- The low word of a value in the low-word file `L`.
Example: `(Val.imm 0x108909ae5).eval L = 0x08909ae5`. -/
def Val.eval (L : VReg → BitVec 32) : Val → BitVec 32
  | .reg r => L r
  | .imm v => w32 v

/-- The value is a constant or a register outside `W`. -/
def Val.Avoids (x : Val) (W : VReg → Prop) : Prop := ∀ r, x = .reg r → ¬ W r

/-- The value is a constant or the register `d`: where a block leaves its result. -/
def Val.At (x : Val) (d : VReg) : Prop := x = .reg d ∨ ∃ v, x = .imm v

/-- A value at `d` avoids every set without `d`. -/
theorem Val.At.avoids {x : Val} {d : VReg} {W : VReg → Prop} (h : x.At d) (hW : ¬ W d) :
    x.Avoids W := by
  rintro r rfl
  rcases h with h | ⟨v, h⟩
  · cases h; exact hW
  · cases h

/-- A value that avoids the registers a run writes reads the same after the run. -/
theorem Runs.eval {l : List Instr} {L L' : VReg → BitVec 32} {W : VReg → Prop}
    (h : Runs l L L' W) {x : Val} (hx : x.Avoids W) : x.eval L' = x.eval L := by
  cases x with
  | reg r => exact h.frame r (hx r rfl)
  | imm v => rfl

/-- A value avoids a smaller set. -/
theorem Val.Avoids.mono {x : Val} {W W' : VReg → Prop} (h : x.Avoids W) (hW : ∀ r, W' r → W r) :
    x.Avoids W' :=
  fun r hr hw => h r hr (hW r hw)

/-! ## Folded operations -/

/-- **A folded binary operation.** `bin` writes only `d`, leaves its result at `d`, and the
result is the operation on the low words of the operands, when the row and the fold both compute
the operation on low words and the operation is commutative (for the swapped I-row). -/
theorem bin_spec {rk : Dst → Src → Src → Instr} {ik : Dst → Src → BitVec 64 → Instr}
    {fold : BitVec 64 → BitVec 64 → BitVec 64} (op : BitVec 32 → BitVec 32 → BitVec 32)
    (hrk : ∀ d x y, row32? (rk (.vreg d) (.vreg x) (.vreg y)) = some (d, fun L => op (L x) (L y)))
    (hik : ∀ d x i, row32? (ik (.vreg d) (.vreg x) i) = some (d, fun L => op (L x) (w32 i)))
    (hfold : ∀ i j, w32 (fold i j) = op (w32 i) (w32 j)) (hcomm : ∀ a b, op a b = op b a)
    (x y : Val) (d : VReg) (hd : 32 ≤ d.toNat) (L : VReg → BitVec 32) :
    ∃ L', Runs (bin rk ik fold x y d).1 L L' (· = d) ∧
      (bin rk ik fold x y d).2.eval L' = op (x.eval L) (y.eval L) ∧
      (bin rk ik fold x y d).2.At d := by
  cases x with
  | reg x =>
    cases y with
    | reg y =>
      exact ⟨_, Runs.single (hrk d x y) hd L, by simp [bin, Val.eval, set32], Or.inl rfl⟩
    | imm j =>
      exact ⟨_, Runs.single (hik d x j) hd L, by simp [bin, Val.eval, set32], Or.inl rfl⟩
  | imm i =>
    cases y with
    | reg y =>
      exact ⟨_, Runs.single (hik d y i) hd L, by simp [bin, Val.eval, set32, hcomm],
        Or.inl rfl⟩
    | imm j =>
      exact ⟨L, Runs.nil L _, by simp [bin, Val.eval, hfold], Or.inr ⟨_, rfl⟩⟩

/-- `add` adds low words. -/
theorem add_spec (x y : Val) (d : VReg) (hd : 32 ≤ d.toNat) (L : VReg → BitVec 32) :
    ∃ L', Runs (add x y d).1 L L' (· = d) ∧
      (add x y d).2.eval L' = x.eval L + y.eval L ∧ (add x y d).2.At d :=
  bin_spec (· + ·) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    (fun i j => BitVec.setWidth_add i j (by decide)) BitVec.add_comm x y d hd L

/-- `xor` XORs low words. -/
theorem xor_spec (x y : Val) (d : VReg) (hd : 32 ≤ d.toNat) (L : VReg → BitVec 32) :
    ∃ L', Runs (xor x y d).1 L L' (· = d) ∧
      (xor x y d).2.eval L' = x.eval L ^^^ y.eval L ∧ (xor x y d).2.At d :=
  bin_spec (· ^^^ ·) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    (fun _ _ => BitVec.setWidth_xor) BitVec.xor_comm x y d hd L

/-- `and` ANDs low words. -/
theorem and_spec (x y : Val) (d : VReg) (hd : 32 ≤ d.toNat) (L : VReg → BitVec 32) :
    ∃ L', Runs (and x y d).1 L L' (· = d) ∧
      (and x y d).2.eval L' = x.eval L &&& y.eval L ∧ (and x y d).2.At d :=
  bin_spec (· &&& ·) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    (fun _ _ => BitVec.setWidth_and) BitVec.and_comm x y d hd L

end JoltISA.Inlines.Sha256
