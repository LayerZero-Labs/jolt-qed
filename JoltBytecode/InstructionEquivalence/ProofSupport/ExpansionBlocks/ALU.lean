import JoltBytecode.JoltISA.Expansions.ALU
import JoltBytecode.InstructionEquivalence.ProofSupport.InstructionLemmas.Mul
import JoltBytecode.InstructionEquivalence.ProofSupport.InstructionLemmas.VirtualPow2
import JoltBytecode.InstructionEquivalence.ProofSupport.InstructionLemmas.VirtualShiftRightBitmask
import JoltBytecode.InstructionEquivalence.ProofSupport.InstructionLemmas.VirtualSRL
import JoltBytecode.InstructionEquivalence.ProofSupport.InstructionLemmas.VirtualSRLI
import JoltBytecode.InstructionEquivalence.ProofSupport.Lemmas
import JoltBytecode.InstructionEquivalence.ProofSupport.RegisterAccess
import JoltBytecode.InstructionEquivalence.ProofSupport.ValueLemmas

/-!
# ALU expansion block semantics

These lemmas describe source-instruction inline blocks after they have been
lowered to real Jolt ISA rows.  They keep instruction-equivalence proofs from
depending on source-level pseudo-instructions that are not part of `JoltISA.Instr`.
-/

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace JoltISA

/-- The Rust `SLLI` block's `VirtualMULI` value is the same left shift that
Sail uses for `SLLI`. -/
theorem slli_block_value_eq (x : BitVec 64) (shamt : BitVec 6) :
    jolt_virtual_muli_value x (slliMultiplier shamt) = shift_bits_left x shamt := by
  unfold jolt_virtual_muli_value slliMultiplier shift_bits_left
  exact (shiftLeft_eq_mul_pow2 x shamt.toNat).symm

/-- `VirtualMULI` by eight is the lowered form of shifting left by three. -/
theorem virtual_muli_eight_eq_shift_left_three (x : BitVec 64) :
    jolt_virtual_muli_value x (8 : BitVec 64) =
      shift_bits_left x (3 : BitVec 6) := by
  simpa [slliMultiplier] using slli_block_value_eq x (3 : BitVec 6)

/-- Narrowing a 64-bit word to six bits is the same as extracting bits `5:0`. -/
theorem setWidth6_eq_extractLsb_5_0 (v : BitVec 64) :
    v.setWidth 6 = Sail.BitVec.extractLsb v 5 0 := by
  unfold Sail.BitVec.extractLsb
  ext i
  simp

/-- Multiplication by the `VirtualPow2` value is the same left shift used by
Sail, with the shift amount taken from the source word's low six bits. -/
theorem mul_jolt_virtual_pow2_value_eq_shift_bits_left
    (x shift : BitVec 64) :
    x * jolt_virtual_pow2_value shift =
      shift_bits_left x (Sail.BitVec.extractLsb shift 5 0) := by
  unfold jolt_virtual_pow2_value shift_bits_left
  rw [← setWidth6_eq_extractLsb_5_0 shift]
  exact (shiftLeft_eq_mul_pow2 x (shift.setWidth 6).toNat).symm

/-- A `VirtualSRL` using the standard lowered bitmask computes Sail's logical
right shift by the source word's low six bits. -/
theorem virtual_srl_shift_right_bitmask_value_eq
    (x shift : BitVec 64) :
    jolt_virtual_srl_value x (jolt_virtual_shift_right_bitmask_value shift) =
      shift_bits_right x (Sail.BitVec.extractLsb shift 5 0) := by
  unfold jolt_virtual_srl_value shift_bits_right
  rw [ctz_jolt_virtual_shift_right_bitmask_value]
  rw [← setWidth6_eq_extractLsb_5_0 shift]
  simp

/-- The encoded `SRAI` bitmask has trailing-zero count equal to the immediate
shift amount. -/
theorem ctz_sraiBitmask (shamt : BitVec 6) :
    ctz (sraiBitmask shamt) = shamt.toNat := by
  unfold sraiBitmask srliBitmask
  simp only [Nat.shiftLeft_eq, one_mul]
  set shift := shamt.toNat
  have h_lt : shift < 64 := by
    have := shamt.isLt
    norm_num at this
    exact this
  have h_diff_pos : 0 < 64 - shift := by omega
  have h_m_pos : 0 < 2 ^ (64 - shift) - 1 := by
    have : 2 ≤ 2 ^ (64 - shift) :=
      le_trans (show (2 : Nat) ≤ 2 ^ 1 from by norm_num)
        (Nat.pow_le_pow_right (by omega) (by omega))
    omega
  rw [mul_comm, ctz_mul_pow2 shift h_m_pos, ctz_of_odd (pow2_sub_one_odd h_diff_pos)]
  omega

/-- The encoded `SRLI` bitmask has trailing-zero count equal to the immediate
shift amount. -/
theorem ctz_srliBitmask (shamt : BitVec 6) :
    ctz (srliBitmask shamt) = shamt.toNat := by
  simpa [sraiBitmask] using ctz_sraiBitmask shamt

/-- The Rust `SRLI` block's `VirtualSRLI` value is the same logical right
shift that Sail uses for `SRLI`. -/
theorem srli_block_value_eq (x : BitVec 64) (shamt : BitVec 6) :
    jolt_virtual_srli_value x (srliBitmask shamt) =
      shift_bits_right x shamt := by
  unfold jolt_virtual_srli_value shift_bits_right
  simp [ctz_srliBitmask]

/-- The Rust `SRAI` block's `VirtualSRAI` value is the same arithmetic right
shift that Sail uses for `SRAI`. -/
theorem srai_block_value_eq (x : BitVec 64) (shamt : BitVec 6) :
    jolt_virtual_srai_value x (sraiBitmask shamt) = shift_bits_right_arith x shamt := by
  unfold jolt_virtual_srai_value shift_bits_right_arith
  simp [Sail.BitVec.toNatInt, ctz_sraiBitmask]

/-- The lowered `SLLI` block from a real source to a virtual destination reads
the architectural source and writes the shifted value to the virtual register. -/
private theorem slli_block_run_vreg_xreg
    (vd : VReg) (rs : regidx) (shamt : BitVec 6)
    (js : SailJoltState) (x : BitVec 64)
    (h : rX_bits rs js.sail = .ok x js.sail)
    (hvd : WritableVReg vd) :
    (execInstr (.VirtualMULI (.vreg vd) (.xreg rs) (slliMultiplier shamt))).run js =
      .ok RETIRE_SUCCESS
        { sail := js.sail
          vregs := fun r => if r = vd then shift_bits_left x shamt else js.vregs r } := by
  have h_value :
      jolt_virtual_muli_value x (slliMultiplier shamt) = shift_bits_left x shamt :=
    slli_block_value_eq x shamt
  unfold WritableVReg at hvd
  unfold execInstr readSrc writeDst liftSail writeVReg
  simp only [h, h_value, bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    hvd, ↓reduceIte, modify, modifyGet, MonadStateOf.modifyGet,
    EStateM.modifyGet]

/-- The lowered `SLLI` block from a real source to a real destination reads the
architectural source and writes the shifted value through Sail. -/
private theorem slli_block_run_xreg_xreg
    (rd rs : regidx) (shamt : BitVec 6)
    (js : SailJoltState) (x : BitVec 64) (s' : SailState)
    (h : rX_bits rs js.sail = .ok x js.sail)
    (hw : wX_bits rd (shift_bits_left x shamt) js.sail = .ok () s') :
    (execInstr (.VirtualMULI (.xreg rd) (.xreg rs) (slliMultiplier shamt))).run js =
      .ok RETIRE_SUCCESS { sail := s', vregs := js.vregs } := by
  have h_value :
      jolt_virtual_muli_value x (slliMultiplier shamt) = shift_bits_left x shamt :=
    slli_block_value_eq x shamt
  unfold execInstr readSrc writeDst liftSail
  simp only [h, h_value, hw, bind, EStateM.bind, pure, EStateM.pure, EStateM.run]

/-- The lowered `SLLI` block from a virtual source to a virtual destination
writes the shifted virtual-register value and leaves Sail unchanged. -/
private theorem slli_block_run_vreg_vreg
    (vd vs : VReg) (shamt : BitVec 6)
    (js : SailJoltState) (hvd : WritableVReg vd) :
    (execInstr (.VirtualMULI (.vreg vd) (.vreg vs) (slliMultiplier shamt))).run js =
      .ok RETIRE_SUCCESS
        { sail := js.sail
          vregs := fun r => if r = vd then shift_bits_left (js.vregs vs) shamt else js.vregs r } := by
  have h_value :
      jolt_virtual_muli_value (js.vregs vs) (slliMultiplier shamt) =
        shift_bits_left (js.vregs vs) shamt :=
    slli_block_value_eq (js.vregs vs) shamt
  unfold WritableVReg at hvd
  unfold execInstr readSrc writeDst readVReg writeVReg
  simp only [h_value, bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get,
    hvd, ↓reduceIte, modify, modifyGet, MonadStateOf.modifyGet,
    EStateM.modifyGet]

/-- Existential package for the lowered `SLLI` block from a real source to a
virtual destination.  It exposes the source read, the virtual-register write,
preservation of other virtual registers, and the block's effect on every
continuation program. -/
theorem exists_state_after_slli_block_run_vreg_xreg
    (vd : VReg) (rs : regidx) (shamt : BitVec 6)
    (js : SailJoltState) (x : BitVec 64)
    (h : rX_bits rs js.sail = .ok x js.sail)
    (hvd : WritableVReg vd) :
    ∃ js',
      rX_bits rs js.sail = .ok x js.sail ∧
      js'.sail = js.sail ∧
      js'.vregs vd = shift_bits_left x shamt ∧
      (∀ r, r ≠ vd → js'.vregs r = js.vregs r) ∧
      ∀ tail,
        (execProgram (slliBlock (.vreg vd) (.xreg rs) shamt tail)).run js =
          (execProgram tail).run js' := by
  let js' : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = vd then shift_bits_left x shamt else js.vregs r }
  refine ⟨js', h, rfl, ?_, ?_, ?_⟩
  · simp [js']
  · intro r hne
    simp [js', hne]
  · intro tail
    unfold slliBlock
    rw [execProgram_instr_run_retire _ _ js js'
      (by simpa only [js'] using slli_block_run_vreg_xreg vd rs shamt js x h hvd)]

/-- Existential package for the lowered `SLLI` block from a real source to a
real destination.  It exposes the source read, the architectural write,
preservation of virtual registers, and the block's effect on every continuation
program. -/
theorem exists_state_after_slli_block_run_xreg_xreg
    (rd rs : regidx) (shamt : BitVec 6)
    (js : SailJoltState) (x : BitVec 64)
    (h : rX_bits rs js.sail = .ok x js.sail) :
    ∃ js',
      rX_bits rs js.sail = .ok x js.sail ∧
      js'.sail = stateAfterWrite js.sail rd (shift_bits_left x shamt) ∧
      js'.vregs = js.vregs ∧
      ∀ tail,
        (execProgram (slliBlock (.xreg rd) (.xreg rs) shamt tail)).run js =
          (execProgram tail).run js' := by
  obtain ⟨s', h_write⟩ := wX_shape rd (shift_bits_left x shamt) js.sail
  let js' : SailJoltState := { sail := s', vregs := js.vregs }
  have h_sail_after_slli :
      s' = stateAfterWrite js.sail rd (shift_bits_left x shamt) :=
    wX_bits_eq_stateAfterWrite rd (shift_bits_left x shamt) js.sail s' h_write
  refine ⟨js', h, ?_, rfl, ?_⟩
  · exact h_sail_after_slli
  · intro tail
    unfold slliBlock
    rw [execProgram_instr_run_retire _ _ js js'
      (by simpa only [js'] using slli_block_run_xreg_xreg rd rs shamt js x s' h h_write)]

/-- Existential package for the lowered `SLLI` block from a virtual source to a
virtual destination.  It exposes the shifted value, preservation of other
virtual registers, and the block's effect on every continuation program. -/
theorem exists_state_after_slli_block_run_vreg_vreg
    (vd vs : VReg) (shamt : BitVec 6)
    (js : SailJoltState) (hvd : WritableVReg vd) :
    ∃ js',
      js'.sail = js.sail ∧
      js'.vregs vd = shift_bits_left (js.vregs vs) shamt ∧
      (∀ r, r ≠ vd → js'.vregs r = js.vregs r) ∧
      ∀ tail,
        (execProgram (slliBlock (.vreg vd) (.vreg vs) shamt tail)).run js =
          (execProgram tail).run js' := by
  let js' : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = vd then shift_bits_left (js.vregs vs) shamt else js.vregs r }
  refine ⟨js', rfl, ?_, ?_, ?_⟩
  · simp [js']
  · intro r hne
    simp [js', hne]
  · intro tail
    unfold slliBlock
    rw [execProgram_instr_run_retire _ _ js js'
      (by simpa only [js'] using slli_block_run_vreg_vreg vd vs shamt js hvd)]

/-- Existential package for the lowered `SLL` block from virtual sources to a
virtual destination.  The scratch register first receives `2 ^ shift[5:0]`,
then the destination receives the corresponding left shift. -/
theorem exists_state_after_sll_block_run_vreg_vreg_vreg
    (vd value shift scratch : VReg) (js : SailJoltState)
    (h_value_ne_scratch : value ≠ scratch)
    (hvd : WritableVReg vd) (hscratch : WritableVReg scratch) :
    ∃ js',
      js'.sail = js.sail ∧
      js'.vregs vd =
        shift_bits_left (js.vregs value) (Sail.BitVec.extractLsb (js.vregs shift) 5 0) ∧
      (∀ r, r ≠ vd → r ≠ scratch → js'.vregs r = js.vregs r) ∧
      ∀ tail,
        (execProgram
          (sllBlock (.vreg vd) (.vreg value) (.vreg shift) scratch tail)).run js =
          (execProgram tail).run js' := by
  let js_pow2 : SailJoltState :=
    { sail := js.sail
      vregs := fun r =>
        if r = scratch then jolt_virtual_pow2_value (js.vregs shift) else js.vregs r }
  let js' : SailJoltState :=
    { sail := js.sail
      vregs := fun r =>
        if r = vd then js_pow2.vregs value * js_pow2.vregs scratch else js_pow2.vregs r }
  have hpow2 :
      (execInstr (.VirtualPow2 (.vreg scratch) (.vreg shift))).run js =
        .ok RETIRE_SUCCESS js_pow2 := by
    simpa [js_pow2] using virtual_pow2_run_vreg_vreg scratch shift js hscratch
  have hmul :
      (execInstr (.MUL (.vreg vd) (.vreg value) (.vreg scratch))).run js_pow2 =
        .ok RETIRE_SUCCESS js' := by
    simpa [js'] using mul_run_vreg_vreg_vreg vd value scratch js_pow2 hvd
  refine ⟨js', rfl, ?_, ?_, ?_⟩
  · dsimp [js']
    simp only [↓reduceIte]
    change js_pow2.vregs value * js_pow2.vregs scratch =
      shift_bits_left (js.vregs value) (Sail.BitVec.extractLsb (js.vregs shift) 5 0)
    have h_value : js_pow2.vregs value = js.vregs value := by
      simp [js_pow2, h_value_ne_scratch]
    have h_scratch : js_pow2.vregs scratch = jolt_virtual_pow2_value (js.vregs shift) := by
      simp [js_pow2]
    rw [h_value, h_scratch]
    exact mul_jolt_virtual_pow2_value_eq_shift_bits_left (js.vregs value) (js.vregs shift)
  · intro r h_ne_dst h_ne_scratch
    dsimp [js']
    simp [h_ne_dst, js_pow2, h_ne_scratch]
  · intro tail
    unfold sllBlock
    rw [execProgram_instr_run_retire _ _ js js_pow2 hpow2]
    rw [execProgram_instr_run_retire _ _ js_pow2 js' hmul]

/-- Existential package for the lowered `SLL` block from a real source and a
virtual shift amount to a virtual destination.  The scratch register first
receives `2 ^ shift[5:0]`, then the destination receives the corresponding
left shift of the real source value. -/
theorem exists_state_after_sll_block_run_vreg_xreg_vreg
    (vd : VReg) (value : regidx) (shift scratch : VReg)
    (js : SailJoltState) (x : BitVec 64)
    (h_read : rX_bits value js.sail = .ok x js.sail)
    (hvd : WritableVReg vd) (hscratch : WritableVReg scratch) :
    ∃ js',
      rX_bits value js.sail = .ok x js.sail ∧
      js'.sail = js.sail ∧
      js'.vregs vd =
        shift_bits_left x (Sail.BitVec.extractLsb (js.vregs shift) 5 0) ∧
      (∀ r, r ≠ vd → r ≠ scratch → js'.vregs r = js.vregs r) ∧
      ∀ tail,
        (execProgram
          (sllBlock (.vreg vd) (.xreg value) (.vreg shift) scratch tail)).run js =
          (execProgram tail).run js' := by
  let js_pow2 : SailJoltState :=
    { sail := js.sail
      vregs := fun r =>
        if r = scratch then jolt_virtual_pow2_value (js.vregs shift) else js.vregs r }
  let js' : SailJoltState :=
    { sail := js.sail
      vregs := fun r =>
        if r = vd then x * js_pow2.vregs scratch else js_pow2.vregs r }
  have hpow2 :
      (execInstr (.VirtualPow2 (.vreg scratch) (.vreg shift))).run js =
        .ok RETIRE_SUCCESS js_pow2 := by
    simpa [js_pow2] using virtual_pow2_run_vreg_vreg scratch shift js hscratch
  have h_read_pow2 : rX_bits value js_pow2.sail = .ok x js_pow2.sail := by
    exact h_read
  have hmul :
      (execInstr (.MUL (.vreg vd) (.xreg value) (.vreg scratch))).run js_pow2 =
        .ok RETIRE_SUCCESS js' := by
    simpa [js'] using mul_run_vreg_xreg_vreg vd value scratch js_pow2 x h_read_pow2 hvd
  refine ⟨js', h_read, rfl, ?_, ?_, ?_⟩
  · dsimp [js']
    simp only [↓reduceIte]
    change x * js_pow2.vregs scratch =
      shift_bits_left x (Sail.BitVec.extractLsb (js.vregs shift) 5 0)
    have h_scratch :
        js_pow2.vregs scratch = jolt_virtual_pow2_value (js.vregs shift) := by
      simp [js_pow2]
    rw [h_scratch]
    exact mul_jolt_virtual_pow2_value_eq_shift_bits_left x (js.vregs shift)
  · intro r h_ne_dst h_ne_scratch
    dsimp [js']
    simp [h_ne_dst, js_pow2, h_ne_scratch]
  · intro tail
    unfold sllBlock
    rw [execProgram_instr_run_retire _ _ js js_pow2 hpow2]
    rw [execProgram_instr_run_retire _ _ js_pow2 js' hmul]

/-- The lowered `SRLI` block from a virtual source to a virtual destination
writes the logical right shift selected by the immediate. -/
private theorem srli_block_run_vreg_vreg
    (vd vs : VReg) (shamt : BitVec 6)
    (js : SailJoltState) (hvd : WritableVReg vd) :
    (execInstr (.VirtualSRLI (.vreg vd) (.vreg vs) (srliBitmask shamt))).run js =
      .ok RETIRE_SUCCESS
        { sail := js.sail
          vregs := fun r =>
            if r = vd then shift_bits_right (js.vregs vs) shamt else js.vregs r } := by
  have h_value :
      jolt_virtual_srli_value (js.vregs vs) (srliBitmask shamt) =
        shift_bits_right (js.vregs vs) shamt :=
    srli_block_value_eq (js.vregs vs) shamt
  simpa [h_value] using virtual_srli_run_vreg_vreg vd vs (srliBitmask shamt) js hvd

/-- Existential package for the lowered `SRLI` block from a virtual source to
a virtual destination.  It exposes the virtual-register write, preservation of
other virtual registers, and the block's effect on every continuation program. -/
theorem exists_state_after_srli_block_run_vreg_vreg
    (vd vs : VReg) (shamt : BitVec 6)
    (js : SailJoltState) (hvd : WritableVReg vd) :
    ∃ js',
      js'.sail = js.sail ∧
      js'.vregs vd = shift_bits_right (js.vregs vs) shamt ∧
      (∀ r, r ≠ vd → js'.vregs r = js.vregs r) ∧
      ∀ tail,
        (execProgram (srliBlock (.vreg vd) (.vreg vs) shamt tail)).run js =
          (execProgram tail).run js' := by
  let js' : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = vd then shift_bits_right (js.vregs vs) shamt else js.vregs r }
  refine ⟨js', rfl, ?_, ?_, ?_⟩
  · simp [js']
  · intro r hne
    simp [js', hne]
  · intro tail
    unfold srliBlock
    rw [execProgram_instr_run_retire _ _ js js'
      (by simpa only [js'] using srli_block_run_vreg_vreg vd vs shamt js hvd)]

/-- Existential package for the lowered `SRL` block from virtual sources to a
virtual destination.  The scratch register first receives the encoded right
shift bitmask, then the destination receives the logical right shift. -/
theorem exists_state_after_srl_block_run_vreg_vreg_vreg
    (vd value shift scratch : VReg) (js : SailJoltState)
    (h_value_ne_scratch : value ≠ scratch)
    (hvd : WritableVReg vd) (hscratch : WritableVReg scratch) :
    ∃ js',
      js'.sail = js.sail ∧
      js'.vregs vd =
        shift_bits_right (js.vregs value) (Sail.BitVec.extractLsb (js.vregs shift) 5 0) ∧
      (∀ r, r ≠ vd → r ≠ scratch → js'.vregs r = js.vregs r) ∧
      ∀ tail,
        (execProgram
          (srlBlock (.vreg vd) (.vreg value) (.vreg shift) scratch tail)).run js =
          (execProgram tail).run js' := by
  let js_bitmask : SailJoltState :=
    { sail := js.sail
      vregs := fun r =>
        if r = scratch then jolt_virtual_shift_right_bitmask_value (js.vregs shift)
        else js.vregs r }
  let js' : SailJoltState :=
    { sail := js.sail
      vregs := fun r =>
        if r = vd then jolt_virtual_srl_value (js_bitmask.vregs value) (js_bitmask.vregs scratch)
        else js_bitmask.vregs r }
  have hbitmask :
      (execInstr (.VirtualShiftRightBitmask (.vreg scratch) (.vreg shift))).run js =
        .ok RETIRE_SUCCESS js_bitmask := by
    simpa [js_bitmask] using
      virtual_shift_right_bitmask_run_vreg_vreg scratch shift js hscratch
  have hsrl :
      (execInstr (.VirtualSRL (.vreg vd) (.vreg value) (.vreg scratch))).run js_bitmask =
        .ok RETIRE_SUCCESS js' := by
    simpa [js'] using virtual_srl_run_vreg_vreg_vreg vd value scratch js_bitmask hvd
  refine ⟨js', rfl, ?_, ?_, ?_⟩
  · dsimp [js']
    simp only [↓reduceIte]
    change jolt_virtual_srl_value (js_bitmask.vregs value) (js_bitmask.vregs scratch) =
      shift_bits_right (js.vregs value) (Sail.BitVec.extractLsb (js.vregs shift) 5 0)
    have h_value : js_bitmask.vregs value = js.vregs value := by
      simp [js_bitmask, h_value_ne_scratch]
    have h_scratch :
        js_bitmask.vregs scratch = jolt_virtual_shift_right_bitmask_value (js.vregs shift) := by
      simp [js_bitmask]
    rw [h_value, h_scratch]
    exact virtual_srl_shift_right_bitmask_value_eq (js.vregs value) (js.vregs shift)
  · intro r h_ne_dst h_ne_scratch
    dsimp [js']
    simp [h_ne_dst, js_bitmask, h_ne_scratch]
  · intro tail
    unfold srlBlock
    rw [execProgram_instr_run_retire _ _ js js_bitmask hbitmask]
    rw [execProgram_instr_run_retire _ _ js_bitmask js' hsrl]

/-- The lowered `SRAI` block from a virtual source to a virtual destination
writes the arithmetic right shift selected by the immediate. -/
private theorem srai_block_run_vreg_vreg
    (vd vs : VReg) (shamt : BitVec 6)
    (js : SailJoltState) (hvd : WritableVReg vd) :
    (execInstr (.VirtualSRAI (.vreg vd) (.vreg vs) (sraiBitmask shamt))).run js =
      .ok RETIRE_SUCCESS
        { sail := js.sail
          vregs := fun r =>
            if r = vd then shift_bits_right_arith (js.vregs vs) shamt else js.vregs r } := by
  have h_value :
      jolt_virtual_srai_value (js.vregs vs) (sraiBitmask shamt) =
        shift_bits_right_arith (js.vregs vs) shamt :=
    srai_block_value_eq (js.vregs vs) shamt
  unfold WritableVReg at hvd
  unfold execInstr readSrc writeDst readVReg writeVReg
  simp only [h_value, bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get,
    hvd, ↓reduceIte, modify, modifyGet, MonadStateOf.modifyGet,
    EStateM.modifyGet]

/-- The lowered `SRAI` block from a real source to a virtual destination reads
the architectural source and writes the arithmetic right shift. -/
private theorem srai_block_run_vreg_xreg
    (vd : VReg) (rs : regidx) (shamt : BitVec 6)
    (js : SailJoltState) (x : BitVec 64)
    (h : rX_bits rs js.sail = .ok x js.sail)
    (hvd : WritableVReg vd) :
    (execInstr (.VirtualSRAI (.vreg vd) (.xreg rs) (sraiBitmask shamt))).run js =
      .ok RETIRE_SUCCESS
        { sail := js.sail
          vregs := fun r =>
            if r = vd then shift_bits_right_arith x shamt else js.vregs r } := by
  have h_value :
      jolt_virtual_srai_value x (sraiBitmask shamt) = shift_bits_right_arith x shamt :=
    srai_block_value_eq x shamt
  unfold WritableVReg at hvd
  unfold execInstr readSrc writeDst liftSail writeVReg
  simp only [h, h_value, bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    hvd, ↓reduceIte, modify, modifyGet, MonadStateOf.modifyGet,
    EStateM.modifyGet]

/-- Existential package for the lowered `SRAI` block from a virtual source to
a virtual destination.  It exposes the virtual-register write, preservation of
other virtual registers, and the block's effect on every continuation program. -/
theorem exists_state_after_srai_block_run_vreg_vreg
    (vd vs : VReg) (shamt : BitVec 6)
    (js : SailJoltState) (hvd : WritableVReg vd) :
    ∃ js',
      js'.sail = js.sail ∧
      js'.vregs vd = shift_bits_right_arith (js.vregs vs) shamt ∧
      (∀ r, r ≠ vd → js'.vregs r = js.vregs r) ∧
      ∀ tail,
        (execProgram (sraiBlock (.vreg vd) (.vreg vs) shamt tail)).run js =
          (execProgram tail).run js' := by
  let js' : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = vd then shift_bits_right_arith (js.vregs vs) shamt else js.vregs r }
  refine ⟨js', rfl, ?_, ?_, ?_⟩
  · simp [js']
  · intro r hne
    simp [js', hne]
  · intro tail
    unfold sraiBlock
    rw [execProgram_instr_run_retire _ _ js js'
      (by simpa only [js'] using srai_block_run_vreg_vreg vd vs shamt js hvd)]

/-- Existential package for the lowered `SRAI` block from a real source to a
virtual destination.  It exposes the source read, virtual-register write,
preservation of other virtual registers, and the block's effect on every
continuation program. -/
theorem exists_state_after_srai_block_run_vreg_xreg
    (vd : VReg) (rs : regidx) (shamt : BitVec 6)
    (js : SailJoltState) (x : BitVec 64)
    (h : rX_bits rs js.sail = .ok x js.sail)
    (hvd : WritableVReg vd) :
    ∃ js',
      rX_bits rs js.sail = .ok x js.sail ∧
      js'.sail = js.sail ∧
      js'.vregs vd = shift_bits_right_arith x shamt ∧
      (∀ r, r ≠ vd → js'.vregs r = js.vregs r) ∧
      ∀ tail,
        (execProgram (sraiBlock (.vreg vd) (.xreg rs) shamt tail)).run js =
          (execProgram tail).run js' := by
  let js' : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = vd then shift_bits_right_arith x shamt else js.vregs r }
  refine ⟨js', h, rfl, ?_, ?_, ?_⟩
  · simp [js']
  · intro r hne
    simp [js', hne]
  · intro tail
    unfold sraiBlock
    rw [execProgram_instr_run_retire _ _ js js'
      (by simpa only [js'] using srai_block_run_vreg_xreg vd rs shamt js x h hvd)]

/-- Existential single-write post-state for the lowered `SRAI` block (virtual
source). The first conjunct rewrites the whole block against any continuation. -/
theorem srai_block_run_vreg_vreg_ex (vd vs : VReg) (shamt : BitVec 6)
    (js : SailJoltState) (hvd : WritableVReg vd) :
    ∃ js',
      (∀ tail,
        (execProgram (sraiBlock (.vreg vd) (.vreg vs) shamt tail)).run js =
          (execProgram tail).run js') ∧
      js'.vregs vd = shift_bits_right_arith (js.vregs vs) shamt ∧
      (∀ k, k ≠ vd → js'.vregs k = js.vregs k) ∧
      js'.sail = js.sail := by
  obtain ⟨js', h_sail, h_vd, h_pres, h_run⟩ :=
    exists_state_after_srai_block_run_vreg_vreg vd vs shamt js hvd
  exact ⟨js', h_run, h_vd, h_pres, h_sail⟩

/-- Existential single-write post-state for the lowered `SRAI` block (real
source). -/
theorem srai_block_run_vreg_xreg_ex (vd : VReg) (rs : regidx)
    (shamt : BitVec 6) (js : SailJoltState) (x : BitVec 64)
    (hread : rX_bits rs js.sail = .ok x js.sail)
    (hvd : WritableVReg vd) :
    ∃ js',
      (∀ tail,
        (execProgram (sraiBlock (.vreg vd) (.xreg rs) shamt tail)).run js =
          (execProgram tail).run js') ∧
      js'.vregs vd = shift_bits_right_arith x shamt ∧
      (∀ k, k ≠ vd → js'.vregs k = js.vregs k) ∧
      js'.sail = js.sail := by
  obtain ⟨js', _hread, h_sail, h_vd, h_pres, h_run⟩ :=
    exists_state_after_srai_block_run_vreg_xreg vd rs shamt js x hread hvd
  exact ⟨js', h_run, h_vd, h_pres, h_sail⟩

end JoltISA

end
