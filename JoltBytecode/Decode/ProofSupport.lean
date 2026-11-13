import JoltBytecode.Decode.Jolt
import JoltBytecode.Decode.Prefixes
import JoltBytecode.Decode.Configuration
import JoltBytecode.Decode.Execute

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail
  LeanRV64D LeanRV64D.Functions
open Lean Meta Elab Tactic

namespace Step

/-- Sail ASTs represented by a Jolt instruction; for example, ADD represents RTYPE ADD.
This is the decoder-facing spelling of `RiscvInstruction.Matches`. -/
abbrev Matches (i : RiscvInstruction) (ast : instruction) : Prop :=
  RiscvInstruction.Matches i ast

end Step

elab "decode32_start" : tactic => do
  let g ← getMainGoal
  g.withContext do
    let some (_, lhs, rhs) := (← whnf (← g.getType)).eq? | throwError "equality expected"
    let expand (e : Expr) : MetaM Expr := do
      let ci ← getConstInfo e.getAppFn.constName!
      return ci.value!.betaRev e.getAppRevArgs true
    let e ← expand lhs
    let e ← expand e
    let w := lhs.getAppArgs[0]!
    let st := lhs.getAppArgs[1]!
    let k := e.getAppArgs[4]!
    let pref ← mkAppM ``Decode.prefetchPrefix #[w, k]
    let gn ← g.change (← mkEq (mkApp pref st) rhs)
    setGoals [gn]
    evalTactic (← `(tactic| rw [Decode.prefetchPrefix_none]))
    evalTactic (← `(tactic| rw [pure_bind]))
    let gn ← getMainGoal
    let some (_, l, r) := (← whnf (← gn.getType)).eq? | throwError "equality expected"
    let mut l := l.getAppFn.betaRev l.getAppRevArgs true
    while let some r ← reduceRecMatcher? l do
      l := r.getAppFn.betaRev r.getAppRevArgs true
    let k := l.getAppArgs[4]!
    let pref ← mkAppM ``Decode.ntlPrefix #[w, k]
    let gn ← gn.change (← mkEq (mkApp pref st) r)
    setGoals [gn]
    evalTactic (← `(tactic| rw [Decode.ntlPrefix_none]))
    evalTactic (← `(tactic| conv_lhs => whnf))

/-- Compressed register fields add eight without a carry, as in C.LW's x8–x15 operands. -/
private theorem decoder_creg_add (x : BitVec 32) :
    (x &&& 7#32) + 8#32 = (x &&& 7#32) ||| 8#32 := by
  apply BitVec.add_eq_or_of_and_eq_zero
  simp [BitVec.and_assoc]

/-- Jolt's sign mask on a parcel is its bit twelve gating the mask; for example, C.ADDI's
immediate has bits 31:6 set exactly when the parcel's sign bit is set. -/
private theorem decoder_sign_mask_bit (h : BitVec 16) (bit mask : BitVec 32) (hbit : bit.toNat = 4096) (i : Nat) :
    (Decode.signBitMask (h.setWidth 32) bit mask).getLsbD i = (h.getLsbD 12 && mask.getLsbD i) := by
  obtain rfl : bit = 0x1000#32 := BitVec.eq_of_toNat_eq hbit
  have hc : (h.setWidth 32 &&& 0x1000#32 = 0x1000#32) ↔ h.getLsbD 12 = true := by
    constructor
    · intro he
      have := congrArg (fun x : BitVec 32 => x.getLsbD 12) he
      simpa [-BitVec.getLsbD_eq_getElem] using this
    · intro hb
      apply BitVec.eq_of_getLsbD_eq
      intro j hj
      simp only [BitVec.getLsbD_and, BitVec.getLsbD_setWidth, BitVec.getLsbD_ofNat]
      by_cases hj12 : j = 12
      · subst hj12; simp [-BitVec.getLsbD_eq_getElem, hb]
      · have : ¬ Nat.testBit 0x1000 j := by
          rw [show (0x1000 : Nat) = 2 ^ 12 by norm_num, Nat.testBit_two_pow]
          simpa using Ne.symm hj12
        simp [this]
  unfold Decode.signBitMask
  by_cases hb : h.getLsbD 12 = true
  · simp [-BitVec.getLsbD_eq_getElem, hc.mpr hb, hb]
  · simp [-BitVec.getLsbD_eq_getElem, hb, (not_congr hc).mpr hb]

open Lean Meta Simp in
/-- Read one bit of a concatenation, such as bit 3 of `a +++ b`. Simplification normalizes the
widths in the types of a concatenation but not in its instance, so the plain lemma
`BitVec.getLsbD_append` no longer matches; this simproc instantiates it by hand and leaves the
type check to the kernel. -/
simproc decoderAppendBit (BitVec.getLsbD _ _) := fun e => do
  let_expr BitVec.getLsbD _ v i := e | return .continue
  let_expr HAppend.hAppend _ _ _ _ x y := v | return .continue
  let pr ← mkAppOptM ``BitVec.getLsbD_append #[none, none, some i, some x, some y]
  let some (_, _, rhs) := (← inferType pr).eq? | return .continue
  return .visit { expr := rhs, proof? := some pr }

/-- A slice below a left shift is zero; for example, opcode bits ignore an immediate shifted by twenty. -/
private theorem decoder_extract_shift_zero {n : Nat} (x : BitVec n) (start len shift : Nat)
    (h : start + len ≤ shift) : (x <<< shift).extractLsb' start len = 0 := by
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i hi
  have hs : start + i < shift := by omega
  simp [-BitVec.getLsbD_eq_getElem, BitVec.getLsbD_extractLsb',
    BitVec.getLsbD_shiftLeft, hi, hs]

/-- A slice above a left shift reads the original field; for example, bits 19:15 recover a register shifted by fifteen. -/
private theorem decoder_extract_shift_cancel {n : Nat} (x : BitVec n) (start len shift : Nat)
    (hs : shift ≤ start) (hn : start + len ≤ n) :
    (x <<< shift).extractLsb' start len = x.extractLsb' (start - shift) len := by
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i hi
  have hb : start + i < n := by omega
  have hk : ¬ start + i < shift := by omega
  have he : start + i - shift = start - shift + i := by omega
  simp [-BitVec.getLsbD_eq_getElem, BitVec.getLsbD_extractLsb',
    BitVec.getLsbD_shiftLeft, hi, hb, hk, he]

/-- Reduce decoder field arithmetic to natural-number quotients and remainders;
for example, funct3 is the three-bit remainder after shifting by twelve. -/
macro "decoder_omega" : tactic => `(tactic|
  ((try simp only [Sail.BitVec.extractLsb, BitVec.toNat_eq, BitVec.toNat_ne, BitVec.extractLsb_toNat,
    BitVec.extractLsb'_toNat, BitVec.toNat_ushiftRight, BitVec.toNat_setWidth,
    BitVec.toNat_and, BitVec.ofNat_eq_ofNat, BitVec.natCast_eq_ofNat,
    BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.reducePow, Nat.reduceMod,
    Nat.reduceSub, Nat.reduceAdd, Nat.reduceDiv,
    Nat.and_two_pow_sub_one_eq_mod _ 1, Nat.and_two_pow_sub_one_eq_mod _ 2,
    Nat.and_two_pow_sub_one_eq_mod _ 3, Nat.and_two_pow_sub_one_eq_mod _ 5] at *) <;> omega))

/-- Reassociate the remaining field conjunctions, such as two orders of C.ADDI4SPN's zero bits. -/
elab "decoder_conjunctions" : tactic => withMainContext do
  if (← whnf (← getMainTarget)).isConstOf ``False then
    throwError "guard reduced to False"
  evalTactic (← `(tactic| solve | simp_all only [and_assoc, and_left_comm, and_comm]))

/-- Check field identities bit by bit, then solve their Boolean consequences.
For example, extracting two low funct3 bits agrees with extracting them from the word.
Only bit positions are expanded; instruction words are never enumerated. -/
macro "decoder_bits" : tactic => `(tactic|
  ((try simp [-BitVec.shiftLeft_add_distrib, decoder_creg_add,
    Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb'_or, BitVec.extractLsb'_and,
    decoder_extract_shift_zero, decoder_extract_shift_cancel, *]) <;> first
  | decoder_omega
  | (intros
     (try simp only [Sail.BitVec.extractLsb, BitVec.extractLsb,
       ← BitVec.getLsbD_eq_getElem] at *) <;>
     (try simp only [BitVec.eq_of_getLsbD_eq_iff, Nat.forall_lt_succ_right,
       Nat.not_lt_zero, decoderAppendBit] at *) <;>
     simp_all [-BitVec.getLsbD_eq_getElem, -BitVec.append_eq, -Nat.lt_add_one, -BitVec.shiftLeft_add_distrib, decoder_creg_add, BitVec.eq_of_getLsbD_eq_iff,
       Nat.forall_lt_succ_right, Nat.le_one_iff_eq_zero_or_eq_one, BitVec.getLsbD_signExtend,
       decoderAppendBit, BitVec.getLsbD_ofNat, BitVec.toNat_ofNat, decoder_sign_mask_bit,
       ← BitVec.getLsbD_eq_extractLsb', Nat.testBit_eq_decide_div_mod_eq]
     <;> first | assumption | decoder_conjunctions)))

/-- Like `decoder_bits`, but expand every field to bit positions first; for example, the
immediate of C.ADDI equals the sign-extended parcel bits. Used for compressed operand identities. -/
macro "decoder_bits_expanded" : tactic => `(tactic|
  ((try simp [-BitVec.shiftLeft_add_distrib, decoder_creg_add,
    Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb'_or, BitVec.extractLsb'_and,
    decoder_extract_shift_zero, decoder_extract_shift_cancel, *]) <;> first
  | decoder_omega
  | (intros
     (try simp only [Sail.BitVec.extractLsb, BitVec.extractLsb,
       ← BitVec.getLsbD_eq_getElem] at *) <;>
     (try simp only [BitVec.eq_of_getLsbD_eq_iff, Nat.forall_lt_succ_right,
       Nat.not_lt_zero, decoderAppendBit] at *) <;>
     (repeat' apply And.intro) <;>
     (try simp only [decoderAppendBit, decoder_creg_add,
       BitVec.ofNat_eq_ofNat, BitVec.natCast_eq_ofNat, BitVec.eq_of_getLsbD_eq_iff,
       Nat.forall_lt_succ_right, Nat.not_lt_zero, BitVec.getLsbD_extractLsb',
       BitVec.getLsbD_setWidth, BitVec.getLsbD_setWidth', BitVec.getLsbD_shiftLeft,
       BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeftZeroExtend,
       BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_xor,
       BitVec.getLsbD_not, BitVec.getLsbD_signExtend, BitVec.msb_eq_getLsbD_last,
       BitVec.getLsbD_ofNat, BitVec.toNat_ofNat, decoder_sign_mask_bit,
       Nat.testBit_eq_decide_div_mod_eq,
       Nat.reduceAdd, Nat.reduceSub, Nat.reducePow, Nat.reduceMod, Nat.reduceDiv,
       Nat.reduceLT, Nat.reduceLeDiff, decide_true, decide_false,
       Bool.true_and, Bool.false_and, Bool.and_true, Bool.and_false,
       Bool.true_or, Bool.false_or, Bool.or_true, Bool.or_false, ↓reduceIte] at *) <;>
     simp_all [-BitVec.getLsbD_eq_getElem, -BitVec.append_eq, -Nat.lt_add_one, -BitVec.shiftLeft_add_distrib, decoder_creg_add, BitVec.eq_of_getLsbD_eq_iff,
       Nat.forall_lt_succ_right, Nat.le_one_iff_eq_zero_or_eq_one, BitVec.getLsbD_signExtend,
       decoderAppendBit, BitVec.getLsbD_ofNat, BitVec.toNat_ofNat, decoder_sign_mask_bit,
       ← BitVec.getLsbD_eq_extractLsb', Nat.testBit_eq_decide_div_mod_eq]
     <;> first | assumption | decoder_conjunctions)))

private theorem decoder_f3_lo (w : BitVec 32) (n : BitVec 3)
    (h : w.extractLsb 14 12 = n) : w.extractLsb 13 12 = n.extractLsb 1 0 := by
  simp only [BitVec.extractLsb] at *
  decoder_omega
private theorem decoder_f3_hi (w : BitVec 32) (n : BitVec 3)
    (h : w.extractLsb 14 12 = n) : w.extractLsb 14 14 = n.extractLsb 2 2 := by
  simp only [BitVec.extractLsb] at *
  decoder_omega

private def prepareDecoderFields : TacticM Unit := withMainContext do
  let mut g ← getMainGoal
  let decls := (← getLCtx).decls.toArray.filterMap id
  for d in decls do
    unless d.isImplementationDetail do
      if let some (_, l, r) := (← whnf d.type).eq? then
        if l.isAppOfArity ``BitVec.toNat 2 then
          let args := l.getAppArgs
          let n := args[0]!
          let x := args[1]!
          let bv := mkApp2 (mkConst ``BitVec.ofNat) n r
          let ty ← mkEq x bv
          if decls.any (fun existing => existing.type == ty) then continue
          let pr := mkApp4 (mkConst ``BitVec.eq_of_toNat_eq) n x bv d.toExpr
          let name ← mkFreshUserName `decoded_field
          let g' ← g.assert name ty pr
          let (fv, g') ← g'.intro1P
          g := g'
          if x.isAppOfArity ``Sail.BitVec.extractLsb 4 && (← whnf x.getAppArgs[2]!).rawNatLit? == some 14 then
            for name in [``decoder_f3_lo, ``decoder_f3_hi] do
              let p ← g.withContext <| mkAppM name #[x.getAppArgs[1]!, bv, mkFVar fv]
              let g' ← g.assert (← mkFreshUserName `decoded_part) (← g.withContext <| inferType p) p
              let (_, g') ← g'.intro1P
              g := g'
  setGoals [g]

/-- Record the extraction form of the compressed selectors;
for example, quadrant one gives `h.extractLsb 1 0 = 1`. -/
private def addSelectorFacts : TacticM Unit := do
  let mut g ← getMainGoal
  for (name, hi, lo) in [(`hop, 1, 0), (`hf, 15, 13)] do
    let fact? ← g.withContext do
      let some parcel := (← getLCtx).findFromUserName? `h | return none
      let some d := (← getLCtx).findFromUserName? name | return none
      let some (_, _, value) := (← whnf d.type).eq? | return none
      let field ← mkAppM ``Sail.BitVec.extractLsb #[parcel.toExpr, toExpr hi, toExpr lo]
      let ty ← mkEq field (mkApp2 (mkConst ``BitVec.ofNat) (toExpr (hi - lo + 1)) value)
      if (← getLCtx).decls.toArray.any (fun d => d.any (·.type == ty)) then return none
      let m ← mkFreshExprMVar ty
      setGoals [m.mvarId!]
      evalTactic (← `(tactic| decoder_omega))
      return some (ty, ← instantiateMVars m)
    if let some (ty, pr) := fact? then
      let gn ← g.assert (← mkFreshUserName `decoded_selector) ty pr
      let (_, gn) ← gn.intro1P
      g := gn
  setGoals [g]

/-- Record bit-vector forms of selector hypotheses, such as quadrant one. -/
elab "compressed_prepare" : tactic => prepareDecoderFields

private def decoderRunProofs (s : Expr) : TacticM (Array Expr) := withMainContext do
  let mut proofs := #[]
  if let some d := (← getLCtx).findFromUserName? `hreset then
    for (a, b, theoremName) in [(``extension.Ext_M, ``extension.Ext_A, ``Decode.enabledMA_reset),
        (``extension.Ext_Zmmul, ``extension.Ext_Zalrsc, ``Decode.enabledSub_reset)] do
      for left in [true, false] do
        let x := mkConst (if left then a else b)
        let p ← mkEq x (mkConst a)
        let q ← mkEq x (mkConst b)
        let he := mkApp3 (mkConst (if left then ``Or.inl else ``Or.inr)) p q (← mkEqRefl x)
        proofs := proofs.push (← mkAppM theoremName #[x, he, s, d.toExpr])
    proofs := proofs.push (← mkAppM ``Decode.enabledAMO_reset #[s, d.toExpr])
  if let some d := (← getLCtx).findFromUserName? `hinv then
    proofs := proofs.push (← mkAppM ``_root_.Step.currentlyEnabled_Zca_run #[s, d.toExpr])
  return proofs

private theorem decoder_width_matches (x : BitVec 2) : width_enc_backwards_matches x = true := by
  revert x
  decide

private theorem decoder_bool_matches (x : BitVec 1) : bool_bit_backwards_matches x = true := by
  revert x
  decide

private theorem decoder_bool_value (x : BitVec 1) : bool_bit_backwards x = (x == 1) := by
  unfold bool_bit_backwards
  split <;> simp_all

private theorem decoder_reg_beq (a b : BitVec 5) :
    (regidx.Regidx a == regidx.Regidx b) = (a == b) := by rfl

private partial def reduceDecoder (x : Expr) (runs : Array Expr) : TacticM (Expr × Expr) := withoutRecover do
  let ty ← inferType x
  for pr in runs do
    let some (_, l, r) := (← whnf (← inferType pr)).eq? | continue
    if ← isDefEq ty (← inferType l) then
      if ← isDefEq x l then return (r, pr)
  let e ← whnf x
  let fn := e.getAppFn
  let args := e.getAppArgs
  let idx ← if fn.isConstOf ``Bool.rec then pure 3
    else if let some info ← getMatcherInfo? fn.constName! then pure info.getFirstDiscrPos
    else if let .recInfo info ← getConstInfo fn.constName! then pure info.getMajorIdx
    else throwError "stuck decoder: {e}"
  if fn.isConstOf ``Bool.rec then
    let isDecide := args[3]!.isAppOfArity ``decide 2
    let rewriteGuard (value hp : Expr) : MetaM (Expr × Expr) := do
      let p := Expr.lam `guard (mkConst ``Bool) (mkAppN fn (args.set! 3 (.bvar 0))) .default
      return (mkAppN fn (args.set! 3 value), ← mkCongrArg p hp)
    unless isDecide do
      for pr in runs do
        let some (_, l, r) := (← whnf (← inferType pr)).eq? | continue
        if ← isDefEq (← inferType l) (mkConst ``Bool) then
          if ← isDefEq args[3]! l then return ← rewriteGuard r pr
    let prop ← if isDecide then pure args[3]!.getAppArgs[0]!
      else mkEq args[3]! (mkConst ``Bool.true)
    let inst := if isDecide then args[3]!.getAppArgs[1]! else mkConst ``Bool.true
    let saved ← saveState
    let prove (b : Bool) (thorough : Bool) : TacticM Expr := do
      let m ← mkFreshExprMVar (if b then prop else mkNot prop)
      setGoals [m.mvarId!]
      let fieldNames := (← getLCtx).decls.toArray.filterMap fun od => do
        let d ← od
        if d.userName.toString.startsWith "word_field" || d.userName.toString.startsWith "word_part" then
          some (mkIdent d.userName)
        else none
      if !fieldNames.isEmpty then
        evalTactic (← `(tactic| try simp only [encdec_uop_backwards_matches,
          encdec_bop_backwards_matches, encdec_iop_backwards_matches,
          encdec_biop_backwards_matches, encdec_mul_op_backwards_matches,
          encdec_amoop_backwards_matches, encdec_csrop_backwards_matches,
          $[$fieldNames:ident],*]))
      else
        evalTactic (← `(tactic| try simp only [*]))
      if (← getGoals).isEmpty then return (← instantiateMVars m)
      evalTactic (← `(tactic| try simp only [Decode.signBitMask] at *))
      evalTactic (← `(tactic| try simp only [Sail.BitVec.extractLsb, BitVec.extractLsb] at *))
      if (← getGoals).isEmpty then return (← instantiateMVars m)
      unless thorough do
        -- Guards about parcel fields are linear arithmetic once the field expressions are unfolded.
        evalTactic (← `(tactic| simp [-BitVec.shiftLeft_add_distrib, Sail.BitVec.extractLsb, BitVec.extractLsb,
          Decode.signBitMask, decoder_creg_add, Functions.regidx_bit_width, decoder_reg_beq, bne, zreg, sp, ra, zero_extend, Sail.BitVec.zeroExtend, encdec_reg_backwards_matches, encdec_creg_backwards_matches, Functions.base_E_enabled,
          encdec_uop_backwards_matches, encdec_bop_backwards_matches, encdec_iop_backwards_matches,
          encdec_amoop_backwards_matches, encdec_mul_op_backwards_matches, encdec_csrop_backwards_matches, width_enc_wide_backwards_matches,
          encdec_biop_backwards_matches, lrsc_width_valid, decoder_width_matches, decoder_bool_matches, valid_load_encdec, Functions.xlen_bytes, Functions.xlen, width_enc_backwards, width_enc_wide_backwards, decoder_bool_value, Functions.not] <;> decoder_omega))
        unless (← getGoals).isEmpty do throwError "guard needs the thorough proof"
        return (← instantiateMVars m)
      evalTactic (← `(tactic| simp [-BitVec.shiftLeft_add_distrib, Sail.BitVec.extractLsb, BitVec.extractLsb,
        Decode.signBitMask, decoder_creg_add, Functions.regidx_bit_width, decoder_reg_beq, bne, zreg, sp, ra, zero_extend, Sail.BitVec.zeroExtend, encdec_reg_backwards_matches, encdec_creg_backwards_matches, Functions.base_E_enabled,
        encdec_uop_backwards_matches, encdec_bop_backwards_matches, encdec_iop_backwards_matches,
        encdec_amoop_backwards_matches, encdec_mul_op_backwards_matches, encdec_csrop_backwards_matches, width_enc_wide_backwards_matches,
        encdec_biop_backwards_matches, lrsc_width_valid, decoder_width_matches, decoder_bool_matches, valid_load_encdec, Functions.xlen_bytes, Functions.xlen, width_enc_backwards, width_enc_wide_backwards, decoder_bool_value, Functions.not, *]))
      for g in ← getGoals do
        if (← whnf (← g.getType)).isConstOf ``False then
          throwError "guard has the opposite value"
      unless (← getGoals).isEmpty do evalTactic (← `(tactic| decoder_bits))
      unless (← getGoals).isEmpty do throwError "guard unresolved"
      instantiateMVars m
    -- Failing a guard's proof is expensive, so try the cheap bit-arithmetic proof of each value
    -- before the thorough one.
    let (b, hp) ← try pure (false, ← prove false false) catch _ => do
      saved.restore
      try pure (true, ← prove true false) catch _ => do
        saved.restore
        try pure (false, ← prove false true) catch _ => do
          saved.restore
          pure (true, ← prove true true)
    unless isDecide do
      let hp ← if b then pure hp else mkAppM ``Bool.eq_false_of_not_eq_true #[hp]
      let value := mkConst (if b then ``Bool.true else ``Bool.false)
      return ← rewriteGuard value hp
    let .forallE _ _ resultTy _ ← inferType args[1]! | throwError "branch type expected"
    let u ← getLevel resultTy
    let mut eq := mkApp6 (mkConst (if b then ``dite_eq_left else ``dite_eq_right) [u])
      prop inst hp resultTy args[2]! args[1]!
    let mut result := mkApp args[if b then 2 else 1]! hp
    for arg in args.toList.drop 5 do
      result := mkApp result arg
      eq ← mkCongrFun eq arg
    return (result, eq)
  let (v, pr) ← reduceDecoder args[idx]! runs
  let p := Expr.lam `decoded_arg (← inferType args[idx]!)
    (mkAppN fn (args.set! idx (.bvar 0))) .default
  let eq ← mkCongrArg p pr
  return (mkAppN fn (args.set! idx v), eq)

/-- Reduce one accepted opcode/function-field case, such as ADD's funct7=0 case.
The emitted equality and matching proofs are checked by Lean's kernel. -/
elab "decode32_case" : tactic => do
  prepareDecoderFields
  withMainContext <| evalTactic (← `(tactic| refine ⟨?_, ?_, ?_⟩))
  let gs ← getGoals
  let (eqGoal, remaining) ← if (← whnf (← gs.head!.getType)).isConstOf ``instruction then
    gs.head!.setKind .natural
    pure (gs[1]!, gs.drop 2)
  else pure (gs.head!, gs.tail!)
  setGoals [eqGoal]
  let s ← withMainContext do
    let some (_, l, _) := (← whnf (← eqGoal.getType)).eq? | throwError "decoder equality expected"
    pure l.getAppArgs[1]!
  let mut runs ← decoderRunProofs s
  let fields ← withMainContext do
    let mut fs := #[]
    for d in ← getLCtx do
      unless d.isImplementationDetail do
        if let some (_, _, _) := (← whnf d.type).eq? then
          fs := fs.push d.toExpr
    pure fs
  runs := runs ++ fields
  for name in [``Decode.pause_disabled, ``Decode.landingPad_disabled, ``Decode.csr_enabled] do
    runs := runs.push (← mkCongrFun (mkConst name) s)
  evalTactic (← `(tactic| decode32_start))
  let g ← getMainGoal
  g.withContext do
    let some (_, left, right) := (← whnf (← g.getType)).eq? | throwError "equality expected"
    let ty ← inferType left
    let u ← getLevel ty
    let mut cursor := left
    let mut proof ← mkEqRefl left
    let mut done_ := false
    for _ in [:400] do
      unless done_ do
        let e ← whnf cursor
        if e.isAppOf ``EStateM.Result.ok then
          unless ← isDefEq e right do throwError "wrong decoded result"
          g.assign proof
          done_ := true
        else
          setGoals [g]
          let (next, pr) ← reduceDecoder cursor runs
          proof := mkApp6 (mkConst ``Eq.trans [u]) ty left cursor next proof pr
          cursor := next
    unless done_ do throwError "decoder reduction did not finish"
    setGoals []
  setGoals remaining
  withMainContext <| evalTactic (← `(tactic| try simp only [Sail.BitVec.extractLsb, BitVec.extractLsb] at *))
  -- Supply FENCE's operands before normalization expands their equalities.
  withMainContext <| evalTactic (← `(tactic| first
  | exact Or.inl ⟨_, _, _, _, _, rfl⟩
  | exact Or.inr rfl
  | simp [_root_.Step.Matches, RiscvInstruction.Matches, Decode.rd, Decode.rs1, Decode.rs2,
    Decode.immI, Decode.immS, Decode.immB, Decode.immU, Decode.immJ,
    Sail.BitVec.extractLsb, BitVec.extractLsb, Functions.regidx_bit_width,
    Sail.BitVec.access, width_enc_backwards, width_enc_wide_backwards, decoder_bool_value, *] <;> first | rfl | decoder_bits))

/-- Reduce a compressed decoder field case, such as quadrant zero's C.LW arm. -/
elab "decode16_start" : tactic => do
  let g ← getMainGoal
  g.withContext do
    let some (_, lhs, rhs) := (← whnf (← g.getType)).eq? | throwError "equality expected"
    let expand (e : Expr) : MetaM Expr := do
      let ci ← getConstInfo e.getAppFn.constName!
      return ci.value!.betaRev e.getAppRevArgs true
    let e ← expand lhs
    let e ← expand e
    let h := lhs.getAppArgs[0]!
    let st := lhs.getAppArgs[1]!
    let k := e.getAppArgs[4]!
    let pref ← mkAppM ``Decode.compressedNtlPrefix #[h, k]
    let gn ← g.change (← mkEq (mkApp pref st) rhs)
    setGoals [gn]
    evalTactic (← `(tactic| rw [Decode.compressedNtlPrefix_none]))
    evalTactic (← `(tactic| conv_lhs => whnf))

/-- Evaluate a compressed decoder after fixing its selector fields, without enumerating parcels. -/
elab "decode16_case" : tactic => do
  prepareDecoderFields
  addSelectorFacts
  let g ← getMainGoal
  let s ← withMainContext do
    let some (_, l, _) := (← whnf (← g.getType)).eq? | throwError "decoder equality expected"
    pure l.getAppArgs[1]!
  let runs ← decoderRunProofs s
  evalTactic (← `(tactic| decode16_start))
  let g ← getMainGoal
  g.withContext do
    let some (_, left, right) := (← whnf (← g.getType)).eq? | throwError "equality expected"
    let ty ← inferType left
    let u ← getLevel ty
    let mut cursor := left
    let mut proof ← mkEqRefl left
    let mut done_ := false
    for _ in [:150] do
      unless done_ do
        let e ← whnf cursor
        if e.isAppOf ``EStateM.Result.ok then
          unless ← isDefEq e right do throwError "wrong decoded result"
          g.assign proof
          done_ := true
        else
          setGoals [g]
          let (next, pr) ← reduceDecoder cursor runs
          proof := mkApp6 (mkConst ``Eq.trans [u]) ty left cursor next proof pr
          cursor := next
    unless done_ do throwError "compressed decoder reduction did not finish"
    setGoals []

/-- A compressed ExecuteAs result runs its base AST; for example, C.LW runs LOAD. -/
private theorem decoded_expansion (cast base : instruction)
    (he : execute cast = pure (.ExecuteAs base)) :
    _root_.Step.executeFull cast = execute base := by
  simp only [_root_.Step.executeFull, he, pure_bind]

/-- Read constant encoding bits as candidate selectors, such as ADDI's opcode 19. -/
private partial def encodingConstant (e : Expr) : MetaM Nat := do
  if e.isAppOf ``HOr.hOr || e.isAppOf ``BitVec.or then
    let args := e.getAppArgs
    return (← encodingConstant args[args.size - 2]!) |||
      (← encodingConstant args.back!)
  if e.hasFVar || e.hasMVar then return 0
  let type ← inferType e
  unless ← isDefEq type (mkApp (mkConst ``BitVec) (toExpr 32)) do return 0
  let value ← whnf (← mkAppM ``BitVec.toNat #[e])
  return (← getNatValue? value).getD 0

/-- Record the opcode and function fields that select a base case, such as ADDI. -/
elab "decode_word_fields" : tactic => withoutRecover do
  prepareDecoderFields
  withMainContext do
    let mut g ← getMainGoal
    let word ← g.withContext do
      let some (_, lhs, _) := (← whnf (← g.getType)).eq? | throwError "decoder equality expected"
      pure lhs.getAppArgs[0]!
    let constant ← encodingConstant word
    let mut opcode := 0
    let mut funct := 0
    for (hi, lo, values) in [(6, 0, [19, 27, 51, 59, 55, 103, 111, 99, 3, 35, 115]),
        (14, 12, [0, 1, 2, 3, 4, 5, 6, 7]), (31, 25, [0, 32]), (31, 26, [0, 16])] do
      let needed := if hi == 14 then opcode != 55 && opcode != 111 && opcode != 115
        else hi != 31 ||
          (lo == 25 && (opcode == 51 || opcode == 59 || (opcode == 27 && (funct == 1 || funct == 5)))) ||
          (lo == 26 && opcode == 19 && (funct == 1 || funct == 5))
      let hint := (constant >>> lo) &&& (2 ^ (hi - lo + 1) - 1)
      let candidates := hint :: values.filter (· != hint)
      let mut found := !needed
      for value in candidates do
        unless found do
          let saved ← saveState
          try
            let field ← mkAppM ``Sail.BitVec.extractLsb #[word, toExpr hi, toExpr lo]
            let n ← whnf (← inferType field)
            let width := n.getAppArgs[0]!
            let ty ← mkEq field (mkApp2 (mkConst ``BitVec.ofNat) width (toExpr value))
            let m ← mkFreshExprMVar ty
            setGoals [m.mvarId!]
            -- Keep sign masks folded first, so their bits are read by `decoder_sign_mask_bit`.
            let folded ← saveState
            try
              evalTactic (← `(tactic| try simp only [Decode.branchImmediates, Decode.jOffset,
                Sail.BitVec.extractLsb, BitVec.extractLsb]))
              unless (← getGoals).isEmpty do evalTactic (← `(tactic| decoder_bits))
            catch _ =>
              folded.restore
              setGoals [m.mvarId!]
              evalTactic (← `(tactic| try simp only [Decode.branchImmediates, Decode.jOffset,
                Decode.signBitMask, Sail.BitVec.extractLsb, BitVec.extractLsb]))
              unless (← getGoals).isEmpty do evalTactic (← `(tactic| decoder_bits))
            let pr ← instantiateMVars m
            let gn ← g.assert (← mkFreshUserName `word_field) ty pr
            let (_, gn) ← gn.intro1P
            g := gn
            if hi == 14 then
              for (name, high, low) in [(``decoder_f3_lo, 13, 12), (``decoder_f3_hi, 14, 14)] do
                let p ← g.withContext <| mkAppM name #[word, mkApp2 (mkConst ``BitVec.ofNat) width (toExpr value), pr]
                let some (_, _, rhs) := (← g.withContext <| inferType p).eq? | throwError "field equality expected"
                let lhs ← mkAppM ``Sail.BitVec.extractLsb #[word, toExpr high, toExpr low]
                let gn ← g.assert (← mkFreshUserName `word_part) (← mkEq lhs rhs) p
                let (_, gn) ← gn.intro1P
                g := gn
            if hi == 6 then opcode := value
            if hi == 14 then funct := value
            found := true
          catch _ => saved.restore
      unless found do throwError "expanded selector {hi}:{lo} is unresolved"
    setGoals [g]

/-- Decode one expanded parcel, such as the LOAD word produced by C.LW. -/
elab "decode_word_case" : tactic => do
  evalTactic (← `(tactic| decode_word_fields))
  let g ← getMainGoal
  let s ← withMainContext do
    let some (_, lhs, _) := (← whnf (← g.getType)).eq? | throwError "decoder equality expected"
    pure lhs.getAppArgs[1]!
  let mut runs ← decoderRunProofs s
  for name in [``Decode.pause_disabled, ``Decode.landingPad_disabled, ``Decode.csr_enabled] do
    runs := runs.push (← mkCongrFun (mkConst name) s)
  let fields ← withMainContext do
    let mut fields := #[]
    for d in ← getLCtx do
      unless d.isImplementationDetail do
        if let some (_, _, _) := (← whnf d.type).eq? then
          fields := fields.push d.toExpr
    pure fields
  runs := runs ++ fields
  evalTactic (← `(tactic| decode32_start))
  let g ← getMainGoal
  g.withContext do
    let some (_, left, right) := (← whnf (← g.getType)).eq? | throwError "equality expected"
    let ty ← inferType left
    let u ← getLevel ty
    let mut cursor := left
    let mut proof ← mkEqRefl left
    let mut done_ := false
    for _ in [:400] do
      unless done_ do
        let e ← whnf cursor
        if e.isAppOf ``EStateM.Result.ok then
          let m ← mkFreshExprMVar (← mkEq e right)
          setGoals [m.mvarId!]
          let fieldNames := (← getLCtx).decls.toArray.filterMap fun od => do
            let d ← od
            if d.userName.toString.startsWith "word_field" || d.userName.toString.startsWith "word_part" then
              some (mkIdent d.userName)
            else none
          evalTactic (← `(tactic| try simp only [width_enc_backwards,
            width_enc_wide_backwards, decoder_bool_value, $[$fieldNames:ident],*]))
          unless (← getGoals).isEmpty do evalTactic (← `(tactic| all_goals rfl))
          let final ← instantiateMVars m
          g.assign (mkApp6 (mkConst ``Eq.trans [u]) ty left cursor right proof final)
          done_ := true
        else
          setGoals [g]
          let (next, pr) ← reduceDecoder cursor runs
          proof := mkApp6 (mkConst ``Eq.trans [u]) ty left cursor next proof pr
          cursor := next
    unless done_ do throwError "decoder reduction did not finish"
    setGoals []

/-- Expose the two decoding results and execution equality, as in the C.LW comparison. -/
elab "decoder_pair" : tactic => do
  evalTactic (← `(tactic| refine ⟨?_, ?_, ?_, ?_, ?_⟩))
  let gs ← getGoals
  gs[0]!.setKind .natural
  gs[1]!.setKind .natural
  setGoals (gs.drop 2)

/-- Drop every proposition from the local context except the parcel's clear bits (`zbit…`);
for example, selector hypotheses are not needed for operand identities. -/
private def clearHypotheses (g : MVarId) : MetaM MVarId := g.withContext do
  let mut g := g
  for d in (← getLCtx).decls.toList.reverse.filterMap id do
    if !d.isImplementationDetail && (← isProp d.type) &&
        !(d.userName.toString.startsWith "zbit") then g ← g.tryClear d.fvarId
  return g

/-- Prove operand identities after normalizing compressed fields, such as C.J offsets. -/
private def proveCompressedBits (ty : Expr) : TacticM Expr := withoutRecover do
  let attempt (minimal : Bool) : TacticM Expr := do
    let m ← mkFreshExprMVar ty
    setGoals [m.mvarId!]
    let stateNames := #[`hinv', `s', `hinv, `s].map mkIdent
    evalTactic (← `(tactic| try clear $[$stateNames:ident]*))
    -- Most operand identities hold for every parcel, so selector hypotheses only slow them down.
    if minimal then
      setGoals [← clearHypotheses (← getMainGoal)]
      evalTactic (← `(tactic| simp [-BitVec.shiftLeft_add_distrib, decoder_creg_add, encdec_creg_backwards, creg2reg_idx, zero_extend,
        Sail.BitVec.zeroExtend, sign_extend, Sail.BitVec.signExtend,
        Sail.BitVec.extractLsb, BitVec.extractLsb, Functions.regidx_bit_width, zreg, sp, ra,
        zeros, Decode.jOffset, Decode.branchImmediates] <;> decoder_bits_expanded))
    else
      evalTactic (← `(tactic| simp [-BitVec.shiftLeft_add_distrib, decoder_creg_add, encdec_creg_backwards, creg2reg_idx, zero_extend,
        Sail.BitVec.zeroExtend, sign_extend, Sail.BitVec.signExtend,
        Sail.BitVec.extractLsb, BitVec.extractLsb, Functions.regidx_bit_width, zreg, sp, ra,
        zeros, Decode.jOffset, Decode.branchImmediates, *] <;> decoder_bits_expanded))
    unless (← getGoals).isEmpty do throwError "compressed bits unresolved"
    instantiateMVars m
  let saved ← saveState
  -- Runtime failures (recursion depth) must become ordinary errors so callers can fall back.
  tryCatchRuntimeEx (attempt true) fun _ => do
    saved.restore
    tryCatchRuntimeEx (attempt false) fun _ =>
      throwError "compressed operand identity unresolved"

/-- Compare compressed execution with its base expansion, including C.MV and hints. -/
elab "compressed_execution" : tactic => withoutRecover do
  prepareDecoderFields
  addSelectorFacts
  withMainContext do
    let g ← getMainGoal
    let some (_, lhs, rhs) := (← instantiateMVars (← g.getType)).eq? | throwError "execution equality expected"
    let cast := lhs.getAppArgs[0]!
    let base := rhs.getAppArgs[0]!
    let st := lhs.getAppArgs[1]!
    let some inv := (← getLCtx).findFromUserName? `hinv' | throwError "execution invariant expected"
    let result ← whnf (← mkAppM ``execute #[cast, st])
    let ret ← whnf result.getAppArgs[result.getAppNumArgs - 2]!
    let hb ← mkFreshExprMVar (← mkAppM ``Decode.CompressedBase #[base])
    setGoals [hb.mvarId!]
    evalTactic (← `(tactic| constructor))
    let hb ← instantiateMVars hb
    let baseProof ← mkAppM ``Decode.compressedBase_executeFull #[hb]
    let baseProof ← mkEqSymm (← mkCongrFun baseProof st)
    let nopRun ← mkAppM ``Decode.compressed_addi_zero #[
      mkApp2 (mkConst ``BitVec.ofNat) (toExpr 12) (toExpr 0), mkConst ``zreg, st, inv.toExpr]
    let some (_, nopLeft, retired) := (← inferType nopRun).eq? | throwError "no-op equality expected"
    let nop := nopLeft.getAppArgs[0]!
    let execution := Expr.lam `ast (mkConst ``instruction)
      (mkApp2 (mkConst ``execute) (.bvar 0) st) .default
    if ret.isAppOf ``ExecutionResult.ExecuteAs then
      let expanded := ret.getAppArgs[0]!
      let saved ← saveState
      let middle ← try
        let heq ← proveCompressedBits (← mkEq expanded base)
        let f := Expr.lam `ast (mkConst ``instruction) (mkApp2 (mkConst ``execute) (.bvar 0) st) .default
        mkCongrArg f heq
      catch _ => do
        saved.restore
        -- The remaining cases are architectural hints or branches with swapped inputs.
        let target ← mkEq (← mkAppM ``execute #[expanded, st]) (← mkAppM ``execute #[base, st])
        let m ← mkFreshExprMVar target
        setGoals [m.mvarId!]
        let key := expanded.getAppFn.constName!
        let tup ← whnf expanded.getAppArgs[0]!
        let mut args := #[]
        let mut rest := tup
        for _ in [:3] do
          if rest.isAppOf ``Prod.mk then
            args := args.push rest.getAppArgs[2]!
            rest ← whnf rest.getAppArgs[3]!
        args := args.push rest
        if key == ``instruction.BTYPE then
          let other ← mkAppM ``instruction.BTYPE #[← mkAppM ``Prod.mk #[args[0]!, ← mkAppM ``Prod.mk #[args[2]!, ← mkAppM ``Prod.mk #[args[1]!, args[3]!]]]]
          let heq ← proveCompressedBits (← mkEq other base)
          let hop ← mkFreshExprMVar (mkOr (← mkEq args[3]! (mkConst ``bop.BEQ)) (← mkEq args[3]! (mkConst ``bop.BNE)))
          setGoals [hop.mvarId!]
          evalTactic (← `(tactic| first | exact Or.inl rfl | exact Or.inr rfl))
          let pr ← mkAppM `Decode.compressed_branch_swap #[args[0]!, args[1]!, args[2]!, args[3]!, ← instantiateMVars hop, st, inv.toExpr]
          let f := Expr.lam `ast (mkConst ``instruction) (mkApp2 (mkConst ``execute) (.bvar 0) st) .default
          m.mvarId!.assign (← mkEqTrans pr (← mkCongrArg f heq))
        else
          -- Normalize just the fields responsible for the hint's discarded write.
          let mut facts := #[]
          let addFact (ty : Expr) : TacticM Expr := do
            let pr ← proveCompressedBits ty
            return pr
          if key == ``instruction.ITYPE then
            try
              facts := facts.push (← addFact (← mkEq args[2]! (mkConst ``zreg)))
            catch _ =>
              facts := facts.push (← addFact (← mkEq args[0]! (mkApp2 (mkConst ``BitVec.ofNat) (toExpr 12) (toExpr 0))))
              facts := facts.push (← addFact (← mkEq args[1]! args[2]!))
          else if key == ``instruction.UTYPE then facts := facts.push (← addFact (← mkEq args[1]! (mkConst ``zreg)))
          else if key == ``instruction.RTYPE then facts := facts.push (← addFact (← mkEq args[2]! (mkConst ``zreg)))
          else throwError "unhandled compressed expansion {expanded}"
          let hnop ← proveCompressedBits (← mkEq base nop)
          let baseRun ← mkEqTrans (← mkCongrArg execution hnop) nopRun
          let n ← mkFreshExprMVar (← mkEq (← mkAppM ``execute #[expanded, st]) retired)
          let mut goal := n.mvarId!
          let mut names := #[]
          for fact in facts do
            let name ← mkFreshUserName `hint_field
            let gn ← goal.assert name (← inferType fact) fact
            let (_, gn) ← gn.intro1P
            goal := gn
            names := names.push (mkIdent name)
          setGoals [goal]
          evalTactic (← `(tactic| try simp only [$[$names:ident],*]))
          unless (← getGoals).isEmpty do evalTactic (← `(tactic| first
            | exact Decode.compressed_addi_zero _ _ _ $(mkIdent inv.userName)
            | exact Decode.compressed_add_zero _ _ $(mkIdent inv.userName)
            | exact Decode.compressed_lui_zero _ _
            | exact Decode.compressed_add_zero_dest _ _ _ $(mkIdent inv.userName)))
          m.mvarId!.assign (← mkEqTrans (← instantiateMVars n) (← mkEqSymm baseRun))
        instantiateMVars m
      let expProof ← mkAppM ``decoded_expansion #[cast, expanded, ← mkEqRefl (← mkAppM ``execute #[cast])]
      let expProof ← mkCongrFun expProof st
      g.assign (← mkEqTrans expProof (← mkEqTrans middle baseProof))
    else
      let hnop ← proveCompressedBits (← mkEq base nop)
      let baseRun ← mkEqTrans (← mkCongrArg execution hnop) nopRun
      let m ← mkFreshExprMVar (← mkEq lhs retired)
      setGoals [m.mvarId!]
      evalTactic (← `(tactic| rfl))
      g.assign (← mkEqTrans (← instantiateMVars m)
        (← mkEqTrans (← mkEqSymm baseRun) baseProof))
    setGoals []
