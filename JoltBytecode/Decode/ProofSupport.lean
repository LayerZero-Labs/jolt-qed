import JoltBytecode.Decode.Jolt
import JoltBytecode.Decode.Prefixes
import JoltBytecode.Decode.Configuration

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

private theorem decoder_f3_lo (w : BitVec 32) (n : BitVec 3)
    (h : w.extractLsb 14 12 = n) : w.extractLsb 13 12 = n.extractLsb 1 0 := by bv_decide
private theorem decoder_f3_hi (w : BitVec 32) (n : BitVec 3)
    (h : w.extractLsb 14 12 = n) : w.extractLsb 14 14 = n.extractLsb 2 2 := by bv_decide

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
  unfold width_enc_backwards_matches
  split <;> bv_decide

private theorem decoder_bool_matches (x : BitVec 1) : bool_bit_backwards_matches x = true := by
  unfold bool_bit_backwards_matches
  split <;> bv_decide

private theorem decoder_bool_value (x : BitVec 1) : bool_bit_backwards x = (x == 1) := by
  unfold bool_bit_backwards
  split <;> simp_all

private partial def reduceDecoder (x : Expr) (runs : Array Expr) : TacticM (Expr × Expr) := do
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
    let prop := args[3]!.getAppArgs[0]!
    let inst := args[3]!.getAppArgs[1]!
    let saved ← saveState
    let prove (b : Bool) : TacticM Expr := do
      let m ← mkFreshExprMVar (if b then prop else mkNot prop)
      setGoals [m.mvarId!]
      evalTactic (← `(tactic| try simp only [*]))
      evalTactic (← `(tactic| try simp only [Sail.BitVec.extractLsb, BitVec.extractLsb] at *))
      evalTactic (← `(tactic| simp [Sail.BitVec.extractLsb, BitVec.extractLsb,
        encdec_reg_backwards_matches, encdec_creg_backwards_matches, Functions.base_E_enabled,
        encdec_uop_backwards_matches, encdec_bop_backwards_matches, encdec_iop_backwards_matches,
        encdec_amoop_backwards_matches, encdec_mul_op_backwards_matches, encdec_csrop_backwards_matches, width_enc_wide_backwards_matches,
        encdec_biop_backwards_matches, lrsc_width_valid, decoder_width_matches, decoder_bool_matches, valid_load_encdec, Functions.xlen_bytes, Functions.xlen, width_enc_backwards, width_enc_wide_backwards, decoder_bool_value, Functions.not, *] <;> bv_decide))
      unless (← getGoals).isEmpty do throwError "guard unresolved"
      instantiateMVars m
    let (b, hp) ← try pure (false, ← prove false) catch _ => do
      saved.restore
      pure (true, ← prove true)
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
        if let some (_, l, _) := (← whnf d.type).eq? then
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
  withMainContext <| evalTactic (← `(tactic| simp [_root_.Step.Matches, RiscvInstruction.Matches, Decode.rd, Decode.rs1, Decode.rs2,
    Decode.immI, Decode.immS, Decode.immB, Decode.immU, Decode.immJ,
    Sail.BitVec.extractLsb, BitVec.extractLsb, Functions.regidx_bit_width,
    Sail.BitVec.access, width_enc_backwards, width_enc_wide_backwards, decoder_bool_value, *] <;> first | rfl | bv_decide))

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
