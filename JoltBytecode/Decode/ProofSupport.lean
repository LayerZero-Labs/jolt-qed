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
  unfold width_enc_backwards_matches
  split <;> bv_decide

private theorem decoder_bool_matches (x : BitVec 1) : bool_bit_backwards_matches x = true := by
  unfold bool_bit_backwards_matches
  split <;> bv_decide

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
    let prop ← if isDecide then pure args[3]!.getAppArgs[0]!
      else mkEq args[3]! (mkConst ``Bool.true)
    let inst := if isDecide then args[3]!.getAppArgs[1]! else mkConst ``Bool.true
    let saved ← saveState
    let prove (b : Bool) : TacticM Expr := do
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
      evalTactic (← `(tactic| simp [Sail.BitVec.extractLsb, BitVec.extractLsb,
        Decode.signBitMask, Functions.regidx_bit_width, decoder_reg_beq, bne, zreg, sp, ra, zero_extend, Sail.BitVec.zeroExtend, encdec_reg_backwards_matches, encdec_creg_backwards_matches, Functions.base_E_enabled,
        encdec_uop_backwards_matches, encdec_bop_backwards_matches, encdec_iop_backwards_matches,
        encdec_amoop_backwards_matches, encdec_mul_op_backwards_matches, encdec_csrop_backwards_matches, width_enc_wide_backwards_matches,
        encdec_biop_backwards_matches, lrsc_width_valid, decoder_width_matches, decoder_bool_matches, valid_load_encdec, Functions.xlen_bytes, Functions.xlen, width_enc_backwards, width_enc_wide_backwards, decoder_bool_value, Functions.not, *] <;> bv_decide))
      unless (← getGoals).isEmpty do throwError "guard unresolved"
      instantiateMVars m
    let (b, hp) ← try pure (false, ← prove false) catch _ => do
      saved.restore
      pure (true, ← prove true)
    unless isDecide do
      let hp ← if b then pure hp else mkAppM ``Bool.eq_false_of_not_eq_true #[hp]
      let value := mkConst (if b then ``Bool.true else ``Bool.false)
      let p := Expr.lam `guard (mkConst ``Bool) (mkAppN fn (args.set! 3 (.bvar 0))) .default
      return (mkAppN fn (args.set! 3 value), ← mkCongrArg p hp)
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
            evalTactic (← `(tactic| try simp only [Decode.branchImmediates, Decode.jOffset, Decode.signBitMask,
              Sail.BitVec.extractLsb, BitVec.extractLsb]))
            unless (← getGoals).isEmpty do evalTactic (← `(tactic| bv_decide))
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

/-- Prove operand identities after normalizing compressed fields, such as C.J offsets. -/
private def proveCompressedBits (ty : Expr) : TacticM Expr := withoutRecover do
  let m ← mkFreshExprMVar ty
  setGoals [m.mvarId!]
  let stateNames := #[`hinv', `s', `hinv, `s].map mkIdent
  evalTactic (← `(tactic| try clear $[$stateNames:ident]*))
  evalTactic (← `(tactic| try simp only [Decode.signBitMask] at *))
  unless (← getGoals).isEmpty do evalTactic (← `(tactic| simp [encdec_creg_backwards, creg2reg_idx, zero_extend,
    Sail.BitVec.zeroExtend, sign_extend, Sail.BitVec.signExtend,
    Sail.BitVec.extractLsb, BitVec.extractLsb, Functions.regidx_bit_width, zreg, sp, ra,
    zeros, Decode.signBitMask, Decode.jOffset, Decode.branchImmediates, *] <;> bv_decide))
  instantiateMVars m

/-- Compare compressed execution with its base expansion, including C.MV and hints. -/
elab "compressed_execution" : tactic => withoutRecover do
  prepareDecoderFields
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
