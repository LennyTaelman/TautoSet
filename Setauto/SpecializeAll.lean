import Mathlib.Tactic.Tauto
import Lean.Elab.SyntheticMVars

/-
  Playground to try to produce a tactic 'specialize_all'
  intended usage: 'specialize_all x', where x is a term loops over
  all hypotheses in the local context and tries to specialize them with x

  TODO: learn some more about metaprogramming

  Better: 'allhyp tactic' : loops over all hypotheses and tries to apply tactic to them?
  Don't reinvent the wheel.....
-/

open Lean Elab.Tactic Parser.Tactic Lean.Meta MVarId Meta

#check evalSpecialize


-- the my_specialize tactic should attempt to specialize
-- and do nothing if things don't typecheck

syntax (name := my_specialize) "my_specialize" term term : tactic

@[tactic my_specialize] def evalMySpecialize : Tactic :=
    fun stx => withMainContext do
  match stx with
  | `(tactic| specialize $h:term $x:term) =>
    dbg_trace f!"+ [my_specialize] h: {h}, x: {x}"
    let h_expr ← elabTerm h none
    let x_expr ← elabTerm x none
    -- now apply h to x
    let hx_expr := (mkApp h_expr x_expr)
    dbg_trace f!"+ [my_specialize] hx_expr: {hx_expr}"
    `(specialize $hx_expr)



  | _ => throwError "unexpected input"


example (h : ∀ x : ℕ , x = x) : ∀ y : ℕ , 1 = 0 := by
  intro y
  specialize h y





  sorry

syntax (name := specialize_all) "specialize_all " term : tactic

#check TSyntax `term

@[tactic specialize_all] def evalSpecializeAll : Tactic :=
    fun stx => withMainContext do
  match stx with
  | `(tactic| specialize_all $x:term) =>
    let ctx ← Lean.MonadLCtx.getLCtx -- get the local context.
    ctx.forM fun decl: Lean.LocalDecl => do
      let s ← saveState
      try
        let n := decl.toExpr
        -- produce syntax for 'n applied to x'
        let e := Syntax.mkApp n.toSyntax #[x]
        let (e, mvarIds') ← elabTermWithHoles e none `specialize (allowNaturalHoles := true)
      catch _ =>
        restoreState s
        -- let h := e.getAppFn
        -- if h.isFVar then
        --   let localDecl ← h.fvarId!.getDecl
        --   let mvarId ← (← getMainGoal).assert localDecl.userName (← inferType e).headBeta e
        --   let (_, mvarId) ← mvarId.intro1P
        --   let mvarId ← mvarId.tryClear h.fvarId!
        --   replaceMainGoal (mvarIds' ++ [mvarId])
        -- else
        --   throwError "'specialize' requires a term of the form `h x_1 .. x_n` where `h` appears in the local context"
  | _ => throwError "unexpected input"




syntax (name := intro_and_specialize) "intro_and_specialize"  : tactic

@[tactic intro_and_specialize] def evalIntroSpec : Tactic := fun _ => do
    -- do `intro' on the target
    let fvarId ← liftMetaTacticAux fun mvarId => do
      let (fvarId, mvarId) ← mvarId.intro `x
      pure (fvarId, [mvarId])
    -- now loop over all hypotheses and try to specialize them with fvarId
    let ctx ← Lean.MonadLCtx.getLCtx -- get the local context.
    ctx.forM fun decl: Lean.LocalDecl => do
      let s ← saveState
      try
        let expr := decl.toExpr -- Find the expression of the declaration.
        -- need to apply e to `random_name; this may fail!
        let e := Expr.app expr (Expr.fvar fvarId)
        -- dbg_trace f!"+ [my_intro] expr: {e}"
        let h := e.getAppFn
        if h.isFVar then
          let localDecl ← h.fvarId!.getDecl
          -- dbg_trace f!"+ [my_intro] h: {localDecl.userName}"
          let t ← inferType e
          -- dbg_trace f!"+ [my_intro] type: {t}"
          let mvarId ← (← getMainGoal).assert localDecl.userName
            t.headBeta e
          -- dbg_trace f!"+ [my_intro] passed assert"
          let (_, mvarId) ← mvarId.intro1P
          let mvarId ← mvarId.tryClear h.fvarId!
          replaceMainGoal ([mvarId])
      catch _ =>
        restoreState s
    pure ()




lemma intro_test (h2 : ∀ y : ℕ , y = y ): ∀ x : ℕ , x = x := by
  intro_and_specialize
  exact h2
  -- weird side effect: intro_test introduced in local context!

-- this fails, need to typecheck before specializing; or catch the error

lemma intro_test2 (h1 : 1 = 0) (h2 : ∀ y : ℕ , y = y ): ∀ x : ℕ , x = x := by
  intro_and_specialize
  exact h2
