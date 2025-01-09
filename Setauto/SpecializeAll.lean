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

open Lean Elab.Tactic





syntax (name := specialize_all) "specialize_all " term : tactic

-- attempts to specialize all hypotheses with the given term

@[tactic specialize_all] def evalSpecializeAll : Tactic :=
    fun stx => withMainContext do
  match stx with
  | `(tactic| specialize_all $x:term) =>
    -- loop over all hypotheses 'decl'
    let ctx ← Lean.MonadLCtx.getLCtx
    ctx.forM fun decl: Lean.LocalDecl => do
      let s ← saveState
      try
        let n := decl.userName
        dbg_trace f!"+ [specialize_all] n: {n}"
        evalTactic (← `(tactic|specialize $(mkIdent n) $x))
        -- produce syntax for 'n applied to x'
      catch _ =>
        restoreState s
  | _ => throwError "unexpected input"

-- test for specialize_all

example (h1 : ∀ x : ℕ , x = x)
    (h2 : 1 + 2 = 2)
    (h3 : ∀ y : ℕ , y = y + 1) : ∀ y : ℕ, 0 = 1 := by
  intro y
  specialize_all (y+3)
  simp at h2
