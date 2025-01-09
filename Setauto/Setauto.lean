import Mathlib.Tactic.Tauto
import Mathlib.Data.Set.Basic

/-
  This file defines a `setauto` tactic and runs a number of tests against it

  The hope is to prove any tautology involving hypotheses and goals of the form
  X ⊆ Y or X = Y, where X, Y are expressions built using ∪, ∩, \, and ᶜ from
  finitely many variables of type Set α. It also unfolds expressions of the form
  Disjoint A B.

  See the test examples below.
-/

open Lean Elab.Tactic

/-
  The `specialize_all` tactic is a simple tactic that loops over
  all hypotheses in the local context.

  Usage: `specialize_all x`, where `x` is a term. Equivalent to running
  `specialize h x` for all hypotheses h where this tactic succeeds.
-/

syntax (name := specialize_all) "specialize_all" term : tactic

@[tactic specialize_all] def evalSpecializeAll : Tactic :=
    fun stx => withMainContext do
  match stx with
  | `(tactic| specialize_all $x:term) =>
    -- loop over all hypotheses h
    let ctx ← Lean.MonadLCtx.getLCtx
    ctx.forM fun h: Lean.LocalDecl => do
      let s ← saveState
      try
        -- run `specialize h x`
        evalTactic (← `(tactic|specialize $(mkIdent h.userName) $x))
      catch _ =>
        restoreState s
  | _ => throwError "unexpected input"

-- test for specialize_all
example (h1 : ∀ x : ℕ , x = x) (h2 : 1 + 2 = 2)
    (h3 : ∀ x : ℕ , x = x + 1) : ∀ y : ℕ, 0 = 1 := by
  intro y
  specialize_all (y+3)
  sorry


macro "setauto" : tactic => `(tactic|(
  · (
  simp_all only [
    Set.diff_eq, Set.disjoint_iff,
    Set.ext_iff, Set.subset_def,
    Set.mem_union, Set.mem_compl_iff, Set.mem_empty_iff_false,
    Set.mem_inter_iff,
  ];
  try intro x
  try specialize_all x
  <;> tauto)
))



-- TODO: make setauto a finishing tactic; either closes goal, or throws error
-- TODO: check what happens in the presence of multiple goals


variable {α : Type} (A B C D E : Set α)


-- non-finishing example; raises error as desired
example (h : B ⊆ A ∪ A) : 1=0 := by
-- setauto -- tauto failed to solve some goals
  sorry

-- finishes early, tauto returns 'no goals to be solved'
example (h : B ⊆ A ∪ A) : 1=1 := by
  setauto -- simp closed the goal, tauto raises error





-- intended use examples

example (h : B ∪ C ⊆ A ∪ A) : B ⊆ A := by setauto

example (h: B ∩ B ∩ C ⊇ A) : A ⊆ B := by setauto

example (h1 : A ⊆ B ∪ C) (h2 : C ⊆ D): A ⊆ B ∪ D := by setauto

example (h1 : A = Aᶜ) : B = ∅ := by setauto

example (h1 : A ⊆ Aᶜ \ B) : A = ∅ := by setauto

example (h : A ∩ B ⊆ C) (h2 : C ∩ D ⊆ E) : A ∩ B ∩ D ⊆ E := by setauto

example (h : E = Aᶜᶜ ∩ Cᶜᶜᶜ ∩ D) : D ∩ (B ∪ Cᶜ) ∩ A = E ∪ (A ∩ Dᶜᶜ ∩ B)ᶜᶜ := by setauto

example (h : E ⊇ Aᶜᶜ ∩ Cᶜᶜᶜ ∩ D) : D ∩ (B ∪ Cᶜ) ∩ A ⊆  E ∪ (A ∩ Dᶜᶜ ∩ B)ᶜᶜ := by setauto

example (h1 : A = B) : A = B := by setauto

example (h1 : A = B) (h2 : B ⊆ C): A ⊆ C := by setauto

example (h1 : A ⊆ B \ C) : A ⊆ B := by setauto

example (h1 : A ∩ B = Set.univ) : A = Set.univ := by setauto

example (h1 : A ∪ B = ∅) : A = ∅ := by setauto

example (h1 : Aᶜ ⊆ ∅) : A = Set.univ := by setauto

example (h1: Set.univ ⊆ Aᶜ) : A = ∅ := by setauto

example : A ∩ ∅ = ∅ := by setauto

example : A ∪ Set.univ = Set.univ := by setauto

example : A ⊆ Set.univ := by setauto

example (h1 : A ⊆ B) (h2: B ⊆ A) : A = B := by setauto

example : A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) := by setauto

example : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := by setauto

example : A ⊆ (A ∪ B) ∪ C := by setauto

example : A ∩ (B ∪ C) ⊆ (A ∩ B) ∪ (A ∩ C) := by setauto

example : A ∩ B ⊆ A := by setauto

example : A ⊆ A ∪ B := by setauto

example (h1 : Set.univ ⊆ A) : A = Set.univ := by setauto

example (h1 : B ⊆ A) (h2 : Set.univ ⊆ B): Set.univ = A := by setauto

example (h1 : A ⊆ B) (h2 : C ⊆ D) : C \ B ⊆ D \ A := by setauto

example (h : A ⊆ B ∧ C ⊆ D) : C \ B ⊆ D \ A := by setauto

example (h1 : Disjoint A B) (h2 : C ⊆ A) : Disjoint C (B \ D) := by setauto

example : Aᶜᶜᶜ = Aᶜ := by setauto

example : A ⊆ Set.univ := by setauto

example : ∅ ⊆ A := by setauto

example (hA : A ⊆ ∅) : A = ∅ := by setauto

example : Aᶜᶜ = A := by setauto

example (hAB : A ⊆ B) (hBC : B ⊆ C) : A ⊆ C := by setauto

example : (Aᶜ ∪ B ∪ C)ᶜ = Cᶜ ∩ Bᶜ ∩ A := by setauto

example : (Aᶜ ∩ B ∩ Cᶜᶜ)ᶜᶜᶜᶜᶜ = Cᶜ ∪ Bᶜ ∪ ∅ ∪ A ∪ ∅ := by setauto

example : D ∩ (B ∪ Cᶜ) ∩ A = (Aᶜᶜ ∩ Cᶜᶜᶜ ∩ D) ∪ (A ∩ Dᶜᶜ ∩ B)ᶜᶜ := by setauto

example (h1 : A ⊆ B) (h2 : B ⊆ C) (h3 : C ⊆ D) (h4 : D = E) (h5 : E ⊆ A) :
  (Aᶜ ∩ B ∪ (C ∩ Bᶜ)ᶜ ∩ (Eᶜ ∪ A))ᶜ ∩ (B ∪ Eᶜᶜ)ᶜ =
  (Dᶜ ∩ C ∪ (B ∩ Aᶜ)ᶜ ∩ (Eᶜ ∪ E))ᶜ ∩ (D ∪ Cᶜᶜ)ᶜ := by setauto

example (h1 : Set.univ ⊆ A) (h2 : A ⊆ ∅) :
  (Aᶜ ∩ B ∩ Cᶜᶜ)ᶜᶜᶜ = (Aᶜ ∩ B ∪ (C ∩ Dᶜ)ᶜ ∩ (Eᶜ ∪ A))ᶜ ∩ (B ∪ Eᶜᶜ)ᶜ := by setauto

example (h1 : A ⊆ B) (h2 : A ⊆ C) (h3 : B ⊆ D) (h4 : C ⊆ D) (h5 : A = D) :
  Bᶜ = Cᶜ := by setauto
