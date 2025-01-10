import Mathlib.Tactic.Tauto
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.SymmDiff

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

#check Set.symmDiff_def

macro "setauto" : tactic => `(tactic|
  · simp_all only [
      Set.diff_eq, Set.disjoint_iff, Set.symmDiff_def,
      Set.ext_iff, Set.subset_def,
      Set.mem_union, Set.mem_compl_iff, Set.mem_inter_iff
    ]
    try intro x
    try specialize_all x
    <;> tauto
)


variable {α : Type} (A B C D E : Set α)


-- non-finishing example; raises error as desired
example (h : B ⊆ A ∪ A) : 1=0 := by
-- setauto -- tauto failed to solve some goals
  sorry

-- finishes early (on simp)
example (h : B ⊆ A ∪ A) : 1=1 := by
  setauto





-- intended use examples

example (h : B ∪ C ⊆ A ∪ A) : B ⊆ A := by setauto

example (h: B ∩ B ∩ C ⊇ A) : A ⊆ B := by setauto

example (h1 : A ⊆ B ∪ C) (h2 : C ⊆ D): A ⊆ B ∪ D := by setauto

example (h1 : A = Aᶜ) : B = ∅ := by setauto

example (h1 : A = Aᶜ) : B = C := by setauto

example (h1 : A ⊆ Aᶜ \ B) : A = ∅ := by setauto

example (h : Set.univ ⊆ ((A ∪ B) ∩ C) ∩ ((Aᶜ ∩ Bᶜ) ∪ Cᶜ)) : D \ B ⊆ E ∩ Aᶜ := by setauto

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


-- examples from https://github.com/Ivan-Sergeyev/seymour/blob/d8fcfa23336efe50b09fa0939e8a4ec3a5601ae9/Seymour/ForMathlib/SetTheory.lean

section Other

/-- todo: desc -/
lemma setminus_inter_union_eq_union {X Y : Set α} : X \ (X ∩ Y) ∪ Y = X ∪ Y := by setauto

/-- todo: desc -/
lemma nonempty_inter_not_ssubset_empty_inter {A B E : Set α} (hA : (A ∩ E).Nonempty) (hB : B ∩ E = ∅) :
    ¬(A ⊂ B) := by sorry

/-- todo: desc -/
lemma ssubset_self_union_other_elem {a : α} {X : Set α} (ha : a ∉ X) : X ⊂ X ∪ {a} := by sorry

/-- todo: desc -/
lemma singleton_union_ssubset_union_iff {a : α} {A B : Set α} (haA : a ∉ A) (haB : a ∉ B) :
    A ∪ {a} ⊂ B ∪ {a} ↔ A ⊂ B := by sorry

/-- todo: desc -/
lemma ssub_parts_ssub {A B E₁ E₂ : Set α}
    (hA : A ⊆ E₁ ∪ E₂) (hB : B ⊆ E₁ ∪ E₂) : (A ∩ E₁ ⊂ B ∩ E₁) ∧ (A ∩ E₂ ⊂ B ∩ E₂) → A ⊂ B := by sorry


/-- todo: desc -/
lemma sub_parts_eq {A E₁ E₂ : Set α} (hA : A ⊆ E₁ ∪ E₂) : (A ∩ E₁) ∪ (A ∩ E₂) = A := by setauto

/-- todo: desc -/
lemma elem_notin_set_minus_singleton (a : α) (X : Set α) : a ∉ X \ {a} := by setauto

/-- todo: desc -/
lemma sub_union_diff_sub_union {A B C : Set α} (hA : A ⊆ B \ C) : A ⊆ B := by setauto

/-- todo: desc -/
lemma singleton_inter_subset_left {X Y : Set α} {a : α} (ha : X ∩ Y = {a}) : {a} ⊆ X := by setauto

/-- todo: desc -/
lemma singleton_inter_subset_right {X Y : Set α} {a : α} (ha : X ∩ Y = {a}) : {a} ⊆ Y := by setauto

/-- Being a subset is preserved under subtracting sets. -/
lemma diff_subset_parent {X₁ X₂ E : Set α} (hX₁E : X₁ ⊆ E) : X₁ \ X₂ ⊆ E := by setauto

/-- Being a subset is preserved under taking intersections. -/
lemma inter_subset_parent_left {X₁ X₂ E : Set α} (hX₁E : X₁ ⊆ E) : X₁ ∩ X₂ ⊆ E := by setauto

/-- Being a subset is preserved under taking intersections. -/
lemma inter_subset_parent_right {X₁ X₂ E : Set α} (hX₂E : X₂ ⊆ E) : X₁ ∩ X₂ ⊆ E := by setauto

/-- Intersection of two sets is subset of their union. -/
lemma inter_subset_union {X₁ X₂ : Set α} : X₁ ∩ X₂ ⊆ X₁ ∪ X₂ := by setauto

/-- todo: desc -/
lemma subset_diff_empty_eq {A B : Set α} (hAB : A ⊆ B) (hBA : B \ A = ∅) : A = B := by setauto

end Other


section Disjoint

/-- todo: desc -/
lemma Disjoint.ni_of_in {X Y : Set α} {a : α} (hXY : Disjoint X Y) (ha : a ∈ X) :
    a ∉ Y := by setauto

/-- todo: desc -/
lemma disjoint_of_singleton_inter_left_wo {X Y : Set α} {a : α} (hXY : X ∩ Y = {a}) :
    Disjoint (X \ {a}) Y := by setauto

/-- todo: desc -/
lemma disjoint_of_singleton_inter_right_wo {X Y : Set α} {a : α} (hXY : X ∩ Y = {a}) :
    Disjoint X (Y \ {a}) := by setauto

/-- todo: desc -/
lemma disjoint_of_singleton_inter_both_wo {X Y : Set α} {a : α} (hXY : X ∩ Y = {a}) :
    Disjoint (X \ {a}) (Y \ {a}) := by setauto

/-- todo: desc -/
lemma disjoint_of_singleton_inter_subset_left {X Y Z : Set α} {a : α} (hXY : X ∩ Y = {a}) (hZ : Z ⊆ X) (haZ : a ∉ Z) :
    Disjoint Z Y := by sorry

/-- todo: desc -/
lemma disjoint_of_singleton_inter_subset_right {X Y Z : Set α} {a : α} (hXY : X ∩ Y = {a}) (hZ : Z ⊆ Y) (haZ : a ∉ Z) :
    Disjoint X Z := by sorry

/-- todo: desc -/
lemma disjoint_nonempty_not_subset {A B : Set α} (hAB : Disjoint A B) (hA : A.Nonempty) :
    ¬(A ⊆ B) := by sorry

/-- todo: desc -/
lemma disjoint_nonempty_not_ssubset {A B : Set α} (hAB : Disjoint A B) (hA : A.Nonempty) :
    ¬(A ⊂ B) := by sorry

/-- todo: desc -/
lemma ssubset_union_disjoint_nonempty {X Y : Set α} (hXY : Disjoint X Y) (hY : Y.Nonempty) :
    X ⊂ X ∪ Y := by sorry

/-- todo: desc -/
lemma union_ssubset_union_iff {A B X : Set α} (hAX : Disjoint A X) (hBX : Disjoint B X) :
    A ∪ X ⊂ B ∪ X ↔ A ⊂ B := by sorry

/-- todo: desc -/
lemma union_subset_union_iff {A B X : Set α} (hAX : Disjoint A X) (hBX : Disjoint B X) :
    A ∪ X ⊆ B ∪ X ↔ A ⊆ B := by
  constructor
  · intro h; setauto
  · intro h; setauto

lemma ssubset_disjoint_union_nonempty {X₁ X₂ : Set α} (hXX : Disjoint X₁ X₂) (hX₂ : X₂.Nonempty) :
    X₁ ⊂ X₁ ∪ X₂ := by sorry

lemma ssubset_disjoint_nonempty_union {X₁ X₂ : Set α} (hXX : Disjoint X₁ X₂) (hX₁ : X₁.Nonempty) :
    X₂ ⊂ X₁ ∪ X₂ := by sorry


/-- Symmetric difference of two sets is their union minus their intersection. -/
lemma symmDiff_eq_alt (X Y : Set α) : symmDiff X Y = (X ∪ Y) \ (X ∩ Y) := by setauto

/-- Symmetric difference of two sets is disjoint with their intersection. -/
lemma symmDiff_disjoint_inter (X Y : Set α) : Disjoint (symmDiff X Y) (X ∩ Y) := by setauto

/-- todo: desc -/
lemma symmDiff_empty_eq (X : Set α) : symmDiff X ∅ = X := by setauto

/-- todo: desc -/
lemma empty_symmDiff_eq (X : Set α) : symmDiff ∅ X = X := by setauto

/-- todo: desc -/
lemma symmDiff_subset_ground_right {X Y E : Set α} (hE : symmDiff X Y ⊆ E) (hX : X ⊆ E) : Y ⊆ E := by setauto

/-- todo: desc -/
lemma symmDiff_subset_ground_left {X Y E : Set α} (hE : symmDiff X Y ⊆ E) (hX : Y ⊆ E) : X ⊆ E := by setauto
