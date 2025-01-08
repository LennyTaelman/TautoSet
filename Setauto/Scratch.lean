import Mathlib.Tactic.Tauto
import Mathlib.Data.Set.Basic



variable {α : Type} (A B C D E : Set α)


/-
  TODO: understand why the two examples below fail.
  Notes:
  1) they are resolved by strengthening the hypotheses to =
  2) they can be resolved by adding intro x and specialize h x

  priority: understand how I can loop over all hypotheses h and
  try "specialize h x"
-/

example (h : B ⊆ A ∪ A) : B ⊆ A := by
-- example (h1 : A ⊆ B ∪ C) (h2 : C ⊆ D): A ⊆ B ∪ D := by
-- example (h1 : A = Aᶜ) : B = ∅ := by
-- example (h1 : A ⊆ Aᶜ \ B) : A = ∅ := by
-- example (h1 : A ∩ B ⊆ C) (h2 : C ∩ D ⊆ E) : A ∩ B ∩ D ⊆ E := by
-- example (h1 : E = Aᶜᶜ ∩ Cᶜᶜᶜ ∩ D) : D ∩ (B ∪ Cᶜ) ∩ A = E ∪ (A ∩ Dᶜᶜ ∩ B)ᶜᶜ := by
-- example (h1 : E ⊇ Aᶜᶜ ∩ Cᶜᶜᶜ ∩ D) : D ∩ (B ∪ Cᶜ) ∩ A ⊆  E ∪ (A ∩ Dᶜᶜ ∩ B)ᶜᶜ := by
-- example (h1 : A = B) : A = B := by
-- example (h1 : A = B) (h2 : B ⊆ C): A ⊆ C := by
-- example (h1 : A ⊆ B \ C) : A ⊆ B := by
-- example (h1 : A ∩ B = Set.univ) : A = Set.univ := by
-- example (h1 : A ∪ B = ∅) : A = ∅ := by
-- example (h1 : Aᶜ ⊆ ∅) : A = Set.univ := by
-- example (h1: Set.univ ⊆ Aᶜ) : A = ∅ := by
-- example : A ∩ ∅ = ∅ := by
-- example : A ∪ Set.univ = Set.univ := by
-- example : A ⊆ Set.univ := by
-- example (h1 : A ⊆ B) (h2: B ⊆ A) : A = B := by
-- example : A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) := by
-- example : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := by
-- example : A ⊆ (A ∪ B) ∪ C := by
-- example : A ∩ (B ∪ C) ⊆ (A ∩ B) ∪ (A ∩ C) := by
-- example : A ∩ B ⊆ A := by
-- example : A ⊆ A ∪ B := by
-- example (h1 : Set.univ ⊆ A) : A = Set.univ := by
-- example (h1 : B ⊆ A) (h2 : Set.univ ⊆ B): Set.univ = A := by
-- example (h1 : A ⊆ B) (h2 : C ⊆ D) : C \ B ⊆ D \ A := by
-- example (h1 : A ⊆ B ∧ C ⊆ D) : C \ B ⊆ D \ A := by
-- example (h1 : Disjoint A B) (h2 : C ⊆ A) : Disjoint C (B \ D) := by
-- example : Aᶜᶜᶜ = Aᶜ := by
-- example : A ⊆ Set.univ := by
-- example : ∅ ⊆ A := by
-- example (h1 : A ⊆ ∅) : A = ∅ := by
-- example : Aᶜᶜ = A := by
-- example (h1 : A ⊆ B) (h2 : B ⊆ C) : A ⊆ C := by
-- example : (Aᶜ ∪ B ∪ C)ᶜ = Cᶜ ∩ Bᶜ ∩ A := by
-- example : (Aᶜ ∩ B ∩ Cᶜᶜ)ᶜᶜᶜᶜᶜ = Cᶜ ∪ Bᶜ ∪ ∅ ∪ A ∪ ∅ := by
-- example : D ∩ (B ∪ Cᶜ) ∩ A = (Aᶜᶜ ∩ Cᶜᶜᶜ ∩ D) ∪ (A ∩ Dᶜᶜ ∩ B)ᶜᶜ := by
-- example (h1 : A ⊆ B) (h2 : B ⊆ C) (h3 : C ⊆ D) (h4 : D = E) (h5 : E ⊆ A) :
--   (Aᶜ ∩ B ∪ (C ∩ Bᶜ)ᶜ ∩ (Eᶜ ∪ A))ᶜ ∩ (B ∪ Eᶜᶜ)ᶜ =
--   (Dᶜ ∩ C ∪ (B ∩ Aᶜ)ᶜ ∩ (Eᶜ ∪ E))ᶜ ∩ (D ∪ Cᶜᶜ)ᶜ := by
-- example (h1 : Set.univ ⊆ A) (h2 : A ⊆ ∅) :
--   (Aᶜ ∩ B ∩ Cᶜᶜ)ᶜᶜᶜ = (Aᶜ ∩ B ∪ (C ∩ Dᶜ)ᶜ ∩ (Eᶜ ∪ A))ᶜ ∩ (B ∪ Eᶜᶜ)ᶜ := by
-- example (h1 : A ⊆ B) (h2 : A ⊆ C) (h3 : B ⊆ D) (h4 : C ⊆ D) (h5 : A = D) :
--   Bᶜ = Cᶜ := by

  -- unfold definitions of A \ B and Disjoint A B,
  try simp only [Set.diff_eq, Set.disjoint_iff] at *
  -- and various simplifications involving univ, ∅, and complements
  -- try simp only [
  --   ←Set.univ_subset_iff, ←Set.subset_empty_iff,
  --   Set.union_empty, Set.inter_univ,
  --   Set.compl_subset_iff_union, compl_compl,
  --   -- Set.union_self,
  -- ] at *;
  -- now apply extensionality
  try simp_all only [
    Set.ext_iff, Set.subset_def,
    Set.mem_union, Set.mem_compl_iff, Set.mem_empty_iff_false,
    Set.mem_inter_iff, and_imp, not_true_eq_false, false_and, and_false,
    iff_not_self,
  ];
  try intro x
  try specialize h x
  try specialize h1 x
  try specialize h2 x
  try specialize h3 x
  try specialize h4 x
  try specialize h5 x
  tauto
