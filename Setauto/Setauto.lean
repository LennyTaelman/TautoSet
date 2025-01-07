import Mathlib.Tactic.Tauto
import Mathlib.Data.Set.Basic


/-
  This file defines a `setauto` tactic and runs a number of tests against it

  The hope is to prove any tautology involving hypotheses and goals of the form X ⊆ Y or X = Y,
  where X, Y are expressions built using ∪, ∩, \, and ᶜ from finitely many variables of type Set α.
  We also allow expressions of the form Disjoint A B.

  See the test examples below.

  Based on suggestions by Martin Dvořák and Damiano Testa
-/

/-
  TODO: make this tactic fail if it fails to prove the goal? If not, then it probably should not
  modify the proof state if not succesful?

  TODO: look at univ_subset_iff and subset_empty_iff; should these simp lemmas be reversed?
-/




macro "setauto" : tactic => `(tactic|(
  -- unfold definitions of A \ B and Disjoint A B,
  try simp only [Set.diff_eq, Set.disjoint_iff] at *
  -- and various simplifications involving univ, ∅, and complements
  try simp only [
    ←Set.univ_subset_iff, ←Set.subset_empty_iff,
    Set.union_empty, Set.inter_univ,
    Set.compl_subset_iff_union, compl_compl,
    -- Set.union_self,
  ] at *;
  -- now apply extensionality
  try simp_all only [
    Set.ext_iff, Set.subset_def,
    Set.mem_union, Set.mem_compl_iff, Set.mem_empty_iff_false,
    Set.mem_inter_iff, and_imp, not_true_eq_false, false_and, and_false,
    iff_not_self,
  ];
  try tauto
))


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
  -- unfold definitions of A \ B and Disjoint A B,
  try simp only [Set.diff_eq, Set.disjoint_iff] at *
  -- and various simplifications involving univ, ∅, and complements
  try simp only [
    ←Set.univ_subset_iff, ←Set.subset_empty_iff,
    Set.union_empty, Set.inter_univ,
    Set.compl_subset_iff_union, compl_compl,
    -- Set.union_self,
  ] at *;
  -- now apply extensionality
  try simp_all only [
    Set.ext_iff, Set.subset_def,
    Set.mem_union, Set.mem_compl_iff, Set.mem_empty_iff_false,
    Set.mem_inter_iff, and_imp, not_true_eq_false, false_and, and_false,
    iff_not_self,
  ];
  intro x
  specialize h x
  tauto


example (h1 : A ⊆ B ∪ C) (h2 : C ⊆ D): A ⊆ B ∪ D := by
   -- unfold definitions of A \ B and Disjoint A B,
  try simp only [Set.diff_eq, Set.disjoint_iff] at *
  -- and various simplifications involving univ, ∅, and complements
  try simp only [
    ←Set.univ_subset_iff, ←Set.subset_empty_iff,
    Set.union_empty, Set.inter_univ,
    Set.compl_subset_iff_union, compl_compl,
    -- Set.union_self,
  ] at *;
  -- now apply extensionality
  try simp_all only [
    Set.ext_iff, Set.subset_def,
    Set.mem_union, Set.mem_compl_iff, Set.mem_empty_iff_false,
    Set.mem_inter_iff, and_imp, not_true_eq_false, false_and, and_false,
    iff_not_self,
  ];
  intro x
  specialize h1 x
  specialize h2 x
  tauto



-- requires iff_not_self
example (h1 : A = Aᶜ) : B = ∅ := by setauto

-- this one requires not_true_eq_false, false_and, and_false
example (h1 : A ⊆ Aᶜ \ B) : A = ∅ := by setauto

-- does not feel very hyghienic...




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
