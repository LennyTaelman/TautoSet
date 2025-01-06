import Mathlib.Tactic.Tauto
import Mathlib.Data.Set.Basic


/-
  This file defines a `setauto` tactic and runs a number of tests against it

  The hope is to prove any tautology involving hypotheses and goals of the form X ⊆ Y or X = Y,
  where X, Y are expressions built using ∪, ∩, \, and ᶜ from finitely many variables of type Set α

  See the test examples below.

  Based on suggestions by Martin Dvořák and Damiano Testa
-/

/-
  TODO: make this tactic fail if it fails to prove the goal?
-/


-- macro "setauto" : tactic => `(tactic|(
--   -- unfold definition of \ and Disjoint
--   try simp only [Set.diff_eq, Set.disjoint_iff] at *;
--   -- bring hypotheses and goal into some kind of normal form
--   try simp only [
--     ←Set.univ_subset_iff, ←Set.subset_empty_iff,
--     Set.compl_subset_iff_union,
--     Set.union_empty, Set.inter_univ,
--     Set.compl_union, Set.compl_inter,
--     compl_compl,
--   ] at *;
--   -- now at goal only (!) apply extensionality
--   try simp only [
--     Set.ext_iff, Set.subset_def,
--     Set.mem_union, Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_empty_iff_false];
--   -- further simplification at hypotheses;
--   -- this could be done earlier, but don't know how to exclude applying them to the goal!
--   try simp only [Set.Subset.antisymm_iff, Set.subset_inter_iff, Set.union_subset_iff, ← Set.univ_subset_iff] at *;
--   try tauto
--   ))


macro "setauto" : tactic => `(tactic|(
  -- unfold definition of \ and Disjoint
  try simp only [Set.diff_eq, Set.disjoint_iff] at *;
  -- bring hypotheses and goal into some kind of normal form
  try simp only [
    ←Set.univ_subset_iff, ←Set.subset_empty_iff,
    Set.compl_subset_iff_union,
    Set.union_empty, Set.inter_univ,
    Set.compl_union, Set.compl_inter,
    compl_compl,
  ] at *;
  -- now at goal only (!) apply extensionality
  try simp only [
    Set.ext_iff, Set.subset_def,
    Set.mem_union, Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_empty_iff_false] at *;
  -- further simplification at hypotheses;
  -- this could be done earlier, but don't know how to exclude applying them to the goal!
  try simp only [Set.Subset.antisymm_iff, Set.subset_inter_iff, Set.union_subset_iff, ← Set.univ_subset_iff] at *;
  -- try simp only [
  --   Set.ext_iff, Set.subset_def,
  --   Set.mem_union, Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_empty_iff_false ] at *
  try intro x
  try simp_all only [and_imp, implies_true]
  try tauto
))


-- test

variable {α : Type} (A B C D E : Set α)


-- this still fails, but it looks like we should be close!
example (h : A ∩ B ⊆ C) (h2 : C ∩ D ⊆ E) : A ∩ B ∩ D ⊆ E := by setauto

example (h : E = Aᶜᶜ ∩ Cᶜᶜᶜ ∩ D) : D ∩ (B ∪ Cᶜ) ∩ A = E ∪ (A ∩ Dᶜᶜ ∩ B)ᶜᶜ := by setauto

example (h1 : A = B) : A = B := by setauto

example (h1 : A = B) (h2 : B ⊆ C): A ⊆ C := by setauto

example (h1 : A ⊆ B \ C) : A ⊆ B := by setauto

example (h1 : A ∩ B = Set.univ) : A = Set.univ := by setauto

example (h1 : Aᶜ ⊆ ∅) : A = Set.univ := by setauto

example (h1: Set.univ ⊆ Aᶜ) : A = ∅ := by setauto

example : A ∩ ∅ = ∅ := by setauto

example : A ∪ Set.univ = Set.univ := by setauto

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
