import Mathlib.Tactic.Tauto
import Mathlib.Data.Set.Basic



/-
  This file runs the testsuite against a `setauto` tactic.
  Either define this tactic in a macro here, or import it from another file

  Importing from other file is slow! Each change requires 'restart file' in vscode
-/

import Setauto.SimpTauto

-- macro "set-tactic" : tactic => `(tactic|sorry)

-- macro "setauto" : tactic =>
--   `(tactic|
--     try simp only [
--       Set.ext_iff,
--       Set.subset_def,
--       Set.mem_inter_iff,
--       Set.mem_union,
--       Set.mem_compl_iff,
--       Set.mem_diff,
--       Set.disjoint_iff,
--       Set.mem_empty_iff_false,
--       -- Set.mem_univ,
--       imp_false,
--       not_not
--     ] at *
--     <;>
--     try tauto)

variable {α : Type} (A B C D E : Set α)


example (h1 : A ⊆ B \ C) : A ⊆ B := by setauto

example (h1 : A ∩ B = Set.univ) : A = Set.univ := by setauto

example (h1 : Aᶜ ⊆ ∅) : A = Set.univ := by setauto

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
