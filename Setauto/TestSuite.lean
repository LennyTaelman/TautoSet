import Mathlib.Tactic.Tauto
import Mathlib.Data.Set.Basic


/-
  This collects a wide range of `trivial' set-theoretic
  lemma's that should be provable by a generic hammer

  The proofs below serve no purpose other than to make sure there are no
  false stamtements in the test suite

  The goal is restricted to = and ⊆ between terms of type Set α,
-/

variable {α : Type} (A B C D E : Set α)


example : A ∩ ∅ = ∅ := by simp only [Set.inter_empty]

example : A ∪ Set.univ = Set.univ := Set.union_univ A

example (h1 : A ⊆ B) (h2: B ⊆ A) : A = B := Set.Subset.antisymm h1 h2

example : A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) := Set.union_inter_distrib_left A B C

example : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := Set.inter_union_distrib_left A B C

example : A ⊆ (A ∪ B) ∪ C := by tauto

example : A ∩ (B ∪ C) ⊆ (A ∩ B) ∪ (A ∩ C) := by
  rw [← Set.inter_union_distrib_left]

example : A ∩ B ⊆ A := Set.inter_subset_left

example : A ⊆ A ∪ B := Set.subset_union_left

example (h1 : A ∩ B = Set.univ) : A = Set.univ := by
  rw [Set.eq_univ_iff_forall] at *
  intro x
  simp_all only [Set.mem_inter_iff]

example (h1 : Set.univ ⊆ A) : A = Set.univ := by
  exact Set.eq_univ_of_univ_subset h1

example (h1 : B ⊆ A) (h2 : Set.univ ⊆ B): Set.univ = A := by
  simp_all only [Set.univ_subset_iff]

example (h1 : Aᶜ ⊆ ∅) : A = Set.univ := by
  simp_all only [Set.subset_empty_iff, Set.compl_empty_iff]

example (h1 : A ⊆ B \ C) : A ⊆ B := subset_trans h1 Set.diff_subset

example (h1 : A ⊆ B) (h2 : C ⊆ D) : C \ B ⊆ D \ A := by
  exact Set.diff_subset_diff h2 h1

example (h : A ⊆ B ∧ C ⊆ D) : C \ B ⊆ D \ A := by
  exact Set.diff_subset_diff h.2 h.1

example (h1 : Disjoint A B) (h2 : C ⊆ A) : Disjoint C (B \ D) := by
  simp only [
    Set.ext_iff,
    Set.subset_def,
    Set.mem_inter_iff,
    Set.mem_union,
    Set.mem_compl_iff,
    Set.mem_diff,
    Set.disjoint_iff,
    Set.mem_empty_iff_false,
    -- Set.mem_univ,
    -- imp_false,
    -- not_not
  ] at *
  tauto

example : Aᶜᶜᶜ = Aᶜ := compl_compl_compl A

example : A ⊆ Set.univ := Set.subset_univ A

example : ∅ ⊆ A := Set.empty_subset A

example (hA : A ⊆ ∅) : A = ∅ := Set.subset_empty_iff.mp hA

example : Aᶜᶜ = A := compl_compl A

example (hAB : A ⊆ B) (hBC : B ⊆ C) : A ⊆ C := subset_trans hAB hBC

example : (Aᶜ ∪ B ∪ C)ᶜ = Cᶜ ∩ Bᶜ ∩ A := by
  simp only [Set.compl_union, compl_compl]
  ext x
  apply Iff.intro
  · intro h
    simp_all only [Set.mem_inter_iff, Set.mem_compl_iff, not_false_eq_true, and_self]
  · intro h
    simp_all only [Set.mem_inter_iff, Set.mem_compl_iff, not_false_eq_true, and_self]

example (α : Type) (A B C : Set α) :
    (Aᶜ ∩ B ∩ Cᶜᶜ)ᶜᶜᶜᶜᶜ = Cᶜ ∪ Bᶜ ∪ ∅ ∪ A ∪ ∅ := by
  simp only [compl_compl, Set.union_empty]
  ext x
  apply Iff.intro
  · intro h
    simp_all
    tauto
  · intro h
    simp_all
    tauto

example (α : Type) (A B C D : Set α) :
    D ∩ (B ∪ Cᶜ) ∩ A = (Aᶜᶜ ∩ Cᶜᶜᶜ ∩ D) ∪ (A ∩ Dᶜᶜ ∩ B)ᶜᶜ := by
  simp_all
  ext x
  apply Iff.intro
  · intro h
    simp_all
    tauto
  · intro h
    simp_all
    tauto
