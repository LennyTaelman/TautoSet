import Mathlib.Tactic.Tauto
import Mathlib.Data.Set.Basic


/-
  This collects a wide range of `trivial' set-theoretic
  lemma's that should be provable by a generic setauto hammer

  The proofs below serve no purpose other than to make sure there are no
  false stamtements in the test suite

  The goal is restricted to = and ⊆ between terms of type Set α,
  in particular, no implication arrows or conjunctions/disjunctions in the statements
-/

variable {α : Type} (A B C D E : Set α)


/-
  the core set (including the hardest ones)
-/

example : A ∩ (B ∪ C) ⊆ (A ∩ B) ∪ (A ∩ C) := by sorry

example : A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) := by sorry

example (h1 : A ∩ B = Set.univ) : A = Set.univ := by sorry

example (h1 : Aᶜ ⊆ ∅) : A = Set.univ := by sorry

example (h1 : A ⊆ B) (h2 : C ⊆ D) : C \ B ⊆ D \ A := by sorry

example (h1 : Disjoint A B) (h2 : C ⊆ A) : Disjoint C (B \ D) := by sorry

example (h1 : A ⊆ B \ C ) : A ⊆ B := by sorry

example : Aᶜᶜᶜ = Aᶜ := by sorry




/-
  the rest
-/

example : A ∩ ∅ = ∅ := by simp only [Set.inter_empty]

example : A ∪ Set.univ = Set.univ := Set.union_univ A

example (h1 : A ⊆ B) (h2: B ⊆ A) : A = B := Set.Subset.antisymm h1 h2

example : A ∪ B ∩ C = (A ∪ B) ∩ (A ∪ C) := Set.union_inter_distrib_left A B C

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
  rw [Set.disjoint_iff] at *
  have h3 : C ∩ B ⊆ A ∩ B := Set.inter_subset_inter h2 fun ⦃a⦄ a ↦ a
  have h4 : C ∩ (B \ D) ⊆ C ∩ B := Set.inter_subset_inter (fun ⦃a⦄ a ↦ a) Set.diff_subset
  aesop



example (h1 : Disjoint A B) (h2 : C ⊆ A) : Disjoint C (B \ D) := by
  simp only [Set.disjoint_iff] at *
  simp only [Set.diff_eq] at *
  simp_all only [Set.subset_def, Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_empty_iff_false]
  tauto

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
