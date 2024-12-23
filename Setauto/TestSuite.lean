import Mathlib

/-
  This collects a wide range of `trivial' set-theoretic
  lemma's that should be provable by a generic setauto hammer
-/

variable {α : Type} (A B C D E : Set α)


-- not solved by aesop, simp_all
example : A ⊆ (A ∪ B) ∪ C := by tauto

example : A ⊆ B ∧ C ⊆ D → C \ B ⊆ D \ A := by
  intro ⟨ h1, h2 ⟩
  exact Set.diff_subset_diff h2 h1

example (h1 : Disjoint A B) (h2 : C ⊆ A) : Disjoint C (B \ D) := by
  rw [Set.disjoint_iff] at *
  have h3 : C ∩ B ⊆ A ∩ B := Set.inter_subset_inter h2 fun ⦃a⦄ a ↦ a
  have h4 : C ∩ (B \ D) ⊆ C ∩ B := Set.inter_subset_inter (fun ⦃a⦄ a ↦ a) Set.diff_subset
  aesop
