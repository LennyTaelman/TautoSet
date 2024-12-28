import Mathlib.Tactic.Tauto
import Mathlib.Data.Set.Basic


/-
  try to setup brutal case distinction loop
-/


/-
  run against testsuite:
-/

variable {α : Type} (A B C D E : Set α)

-- cleaner version
example : A ⊆ B ∧ C ⊆ D → C \ B ⊆ D \ A := by
  -- whatever happens, need to eliminate implication arrows?
  intro ⟨ h1, h2 ⟩
  intro x
  simp only [Set.mem_diff, and_imp]
  tauto

-- this is what a case distinction proof could look like ...
example : A ⊆ B ∧ C ⊆ D → C \ B ⊆ D \ A := by
  intro ⟨ h1, h2 ⟩
  intro x
  simp_all
  by_cases hA : x ∈ A
  <;> by_cases hB : x ∈ B
  <;> by_cases hC : x ∈ C
  <;> by_cases hD : x ∈ D
  <;> tauto

  -- but actually, it works without the by_cases
example : A ⊆ B ∧ C ⊆ D → C \ B ⊆ D \ A := by
  intro ⟨ h1, h2 ⟩
  intro x
  simp_all
  tauto



example (h1 : Disjoint A B) (h2 : C ⊆ A) : Disjoint C (B \ D) := by
  rw [Set.disjoint_iff] at *
  have h3 : C ∩ B ⊆ A ∩ B := Set.inter_subset_inter h2 fun ⦃a⦄ a ↦ a
  have h4 : C ∩ (B \ D) ⊆ C ∩ B := Set.inter_subset_inter (fun ⦃a⦄ a ↦ a) Set.diff_subset
  aesop

example : Disjoint A B ∧ C ⊆ A → Disjoint C (B \ D) := by
  intro ⟨h1, h2⟩
  rw [Set.disjoint_iff] at *
  have h3 : C ∩ B ⊆ A ∩ B := Set.inter_subset_inter h2 fun ⦃a⦄ a ↦ a
  have h4 : C ∩ (B \ D) ⊆ C ∩ B := Set.inter_subset_inter (fun ⦃a⦄ a ↦ a) Set.diff_subset
  aesop
