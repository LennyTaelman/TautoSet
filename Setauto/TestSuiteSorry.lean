import Mathlib.Data.Set.Basic

variable {α : Type} (A B C D E : Set α)


example : A ∩ ∅ = ∅ := by sorry

example : A ∪ Set.univ = Set.univ := by sorry

example (h1 : A ⊆ B) (h2: B ⊆ A) : A = B := by sorry

example : A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) := by sorry

example : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := by sorry

example : A ⊆ (A ∪ B) ∪ C := by sorry

example : A ∩ (B ∪ C) ⊆ (A ∩ B) ∪ (A ∩ C) := by sorry

example : A ∩ B ⊆ A := by sorry

example : A ⊆ A ∪ B := by sorry

example (h1 : A ∩ B = Set.univ) : A = Set.univ := by sorry

example (h1 : Set.univ ⊆ A) : A = Set.univ :=by sorry

example (h1 : B ⊆ A) (h2 : Set.univ ⊆ B): Set.univ = A := by sorry

example (h1 : Aᶜ ⊆ ∅) : A = Set.univ := by sorry

example (h1 : A ⊆ B \ C) : A ⊆ B := by sorry

example (h1 : A ⊆ B) (h2 : C ⊆ D) : C \ B ⊆ D \ A := by sorry

example (h : A ⊆ B ∧ C ⊆ D) : C \ B ⊆ D \ A := by sorry

example (h1 : Disjoint A B) (h2 : C ⊆ A) : Disjoint C (B \ D) := by sorry
