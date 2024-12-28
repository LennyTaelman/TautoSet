import Mathlib.Tactic.Tauto
import Mathlib.Data.Set.Basic


/-
  play a bit with tauto, to get a feel for its scope
  in particular: problems with handling things under universal
  quantifiers
-/

variable {α : Type}

example (P Q : α → Prop) (h1 : ∀ x, P x ∧ Q x) : ∀ x, P x := by
  intro x
  simp_all only

example (P Q : α → Prop) (h1 : ∀ x, P x → Q x) (h2 : ∀ x, P x):
    ∀ x, Q x := by
  intro x
  tauto
