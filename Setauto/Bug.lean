import Mathlib.Tactic.Tauto

-- solved with Mathlib bump

lemma weird (α : Type) (h : α → False) (x : α) : False := by
  tauto -- No goals, yet lean gives "application type mismatch"

#check weird -- unknown identifier 'weird'
