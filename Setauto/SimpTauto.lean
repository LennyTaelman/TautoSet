import Mathlib


macro "setauto" : tactic => `(tactic|(
  try simp only [] at *;
  try simp only [
    Set.diff_eq,
    Set.disjoint_iff,
    ←Set.univ_subset_iff, ←Set.subset_empty_iff,
    Set.compl_subset_iff_union,
    Set.union_empty, Set.inter_univ,
    Set.compl_union, Set.compl_inter,
    compl_compl,
  ] at *;
  try simp only [Set.ext_iff, Set.subset_def];
  try simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_empty_iff_false];
  try simp only [Set.subset_inter_iff, Set.union_subset_iff, ← Set.univ_subset_iff] at *;
  try tauto
  ))


variable {α : Type} (A B C D E : Set α)

example (h1 : A ⊆ B \ C) : A ⊆ B := by setauto


-- false example:

example : Aᶜ = A := by
  setauto
  -- should fail!
  sorry
