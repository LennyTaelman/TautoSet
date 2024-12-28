import Mathlib


lemma extract_univ  (P Q : α → Prop) : (∀ x, P x → Q x) → (∀ x, P x) → ∀ x, Q x :=
  fun h1 h2 x ↦ h1 x (h2 x)


macro "setauto" : tactic =>
  `(tactic|
    try simp only [
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
    <;>
    -- apply extract_univ <;>
    try tauto)







-- test suite

variable {α : Type} (A B C D : Set α)


example : A ∩ ∅ = ∅ := by setauto

example : A ∪ Set.univ = Set.univ := by setauto

example (h1 : A ⊆ B) (h2: B ⊆ A) : A = B := by setauto

example : A ∪ B ∩ C = (A ∪ B) ∩ (A ∪ C) := by setauto

example : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := by setauto

example : A ⊆ (A ∪ B) ∪ C := by setauto

example : A ∩ (B ∪ C) ⊆ (A ∩ B) ∪ (A ∩ C) := by setauto

example : A ∩ B ⊆ A := by setauto

example : A ⊆ A ∪ B := by setauto

example (h1 : Aᶜ ⊆ ∅) : A = Set.univ := by
  try simp only [
    Set.ext_iff,
    Set.subset_def,
    Set.mem_inter_iff,
    Set.mem_union,
    Set.mem_compl_iff,
    Set.mem_diff,
    Set.disjoint_iff,
    Set.mem_empty_iff_false,
    Set.mem_univ,
    -- imp_false,
    -- not_not
  ] at *
  simp only [iff_true]
  simp_all only [imp_false, not_not]
  tauto

example (h1 : A ⊆ B \ C) : A ⊆ B := by
  try simp only [
    Set.ext_iff,
    Set.subset_def,
    Set.mem_inter_iff,
    Set.mem_union,
    Set.mem_compl_iff,
    Set.mem_diff,
    Set.disjoint_iff,
    Set.mem_empty_iff_false,
    Set.mem_univ,
    -- imp_false,
    -- not_not
  ] at *
  intro x hx
  specialize h1 x
  tauto


example (h1 : A ⊆ B) (h2 : C ⊆ D) : C \ B ⊆ D \ A := by setauto

example (h : A ⊆ B ∧ C ⊆ D) : C \ B ⊆ D \ A := by setauto

example (h1 : Disjoint A B) (h2 : C ⊆ A) : Disjoint C (B \ D) := by setauto




/-
  run against testsuite:
-/



example : A ∩ ∅ = ∅ := by setauto

example : A ∪ Set.univ = Set.univ := by setauto

example : A ⊆ B → B ⊆ A → A = B := by setauto

example : A ∪ B ∩ C = (A ∪ B) ∩ (A ∪ C) := by setauto

example : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := by setauto

example : A ⊆ (A ∪ B) ∪ C := by setauto

example : A ∩ (B ∪ C) ⊆ (A ∩ B) ∪ (A ∩ C) := by setauto

example : A ∩ B ⊆ A := by setauto

example : A ⊆ A ∪ B := by setauto


-- this one is suspicious, needs the imp_false and not_not simp rules
-- I do not really understand why; tauto should handle that
-- try to hack further counter-examples
example : Aᶜ ⊆ ∅ → A = Set.univ := by
  simp only [
      Set.disjoint_iff,
      Set.ext_iff,
      Set.subset_def,
      Set.mem_inter_iff,
      Set.mem_union,
      Set.mem_compl_iff,
      Set.mem_diff,
      Set.mem_empty_iff_false,
      Set.mem_univ,
    ] at *
  apply extract_univ
  tauto

example : A ⊆ B →  C ⊆ D → C \ B ⊆ D \ A := by
  try simp only [
      Set.ext_iff,
      Set.subset_def,
      Set.mem_inter_iff,
      Set.mem_union,
      Set.mem_compl_iff,
      Set.mem_diff,
      Set.disjoint_iff,
      Set.mem_empty_iff_false,
      Set.mem_univ,
    --   imp_false,
    --   not_not
    ] at *

  intro h1


  sorry

example : A ⊆ B ∧ C ⊆ D → C \ B ⊆ D \ A := by
  try simp only [
      Set.ext_iff,
      Set.subset_def,
      Set.mem_inter_iff,
      Set.mem_union,
      Set.mem_compl_iff,
      Set.mem_diff,
      Set.disjoint_iff,
      Set.mem_empty_iff_false,
      Set.mem_univ,
    --   imp_false,
    --   not_not
    ] at *
  intro h1


  sorry

-- why does this variation not work?
-- nested implication; perhaps first deconstruct
-- P → Q as ¬P ∨ Q ?


example : A ⊆ B \ C → A ⊆ B := by
  simp only [
      Set.disjoint_iff,
      Set.ext_iff,
      Set.subset_def,
      Set.mem_inter_iff,
      Set.mem_union,
      Set.mem_compl_iff,
      Set.mem_diff,
      Set.mem_empty_iff_false,
      Set.mem_univ,
      imp_false,
      not_not
    ] at *
  apply extract_univ
  tauto




example (h1 : Disjoint A B) (h2 : C ⊆ A) : Disjoint C (B \ D) := by
  setauto

example : Disjoint A B ∧ C ⊆ A → Disjoint C (B \ D) := by
  setauto


/-
  real world example from the light injective project
-/

noncomputable section

namespace LightProfinite

universe u

open Set

/-
  For every closed Z ⊆ open U ⊆ profinite X, there is an clopen C with
  Z ⊆ C ⊆ U.  Perhaps this should go in mathlib somewhere?
-/

lemma clopen_of_closed_subset_open  (X : Profinite.{u}) (Z U : Set X)
    (hZ : IsClosed Z) (hU : IsOpen U) (hZU : Z ⊆ U) :
    ∃ C : Set X, IsClopen C ∧ Z ⊆ C ∧ C ⊆ U := by
  -- every z ∈ Z has clopen neighborhood V z ⊆ U
  choose V hV using fun (z : Z) ↦ compact_exists_isClopen_in_isOpen hU (hZU z.property)
  -- the V z cover Z
  have V_cover : Z ⊆ iUnion V := fun z hz ↦ mem_iUnion.mpr ⟨⟨z, hz⟩, (hV ⟨z, hz⟩).2.1⟩
  -- there is a finite subcover
  choose I hI using IsCompact.elim_finite_subcover (IsClosed.isCompact hZ)
    V (fun z ↦ (hV z).1.2) V_cover
  -- the union C of this finite subcover does the job
  let C := ⋃ (i ∈ I), V i
  have C_clopen : IsClopen C := Finite.isClopen_biUnion (Finset.finite_toSet I)
    (fun i _ ↦ (hV i).1)
  have C_subset_U : C ⊆ U := by simp_all only [iUnion_subset_iff, C,  implies_true]
  exact ⟨C, C_clopen, hI, C_subset_U⟩


open Fin

/-
  Let X be profinite, D i ⊆ X a finite family of clopens, and Z i ⊆ D i closed.
  Assume that all the Z i are disjoint. Then there exist clopens Z i ⊆ C i ⊆ D i
  with the C i disjoint, and such that ∪ C i = ∪ D i
-/

lemma clopen_partition_of_disjoint_closeds_in_clopens
    (X : Profinite.{u}) (n : ℕ) (Z : Fin n → Set X) (D : Fin n → Set X)
    (Z_closed : ∀ i, IsClosed (Z i)) (D_clopen : ∀ i, IsClopen (D i))
    (Z_subset_D : ∀ i, Z i ⊆ D i) (Z_disj : ∀ i j, i < j → Disjoint (Z i) (Z j) ) :
    ∃ C : Fin n → Set X, (∀ i, IsClopen (C i)) ∧ (∀ i, Z i ⊆ C i) ∧ (∀ i, C i ⊆ D i) ∧
    (⋃ i, D i) ⊆ (⋃ i, C i)  ∧ (∀ i j, i < j → Disjoint (C i) (C j)) := by
  induction n
  case zero =>
    -- single Z given, can take C 0 = D
    use fun _ ↦ univ -- empty range, can use junk
    exact ⟨elim0, fun i ↦ elim0 i, fun i ↦ elim0 i, by
      simp only [iUnion_of_empty]; trivial, fun i j ↦ elim0 i⟩
  case succ n ih =>
    -- let Z' be the restriction of Z along succ : Fin n → Fin (n+1)
    let Z' : Fin n → Set X := fun i ↦ Z (succ i)
    have Z'_closed (i : Fin n) : IsClosed (Z' i) := Z_closed (succ i)
    have Z'_disj (i j : Fin n) (hij : i < j) : Disjoint (Z' i) (Z' j)  :=
      Z_disj (succ i) (succ j) (succ_lt_succ_iff.mpr hij)
    -- find Z 0 ⊆ V ⊆ D 0 \ ⋃ Z' using clopen_sandwich
    let U : Set X  := D 0 \ iUnion Z'
    have U_open : IsOpen U := IsOpen.sdiff (D_clopen 0).2
      (isClosed_iUnion_of_finite Z'_closed)
    have Z0_subset_U : Z 0 ⊆ U := subset_diff.mpr ⟨Z_subset_D 0,
      disjoint_iUnion_right.mpr (fun i ↦ Z_disj 0 (succ i) (succ_pos ↑↑i))⟩
    obtain ⟨V, V_clopen, Z0_subset_V, V_subset_U⟩ :=
      clopen_of_closed_subset_open X (Z 0) U (Z_closed 0) U_open Z0_subset_U
    -- SETAUTO: SHOULD WORK make mmw of this!
    have V_subset_D0 : V ⊆ D 0 := subset_trans V_subset_U diff_subset
    -- choose Z' i ⊆ C' i ⊆ D' i = D i.succ \ V using induction hypothesis
    let D' : Fin n → Set X := fun i ↦ D (succ i) \ V
    have D'_clopen (i : Fin n): IsClopen (D' i) := IsClopen.diff (D_clopen i.succ) V_clopen
    have Z'_subset_D' (i : Fin n) : Z' i ⊆ D' i := by
      apply subset_diff.mpr
      constructor
      · exact Z_subset_D (succ i)
      · apply Disjoint.mono_right V_subset_U
        exact Disjoint.mono_left (subset_iUnion_of_subset i fun ⦃_⦄ h ↦ h) disjoint_sdiff_right
    obtain ⟨C', C'_clopen, Z'_subset_C', C'_subset_D', C'_cover_D', C'_disj⟩ :=
      ih Z' D' Z'_closed D'_clopen Z'_subset_D' Z'_disj
    have C'_subset_D (i : Fin n): C' i ⊆ D (succ i) := subset_trans (C'_subset_D' i) diff_subset
    -- now choose C0 = D 0 \ ⋃ C' i
    let C0 : Set X := D 0 \ iUnion (fun i ↦ C' i)
    have C0_subset_D0 : C0 ⊆ D 0 := diff_subset
    have C0_clopen : IsClopen C0 := IsClopen.diff (D_clopen 0) (isClopen_iUnion_of_finite C'_clopen)
    have Z0_subset_C0 : Z 0 ⊆ C0 := by
      unfold C0
      apply subset_diff.mpr
      constructor
      · exact Z_subset_D 0
      · apply Disjoint.mono_left Z0_subset_V
        exact disjoint_iUnion_right.mpr fun i ↦ Disjoint.mono_right (C'_subset_D' i) disjoint_sdiff_right
    -- patch together to define C := cases C0 C', and verify the needed properties
    let C : Fin (n+1) → Set X := cases C0 C'
    have C_clopen : ∀ i, IsClopen (C i) := cases C0_clopen C'_clopen
    have Z_subset_C : ∀ i, Z i ⊆ C i := cases Z0_subset_C0 Z'_subset_C'
    have C_subset_D : ∀ i, C i ⊆ D i := cases C0_subset_D0 C'_subset_D
    have C_cover_D : (⋃ i, D i) ⊆ (⋃ i, C i) := by -- messy, but I don't see easy simplification
      intro x hx
      simp only [mem_iUnion]
      by_cases hx0 : x ∈ C0
      · exact ⟨0, hx0⟩
      · by_cases hxD : x ∈ D 0
        · have hxC' : x ∈ iUnion C' := by
            rw [mem_diff] at hx0
            push_neg at hx0
            exact hx0 hxD
          obtain ⟨i, hi⟩ := mem_iUnion.mp hxC'
          exact ⟨i.succ, hi⟩
        · obtain ⟨i, hi⟩ := mem_iUnion.mp hx
          have hi' : i ≠ 0 := by
            intro h
            rw [h] at hi
            tauto
          let j := i.pred hi'
          have hij : i = j.succ := (pred_eq_iff_eq_succ hi').mp rfl
          rw [hij] at hi
          have hxD' : x ∈ ⋃ i, D' i := by
            apply mem_iUnion.mpr ⟨j, _⟩
            apply mem_diff_of_mem hi
            exact fun h ↦ hxD (V_subset_D0 h)
          apply C'_cover_D' at hxD'
          obtain ⟨k, hk⟩ := mem_iUnion.mp hxD'
          exact ⟨k.succ, hk⟩
    have C_disj (i j : Fin (n+1)) (hij : i < j) : Disjoint (C i) (C j) := by
      by_cases hi : i = 0
      · rw [hi]; rw [hi] at hij
        rw [(pred_eq_iff_eq_succ (pos_iff_ne_zero.mp hij)).mp rfl] -- j = succ _
        apply Disjoint.mono_right (subset_iUnion (fun i ↦ C' i) (j.pred (ne_zero_of_lt hij)))
        exact disjoint_sdiff_left
      · have hj : j ≠ 0 := ne_zero_of_lt hij
        rw [(pred_eq_iff_eq_succ hi).mp rfl, (pred_eq_iff_eq_succ hj).mp rfl]
        exact C'_disj (i.pred hi) (j.pred hj) (pred_lt_pred_iff.mpr hij)
    exact ⟨C, C_clopen, Z_subset_C, C_subset_D, C_cover_D, C_disj⟩
