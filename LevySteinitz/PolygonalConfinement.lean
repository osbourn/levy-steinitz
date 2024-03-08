import Mathlib

set_option autoImplicit false

open scoped BigOperators

noncomputable def polygonalConstant : ℕ → ℝ
| 0 => 0
| n + 1 => Real.sqrt (4 * (polygonalConstant n) ^ 2 + 1)

-- Might be needed if the base case for induction needs to be `1` rather than `0`
lemma polygonalConstantOne : polygonalConstant 1 = 1 := by
  unfold polygonalConstant
  unfold polygonalConstant
  norm_num

/-
variable {m : ℕ} (hm : 0 < m) (v : Fin m → ℝ)

theorem linear_polygonal_confinement_theorem {m : ℕ} (hm : 0 < m) (v : Fin m → ℝ)
  (hv₁ : ∑ i : Fin m, v i = 0) (hv₂ : ∀ i : Fin m, ‖v i‖ ≤ 1) :
  ∃ P : Equiv.Perm (Fin m), P ⟨0, hm⟩ = ⟨0, hm⟩ ∧
  ∀ j : Fin m, ‖∑ i in Finset.Iic j, v i‖ ≤ 1 := sorry
-/

variable {n : ℕ} {m : ℕ} {hm : 0 < m} (v : Fin m → EuclideanSpace ℝ (Fin n))

abbrev sum_indicies (s : Finset (Fin m)) : EuclideanSpace ℝ (Fin n) := ∑ i : s, v i

-- TODO: This needs to be changed to only include combinations that include 0
noncomputable def maximal_indicies_aux : Option (Finset (Fin m)) :=
  (Finset.univ.powerset : Finset (Finset (Fin m))).toList.argmax (‖sum_indicies v ·‖)

lemma maximal_indicies_aux_isSome : (maximal_indicies_aux v).isSome = true := by
  by_contra h
  rw [Option.not_isSome_iff_eq_none] at h
  unfold maximal_indicies_aux at h
  rw [List.argmax_eq_none] at h
  apply Finset.Nonempty.toList_ne_nil _ h
  exact Finset.powerset_nonempty _

noncomputable def maximal_indicies : Finset (Fin m) :=
  Option.get (maximal_indicies_aux v) (maximal_indicies_aux_isSome v)

lemma maximal_indicies_mem_aux : maximal_indicies v ∈ maximal_indicies_aux v :=
  Option.get_mem (maximal_indicies_aux_isSome v)

noncomputable def maximal_vector : EuclideanSpace ℝ (Fin n) :=
  sum_indicies v (maximal_indicies v)

noncomputable def maximal_vector_spec (s : Finset (Fin m))
  : ‖sum_indicies v s‖ ≤ ‖maximal_vector v‖ := by
  unfold maximal_vector
  apply List.le_of_mem_argmax (f := (‖sum_indicies v ·‖))
  · change s ∈ (Finset.univ.powerset : Finset (Finset (Fin m))).toList
    aesop
  · exact maximal_indicies_mem_aux v

lemma same_direction_as_maximal_vector (i : Fin m) (hi : i ∈ maximal_indicies v)
  : (0 : ℝ) ≤ ⟪v i, maximal_vector v⟫_ℝ := by
  sorry

theorem polygonal_confinement_theorem
  (hv₁ : ∑ i : Fin m, v i = 0) (hv₂ : ∀ i : Fin m, ‖v i‖ ≤ 1) :
  ∃ P : Equiv.Perm (Fin m), P ⟨0, hm⟩ = ⟨0, hm⟩ ∧
  ∀ j : Fin m, ‖∑ i in Finset.Iic j, v i‖ ≤ polygonalConstant n := sorry
