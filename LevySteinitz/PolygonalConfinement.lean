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

variable {n : ℕ} {m : ℕ} [hm : NeZero m] (v : Fin m → EuclideanSpace ℝ (Fin n))

abbrev sum_indicies (s : Finset (Fin m)) : EuclideanSpace ℝ (Fin n) := ∑ i : s, v i

/--
  All possible combinations of indicies that contain 0
-/
def possible_indicies : Finset (Finset (Fin m)) :=
  (Finset.univ.powerset : Finset (Finset (Fin m))).filter (0 ∈ ·)

lemma possible_indicies_nonempty : (possible_indicies (hm := hm)).Nonempty := by
  use {0}
  unfold possible_indicies
  aesop

noncomputable def maximal_indicies_aux : Option (Finset (Fin m)) :=
  possible_indicies.toList.argmax (‖sum_indicies v ·‖)

lemma maximal_indicies_aux_isSome : (maximal_indicies_aux v).isSome = true := by
  by_contra h
  rw [Option.not_isSome_iff_eq_none] at h
  unfold maximal_indicies_aux at h
  rw [List.argmax_eq_none] at h
  apply Finset.Nonempty.toList_ne_nil _ h
  exact possible_indicies_nonempty

noncomputable def maximal_indicies : Finset (Fin m) :=
  Option.get (maximal_indicies_aux v) (maximal_indicies_aux_isSome v)

lemma maximal_indicies_mem_aux : maximal_indicies v ∈ maximal_indicies_aux v :=
  Option.get_mem (maximal_indicies_aux_isSome v)

noncomputable def maximal_vector : EuclideanSpace ℝ (Fin n) :=
  sum_indicies v (maximal_indicies v)

noncomputable def maximal_vector_spec (s : Finset (Fin m)) (h : 0 ∈ s)
  : ‖sum_indicies v s‖ ≤ ‖maximal_vector v‖ := by
  have : s ∈ possible_indicies := by
    unfold possible_indicies
    aesop
  unfold maximal_vector
  apply List.le_of_mem_argmax (f := (‖sum_indicies v ·‖))
  · change s ∈ possible_indicies.toList
    aesop
  · exact maximal_indicies_mem_aux v

noncomputable def maximal_vector_pos : 0 < ‖maximal_vector v‖ := sorry

lemma same_direction_as_maximal_vector (i : Fin m) (hi : i ∈ maximal_indicies v)
  : (0 : ℝ) ≤ ⟪v i, maximal_vector v⟫_ℝ := by
  by_contra h
  push_neg at h
  have : ‖(1 / ‖maximal_vector v‖) • (maximal_vector v)‖ = (1 : ℝ) := by
    simp [norm_smul, inv_mul_cancel (maximal_vector_pos v).ne.symm]
  have : ‖maximal_vector v - v i‖ > ‖maximal_vector v‖ := (calc
    ‖maximal_vector v - v i‖ ≥ ‖maximal_vector v - v i‖ * ‖(1 / ‖maximal_vector v‖) • (maximal_vector v)‖ := by simp_all
    _ ≥ ⟪maximal_vector v - v i, (1 / ‖maximal_vector v‖) • (maximal_vector v)⟫_ℝ := by
        exact real_inner_le_norm (maximal_vector v - v i) ((1 / ‖maximal_vector v‖) • (maximal_vector v))
    _ = ⟪maximal_vector v, (1 / ‖maximal_vector v‖) • (maximal_vector v)⟫_ℝ - ⟪v i, (1 / ‖maximal_vector v‖) • (maximal_vector v)⟫_ℝ := inner_sub_left _ _ _
    _ = (1 / ‖maximal_vector v‖) * ⟪maximal_vector v, maximal_vector v⟫_ℝ - ⟪v i, (1 / ‖maximal_vector v‖) • (maximal_vector v)⟫_ℝ := by rw [inner_smul_right]
    _ = (1 / ‖maximal_vector v‖) * (‖maximal_vector v‖ * ‖maximal_vector v‖) - ⟪v i, (1 / ‖maximal_vector v‖) • (maximal_vector v)⟫_ℝ := by rw [real_inner_self_eq_norm_mul_norm]
    _ = (1 / ‖maximal_vector v‖ * ‖maximal_vector v‖) * ‖maximal_vector v‖ - ⟪v i, (1 / ‖maximal_vector v‖) • (maximal_vector v)⟫_ℝ := by rw [mul_assoc]
    _ = ‖maximal_vector v‖ - ⟪v i, (1 / ‖maximal_vector v‖) • (maximal_vector v)⟫_ℝ := by simp
    _ = ‖maximal_vector v‖ - (1 / ‖maximal_vector v‖) * ⟪v i, maximal_vector v⟫_ℝ := by rw [inner_smul_right]
    _ > ‖maximal_vector v‖ := sorry
  )
  sorry

theorem polygonal_confinement_theorem
  (hv₁ : ∑ i : Fin m, v i = 0) (hv₂ : ∀ i : Fin m, ‖v i‖ ≤ 1) :
  ∃ P : Equiv.Perm (Fin m), P 0 = 0 ∧
  ∀ j : Fin m, ‖∑ i in Finset.Iic j, v i‖ ≤ polygonalConstant n := sorry
