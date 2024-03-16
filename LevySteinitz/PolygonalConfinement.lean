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
  (hv₁ : ∃ i : Fin m, v i ≠ 0) (hv₂ : ∑ i : Fin m, v i = 0)

abbrev sum_indicies (s : Finset (Fin m)) : EuclideanSpace ℝ (Fin n) := ∑ i in s, v i

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

lemma maximal_indicies_sum_compl : sum_indicies v (maximal_indicies v) + sum_indicies v (maximal_indicies v)ᶜ = 0 := by
  unfold sum_indicies
  rwa [add_comm, Finset.sum_compl_add_sum]

lemma maximal_indicies_mem_aux : maximal_indicies v ∈ maximal_indicies_aux v :=
  Option.get_mem (maximal_indicies_aux_isSome v)

lemma zero_mem_maximal_indicies : 0 ∈ maximal_indicies v := by
  have := List.argmax_mem (maximal_indicies_mem_aux v)
  unfold possible_indicies at this
  aesop

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

lemma maximal_vector_pos : 0 < ‖maximal_vector v‖ := by
  by_cases h : v 0 = 0
  · have ⟨i, hi⟩ := hv₁
    apply lt_of_lt_of_le _ (maximal_vector_spec v {0, i} (Finset.mem_insert.mpr (Or.inl rfl)))
    aesop
  · apply lt_of_lt_of_le _ (maximal_vector_spec v {0} (Finset.mem_singleton_self 0))
    aesop

lemma same_direction_as_maximal_vector (i : Fin m) (hi₁ : i ∈ maximal_indicies v) (hi₂ : i ≠ 0)
  : (0 : ℝ) ≤ ⟪v i, maximal_vector v⟫_ℝ := by
  by_contra h
  push_neg at h
  have : ‖(1 / ‖maximal_vector v‖) • (maximal_vector v)‖ = (1 : ℝ) := by
    simp [norm_smul, inv_mul_cancel (maximal_vector_pos v hv₁).ne.symm]
  have : (1 / ‖maximal_vector v‖) * ⟪v i, maximal_vector v⟫_ℝ < 0 := by
    exact mul_neg_of_pos_of_neg (div_pos one_pos (maximal_vector_pos v hv₁)) h
  have := maximal_vector_spec v ((maximal_indicies v).erase i)
  specialize this (Finset.mem_erase.mpr ⟨hi₂.symm, zero_mem_maximal_indicies v⟩)
  unfold sum_indicies at this
  rw [Finset.sum_erase_eq_sub hi₁] at this
  change ‖maximal_vector v - v i‖ ≤ ‖maximal_vector v‖ at this
  apply not_lt.mpr this
  calc ‖maximal_vector v - v i‖ ≥ ‖maximal_vector v - v i‖ * ‖(1 / ‖maximal_vector v‖) • (maximal_vector v)‖ := by simp_all
    _ ≥ ⟪maximal_vector v - v i, (1 / ‖maximal_vector v‖) • (maximal_vector v)⟫_ℝ := by
        exact real_inner_le_norm (maximal_vector v - v i) ((1 / ‖maximal_vector v‖) • (maximal_vector v))
    _ = ⟪maximal_vector v, (1 / ‖maximal_vector v‖) • (maximal_vector v)⟫_ℝ - ⟪v i, (1 / ‖maximal_vector v‖) • (maximal_vector v)⟫_ℝ := inner_sub_left _ _ _
    _ = (1 / ‖maximal_vector v‖) * ⟪maximal_vector v, maximal_vector v⟫_ℝ - ⟪v i, (1 / ‖maximal_vector v‖) • (maximal_vector v)⟫_ℝ := by rw [inner_smul_right]
    _ = (1 / ‖maximal_vector v‖) * (‖maximal_vector v‖ * ‖maximal_vector v‖) - ⟪v i, (1 / ‖maximal_vector v‖) • (maximal_vector v)⟫_ℝ := by rw [real_inner_self_eq_norm_mul_norm]
    _ = (1 / ‖maximal_vector v‖ * ‖maximal_vector v‖) * ‖maximal_vector v‖ - ⟪v i, (1 / ‖maximal_vector v‖) • (maximal_vector v)⟫_ℝ := by rw [mul_assoc]
    _ = ‖maximal_vector v‖ - ⟪v i, (1 / ‖maximal_vector v‖) • (maximal_vector v)⟫_ℝ := by simp
    _ = ‖maximal_vector v‖ - (1 / ‖maximal_vector v‖) * ⟪v i, maximal_vector v⟫_ℝ := by rw [inner_smul_right]
    _ > ‖maximal_vector v‖ := by linarith

theorem polygonal_confinement_theorem
  (hv₁ : ∑ i : Fin m, v i = 0) (hv₂ : ∀ i : Fin m, ‖v i‖ ≤ 1) :
  ∃ P : Equiv.Perm (Fin m), P 0 = 0 ∧
  ∀ j : Fin m, ‖∑ i in Finset.Iic j, v i‖ ≤ polygonalConstant n := sorry
