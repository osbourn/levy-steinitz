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

noncomputable def nonneg_indicies (m : ℕ) (v : Fin m → ℝ) : Finset (Fin m) :=
  Finset.univ.filter (0 ≤ v ·)

noncomputable def neg_indicies (m : ℕ) (v : Fin m → ℝ) : Finset (Fin m) :=
  Finset.univ.filter (v · < 0)

-- Output: (actual, unused noneg indicies, unused neg indicies, sum so far)
noncomputable def linear_permutation_aux (m : ℕ) (v : Fin m → ℝ)
  : Fin m → (Fin m × Finset (Fin m) × Finset (Fin m) × ℝ)
| ⟨0, h⟩ => (⟨0, h⟩, (nonneg_indicies m v).erase ⟨0, h⟩, (neg_indicies m v).erase ⟨0, h⟩, v ⟨0, h⟩)
| ⟨(n + 1), h⟩ => let (prev, unused_nonneg, unused_neg, current_sum) := linear_permutation_aux m v ⟨n, Nat.lt_of_succ_lt h⟩
  if current_sum < 0 then
    let val : Fin m := unused_nonneg.min.untop' ⟨0, prev.pos⟩
    (val, unused_nonneg.erase val, unused_neg, current_sum + v val)
  else
    let val : Fin m := unused_neg.min.untop' ⟨0, prev.pos⟩
    (val, unused_nonneg, unused_neg.erase val, current_sum + v val)

noncomputable def linear_permutation (m : ℕ) (v : Fin m → ℝ) (x : Fin m) : Fin m :=
  (linear_permutation_aux m v x).1

section

variable {m : ℕ} (hm : 0 < m) (v : Fin m → ℝ)

lemma linear_permutation_aux_zero
  : linear_permutation_aux m v ⟨0, hm⟩ = (⟨0, hm⟩, (nonneg_indicies m v).erase ⟨0, hm⟩, (neg_indicies m v).erase ⟨0, hm⟩, v ⟨0, hm⟩) := rfl

lemma linaer_permutation_zero : linear_permutation m v ⟨0, hm⟩ = ⟨0, hm⟩ := rfl

lemma linear_permutation_eq_zero_of_start {j : Fin m}
  (h : (linear_permutation_aux m v j).snd.fst = nonneg_indicies m v ∧ (linear_permutation_aux m v j).snd.snd.fst = neg_indicies m v) : j = ⟨0, hm⟩ := by
  revert h
  contrapose
  intro (hj : j ≠ ⟨0, hm⟩)
  sorry
end

theorem linear_polygonal_confinement_theorem {m : ℕ} (hm : 0 < m) (v : Fin m → ℝ)
  (hv₁ : ∑ i : Fin m, v i = 0) (hv₂ : ∀ i : Fin m, ‖v i‖ ≤ 1) :
  ∃ P : Equiv.Perm (Fin m), P ⟨0, hm⟩ = ⟨0, hm⟩ ∧
  ∀ j : Fin m, ‖∑ i in Finset.Iic j, v i‖ ≤ 1 := sorry

variable (n : ℕ) {m : ℕ} (hm : 0 < m) (v : Fin m → EuclideanSpace ℝ (Fin n))

theorem polygonal_confinement_theorem
  (hv₁ : ∑ i : Fin m, v i = 0) (hv₂ : ∀ i : Fin m, ‖v i‖ ≤ 1) :
  ∃ P : Equiv.Perm (Fin m), P ⟨0, hm⟩ = ⟨0, hm⟩ ∧
  ∀ j : Fin m, ‖∑ i in Finset.Iic j, v i‖ ≤ polygonalConstant n := sorry
