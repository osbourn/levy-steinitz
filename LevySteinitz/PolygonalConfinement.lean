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

section

variable {m : ℕ} (hm : 0 < m) (v : Fin m → ℝ)

theorem linear_polygonal_confinement_theorem {m : ℕ} (hm : 0 < m) (v : Fin m → ℝ)
  (hv₁ : ∑ i : Fin m, v i = 0) (hv₂ : ∀ i : Fin m, ‖v i‖ ≤ 1) :
  ∃ P : Equiv.Perm (Fin m), P ⟨0, hm⟩ = ⟨0, hm⟩ ∧
  ∀ j : Fin m, ‖∑ i in Finset.Iic j, v i‖ ≤ 1 := sorry

end

variable (n : ℕ) {m : ℕ} (hm : 0 < m) (v : Fin m → EuclideanSpace ℝ (Fin n))

theorem polygonal_confinement_theorem
  (hv₁ : ∑ i : Fin m, v i = 0) (hv₂ : ∀ i : Fin m, ‖v i‖ ≤ 1) :
  ∃ P : Equiv.Perm (Fin m), P ⟨0, hm⟩ = ⟨0, hm⟩ ∧
  ∀ j : Fin m, ‖∑ i in Finset.Iic j, v i‖ ≤ polygonalConstant n := sorry
