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

noncomputable def maximal_vector : EuclideanSpace ℝ (Fin n) :=
  sum_indicies v (maximal_indicies v)

theorem polygonal_confinement_theorem
  (hv₁ : ∑ i : Fin m, v i = 0) (hv₂ : ∀ i : Fin m, ‖v i‖ ≤ 1) :
  ∃ P : Equiv.Perm (Fin m), P ⟨0, hm⟩ = ⟨0, hm⟩ ∧
  ∀ j : Fin m, ‖∑ i in Finset.Iic j, v i‖ ≤ polygonalConstant n := sorry
