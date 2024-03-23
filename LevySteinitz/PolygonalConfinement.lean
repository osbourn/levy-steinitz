import Mathlib
import LevySteinitz.PermutationBuilder

set_option autoImplicit false

open scoped BigOperators

noncomputable def polygonalConstant : ℕ → ℝ
| 0 => 0
| n + 1 => Real.sqrt (4 * (polygonalConstant n) ^ 2 + 1)

lemma polygonalConstant_nonneg (n : ℕ) : 0 ≤ polygonalConstant n := by
  cases n with
  | zero => exact le_rfl
  | succ n => exact Real.sqrt_nonneg _

-- Might be needed if the base case for induction needs to be `1` rather than `0`
lemma polygonalConstantOne : polygonalConstant 1 = 1 := by
  unfold polygonalConstant
  unfold polygonalConstant
  norm_num

section maximal_vector_lemmas

variable {n : ℕ} {m : ℕ} [hm : NeZero m] (v : Fin m → EuclideanSpace ℝ (Fin n))
  (hv₁ : ∃ i : Fin m, v i ≠ 0) (hv₂ : ∑ i : Fin m, v i = 0)

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
  possible_indicies.toList.argmax (‖∑ i in ·, v i‖)

lemma maximal_indicies_aux_isSome : (maximal_indicies_aux v).isSome = true := by
  by_contra h
  rw [Option.not_isSome_iff_eq_none] at h
  unfold maximal_indicies_aux at h
  rw [List.argmax_eq_none] at h
  apply Finset.Nonempty.toList_ne_nil _ h
  exact possible_indicies_nonempty

noncomputable def maximal_indicies : Finset (Fin m) :=
  Option.get (maximal_indicies_aux v) (maximal_indicies_aux_isSome v)

local notation "I" => maximal_indicies v

lemma maximal_indicies_mem_aux : I ∈ maximal_indicies_aux v :=
  Option.get_mem (maximal_indicies_aux_isSome v)

lemma zero_mem_maximal_indicies : 0 ∈ I := by
  have := List.argmax_mem (maximal_indicies_mem_aux v)
  unfold possible_indicies at this
  aesop

noncomputable def maximal_vector : EuclideanSpace ℝ (Fin n) :=
  ∑ i in I, v i

local notation "L" => maximal_vector v

noncomputable def maximal_vector_spec (s : Finset (Fin m)) (h : 0 ∈ s)
  : ‖∑ i in s, v i‖ ≤ ‖L‖ := by
  have : s ∈ possible_indicies := by
    unfold possible_indicies
    aesop
  unfold maximal_vector
  apply List.le_of_mem_argmax (f := (‖∑ i in ·, v i‖))
  · change s ∈ possible_indicies.toList
    aesop
  · exact maximal_indicies_mem_aux v

lemma maximal_vector_pos : 0 < ‖L‖ := by
  by_cases h : v 0 = 0
  · have ⟨i, hi⟩ := hv₁
    apply lt_of_lt_of_le _ (maximal_vector_spec v {0, i} (Finset.mem_insert.mpr (Or.inl rfl)))
    aesop
  · apply lt_of_lt_of_le _ (maximal_vector_spec v {0} (Finset.mem_singleton_self 0))
    aesop

lemma maximal_vector_ne_zero : L ≠ 0 :=
  norm_ne_zero_iff.mp (maximal_vector_pos v hv₁).ne.symm

lemma maximal_vector_sum_compl : L + ∑ i in Iᶜ, v i = 0 := by
  unfold maximal_vector
  rwa [add_comm, Finset.sum_compl_add_sum]

lemma sum_compl_eq_neg_maximal_vector : ∑ i in Iᶜ, v i = - L :=
  eq_neg_of_add_eq_zero_right (maximal_vector_sum_compl v hv₂)

private lemma same_direction_as_maximal_vector' (i : Fin m) (hi₁ : i ∈ I) (hi₂ : i ≠ 0)
  : (0 : ℝ) ≤ ⟪v i, L⟫_ℝ := by
  by_contra! h
  have : ‖(1 / ‖L‖) • L‖ = (1 : ℝ) := by
    simp [norm_smul, inv_mul_cancel (maximal_vector_pos v hv₁).ne.symm]
  have : (1 / ‖L‖) * ⟪v i, L⟫_ℝ < 0 := by
    exact mul_neg_of_pos_of_neg (div_pos one_pos (maximal_vector_pos v hv₁)) h
  have := maximal_vector_spec v (Finset.erase I i)
  specialize this (Finset.mem_erase.mpr ⟨hi₂.symm, zero_mem_maximal_indicies v⟩)
  rw [Finset.sum_erase_eq_sub hi₁] at this
  change ‖L - v i‖ ≤ ‖L‖ at this
  apply not_lt.mpr this
  calc ‖L - v i‖ ≥ ‖L - v i‖ * ‖(1 / ‖L‖) • L‖ := by simp_all
    _ ≥ ⟪L - v i, (1 / ‖L‖) • L⟫_ℝ := by
        exact real_inner_le_norm (L - v i) ((1 / ‖L‖) • L)
    _ = ⟪L, (1 / ‖L‖) • L⟫_ℝ - ⟪v i, (1 / ‖L‖) • L⟫_ℝ := inner_sub_left _ _ _
    _ = (1 / ‖L‖) * ⟪L, L⟫_ℝ - ⟪v i, (1 / ‖L‖) • L⟫_ℝ := by rw [inner_smul_right]
    _ = (1 / ‖L‖) * (‖L‖ * ‖L‖) - ⟪v i, (1 / ‖L‖) • L⟫_ℝ := by rw [real_inner_self_eq_norm_mul_norm]
    _ = (1 / ‖L‖ * ‖L‖) * ‖L‖ - ⟪v i, (1 / ‖L‖) • L⟫_ℝ := by rw [mul_assoc]
    _ = ‖L‖ - ⟪v i, (1 / ‖L‖) • L⟫_ℝ := by simp
    _ = ‖L‖ - (1 / ‖L‖) * ⟪v i, L⟫_ℝ := by rw [inner_smul_right]
    _ > ‖L‖ := by linarith

private lemma v0_same_direction_as_maximal_vector : (0 : ℝ) ≤ ⟪v 0, L⟫_ℝ := by
  by_contra! h
  apply not_lt.mpr (maximal_vector_spec v ({0} ∪ Iᶜ) (by aesop))
  have : ‖‖L‖⁻¹ • (- L)‖ = (1 : ℝ) := by
    rw [norm_smul, norm_neg, norm_inv, norm_norm]
    exact inv_mul_cancel (by aesop)
  have : ‖L‖⁻¹ * ⟪v 0, L⟫_ℝ < 0 := mul_neg_of_pos_of_neg (by aesop) h
  have : v 0 - L = ∑ i in ({0} ∪ Iᶜ), v i := by
    rw [←Finset.insert_eq, Finset.sum_insert (Finset.not_mem_compl.mpr (zero_mem_maximal_indicies v))]
    have := maximal_vector_sum_compl v hv₂
    rw [←eq_neg_iff_add_eq_zero] at this
    simp [this]
  calc ‖L‖ < ‖L‖ - ‖L‖⁻¹ * ⟪v 0, L⟫_ℝ := by linarith
    _ = ⟪‖L‖⁻¹ • (- L), v 0 - L⟫_ℝ := by
      rw [smul_neg, inner_neg_left]
      rw [real_inner_smul_left, inner_sub_right]
      rw [real_inner_self_eq_norm_sq]
      rw [mul_sub, neg_sub, sq, ←mul_assoc, inv_mul_mul_self, real_inner_comm]
    _ = ⟪‖L‖⁻¹ • (- L), ∑ i in ({0} ∪ Iᶜ), v i⟫_ℝ := by rw [this]
    _ ≤ ‖‖L‖⁻¹ • (- L)‖ * ‖∑ i in ({0} ∪ Iᶜ), v i‖ := real_inner_le_norm _ _
    _ ≤ ‖∑ i in ({0} ∪ Iᶜ), v i‖ := by simp_all

lemma same_direction_as_maximal_vector (i : Fin m) (h : i ∈ I)
  : (0 : ℝ) ≤ ⟪v i, L⟫_ℝ := by
  by_cases h₁ : i = 0
  · rw [h₁]
    exact v0_same_direction_as_maximal_vector v hv₁ hv₂
  · exact same_direction_as_maximal_vector' v hv₁ i h h₁

lemma opposite_direction_as_maximal_vector (i : Fin m) (h : i ∉ I)
  : ⟪v i, L⟫_ℝ ≤ (0 : ℝ) := by
  by_contra! h₁
  apply not_lt.mpr (maximal_vector_spec v ({i} ∪ I)
    (Finset.mem_union_right _ (zero_mem_maximal_indicies v)))
  calc ‖L‖ < ‖L‖ + ‖L‖⁻¹ * ⟪v i, L⟫_ℝ := by
        aesop
      _ = ⟪L + v i, ‖L‖⁻¹ • L⟫_ℝ := by
        rw [inner_smul_right, inner_add_left, real_inner_self_eq_norm_sq, mul_add]
        rw [sq, ←mul_assoc, inv_mul_mul_self]
      _ ≤ ‖L + v i‖ * ‖‖L‖⁻¹ • L‖ := real_inner_le_norm _ _
      _ = ‖L + v i‖ := by
        rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel (by aesop), mul_one]
      _ = ‖∑ j in {i} ∪ I, v j‖ := by
        rw [←Finset.insert_eq, Finset.sum_insert h, add_comm]
        rfl

end maximal_vector_lemmas

section induction_lemmas

variable {n m : ℕ} [hm : NeZero m] (v : Fin m → EuclideanSpace ℝ (Fin (n + 1)))
  (hv₁ : ∑ i : Fin m, v i = 0) (hv₂ : ∀ i : Fin m, ‖v i‖ ≤ 1) (hv₃ : ∃ i : Fin m, v i ≠ 0)

local notation "I" => maximal_indicies v

local notation "L" => maximal_vector v

local notation "L_span" => (Submodule.span ℝ {L})

local notation "L_perp" => (Submodule.span ℝ {L})ᗮ

lemma L_perp_finiteDimensional : FiniteDimensional ℝ L_perp :=
  FiniteDimensional.finiteDimensional_submodule L_perp

lemma L_perp_rank : FiniteDimensional.finrank ℝ L_perp = n := by
  have : Fact (FiniteDimensional.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
    Fact.mk (finrank_euclideanSpace_fin)
  exact finrank_orthogonal_span_singleton (maximal_vector_ne_zero v hv₃)

@[irreducible]
noncomputable def L_perp_orthonormalBasis : OrthonormalBasis (Fin n) ℝ L_perp := by
  have := stdOrthonormalBasis ℝ L_perp
  rwa [L_perp_rank v hv₃] at this

lemma L_projection_def (w : EuclideanSpace ℝ (Fin (n + 1)))
  : orthogonalProjection L_span w = (⟪L, w⟫_ℝ / ↑(‖L‖ ^ 2)) • L :=
  orthogonalProjection_singleton ℝ w

lemma L_perp_projection_def (w : EuclideanSpace ℝ (Fin (n + 1)))
  : (orthogonalProjection L_perp) w = w - orthogonalProjection L_span w := by
  exact orthogonalProjection_orthogonal_val w

lemma L_projection_add_L_perp_projection (w : EuclideanSpace ℝ (Fin (n + 1)))
  : (orthogonalProjection L_span w : EuclideanSpace ℝ (Fin (n + 1)))
    + orthogonalProjection L_perp w = w := by
  rw [L_perp_projection_def]
  simp

local notation "v_proj" => orthogonalProjection L_span ∘ v

local notation "v'" => orthogonalProjection L_perp ∘ v

local notation "v'_repr" => (OrthonormalBasis.repr (L_perp_orthonormalBasis v hv₃)) ∘ v'

lemma v_proj_add_v' (i : Fin m) : (v_proj i : EuclideanSpace ℝ (Fin (n + 1))) + v' i = v i :=
  L_projection_add_L_perp_projection v (v i)

lemma v'_sum_maximal : ∑ i in I, v' i = 0 := by
  have : ∑ i in I, v i = L := rfl
  apply_fun orthogonalProjection L_perp at this
  rw [map_sum] at this
  rw [orthogonalProjection_orthogonalComplement_singleton_eq_zero] at this
  exact this

lemma v'_repr_sum_maximal : ∑ i in I, v'_repr i = 0 := by
  have := v'_sum_maximal v
  apply_fun (L_perp_orthonormalBasis v hv₃).repr at this
  rw [map_sum, map_zero] at this
  exact this

lemma v'_sum_maximal_compl : ∑ i in Iᶜ, v' i = 0 := by
  have := sum_compl_eq_neg_maximal_vector v hv₁
  apply_fun orthogonalProjection L_perp at this
  rw [map_sum, map_neg] at this
  rw [orthogonalProjection_orthogonalComplement_singleton_eq_zero] at this
  rw [neg_zero] at this
  exact this

lemma v'_repr_sum_maximal_compl : ∑ i in Iᶜ, v'_repr i = 0 := by
  have := v'_sum_maximal_compl v hv₁
  apply_fun (L_perp_orthonormalBasis v hv₃).repr at this
  rw [map_sum, map_zero] at this
  exact this

lemma norm_v'_le_one (i : Fin m) : ‖v' i‖ ≤ 1 := by
  rw [Function.comp_apply]
  have := ContinuousLinearMap.le_of_opNorm_le_of_le (orthogonalProjection L_perp)
    (orthogonalProjection_norm_le L_perp) (hv₂ i)
  linarith

lemma norm_v'_repr_le_one (i : Fin m) : ‖v'_repr i‖ ≤ 1 := by
  rw [Function.comp_apply]
  rw [LinearIsometryEquiv.norm_map]
  rw [Function.comp_apply]
  exact norm_v'_le_one v hv₂ i

local notation "s" => Finset.card I

local notation "t" => Finset.card Iᶜ

lemma s_pos : 0 < s := by
  rw [Nat.pos_iff_ne_zero]
  intro h
  have : Finset.card I ≠ 0 := (Finset.Nonempty.card_pos ⟨0, zero_mem_maximal_indicies v⟩).ne.symm
  contradiction

local instance s_ne_zero : NeZero s where
  out := (s_pos v).ne.symm

lemma t_pos : 0 < t := by
  rw [Nat.pos_iff_ne_zero]
  intro h
  rw [Finset.card_eq_zero, Finset.compl_eq_empty_iff] at h
  rcases hv₃ with ⟨i, hi⟩
  have L_eq_zero : L = 0 := by rwa [maximal_vector, h]
  by_cases hi₂ : i = 0
  · apply not_lt.mpr (maximal_vector_spec v {0} (Finset.mem_singleton_self 0))
    rwa [L_eq_zero, norm_zero, Finset.sum_singleton, norm_pos_iff, ←hi₂]
  · apply not_lt.mpr (maximal_vector_spec v (Finset.univ.erase i)
      (Finset.mem_erase.mpr ⟨(Ne.intro hi₂).symm, Finset.mem_univ 0⟩))
    simp [L_eq_zero, hv₁, hi]

/--
This instance might be slightly problematic because it depends on `v`, `hv₁`, and `hv₃`
-/
local instance t_ne_zero : NeZero t where
  out := (t_pos v hv₁ hv₃).ne.symm

lemma s_add_t : s + t = m := by
  rw [add_comm, Finset.card_compl_add_card, Fintype.card_fin]

noncomputable def I_orderEmb : Fin s ↪o Fin m :=
  (Finset.orderEmbOfFin I (rfl : Finset.card I = s))

noncomputable def I_compl_orderEmb : Fin t ↪o Fin m :=
  (Finset.orderEmbOfFin Iᶜ (rfl : Finset.card Iᶜ = t))

/--
`u` is the sequence of vectors `v'_repr` in `ℝ^n`, skipping over vectors not in `I`.
If `I` is `{0,1,3,5}`, then `u 0 = v'_repr 0`, `u 1 = v'_repr 1`, `u 2 = v'_repr 3`, and
`u 3 = v'_repr 5`.

This is represented as a definition instead of a local notation to work around
https://github.com/leanprover/lean4/issues/2535
-/
noncomputable def u := v'_repr ∘ (I_orderEmb v)
--local notation "u" => v'_repr ∘ (I_orderEmb v)

/--
`w` is like `u`, but for indicies in `Iᶜ` instead of `I`
-/
noncomputable def w := v'_repr ∘ (I_compl_orderEmb v)
--local notation "w" => v'_repr ∘ (I_compl_orderEmb v)

lemma u_sum : ∑ i : Fin s, u v hv₃ i = 0 := by
  let f : { x : Fin m // x ∈ I } → EuclideanSpace ℝ (Fin n) := fun x => v'_repr ↑x
  change ∑ i in Finset.univ, f ((Finset.orderIsoOfFin I rfl).toEquiv.toEmbedding i) = 0
  rw [←Finset.sum_map Finset.univ _ f]
  rw [Finset.map_univ_equiv]
  rw [←Finset.sum_subtype_map_embedding (fun x _ => rfl)]
  rw [Finset.univ_eq_attach, Finset.sum_map, Function.Embedding.coe_subtype, Finset.sum_attach]
  exact v'_repr_sum_maximal v hv₃

lemma w_sum : ∑ i : Fin t, w v hv₃ i = 0 := by
  let f : { x : Fin m // x ∈ Iᶜ } → EuclideanSpace ℝ (Fin n) := fun x => v'_repr ↑x
  change ∑ i in Finset.univ, f ((Finset.orderIsoOfFin Iᶜ rfl).toEquiv.toEmbedding i) = 0
  rw [←Finset.sum_map Finset.univ _ f]
  rw [Finset.map_univ_equiv]
  rw [←Finset.sum_subtype_map_embedding (fun x _ => rfl)]
  rw [Finset.univ_eq_attach, Finset.sum_map, Function.Embedding.coe_subtype, Finset.sum_attach]
  exact v'_repr_sum_maximal_compl v hv₁ hv₃

lemma norm_u_le_one (i : Fin s) : ‖u v hv₃ i‖ ≤ 1 :=
  norm_v'_repr_le_one v hv₂ hv₃ _

lemma norm_w_le_one (i : Fin t) : ‖w v hv₃ i‖ ≤ 1 :=
  norm_v'_repr_le_one v hv₂ hv₃ _

-- These definitions are workarounds for https://github.com/leanprover/lean4/issues/2535,
-- since using `Fin s` directly in a variable declaration causes timeouts and hidden `sorryAx`s.
noncomputable def s' := s
noncomputable def t' := t

variable (h_ind_u : ∃ P : Equiv.Perm (Fin (s' v)), P ⟨0, s_pos v⟩ = ⟨0, s_pos v⟩ ∧
  ∀ j : Fin (s' v), ‖∑ i in Finset.Iic j, u v hv₃ i‖ ≤ polygonalConstant n)
variable (h_ind_w : ∃ P : Equiv.Perm (Fin (t' v)), P ⟨0, t_pos v hv₁ hv₃⟩ = ⟨0, t_pos v hv₁ hv₃⟩ ∧
  ∀ j : Fin (t' v), ‖∑ i in Finset.Iic j, w v hv₃ i‖ ≤ polygonalConstant n)

def polygonal_confinement_permutationBuilder : PermutationBuilder m where
  invariant (l : List (Fin m)) := True
  next {l : List (Fin m)} : True → l.length < m → Fin m := sorry
  no_duplicates {l : List (Fin m)} (h₁ : True) (h₂ : l.length < m) := sorry
  preserves_invariant {l : List (Fin m)} (h₁ : True) (h₂ : l.length < m) := sorry
  invariant_empty := sorry

def induction_step : ∃ P : Equiv.Perm (Fin m), P 0 = 0 ∧
  ∀ j : Fin m, ‖∑ i in Finset.Iic j, v i‖ ≤ polygonalConstant (n + 1) := by
  -- Temporary declarations to make sure `induction_step` has all the needed variables
  have := hv₁
  have := hv₂
  have := hv₃
  have := h_ind_u
  have := h_ind_w
  sorry

end induction_lemmas

theorem polygonal_confinement_theorem {n m : ℕ} [hm : NeZero m]
  {v : Fin m → EuclideanSpace ℝ (Fin n)}
  (hv₁ : ∑ i : Fin m, v i = 0) (hv₂ : ∀ i : Fin m, ‖v i‖ ≤ 1) :
  ∃ P : Equiv.Perm (Fin m), P 0 = 0 ∧
  ∀ j : Fin m, ‖∑ i in Finset.Iic j, v i‖ ≤ polygonalConstant n := by
    by_cases hc : ∀ i, v i = 0
    · use (Equiv.refl (Fin m))
      simp [hc, polygonalConstant_nonneg]
    · push_neg at hc
      induction n generalizing m with
      | zero =>
        use (Equiv.refl (Fin m))
        simpa [norm_of_subsingleton] using le_rfl
      | succ n ih =>
        apply induction_step v hv₁ hv₂ hc
        · by_cases hu : ∀ i : Fin (maximal_indicies v).card, u v hc i = 0
          · use (Equiv.refl _)
            simp [hu, polygonalConstant_nonneg]
          · push_neg at hu
            apply ih (hm := s_ne_zero v)
            · exact u_sum v hc
            · exact norm_u_le_one v hv₂ hc
            · exact hu
        · by_cases hw : ∀ i : Fin (maximal_indicies v)ᶜ.card, w v hc i = 0
          · use (Equiv.refl _)
            simp [hw, polygonalConstant_nonneg]
          · push_neg at hw
            apply ih (hm := t_ne_zero v hv₁ hc)
            · exact w_sum v hv₁ hc
            · exact norm_w_le_one v hv₂ hc
            · exact hw
