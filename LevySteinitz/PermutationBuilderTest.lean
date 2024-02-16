import Mathlib
import LevySteinitz.PermutationBuilder

set_option autoImplicit false

variable {n : ℕ}

lemma valid_find_nonnegative (a : Fin n → ℚ) (ha : Finset.univ.sum a = 0) (e : Finset (Fin n))
  (he₁ : e ≠ Finset.univ) (he₂ : e.sum a ≤ 0) : ¬Finset.univ.filter (0 ≤ a ·) ⊆ e := by
    set s := Finset.univ.filter (0 ≤ a ·)
    intro hc

    have he₁ : Finset.Nonempty eᶜ := by
      by_contra _
      aesop

    -- All terms indexed by `eᶜ` are negative
    have : eᶜ ⊆ sᶜ := Finset.compl_subset_compl.mpr hc
    have : ∀ i ∈ eᶜ, a i < 0 := fun i hi => by simpa using (this hi)

    -- The sum of all terms indexed by `eᶜ` is negative
    have : eᶜ.sum a < 0 := Finset.sum_neg this he₁

    -- `e.sum a ≤ 0` and `eᶜ.sum a < 0`, yet `Finset.univ.sum a = 0`, a contradiction
    have : e.sum a + eᶜ.sum a = Finset.univ.sum a := Finset.sum_add_sum_compl e a
    linarith

lemma valid_find_negative (a : Fin n → ℚ) (ha : Finset.univ.sum a = 0) (e : Finset (Fin n))
  (he : 0 < e.sum a) : ¬Finset.univ.filter (a · < 0) ⊆ e := by
      set s := Finset.univ.filter (a · < 0)
      intro hc

      -- All terms indexed by `eᶜ` are nonnegative
      have : eᶜ ⊆ sᶜ := Finset.compl_subset_compl.mpr hc
      have : ∀ i ∈ eᶜ, 0 ≤ a i := fun i hi => by simpa using (this hi)

      -- The sum of all terms indexed by `eᶜ` is nonnegative
      have : 0 ≤ eᶜ.sum a := Finset.sum_nonneg this

      -- `0 < e.sum a` and `0 ≤ eᶜ.sum a`, yet `Finset.univ.sum a = 0`, a contradiction
      have : e.sum a + eᶜ.sum a = Finset.univ.sum a := Finset.sum_add_sum_compl e a
      linarith

def next_rational (a : Fin n → ℚ) (ha : Finset.univ.sum a = 0) (e : Finset (Fin n))
  (he : e ≠ Finset.univ) : Fin n :=
    if h : e.sum a ≤ 0 then
      find_excluding (Finset.univ.filter (0 ≤ a ·)) e (valid_find_nonnegative a ha e he h)
    else
      find_excluding (Finset.univ.filter (a · < 0)) e (valid_find_negative a ha e (Rat.not_le.mp h))

def next_rational_nonneg (a : Fin n → ℚ) (ha : Finset.univ.sum a = 0) (e : Finset (Fin n))
  (he : e ≠ Finset.univ) (h : e.sum a ≤ 0) : 0 ≤ a (next_rational a ha e he) := by
  unfold next_rational
  rw [dif_pos h]
  have := find_excluding_mem _ e (valid_find_nonnegative a ha e he h)
  simpa using this

def next_rational_neg (a : Fin n → ℚ) (ha : Finset.univ.sum a = 0) (e : Finset (Fin n))
  (he : e ≠ Finset.univ) (h : 0 < e.sum a) : a (next_rational a ha e he) < 0 := by
  unfold next_rational
  rw [dif_neg (Rat.not_le.mpr h)]
  have := find_excluding_mem _ e (valid_find_negative a ha e h)
  simpa using this

def next_rational_not_mem (a : Fin n → ℚ) (ha : Finset.univ.sum a = 0) (e : Finset (Fin n))
  (he : e ≠ Finset.univ) : next_rational a ha e he ∉ e := by
  unfold next_rational
  by_cases h : e.sum a ≤ 0
  · rw [dif_pos h]
    exact find_excluding_not_mem _ e (valid_find_nonnegative a ha e he h)
  · rw [dif_neg h]
    exact find_excluding_not_mem _ e (valid_find_negative a ha e (Rat.not_le.mp h))

lemma List.length_dedup_le {α : Type*} [DecidableEq α] (l : List α)
  : (List.dedup l).length ≤ l.length := Sublist.length_le (dedup_sublist l)

lemma toFinset_ne_univ_of_length_lt_card {α : Type*} [Fintype α] [DecidableEq α] {l : List α}
  (h : l.length < Fintype.card α) : l.toFinset ≠ Finset.univ := by
  intro hc
  rw [←Finset.card_univ, ←hc, List.card_toFinset, ←not_le] at h
  exact h (List.length_dedup_le l)

def next_rational_list (a : Fin n → ℚ) (ha : Finset.univ.sum a = 0) (l : List (Fin n))
  (h : l.length < n) : Fin n :=
  next_rational a ha l.toFinset (toFinset_ne_univ_of_length_lt_card (by rwa [Fintype.card_fin]))

lemma next_rational_list_nonneg (a : Fin n → ℚ) (ha : Finset.univ.sum a = 0) (l : List (Fin n))
  (h₁ : l.length < n) (h₂ : l.toFinset.sum a ≤ 0) : 0 ≤ a (next_rational_list a ha l h₁) :=
  next_rational_nonneg a ha l.toFinset (toFinset_ne_univ_of_length_lt_card
    (by rwa [Fintype.card_fin])) h₂

lemma next_rational_list_neg (a : Fin n → ℚ) (ha : Finset.univ.sum a = 0) (l : List (Fin n))
  (h₁ : l.length < n) (h₂ : 0 < l.toFinset.sum a) : a (next_rational_list a ha l h₁) < 0 :=
  next_rational_neg a ha l.toFinset (toFinset_ne_univ_of_length_lt_card
    (by rwa [Fintype.card_fin])) h₂

def next_rational_list_not_mem (a : Fin n → ℚ) (ha : Finset.univ.sum a = 0) (l : List (Fin n))
  (h : l.length < n) : next_rational_list a ha l h ∉ l := by
  rw [←List.mem_toFinset]
  exact next_rational_not_mem a ha l.toFinset (toFinset_ne_univ_of_length_lt_card
    (by rwa [Fintype.card_fin]))

def list_concat_toFinset_eq_cons_toFinset {α : Type*} [DecidableEq α] (l : List α) (a : α)
  : (a :: l).toFinset = (l.concat a).toFinset := by aesop

def list_toFinset_concat {α : Type*} [DecidableEq α] (l : List α) (a : α)
  : (l.concat a).toFinset = insert a (List.toFinset l) := by
    rw [←list_concat_toFinset_eq_cons_toFinset, List.toFinset_cons]

lemma lem2 {a : ℝ} {b : ℝ} (h₁ : -b ≤ a) (h₂ : a ≤ b) : ‖a‖ ≤ b := by
  rw [Real.norm_eq_abs, abs_le]
  exact ⟨h₁, h₂⟩

lemma lem1 {a b : ℝ} (ha₁ : ‖a‖ ≤ 1) (hb₁ : ‖b‖ ≤ 1) (ha₂ : 0 ≤ a) (hb₂ : b ≤ 0) :
  ‖a + b‖ ≤ 1 := by
  rw [Real.norm_of_nonneg ha₂] at ha₁
  rw [Real.norm_of_nonpos hb₂] at hb₁
  apply lem2 <;> linarith

def next_rational_permutation_builder (a : Fin n → ℚ) (ha₁ : Finset.univ.sum a = 0)
  (ha₂ : ∀ i, ‖a i‖ ≤ 1)
  : PermutationBuilder n where
  invariant (l : List (Fin n)) : Prop := ‖l.toFinset.sum a‖ ≤ 1
  next {l : List (Fin n)} _ : l.length < n → Fin n := next_rational_list a ha₁ l
  no_duplicates {l : List (Fin n)} _ (h : l.length < n)
    : next_rational_list a ha₁ l h ∉ l := next_rational_list_not_mem a ha₁ l h
  preserves_invariant {l : List (Fin n)} (h₁ : ‖l.toFinset.sum a‖ ≤ 1) (h₂ : l.length < n)
    : ‖(l.concat (next_rational_list a ha₁ l h₂)).toFinset.sum a‖ ≤ 1 := by
      rw [list_toFinset_concat]
      rw [Finset.sum_insert (by simpa using next_rational_list_not_mem a ha₁ l h₂)]
      by_cases h : l.toFinset.sum a ≤ 0
      · have := next_rational_list_nonneg a ha₁ l h₂ h
        sorry -- exact lem1 (ha₂ _) h₁ this h
      · rw [Rat.not_le] at h
        have := next_rational_list_neg a ha₁ l h₂ h
        rw [add_comm]
        sorry -- exact lem1 h₁ (ha₂ _) h.le this.le
  invariant_empty : ‖[].toFinset.sum a‖ ≤ 1 := by norm_num
