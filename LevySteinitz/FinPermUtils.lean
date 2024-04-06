import Mathlib

lemma isSome_find_mem_sdiff {n : ℕ} {s₁ : Finset (Fin n)} {s₂ : Finset (Fin n)}
  (h : ¬s₁ ⊆ s₂) : (Fin.find (· ∈ s₁ \ s₂)).isSome = true := by
    rw [Fin.isSome_find_iff]
    by_contra hc
    apply h
    intro x hx
    aesop

def find_excluding {n : ℕ} (s : Finset (Fin n)) (exclusions : Finset (Fin n))
  (h : ¬s ⊆ exclusions) : Fin n :=
  (Fin.find (· ∈ s \ exclusions)).get (isSome_find_mem_sdiff h)

lemma find_excluding_spec {n : ℕ} (s : Finset (Fin n)) (exclusions : Finset (Fin n))
  (h : ¬s ⊆ exclusions) : find_excluding s exclusions h ∈ s \ exclusions :=
  (Fin.find_spec (· ∈ s \ exclusions)) (Option.get_mem $ isSome_find_mem_sdiff h)

lemma find_excluding_mem {n : ℕ} (s : Finset (Fin n)) (exclusions : Finset (Fin n))
  (h : ¬s ⊆ exclusions) : find_excluding s exclusions h ∈ s := by
    have := find_excluding_spec s exclusions h
    simp_all only [Finset.mem_sdiff]

lemma find_excluding_not_mem {n : ℕ} (s : Finset (Fin n)) (exclusions : Finset (Fin n))
  (h : ¬s ⊆ exclusions) : find_excluding s exclusions h ∉ exclusions := by
    have := find_excluding_spec s exclusions h
    simp_all [Finset.mem_sdiff]

def FinVec.append {α : Type*} {m : ℕ} (f : Fin m → α) (a : α) (x : Fin (m + 1)) : α :=
  if h : ↑x < m then f (Fin.castLT x h) else a

lemma FinVec.append_injective {α : Type*} {m : ℕ} {f : Fin m → α} {a : α}
  (hf : Function.Injective f) (ha : a ∉ Set.range f) : Function.Injective (FinVec.append f a) := by
  intro x y h
  unfold append at h
  by_cases hx : ↑x < m <;> by_cases hy : ↑y < m
  · rw [dif_pos hx, dif_pos hy] at h
    exact Fin.ext (Fin.mk.inj_iff.mp (hf h))
  · exfalso
    rw [dif_pos hx, dif_neg hy] at h
    rw [←h] at ha
    exact ha (Set.mem_range_self _)
  · exfalso
    rw [dif_neg hx, dif_pos hy] at h
    rw [h] at ha
    exact ha (Set.mem_range_self _)
  · apply Fin.ext
    push_neg at hx
    push_neg at hy
    rw [←Nat.le_antisymm hx (Fin.is_le x)]
    rw [←Nat.le_antisymm hy (Fin.is_le y)]
