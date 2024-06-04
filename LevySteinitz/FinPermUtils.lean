import Mathlib

set_option autoImplicit false

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

lemma Fin.snoc_injective {n : ℕ} {α : Type*} {p : Fin n → α} (hp : Function.Injective p)
  {x : α} (hx : x ∉ Set.range p) : Function.Injective (Fin.snoc p x) := by
  intro j k h
  unfold snoc at h
  by_cases hj : ↑j < n <;> by_cases hk : ↑k < n
  · rw [dif_pos hj, dif_pos hk] at h
    exact Fin.ext (Fin.mk.inj_iff.mp (hp h))
  · exfalso
    aesop
  · exfalso
    apply hx
    simp_all
  · apply Fin.ext
    rw [←Nat.le_antisymm (Nat.not_lt.mp hj) (Fin.is_le j)]
    rw [←Nat.le_antisymm (Nat.not_lt.mp hk) (Fin.is_le k)]

def growing_list {α : Type*} (g : List α → α) : ℕ → List α
| 0 => []
| n + 1 => let l := growing_list g n; List.concat l (g l)

-- A list of 8 elements where each element is one more than the sum of the previous elements
#eval growing_list (fun (l : List ℕ) => List.sum l + 1) 20
-- [1, 2, 4, 8, 16, 32, 64, 128]

def growing_fin_vec {α : Type*} (g : (n : ℕ) → (Fin n → α) → α) : (n : ℕ) → Fin n → α
| 0 => fun _ => g 0 isEmptyElim
| n + 1 => let f := growing_fin_vec g n; Fin.snoc f (g n f)

#eval FinVec.map Thunk.get $ growing_fin_vec (fun n (f : Fin n → Thunk ℕ) =>
  Thunk.mk (fun _ => Finset.univ.sum (Thunk.get ∘ f) + 1)) 13 -- Takes a long time
-- ![1, 2, 4, 8, 16, 32, 64, 128]
