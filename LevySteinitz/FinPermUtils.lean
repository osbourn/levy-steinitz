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

-- To be removed after updating mathlib to newest version
theorem List.get_eq_get? {α : Type*} (l : List α) (i : Fin l.length) :
    l.get i = (l.get? i).get (by simp [get?_eq_get]) := by
  simp [get_eq_iff]

lemma List.concat_get_last {α : Type*} {a : α} {as : List α} {i : Fin (as.concat a).length}
  (h : ¬i < as.length) : (as.concat a).get i = a := by
  rw [List.get_eq_get?]
  let j := Fin.cast (congr_arg List.length (List.concat_eq_append as a)) i
  have : (i : ℕ) = ↑j := rfl
  simp_rw [List.concat_eq_append as a, this]
  rw [←List.get_eq_get?]
  exact List.get_last h

lemma List.concat_get_lt {α : Type*} {a : α} {as : List α} {i : Fin (as.concat a).length}
  (h : i < as.length) : (as.concat a).get i = as.get (Fin.castLT i h) :=
  sorry

def List.recGen {α : Type*} (g : List α → α) : ℕ → List α
| 0 => []
| n + 1 => let l := List.recGen g n; List.concat l (g l)

lemma List.length_recGen {α : Type*} (g : List α → α) (n : ℕ) : (List.recGen g n).length = n :=
match n with
| 0 => rfl
| n + 1 => by
  have := List.length_recGen g n
  unfold recGen
  aesop

lemma List.recGen_take {α : Type*} (g : List α → α) (n : ℕ) (k : ℕ) (h : k ≤ n)
  : List.take k (List.recGen g n) = List.recGen g k := sorry

def FinVec.recGen {α : Type*} (g : (n : ℕ) → (Fin n → α) → α) (n : ℕ) (i : Fin n) : α :=
  List.get (List.recGen (fun l => g l.length l.get) n) (Fin.cast (List.length_recGen _ n).symm i)

lemma FinVec.recGen_zero {α : Type*} (g : (n : ℕ) → (Fin n → α) → α) : FinVec.recGen g 0 = ![] :=
  Matrix.empty_eq (recGen g 0)

lemma FinVec.recGen_succ {α : Type*} (g : (n : ℕ) → (Fin n → α) → α) (n : ℕ)
  : FinVec.recGen g (n + 1) = Fin.snoc (FinVec.recGen g n) (g n (FinVec.recGen g n)) := by
  funext i
  --change List.get (List.recGen (fun l => g l.length l.get) (n + 1))
  --  (Fin.cast (_ : n + 1 = List.length (List.recGen (fun l => g (List.length l) (List.get l)) (n + 1))) i) = _
  let f (l : List α) := g l.length l.get
  change List.get (List.recGen f (n + 1)) _ = _
  change List.get (let l := List.recGen f n; List.concat l (g l.length l.get)) _ = _

  by_cases h : ↑i < n
  · unfold Fin.snoc
    rw [dif_pos h, cast_eq]
    sorry
  · rw [List.concat_get_last sorry]
    change g _ _ = _
    have : i = Fin.last n := sorry
    rw [this, Fin.snoc_last]
    conv =>
      rhs
      rw [←List.length_recGen f n]
    sorry

def growing_fin_vec {α : Type*} (g : (n : ℕ) → (Fin n → α) → α) : (n : ℕ) → Fin n → α
| 0 => fun _ => g 0 isEmptyElim
| n + 1 => let f := growing_fin_vec g n; Fin.snoc f (g n f)
