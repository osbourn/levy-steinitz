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

-- TODO: Expand `next` to also recieve a proof that the list was constructed out of next itself.
structure PermutationBuilder (n : ℕ) where
  invariant : List (Fin n) → Prop
  next {l : List (Fin n)} : invariant l → l.length < n → Fin n
  no_duplicates {l : List (Fin n)} (h₁ : invariant l) (h₂ : l.length < n) : next h₁ h₂ ∉ l
  preserves_invariant {l : List (Fin n)} (h₁ : invariant l) (h₂ : l.length < n)
    : invariant (l.concat (next h₁ h₂))
  invariant_empty : invariant []

def PermutationBuilder.toListAux {n : ℕ} (b : PermutationBuilder n) {m : ℕ} (h : m ≤ n)
  : {l : List (Fin n) // l.length = m ∧ b.invariant l} :=
  match m with
  | 0 => ⟨[], rfl, b.invariant_empty⟩
  | (k + 1) =>
    let currentList := b.toListAux (m := k) (Nat.le_of_lt h)
    ⟨currentList.val.concat (b.next (l := currentList.val) currentList.property.right
      (currentList.property.left.trans_lt h)),
      by simp only [List.length_concat, currentList.property],
      b.preserves_invariant (currentList.property.right) (currentList.property.left.trans_lt h)⟩

def PermutationBuilder.toList {n : ℕ} (b : PermutationBuilder n) {m : ℕ} (h : m ≤ n) : List (Fin n)
  := (b.toListAux h).val

lemma PermutationBuilder.toList_length {n : ℕ} (b : PermutationBuilder n) {m : ℕ} (h : m ≤ n)
  : (b.toList h).length = m := (b.toListAux h).property.left

lemma PermutationBuilder.toList_invariant {n : ℕ} (b : PermutationBuilder n) {m : ℕ} (h : m ≤ n)
  : b.invariant (b.toList h) := (b.toListAux h).property.right

lemma PermutationBuilder.toListSucc {n : ℕ} (b : PermutationBuilder n) {m : ℕ} (h : m.succ ≤ n)
  : (b.toList h) = (b.toList (Nat.le_of_lt h)).concat
    (b.next (b.toList_invariant (Nat.le_of_lt h)) (by rwa [b.toList_length (Nat.le_of_lt h)]))
    := rfl

lemma PermutationBuilder.toList_nodup {n : ℕ} (b : PermutationBuilder n) {m : ℕ} (h : m ≤ n)
  : (b.toList h).Nodup := by
  induction m with
  | zero => exact List.nodup_nil
  | succ k ih =>
    specialize ih (Nat.le_of_lt h)
    rw [PermutationBuilder.toListSucc]
    refine List.Nodup.concat ?_ ih
    exact b.no_duplicates (b.toList_invariant (Nat.le_of_lt h))
      (by rwa [b.toList_length (Nat.le_of_lt h)])

lemma Fin.injective_cast {n m : ℕ} (h : n = m) : Function.Injective (Fin.cast h) := by
  intro i j hij
  cases h
  exact hij

def PermutationBuilder.func {n : ℕ} (b : PermutationBuilder n) (m : Fin n) : Fin n :=
  (b.toList n.le_refl).get (m.cast <| by rw [b.toList_length n.le_refl])

lemma PermutationBuilder.func_injective {n : ℕ} (b : PermutationBuilder n)
  : Function.Injective (b.func) := by
  unfold PermutationBuilder.func
  apply Function.Injective.comp
  · rw [←List.nodup_iff_injective_get]
    exact PermutationBuilder.toList_nodup b n.le_refl
  · exact Fin.injective_cast (by rw [b.toList_length n.le_refl])

lemma PermutationBuilder.func_bijective {n : ℕ} (b : PermutationBuilder n)
  : Function.Bijective (b.func) := by
  rw [←Finite.injective_iff_bijective]
  exact b.func_injective
