import Erdos727.Progression

/-!
# The failure set and its union bound (Section 5)

For `X ≥ 1` we consider the parameters `v ∈ [X, 2X)`.  A parameter fails if `F v` is not
good.  By `exists_bad_prime_of_not_good`, every failure is witnessed by a form `i` and a prime
`p > 1000` dividing `Lv i v` for which either `p² ∣ Lv i v` (the *square event* `sqSet`) or no
level `h ≥ 2` carries in `F v` (the *no-second-carry event* `badSet`).  Such a prime is at most
`Lv i v ≤ Cb · v < 2 Cb X`.  Hence

  `#(failSet X) ≤ ∑ i, ∑ p ∈ primeRange X, (#(sqSet X i p) + #(badSet X i p))`.

If this is `< X` for all large `X`, then infinitely many `n` are good.
-/

namespace Erdos727

open Finset

open Classical in
/-- Parameters `v ∈ [X, 2X)` for which `F v` is not good. -/
noncomputable def failSet (X : ℕ) : Finset ℕ := (Ico X (2 * X)).filter fun v => ¬ Good (F v)

/-- The square event: `p² ∣ Lv i v`. -/
noncomputable def sqSet (X : ℕ) (i : Fin 6) (p : ℕ) : Finset ℕ :=
  (Ico X (2 * X)).filter fun v => p ^ 2 ∣ Lv i v

open Classical in
/-- The no-second-carry event: `p ∣ Lv i v` and no level `h ≥ 2` carries in `F v`. -/
noncomputable def badSet (X : ℕ) (i : Fin 6) (p : ℕ) : Finset ℕ :=
  (Ico X (2 * X)).filter fun v => p ∣ Lv i v ∧ ∀ h, 2 ≤ h → 2 * (F v % p ^ h) < p ^ h

/-- The primes `1000 < p ≤ 2 Cb X` that can divide some `Lv i v` with `v < 2X`. -/
noncomputable def primeRange (X : ℕ) : Finset ℕ := (Nat.primesLE (2 * Cb * X)).filter fun p => Y < p

theorem mem_primeRange {X p : ℕ} : p ∈ primeRange X ↔ p.Prime ∧ Y < p ∧ p ≤ 2 * Cb * X := by
  unfold primeRange
  rw [Finset.mem_filter, Nat.mem_primesLE]
  tauto

theorem prime_mem_primeRange {X v : ℕ} (hv : v ∈ Ico X (2 * X)) {p : ℕ} (hp : p.Prime)
    (hpY : Y < p) (i : Fin 6) (h : p ∣ Lv i v) : p ∈ primeRange X := by
  rw [mem_primeRange]
  refine ⟨hp, hpY, ?_⟩
  rw [Finset.mem_Ico] at hv
  have hv1 : 1 ≤ v := by omega
  have h1 : p ≤ Lv i v := Nat.le_of_dvd (Lv_pos _ _) h
  have h2 := Lv_le i hv1
  calc p ≤ Cb * v := h1.trans h2
    _ ≤ Cb * (2 * X) := Nat.mul_le_mul_left _ hv.2.le
    _ = 2 * Cb * X := by ring

theorem failSet_subset (X : ℕ) :
    failSet X ⊆ (univ : Finset (Fin 6)).biUnion fun i =>
      (primeRange X).biUnion fun p => sqSet X i p ∪ badSet X i p := by
  classical
  intro v hv
  unfold failSet at hv
  rw [Finset.mem_filter] at hv
  obtain ⟨hvI, hbad⟩ := hv
  obtain ⟨i, p, hp, hpY, hdvd, hor⟩ := exists_bad_prime_of_not_good hbad
  rw [Finset.mem_biUnion]
  refine ⟨i, Finset.mem_univ _, ?_⟩
  rw [Finset.mem_biUnion]
  refine ⟨p, prime_mem_primeRange hvI hp hpY i hdvd, ?_⟩
  rw [Finset.mem_union]
  rcases hor with h | h
  · left
    unfold sqSet
    rw [Finset.mem_filter]
    exact ⟨hvI, h⟩
  · right
    unfold badSet
    rw [Finset.mem_filter]
    exact ⟨hvI, hdvd, h⟩

/-- **Union bound**. -/
theorem card_failSet_le (X : ℕ) :
    #(failSet X) ≤ ∑ i, ∑ p ∈ primeRange X, (#(sqSet X i p) + #(badSet X i p)) := by
  calc #(failSet X) ≤ #((univ : Finset (Fin 6)).biUnion fun i =>
      (primeRange X).biUnion fun p => sqSet X i p ∪ badSet X i p) :=
        Finset.card_le_card (failSet_subset X)
    _ ≤ ∑ i, #((primeRange X).biUnion fun p => sqSet X i p ∪ badSet X i p) :=
        Finset.card_biUnion_le
    _ ≤ ∑ i, ∑ p ∈ primeRange X, #(sqSet X i p ∪ badSet X i p) :=
        Finset.sum_le_sum fun i _ => Finset.card_biUnion_le
    _ ≤ _ := Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun p _ => Finset.card_union_le _ _

theorem exists_good_of_card_lt {X : ℕ} (h : #(failSet X) < X) :
    ∃ v ∈ Ico X (2 * X), Good (F v) := by
  classical
  by_contra hcon
  push Not at hcon
  have hsub : Ico X (2 * X) ⊆ failSet X := by
    intro v hv
    unfold failSet
    rw [Finset.mem_filter]
    exact ⟨hv, hcon v hv⟩
  have := Finset.card_le_card hsub
  rw [Nat.card_Ico] at this
  omega

/-- If almost every scale has a good parameter, there are infinitely many good `n`. -/
theorem infinite_good_of_eventually (h : ∀ᶠ X : ℕ in Filter.atTop, #(failSet X) < X) :
    Set.Infinite {n : ℕ | Good n} := by
  rw [Filter.eventually_atTop] at h
  obtain ⟨X₀, hX₀⟩ := h
  apply Set.infinite_of_forall_exists_gt
  intro n
  obtain ⟨v, hv, hgood⟩ := exists_good_of_card_lt (hX₀ (max X₀ (n + 1)) (le_max_left _ _))
  refine ⟨F v, hgood, ?_⟩
  rw [Finset.mem_Ico] at hv
  have h1 : n + 1 ≤ v := (le_max_right _ _).trans hv.1
  have h2 := sq_le_F v
  nlinarith

end Erdos727
