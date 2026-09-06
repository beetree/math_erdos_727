import Erdos727.Ranges

/-!
# The square events (Section 5, (5.1))

For a prime `p > 1000`, `p² ∣ Lv i v` is a single residue class modulo `p²` (because
`slope i * Q` is a unit modulo `p`), so `#(sqSet X i p) ≤ X / p² + 1`; moreover `sqSet X i p`
is empty unless `p² ≤ 2 Cb X`.  Summing, `∑_p #(sqSet X i p) ≤ X ∑_{n > 1000} n⁻² + √(2 Cb X)
≤ X / 1000 + √(2 Cb X)`, and six forms give `≤ 0.006 X + o(X) ≤ 0.01 X`.
-/

namespace Erdos727

open Finset Real Filter

/-- `p² ∣ Lv i v` is a single residue class modulo `p²`. -/
theorem exists_root_sq {p : ℕ} (hp : p.Prime) (hpY : Y < p) (i : Fin 6) :
    ∃ r, ∀ v, p ^ 2 ∣ Lv i v ↔ v % p ^ 2 = r := by
  have hnd := not_dvd_slope_mul_Q hp hpY i
  have hcop : Nat.Coprime (slope i * Q) (p ^ 2) :=
    Nat.Coprime.pow_right 2 ((Nat.Prime.coprime_iff_not_dvd hp).mpr hnd).symm
  have : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  have hunit : IsUnit ((slope i * Q : ℕ) : ZMod (p ^ 2)) :=
    (ZMod.isUnit_iff_coprime _ _).mpr hcop
  obtain ⟨w, hw⟩ := hunit.exists_right_inv
  push_cast at hw hunit
  obtain ⟨r, hr⟩ : ∃ r : ZMod (p ^ 2),
      r = -((slope i : ZMod (p ^ 2)) * (t₀ : ZMod (p ^ 2)) + (icept i : ZMod (p ^ 2))) * w :=
    ⟨_, rfl⟩
  refine ⟨r.val, fun v => ?_⟩
  have key : (Lv i v : ZMod (p ^ 2)) =
      (slope i : ZMod (p ^ 2)) * (Q : ZMod (p ^ 2)) * ((v : ZMod (p ^ 2)) - r) := by
    rw [hr]
    unfold Lv L
    push_cast
    linear_combination (-((slope i : ZMod (p ^ 2)) * (t₀ : ZMod (p ^ 2)) +
      (icept i : ZMod (p ^ 2)))) * hw
  constructor
  · intro hdvd
    have h0 : (Lv i v : ZMod (p ^ 2)) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
    rw [key, hunit.mul_right_eq_zero, sub_eq_zero] at h0
    rw [← ZMod.val_natCast, h0]
  · intro hv
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    rw [key]
    have hvr : (v : ZMod (p ^ 2)) = r := by
      rw [← ZMod.natCast_mod v (p ^ 2), hv, ZMod.natCast_zmod_val]
    rw [hvr, sub_self, mul_zero]

theorem card_sqSet_le {p : ℕ} (hp : p.Prime) (hpY : Y < p) (i : Fin 6) (X : ℕ) :
    #(sqSet X i p) ≤ X / p ^ 2 + 1 := by
  obtain ⟨r, hr⟩ := exists_root_sq hp hpY i
  have hpos : 0 < p ^ 2 := pow_pos hp.pos 2
  have h : sqSet X i p = {v ∈ Ico X (X + X) | v % p ^ 2 = r} := by
    unfold sqSet
    rw [two_mul]
    exact Finset.filter_congr fun v _ => hr v
  rw [h]
  exact card_filter_mod_eq_le hpos

theorem sqSet_eq_empty {p : ℕ} (i : Fin 6) {X : ℕ} (h : 2 * Cb * X < p ^ 2) : sqSet X i p = ∅ := by
  unfold sqSet
  rw [Finset.filter_eq_empty_iff]
  intro v hv hdvd
  rw [Finset.mem_Ico] at hv
  have hv1 : 1 ≤ v := by omega
  have h1 : p ^ 2 ≤ Lv i v := Nat.le_of_dvd (Lv_pos _ _) hdvd
  have h2 := Lv_le i hv1
  have h3 : Cb * v ≤ Cb * (2 * X) := Nat.mul_le_mul_left _ hv.2.le
  nlinarith

/-- Auxiliary telescoping bound: `∑_{m < n ≤ M} 1/n² ≤ 1/m - 1/M` for `1 ≤ m ≤ M`. -/
theorem sum_Ioc_inv_sq_le {m : ℕ} (hm : 1 ≤ m) : ∀ M, m ≤ M →
    ∑ n ∈ Ioc m M, (1 : ℝ) / (n : ℝ) ^ 2 ≤ 1 / (m : ℝ) - 1 / (M : ℝ) := by
  intro M hM
  induction M, hM using Nat.le_induction with
  | base => simp
  | succ M hM ih =>
    rw [Finset.sum_Ioc_succ_top hM]
    have hMpos : (0 : ℝ) < M := by exact_mod_cast (hm.trans hM)
    have hM1 : (M : ℝ) + 1 ≠ 0 := by positivity
    have e : (1 : ℝ) / M - 1 / (M + 1) = 1 / (M * (M + 1)) := by
      rw [div_sub_div _ _ hMpos.ne' hM1]
      congr 1
      ring
    have hle : (1 : ℝ) / (M + 1) ^ 2 ≤ 1 / (M * (M + 1)) :=
      one_div_le_one_div_of_le (by positivity) (by nlinarith)
    push_cast
    linarith

/-- `∑_{n > Y} 1/n² ≤ 1/Y`, in the finite form needed. -/
theorem sum_inv_sq_le (s : Finset ℕ) (hs : ∀ n ∈ s, Y < n) : ∑ n ∈ s, (1 : ℝ) / (n : ℝ) ^ 2 ≤ 1 / Y := by
  have hY : 1 ≤ Y := by unfold Y; norm_num
  have hsub : s ⊆ Ioc Y (max Y (s.sup id)) := by
    intro n hn
    rw [Finset.mem_Ioc]
    refine ⟨hs n hn, ?_⟩
    have h1 : n ≤ s.sup id := Finset.le_sup (f := id) hn
    exact h1.trans (le_max_right _ _)
  have hYM : Y ≤ max Y (s.sup id) := le_max_left _ _
  calc ∑ n ∈ s, (1 : ℝ) / (n : ℝ) ^ 2 ≤ ∑ n ∈ Ioc Y (max Y (s.sup id)), (1 : ℝ) / (n : ℝ) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => by positivity)
    _ ≤ 1 / (Y : ℝ) - 1 / ((max Y (s.sup id) : ℕ) : ℝ) := sum_Ioc_inv_sq_le hY _ hYM
    _ ≤ 1 / Y := by
        have : (0 : ℝ) ≤ 1 / ((max Y (s.sup id) : ℕ) : ℝ) := by positivity
        linarith

/-- Auxiliary: the primes of `primeRange X` with `p² ≤ 2 Cb X`. -/
noncomputable def sqRange (X : ℕ) : Finset ℕ := (primeRange X).filter fun p => p ^ 2 ≤ 2 * Cb * X

/-- Only the primes with `p² ≤ 2 Cb X` contribute to the square events. -/
theorem sum_sqSet_eq (X : ℕ) (i : Fin 6) :
    ∑ p ∈ primeRange X, #(sqSet X i p) = ∑ p ∈ sqRange X, #(sqSet X i p) := by
  unfold sqRange
  symm
  apply Finset.sum_filter_of_ne
  intro p _ hne
  by_contra hlt
  push Not at hlt
  exact hne (by rw [sqSet_eq_empty i hlt, card_empty])

/-- `#(sqRange X) ≤ √(2 Cb X) + 1`. -/
theorem card_sqRange_le (X : ℕ) : (#(sqRange X) : ℝ) ≤ √(2 * Cb * X) + 1 := by
  have hsub : sqRange X ⊆ range (Nat.sqrt (2 * Cb * X) + 1) := by
    intro p hp
    unfold sqRange at hp
    rw [mem_filter] at hp
    rw [mem_range, Nat.lt_succ_iff, Nat.le_sqrt']
    exact hp.2
  have h1 : #(sqRange X) ≤ Nat.sqrt (2 * Cb * X) + 1 := (card_le_card hsub).trans (by simp)
  calc (#(sqRange X) : ℝ) ≤ ((Nat.sqrt (2 * Cb * X) + 1 : ℕ) : ℝ) := by exact_mod_cast h1
    _ = (Nat.sqrt (2 * Cb * X) : ℝ) + 1 := by push_cast; ring
    _ ≤ √(2 * Cb * X) + 1 := by
        have := Real.nat_sqrt_le_real_sqrt (a := 2 * Cb * X)
        push_cast at this
        linarith

/-- The bound for a single form: `∑_p #(sqSet X i p) ≤ X / Y + √(2 Cb X) + 1`. -/
theorem sum_sqSet_le (X : ℕ) (i : Fin 6) :
    (∑ p ∈ primeRange X, (#(sqSet X i p) : ℝ)) ≤ (X : ℝ) / Y + (√(2 * Cb * X) + 1) := by
  have h1 : (∑ p ∈ primeRange X, (#(sqSet X i p) : ℝ)) =
      ∑ p ∈ sqRange X, (#(sqSet X i p) : ℝ) := by
    exact_mod_cast sum_sqSet_eq X i
  rw [h1]
  have hY : ∀ p ∈ sqRange X, Y < p := fun p hp => by
    unfold sqRange at hp
    rw [mem_filter, mem_primeRange] at hp
    exact hp.1.2.1
  calc ∑ p ∈ sqRange X, (#(sqSet X i p) : ℝ)
      ≤ ∑ p ∈ sqRange X, ((X : ℝ) / (p : ℝ) ^ 2 + 1) := by
        apply Finset.sum_le_sum
        intro p hp
        unfold sqRange at hp
        rw [mem_filter, mem_primeRange] at hp
        calc (#(sqSet X i p) : ℝ) ≤ ((X / p ^ 2 + 1 : ℕ) : ℝ) := by
              exact_mod_cast card_sqSet_le hp.1.1 hp.1.2.1 i X
          _ ≤ (X : ℝ) / (p : ℝ) ^ 2 + 1 := by
              have := Nat.cast_div_le (α := ℝ) (m := X) (n := p ^ 2)
              push_cast at this ⊢
              linarith
    _ = (X : ℝ) * ∑ p ∈ sqRange X, (1 : ℝ) / (p : ℝ) ^ 2 + #(sqRange X) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one, Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro p _
        rw [mul_one_div]
    _ ≤ (X : ℝ) * (1 / Y) + (√(2 * Cb * X) + 1) := by
        gcongr
        · exact sum_inv_sq_le _ hY
        · exact card_sqRange_le X
    _ = (X : ℝ) / Y + (√(2 * Cb * X) + 1) := by ring

/-- **Section 5**: the square events. -/
theorem sq_bound : ∀ᶠ X : ℕ in atTop,
    (∑ i, ∑ p ∈ primeRange X, #(sqSet X i p) : ℝ) ≤ (1 / 100) * X := by
  rw [Filter.eventually_atTop]
  refine ⟨2 * Cb * 3000 ^ 2 + 3000, fun X hX => ?_⟩
  have hCb : (1 : ℝ) ≤ Cb := by
    have : 1 ≤ Cb := by unfold Cb; omega
    exact_mod_cast this
  have hXr : (2 * Cb * 3000 ^ 2 + 3000 : ℝ) ≤ X := by exact_mod_cast hX
  have hX0 : (0 : ℝ) ≤ X := Nat.cast_nonneg X
  have hsqrt : √(2 * Cb * X) + 1 ≤ (X : ℝ) / 1500 := by
    have h2 : (2 * Cb * X : ℝ) ≤ ((X : ℝ) / 3000) ^ 2 := by
      have e : ((X : ℝ) / 3000) ^ 2 = X * X / 3000 ^ 2 := by ring
      rw [e, le_div_iff₀ (by norm_num)]
      have : (2 * Cb * 3000 ^ 2 : ℝ) * X ≤ X * X :=
        mul_le_mul_of_nonneg_right (by linarith) hX0
      nlinarith
    have h1 : √(2 * Cb * X) ≤ (X : ℝ) / 3000 :=
      calc √(2 * Cb * X) ≤ √(((X : ℝ) / 3000) ^ 2) := Real.sqrt_le_sqrt h2
        _ = X / 3000 := Real.sqrt_sq (by positivity)
    linarith
  have hY : (Y : ℝ) = 1000 := by unfold Y; norm_num
  calc ∑ i, ∑ p ∈ primeRange X, (#(sqSet X i p) : ℝ)
      ≤ ∑ i : Fin 6, ((X : ℝ) / Y + (√(2 * Cb * X) + 1)) :=
        Finset.sum_le_sum fun i _ => sum_sqSet_le X i
    _ = 6 * ((X : ℝ) / Y + (√(2 * Cb * X) + 1)) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          Nat.cast_ofNat]
    _ ≤ (1 / 100) * X := by rw [hY]; linarith

end Erdos727
