import Erdos727.Analytic.CharacterPartialSums

/-!
# The limit of `∑ χ(n)/n` is `L(1, χ)` (step 3 of `CharacterSums`)

Abel's theorem for the Dirichlet series: for real `s > 1`, summation by parts against the
weights `n ^ (-(s-1))` gives `‖L(s, χ) - ℓ‖ ≤ 4 q (s - 1)`, where `ℓ` is the limit of the partial
sums `∑_{n ≤ N} χ(n)/n` (with rate `2q/N`). Continuity of `LFunction χ` at `1` then forces
`L(1, χ) = ℓ`.
-/

namespace Erdos727

open Finset Real Filter Topology

variable {q : ℕ}

/-! ### Summation by parts on `Icc 1 K` -/

/-- Summation by parts: `∑_{n ≤ K} a n w n = ∑_{n ≤ K} S n (w n - w (n+1)) + S K w (K+1)`. -/
lemma sum_Icc_mul_eq_sum_partial_mul_sub (a w : ℕ → ℂ) (K : ℕ) :
    ∑ n ∈ Icc 1 K, a n * w n =
      ∑ n ∈ Icc 1 K, (∑ m ∈ Icc 1 n, a m) * (w n - w (n + 1))
        + (∑ m ∈ Icc 1 K, a m) * w (K + 1) := by
  induction K with
  | zero => simp
  | succ K ih =>
    simp only [Finset.sum_Icc_succ_top (show 1 ≤ K + 1 by omega)]
    rw [ih]
    ring

/-- Telescoping sum. -/
lemma sum_Icc_sub_succ (w : ℕ → ℂ) (K : ℕ) :
    ∑ n ∈ Icc 1 K, (w n - w (n + 1)) = w 1 - w (K + 1) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_Icc_succ_top (show 1 ≤ K + 1 by omega), ih]
    ring

/-- Summation by parts with the limit `ℓ` subtracted. -/
lemma sum_Icc_mul_sub_eq (a w : ℕ → ℂ) (ℓ : ℂ) (K : ℕ) :
    ∑ n ∈ Icc 1 K, a n * w n - ℓ * w 1 =
      ∑ n ∈ Icc 1 K, (∑ m ∈ Icc 1 n, a m - ℓ) * (w n - w (n + 1))
        + (∑ m ∈ Icc 1 K, a m - ℓ) * w (K + 1) := by
  have h1 := sum_Icc_mul_eq_sum_partial_mul_sub a w K
  have h2 := sum_Icc_sub_succ w K
  have h3 : ∑ n ∈ Icc 1 K, (∑ m ∈ Icc 1 n, a m - ℓ) * (w n - w (n + 1)) =
      ∑ n ∈ Icc 1 K, (∑ m ∈ Icc 1 n, a m) * (w n - w (n + 1)) - ℓ * (w 1 - w (K + 1)) := by
    rw [← h2, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun n _ => by ring)
  rw [h3, h1]
  ring

/-! ### The abstract estimate -/

/-- If the partial sums of `a` converge to `ℓ` with rate `C / N`, and `w` is a weight with
`w 1 = 1`, `‖w n - w (n+1)‖ ≤ t / n`, `‖w (K+1)‖ ≤ 1`, then
`‖∑_{n ≤ K} a n w n - ℓ‖ ≤ 2 C t + C / K`. -/
lemma norm_sum_mul_sub_le (a w : ℕ → ℂ) (ℓ : ℂ) {C t : ℝ} (hC : 0 ≤ C) (ht : 0 ≤ t)
    (hℓ : ∀ N : ℕ, 1 ≤ N → ‖∑ n ∈ Icc 1 N, a n - ℓ‖ ≤ C / N)
    (hw1 : w 1 = 1) (hw : ∀ n : ℕ, 1 ≤ n → ‖w n - w (n + 1)‖ ≤ t / n)
    {K : ℕ} (hK : 1 ≤ K) (hwK : ‖w (K + 1)‖ ≤ 1) :
    ‖∑ n ∈ Icc 1 K, a n * w n - ℓ‖ ≤ 2 * C * t + C / K := by
  have hid := sum_Icc_mul_sub_eq a w ℓ K
  rw [hw1, mul_one] at hid
  rw [hid]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (norm_sum_le _ _).trans ?_
    have hb : ∀ n ∈ Icc 1 K,
        ‖(∑ m ∈ Icc 1 n, a m - ℓ) * (w n - w (n + 1))‖ ≤ C * t * ((n : ℝ) ^ 2)⁻¹ := by
      intro n hn
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
      rw [norm_mul]
      calc ‖∑ m ∈ Icc 1 n, a m - ℓ‖ * ‖w n - w (n + 1)‖
          ≤ (C / n) * (t / n) :=
            mul_le_mul (hℓ n hn1) (hw n hn1) (norm_nonneg _) (div_nonneg hC hn0.le)
        _ = C * t * ((n : ℝ) ^ 2)⁻¹ := by rw [div_mul_div_comm, ← sq, div_eq_mul_inv]
    refine (Finset.sum_le_sum hb).trans ?_
    rw [← Finset.mul_sum]
    have hIcc : Icc 1 K = Ioo 0 (K + 1) := by
      ext n
      simp only [Finset.mem_Icc, Finset.mem_Ioo]
      omega
    rw [hIcc]
    refine (mul_le_mul_of_nonneg_left (sum_Ioo_inv_sq_le (α := ℝ) 0 (K + 1))
      (mul_nonneg hC ht)).trans_eq ?_
    push_cast
    ring
  · rw [norm_mul]
    calc ‖∑ m ∈ Icc 1 K, a m - ℓ‖ * ‖w (K + 1)‖ ≤ (C / K) * 1 :=
          mul_le_mul (hℓ K hK) hwK (norm_nonneg _) (div_nonneg hC (Nat.cast_nonneg _))
      _ = C / K := mul_one _

/-! ### The weights `n ^ (-t)` -/

/-- `exp (-u) - exp (-v) ≤ v - u` for `0 ≤ u ≤ v`. -/
lemma exp_neg_sub_exp_neg_le {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) :
    Real.exp (-u) - Real.exp (-v) ≤ v - u := by
  have hE1 : Real.exp (-u) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hE2 : Real.exp (-(v - u)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hE2' : -(v - u) + 1 ≤ Real.exp (-(v - u)) := Real.add_one_le_exp _
  have hsplit : Real.exp (-v) = Real.exp (-u) * Real.exp (-(v - u)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hsplit]
  nlinarith [mul_nonneg (sub_nonneg.2 hE1) (sub_nonneg.2 hE2), Real.exp_pos (-u)]

/-- `x ^ (-t) - (x + 1) ^ (-t) ≤ t / x` for `x ≥ 1`, `t ≥ 0`. -/
lemma rpow_neg_sub_rpow_neg_le {x t : ℝ} (hx : 1 ≤ x) (ht : 0 ≤ t) :
    x ^ (-t) - (x + 1) ^ (-t) ≤ t / x := by
  have hx0 : 0 < x := by linarith
  have hx1 : 0 < x + 1 := by linarith
  have hxne : x ≠ 0 := hx0.ne'
  have hlog : Real.log (x + 1) - Real.log x ≤ 1 / x := by
    rw [← Real.log_div hx1.ne' hxne]
    calc Real.log ((x + 1) / x) ≤ (x + 1) / x - 1 :=
          Real.log_le_sub_one_of_pos (div_pos hx1 hx0)
      _ = 1 / x := by rw [div_sub_one hxne, add_sub_cancel_left]
  rw [Real.rpow_def_of_pos hx0, Real.rpow_def_of_pos hx1,
    show Real.log x * -t = -(Real.log x * t) by ring,
    show Real.log (x + 1) * -t = -(Real.log (x + 1) * t) by ring]
  calc Real.exp (-(Real.log x * t)) - Real.exp (-(Real.log (x + 1) * t))
      ≤ Real.log (x + 1) * t - Real.log x * t :=
        exp_neg_sub_exp_neg_le (mul_nonneg (Real.log_nonneg hx) ht)
          (mul_le_mul_of_nonneg_right (Real.log_le_log hx0 (by linarith)) ht)
    _ = t * (Real.log (x + 1) - Real.log x) := by ring
    _ ≤ t * (1 / x) := mul_le_mul_of_nonneg_left hlog ht
    _ = t / x := by ring

lemma norm_rpow_neg_sub_le {t : ℝ} (ht : 0 ≤ t) {n : ℕ} (hn : 1 ≤ n) :
    ‖((((n : ℝ) ^ (-t) : ℝ) : ℂ) - ((((n + 1 : ℕ) : ℝ) ^ (-t) : ℝ) : ℂ))‖ ≤ t / n := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hd0 : 0 ≤ (n : ℝ) ^ (-t) - ((n : ℝ) + 1) ^ (-t) :=
    sub_nonneg.2 (Real.rpow_le_rpow_of_nonpos hn0 (by linarith) (by linarith))
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  simp only [Nat.cast_add, Nat.cast_one]
  rw [abs_of_nonneg hd0]
  exact rpow_neg_sub_rpow_neg_le hn1 ht

lemma norm_rpow_neg_le_one {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    ‖((((n + 1 : ℕ) : ℝ) ^ (-t) : ℝ) : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
  exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast Nat.le_add_left 1 n) (by linarith)

/-! ### The L-series -/

/-- The terms of the L-series as `χ(n)/n` times the weight `n ^ (-(s-1))`. -/
lemma term_eq_mul_rpow (χ : DirichletCharacter ℂ q) (s : ℝ) (n : ℕ) :
    LSeries.term (χ ·) s n = (χ n / n) * ((((n : ℝ) ^ (-(s - 1)) : ℝ) : ℂ)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    rw [LSeries.term_of_ne_zero hn.ne']
    have h1 : ((n : ℂ) ^ (s : ℂ)) = (((n : ℝ) ^ s : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow hn0.le, Complex.ofReal_natCast]
    have h2 : (n : ℝ) ^ s = n * (n : ℝ) ^ (s - 1) := by
      conv_lhs => rw [show s = 1 + (s - 1) by ring]
      rw [Real.rpow_add hn0, Real.rpow_one]
    have h3 : (n : ℝ) ^ (-(s - 1)) = ((n : ℝ) ^ (s - 1))⁻¹ := Real.rpow_neg hn0.le _
    rw [h1, h2, h3]
    push_cast
    rw [← div_eq_mul_inv, div_div]

/-- The key estimate: for real `s > 1`, `‖L(s, χ) - ℓ‖ ≤ 4 q (s - 1)`. -/
lemma norm_LSeries_sub_le (χ : DirichletCharacter ℂ q) (ℓ : ℂ)
    (hℓ : ∀ N : ℕ, 1 ≤ N → ‖∑ n ∈ Icc 1 N, χ n / n - ℓ‖ ≤ 2 * q / N)
    {s : ℝ} (hs : 1 < s) :
    ‖LSeries (χ ·) s - ℓ‖ ≤ 4 * q * (s - 1) := by
  have ht : 0 ≤ s - 1 := by linarith
  have hsum : LSeriesSummable (χ ·) s :=
    LSeriesSummable_of_bounded_of_one_lt_real (fun n _ => χ.norm_le_one n) hs
  have hlim : Tendsto
      (fun K : ℕ => ∑ n ∈ Icc 1 K, (χ n / n) * ((((n : ℝ) ^ (-(s - 1)) : ℝ) : ℂ)))
      atTop (𝓝 (LSeries (χ ·) s)) := by
    have h := (hsum.hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)
    refine h.congr fun K => ?_
    show ∑ i ∈ range (K + 1), LSeries.term (χ ·) s i = _
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega : 0 < K + 1), LSeries.term_zero,
      zero_add, zero_add, Finset.Ico_add_one_right_eq_Icc]
    exact Finset.sum_congr rfl fun n _ => term_eq_mul_rpow χ s n
  have hnorm : Tendsto
      (fun K : ℕ => ‖∑ n ∈ Icc 1 K, (χ n / n) * ((((n : ℝ) ^ (-(s - 1)) : ℝ) : ℂ)) - ℓ‖)
      atTop (𝓝 ‖LSeries (χ ·) s - ℓ‖) := (hlim.sub_const ℓ).norm
  have hg : Tendsto (fun K : ℕ => 2 * (2 * (q : ℝ)) * (s - 1) + 2 * (q : ℝ) / K) atTop
      (𝓝 (2 * (2 * (q : ℝ)) * (s - 1) + 0)) :=
    tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat _)
  rw [add_zero] at hg
  have hev : ∀ᶠ K : ℕ in atTop,
      ‖∑ n ∈ Icc 1 K, (χ n / n) * ((((n : ℝ) ^ (-(s - 1)) : ℝ) : ℂ)) - ℓ‖ ≤
        2 * (2 * (q : ℝ)) * (s - 1) + 2 * (q : ℝ) / K := by
    filter_upwards [eventually_ge_atTop 1] with K hK
    exact norm_sum_mul_sub_le (fun n => χ n / n) (fun n => (((n : ℝ) ^ (-(s - 1)) : ℝ) : ℂ)) ℓ
      (by positivity) ht hℓ (by simp) (fun n hn => norm_rpow_neg_sub_le ht hn) hK
      (norm_rpow_neg_le_one ht K)
  exact (le_of_tendsto_of_tendsto hnorm hg hev).trans_eq (by ring)

variable [NeZero q]

/-- The limit of `∑_{n ≤ N} χ(n)/n` is `L(1, χ)`. -/
theorem tendsto_sum_char_div_LFunction (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    Filter.Tendsto (fun N : ℕ => ∑ n ∈ Icc 1 N, χ n / n) Filter.atTop
      (nhds (DirichletCharacter.LFunction χ 1)) := by
  obtain ⟨ℓ, hℓ⟩ := exists_limit_sum_char_div χ hχ
  have hℓ' : ∀ N : ℕ, 1 ≤ N → ‖∑ n ∈ Icc 1 N, χ n / n - ℓ‖ ≤ 2 * q / N := by
    intro N hN
    have h := hℓ N (by exact_mod_cast hN)
    rwa [Nat.floor_natCast] at h
  have key : DirichletCharacter.LFunction χ 1 = ℓ := by
    have hcont : Tendsto (fun s : ℝ => ‖DirichletCharacter.LFunction χ s - ℓ‖) (𝓝[>] 1)
        (𝓝 ‖DirichletCharacter.LFunction χ 1 - ℓ‖) := by
      have hc : Continuous (fun s : ℝ => DirichletCharacter.LFunction χ s) :=
        (DirichletCharacter.differentiable_LFunction hχ).continuous.comp Complex.continuous_ofReal
      have h := ((hc.tendsto 1).sub_const ℓ).norm
      simp only [Complex.ofReal_one] at h
      exact h.mono_left nhdsWithin_le_nhds
    have hzero : Tendsto (fun s : ℝ => 4 * (q : ℝ) * (s - 1)) (𝓝[>] 1) (𝓝 0) := by
      have h : Tendsto (fun s : ℝ => 4 * (q : ℝ) * (s - 1)) (𝓝 1) (𝓝 (4 * (q : ℝ) * (1 - 1))) :=
        (continuous_const.mul (continuous_id.sub continuous_const)).tendsto 1
      rw [sub_self, mul_zero] at h
      exact h.mono_left nhdsWithin_le_nhds
    have hbound : ∀ᶠ s : ℝ in 𝓝[>] 1,
        ‖DirichletCharacter.LFunction χ s - ℓ‖ ≤ 4 * (q : ℝ) * (s - 1) := by
      filter_upwards [self_mem_nhdsWithin] with s hs
      have hs' : 1 < s := hs
      rw [DirichletCharacter.LFunction_eq_LSeries χ (by simpa using hs')]
      exact norm_LSeries_sub_le χ ℓ hℓ' hs'
    have h := le_of_tendsto_of_tendsto hcont hzero hbound
    exact sub_eq_zero.mp (norm_le_zero_iff.mp h)
  rw [key, tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) ?_
    (tendsto_const_div_atTop_nhds_zero_nat (2 * (q : ℝ)))
  filter_upwards [eventually_ge_atTop 1] with N hN
  rw [dist_eq_norm]
  exact hℓ' N hN

end Erdos727
