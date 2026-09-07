import Erdos727.Analytic.LFunctionLink

/-!
# Mertens' first theorem twisted by a nontrivial character (steps 4–5 of `CharacterSums`)
-/

namespace Erdos727

open Finset Real

local notation "Λ" => ArithmeticFunction.vonMangoldt

variable {q : ℕ} [NeZero q]

/-! ### Dirichlet-convolution bookkeeping -/

/-- Reindexing `∑_{n ≤ N} ∑_{d m = n} F d m = ∑_{d ≤ N} ∑_{m ≤ N / d} F d m`. -/
lemma sum_Icc_divisorsAntidiagonal {M : Type*} [AddCommMonoid M] (F : ℕ → ℕ → M) (N : ℕ) :
    ∑ n ∈ Icc 1 N, ∑ x ∈ n.divisorsAntidiagonal, F x.1 x.2
      = ∑ d ∈ Icc 1 N, ∑ m ∈ Icc 1 (N / d), F d m := by
  have hdisj : (↑(Icc 1 N) : Set ℕ).PairwiseDisjoint Nat.divisorsAntidiagonal := by
    intro n _ n' _ hnn'
    rw [Function.onFun, Finset.disjoint_left]
    intro x hx hx'
    rw [Nat.mem_divisorsAntidiagonal] at hx hx'
    exact hnn' (hx.1.symm.trans hx'.1)
  rw [← sum_biUnion hdisj]
  have hset : (Icc 1 N).biUnion Nat.divisorsAntidiagonal
      = (Icc 1 N ×ˢ Icc 1 N).filter (fun x : ℕ × ℕ => x.1 * x.2 ≤ N) := by
    ext ⟨d, m⟩
    simp only [mem_biUnion, mem_Icc, Nat.mem_divisorsAntidiagonal, mem_filter, mem_product]
    constructor
    · rintro ⟨n, ⟨_, hnN⟩, rfl, hn0⟩
      have hd : 1 ≤ d := Nat.pos_of_ne_zero (left_ne_zero_of_mul hn0)
      have hm : 1 ≤ m := Nat.pos_of_ne_zero (right_ne_zero_of_mul hn0)
      have h1 : d ≤ d * m := Nat.le_mul_of_pos_right d hm
      have h2 : m ≤ d * m := Nat.le_mul_of_pos_left m hd
      exact ⟨⟨⟨hd, h1.trans hnN⟩, ⟨hm, h2.trans hnN⟩⟩, hnN⟩
    · rintro ⟨⟨⟨hd, _⟩, ⟨hm, _⟩⟩, hdm⟩
      have hpos : 0 < d * m := Nat.mul_pos hd hm
      exact ⟨d * m, ⟨hpos, hdm⟩, rfl, hpos.ne'⟩
  rw [hset, sum_filter, sum_product]
  refine sum_congr rfl fun d hd => ?_
  rw [mem_Icc] at hd
  have hI : Icc 1 (N / d) = (Icc 1 N).filter (fun m => d * m ≤ N) := by
    ext m
    simp only [mem_filter, mem_Icc]
    constructor
    · rintro ⟨hm, hmd⟩
      have h := (Nat.le_div_iff_mul_le (by omega)).mp hmd
      refine ⟨⟨hm, ?_⟩, by rw [mul_comm]; exact h⟩
      exact (Nat.le_mul_of_pos_right m (by omega)).trans h
    · rintro ⟨⟨hm, _⟩, hdm⟩
      exact ⟨hm, (Nat.le_div_iff_mul_le (by omega)).mpr (by rw [mul_comm]; exact hdm)⟩
  rw [hI, sum_filter]

omit [NeZero q] in
/-- `χ(n) log n / n = ∑_{d m = n} (χ(d) Λ(d) / d) (χ(m) / m)`. -/
lemma char_mul_log_div_eq_sum (χ : DirichletCharacter ℂ q) {n : ℕ} (hn : n ≠ 0) :
    χ n * ((Real.log n / n : ℝ) : ℂ)
      = ∑ x ∈ n.divisorsAntidiagonal, χ x.1 * ((Λ x.1 / x.1 : ℝ) : ℂ) * (χ x.2 / x.2) := by
  have hlog : (Real.log n : ℂ) = ∑ x ∈ n.divisorsAntidiagonal, ((Λ x.1 : ℝ) : ℂ) := by
    have h1 := Nat.sum_divisorsAntidiagonal (fun i _ => ((Λ i : ℝ) : ℂ)) (n := n)
    beta_reduce at h1
    rw [h1, ← ArithmeticFunction.vonMangoldt_sum]
    push_cast
    rfl
  rw [Complex.ofReal_div, Complex.ofReal_natCast, hlog, sum_div, mul_sum]
  refine sum_congr rfl fun x hx => ?_
  rw [Nat.mem_divisorsAntidiagonal] at hx
  obtain ⟨hx, -⟩ := hx
  have h1 : x.1 ≠ 0 := left_ne_zero_of_mul (hx ▸ hn)
  have h2 : x.2 ≠ 0 := right_ne_zero_of_mul (hx ▸ hn)
  have h1' : (x.1 : ℂ) ≠ 0 := by exact_mod_cast h1
  have h2' : (x.2 : ℂ) ≠ 0 := by exact_mod_cast h2
  rw [← hx]
  push_cast
  rw [map_mul]
  field_simp

omit [NeZero q] in
/-- Norm bound on the twisted von Mangoldt weight. -/
lemma norm_char_mul_vonMangoldt_div_le (χ : DirichletCharacter ℂ q) (d : ℕ) :
    ‖χ d * ((Λ d / d : ℝ) : ℂ)‖ ≤ Λ d / d := by
  have h0 : 0 ≤ Λ d / (d : ℝ) :=
    div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg d)
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg h0]
  exact mul_le_of_le_one_left h0 (DirichletCharacter.norm_le_one χ _)

/-- Chebyshev: `∑_{d ≤ N} Λ(d) ≤ (log 4 + 4) N`. -/
lemma sum_vonMangoldt_Icc_le (N : ℕ) : ∑ d ∈ Icc 1 N, Λ d ≤ (Real.log 4 + 4) * N := by
  have h := Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  have hIcc : Icc 1 N = Ioc 0 N := by
    ext d
    simp only [mem_Icc, mem_Ioc]
    omega
  rwa [Chebyshev.psi, Nat.floor_natCast, ← hIcc] at h

/-! ### The rate of convergence of `∑ χ(n)/n` to `L(1, χ)` -/

/-- `‖∑_{n ≤ M} χ(n)/n - L(1, χ)‖ ≤ 2q/M` for `M ≥ 1`. -/
lemma norm_sum_char_div_sub_LFunction_le (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    ∀ M : ℕ, 1 ≤ M →
      ‖∑ n ∈ Icc 1 M, χ n / n - DirichletCharacter.LFunction χ 1‖ ≤ 2 * q / M := by
  obtain ⟨ℓ, hℓ⟩ := exists_limit_sum_char_div χ hχ
  have hM : ∀ M : ℕ, 1 ≤ M → ‖∑ n ∈ Icc 1 M, χ n / n - ℓ‖ ≤ 2 * q / M := fun M hM => by
    have := hℓ M (by exact_mod_cast hM)
    rwa [Nat.floor_natCast] at this
  have hT : Filter.Tendsto (fun N : ℕ => ∑ n ∈ Icc 1 N, χ n / n) Filter.atTop (nhds ℓ) := by
    rw [← tendsto_sub_nhds_zero_iff]
    refine squeeze_zero_norm' ?_ (tendsto_const_div_atTop_nhds_zero_nat (2 * q : ℝ))
    filter_upwards [Filter.eventually_ge_atTop 1] with N hN using hM N hN
  have : ℓ = DirichletCharacter.LFunction χ 1 :=
    tendsto_nhds_unique hT (tendsto_sum_char_div_LFunction χ hχ)
  rw [← this]
  exact hM

/-- `N ≤ 2 d ⌊N/d⌋` for `1 ≤ d ≤ N`. -/
lemma le_two_mul_div {N d : ℕ} (hd : 1 ≤ d) (hdN : d ≤ N) :
    (N : ℝ) ≤ 2 * d * ((N / d : ℕ) : ℝ) := by
  obtain ⟨k, hk⟩ : ∃ k, k = N / d := ⟨_, rfl⟩
  have h1 : N < N / d * d + d := Nat.lt_div_mul_add (by omega)
  have h2 : 1 ≤ N / d := (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
  rw [← hk] at h1 h2 ⊢
  have h4 : d ≤ k * d := Nat.le_mul_of_pos_left d h2
  have h3 : N ≤ 2 * d * k := by nlinarith
  exact_mod_cast h3

/-- The error term `‖T(N/d) - L(1,χ)‖ ≤ 4 q d / N` for `1 ≤ d ≤ N`. -/
lemma norm_sum_char_div_floor_sub_le (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {N d : ℕ}
    (hd : 1 ≤ d) (hdN : d ≤ N) :
    ‖∑ n ∈ Icc 1 (N / d), χ n / n - DirichletCharacter.LFunction χ 1‖ ≤ 4 * q * d / N := by
  have hk : 1 ≤ N / d := (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
  refine (norm_sum_char_div_sub_LFunction_le χ hχ (N / d) hk).trans ?_
  have hk' : (0 : ℝ) < ((N / d : ℕ) : ℝ) := by exact_mod_cast hk
  have hN' : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hb := le_two_mul_div hd hdN
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  rw [div_le_iff₀ hk', div_mul_eq_mul_div, le_div_iff₀ hN']
  nlinarith [mul_le_mul_of_nonneg_left hb (by positivity : (0 : ℝ) ≤ 2 * q)]

/-! ### Step 4 -/

/-- `∑_{d ≤ N} χ(d) Λ(d) / d` is bounded; this uses `L(1, χ) ≠ 0`. -/
theorem exists_bound_sum_char_vonMangoldt_div (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    ∃ C : ℝ, ∀ N : ℕ, ‖∑ d ∈ Icc 1 N, χ d * (ArithmeticFunction.vonMangoldt d / d : ℝ)‖ ≤ C := by
  obtain ⟨ℓ, hℓdef⟩ : ∃ ℓ : ℂ, ℓ = DirichletCharacter.LFunction χ 1 := ⟨_, rfl⟩
  have hℓ : ℓ ≠ 0 := hℓdef ▸ DirichletCharacter.LFunction_apply_one_ne_zero hχ
  have hℓpos : 0 < ‖ℓ‖ := norm_pos_iff.mpr hℓ
  obtain ⟨C₁, hC₁⟩ := exists_bound_sum_char_log_div χ hχ
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = 4 * q * (Real.log 4 + 4) := ⟨_, rfl⟩
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  obtain ⟨T, hT⟩ : ∃ T : ℕ → ℂ, ∀ M, T M = ∑ n ∈ Icc 1 M, χ n / n := ⟨_, fun _ => rfl⟩
  refine ⟨(C₁ + K) / ‖ℓ‖, fun N => ?_⟩
  rw [le_div_iff₀ hℓpos]
  -- the convolution identity
  have hid : ∑ n ∈ Icc 1 N, χ n * ((Real.log n / n : ℝ) : ℂ)
      = ∑ d ∈ Icc 1 N, χ d * ((Λ d / d : ℝ) : ℂ) * T (N / d) := by
    calc ∑ n ∈ Icc 1 N, χ n * ((Real.log n / n : ℝ) : ℂ)
        = ∑ n ∈ Icc 1 N, ∑ x ∈ n.divisorsAntidiagonal,
            χ x.1 * ((Λ x.1 / x.1 : ℝ) : ℂ) * (χ x.2 / x.2) :=
          sum_congr rfl fun n hn =>
            char_mul_log_div_eq_sum χ (Nat.one_le_iff_ne_zero.mp (mem_Icc.mp hn).1)
      _ = ∑ d ∈ Icc 1 N, ∑ m ∈ Icc 1 (N / d), χ d * ((Λ d / d : ℝ) : ℂ) * (χ m / m) :=
          sum_Icc_divisorsAntidiagonal (fun d m => χ d * ((Λ d / d : ℝ) : ℂ) * (χ m / m)) N
      _ = _ := sum_congr rfl fun d _ => by rw [hT, mul_sum]
  -- split off the main term
  have hsplit : ∑ d ∈ Icc 1 N, χ d * ((Λ d / d : ℝ) : ℂ) * T (N / d)
      = (∑ d ∈ Icc 1 N, χ d * ((Λ d / d : ℝ) : ℂ)) * ℓ
        + ∑ d ∈ Icc 1 N, χ d * ((Λ d / d : ℝ) : ℂ) * (T (N / d) - ℓ) := by
    rw [sum_mul, ← sum_add_distrib]
    exact sum_congr rfl fun d _ => by ring
  -- the error term
  have hE : ‖∑ d ∈ Icc 1 N, χ d * ((Λ d / d : ℝ) : ℂ) * (T (N / d) - ℓ)‖ ≤ K := by
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simpa using hK0
    · have hN' : (0 : ℝ) < N := by exact_mod_cast hN
      calc ‖∑ d ∈ Icc 1 N, χ d * ((Λ d / d : ℝ) : ℂ) * (T (N / d) - ℓ)‖
          ≤ ∑ d ∈ Icc 1 N, ‖χ d * ((Λ d / d : ℝ) : ℂ) * (T (N / d) - ℓ)‖ := norm_sum_le _ _
        _ ≤ ∑ d ∈ Icc 1 N, (Λ d / d) * (4 * q * d / N) := by
            refine sum_le_sum fun d hd => ?_
            rw [mem_Icc] at hd
            rw [norm_mul]
            refine mul_le_mul (norm_char_mul_vonMangoldt_div_le χ d) ?_ (norm_nonneg _)
              (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg d))
            rw [hT, hℓdef]
            exact norm_sum_char_div_floor_sub_le χ hχ hd.1 hd.2
        _ = ∑ d ∈ Icc 1 N, (4 * q / N) * Λ d := by
            refine sum_congr rfl fun d hd => ?_
            rw [mem_Icc] at hd
            have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
            field_simp
        _ = (4 * q / N) * ∑ d ∈ Icc 1 N, Λ d := by rw [mul_sum]
        _ ≤ (4 * q / N) * ((Real.log 4 + 4) * N) := by
            gcongr
            exact sum_vonMangoldt_Icc_le N
        _ = K := by rw [hK]; field_simp
  have hmain : (∑ d ∈ Icc 1 N, χ d * ((Λ d / d : ℝ) : ℂ)) * ℓ
      = ∑ n ∈ Icc 1 N, χ n * ((Real.log n / n : ℝ) : ℂ)
        - ∑ d ∈ Icc 1 N, χ d * ((Λ d / d : ℝ) : ℂ) * (T (N / d) - ℓ) := by
    rw [hid, hsplit]
    ring
  calc ‖∑ d ∈ Icc 1 N, χ d * ((Λ d / d : ℝ) : ℂ)‖ * ‖ℓ‖
      = ‖(∑ d ∈ Icc 1 N, χ d * ((Λ d / d : ℝ) : ℂ)) * ℓ‖ := (norm_mul _ _).symm
    _ = ‖∑ n ∈ Icc 1 N, χ n * ((Real.log n / n : ℝ) : ℂ)
        - ∑ d ∈ Icc 1 N, χ d * ((Λ d / d : ℝ) : ℂ) * (T (N / d) - ℓ)‖ := by rw [hmain]
    _ ≤ ‖∑ n ∈ Icc 1 N, χ n * ((Real.log n / n : ℝ) : ℂ)‖
        + ‖∑ d ∈ Icc 1 N, χ d * ((Λ d / d : ℝ) : ℂ) * (T (N / d) - ℓ)‖ := norm_sub_le _ _
    _ ≤ C₁ + K := add_le_add (hC₁ N) hE

/-! ### Step 5: removing the proper prime powers -/

/-- Splitting a sum supported on prime powers into primes and proper prime powers. -/
lemma sum_Icc_eq_sum_primesLE_add {M : Type*} [AddCommMonoid M] (f : ℕ → M)
    (hf : ∀ d, ¬ IsPrimePow d → f d = 0) (N : ℕ) :
    ∑ d ∈ Icc 1 N, f d = ∑ p ∈ Nat.primesLE N, f p
      + ∑ d ∈ (Icc 1 N).filter (fun d => IsPrimePow d ∧ ¬ d.Prime), f d := by
  have h1 : ∑ d ∈ Icc 1 N, f d = ∑ d ∈ (Icc 1 N).filter IsPrimePow, f d :=
    (sum_filter_of_ne fun d _ hd => by_contra fun h => hd (hf d h)).symm
  have h2 : Nat.primesLE N = ((Icc 1 N).filter IsPrimePow).filter Nat.Prime := by
    ext p
    simp only [Nat.mem_primesLE, mem_filter, mem_Icc]
    constructor
    · rintro ⟨hpN, hp⟩
      exact ⟨⟨⟨hp.one_lt.le, hpN⟩, hp.isPrimePow⟩, hp⟩
    · rintro ⟨⟨⟨_, hpN⟩, _⟩, hp⟩
      exact ⟨hpN, hp⟩
  have h3 : (Icc 1 N).filter (fun d => IsPrimePow d ∧ ¬ d.Prime)
      = ((Icc 1 N).filter IsPrimePow).filter (fun d => ¬ d.Prime) := by
    ext d
    simp only [mem_filter]
    tauto
  rw [h1, h2, h3, sum_filter_add_sum_filter_not]

/-- The proper prime powers contribute at most `E₁ ≤ 1` to `∑ Λ(d)/d`. -/
lemma sum_properPrimePow_vonMangoldt_div_le (N : ℕ) :
    ∑ d ∈ (Icc 1 N).filter (fun d => IsPrimePow d ∧ ¬ d.Prime), Λ d / (d : ℝ) ≤ 1 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  · have hsplit := sum_Icc_eq_sum_primesLE_add (fun d => Λ d / (d : ℝ))
      (fun d hd => by rw [ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hd, zero_div]) N
    beta_reduce at hsplit
    have hM := Mertens.sum_vonMangoldt_le_sum_prime_add_E₁ (x := N) (by exact_mod_cast hN)
    have hIcc : Icc 1 N = Ioc 0 N := by
      ext d
      simp only [mem_Icc, mem_Ioc]
      omega
    rw [Nat.floor_natCast, ← hIcc] at hM
    have hprime : ∑ p ∈ Nat.primesLE N, Λ p / (p : ℝ) = ∑ p ∈ Nat.primesLE N, Real.log p / p :=
      sum_congr rfl fun p hp => by
        rw [ArithmeticFunction.vonMangoldt_apply_prime (Nat.prime_of_mem_primesLE hp)]
    have hE := Mertens.E₁_le
    linarith

/-- **Mertens' first theorem twisted by a nontrivial character.** -/
theorem exists_bound_sum_char_prime_log_div (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    ∃ C : ℝ, ∀ N : ℕ, ‖∑ p ∈ Nat.primesLE N, χ p * (log p / p : ℝ)‖ ≤ C := by
  obtain ⟨C, hC⟩ := exists_bound_sum_char_vonMangoldt_div χ hχ
  refine ⟨C + 1, fun N => ?_⟩
  have hsplit := sum_Icc_eq_sum_primesLE_add (fun d => χ d * ((Λ d / d : ℝ) : ℂ))
    (fun d hd => by rw [ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hd]; simp) N
  beta_reduce at hsplit
  have hprime : ∑ p ∈ Nat.primesLE N, χ p * ((Λ p / p : ℝ) : ℂ)
      = ∑ p ∈ Nat.primesLE N, χ p * ((Real.log p / p : ℝ) : ℂ) :=
    sum_congr rfl fun p hp => by
      rw [ArithmeticFunction.vonMangoldt_apply_prime (Nat.prime_of_mem_primesLE hp)]
  rw [← hprime, eq_sub_of_add_eq hsplit.symm]
  have hR : ‖∑ d ∈ (Icc 1 N).filter (fun d => IsPrimePow d ∧ ¬ d.Prime),
      χ d * ((Λ d / d : ℝ) : ℂ)‖ ≤ 1 :=
    calc ‖∑ d ∈ (Icc 1 N).filter (fun d => IsPrimePow d ∧ ¬ d.Prime),
          χ d * ((Λ d / d : ℝ) : ℂ)‖
        ≤ ∑ d ∈ (Icc 1 N).filter (fun d => IsPrimePow d ∧ ¬ d.Prime),
          ‖χ d * ((Λ d / d : ℝ) : ℂ)‖ := norm_sum_le _ _
      _ ≤ ∑ d ∈ (Icc 1 N).filter (fun d => IsPrimePow d ∧ ¬ d.Prime), Λ d / (d : ℝ) :=
          sum_le_sum fun d _ => norm_char_mul_vonMangoldt_div_le χ d
      _ ≤ 1 := sum_properPrimePow_vonMangoldt_div_le N
  exact (norm_sub_le _ _).trans (add_le_add (hC N) hR)

end Erdos727
