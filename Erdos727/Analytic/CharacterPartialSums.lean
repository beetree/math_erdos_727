import Erdos727.Analytic.Mertens

/-!
# Partial sums of Dirichlet characters (steps 1–2 of `CharacterSums`)
-/

namespace Erdos727

open Finset Real Topology

variable {q : ℕ} [NeZero q]

omit [NeZero q] in
/-- A nontrivial Dirichlet character vanishes at `0`. -/
lemma char_apply_zero_eq_zero (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) : χ 0 = 0 := by
  by_contra h
  apply hχ
  have h0 : χ 0 = 1 := by
    have : χ 0 * χ 0 = χ 0 := by rw [← map_mul, mul_zero]
    exact (mul_eq_left₀ h).mp this
  ext a
  rw [MulChar.one_apply_coe]
  calc χ a = χ a * χ 0 := by rw [h0, mul_one]
    _ = χ ((a : ZMod q) * 0) := by rw [map_mul]
    _ = 1 := by rw [mul_zero, h0]

/-- The sum of a nontrivial character over a full period vanishes. -/
lemma sum_range_char_eq_zero (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    ∑ n ∈ range q, χ n = 0 := by
  refine (sum_nbij (fun n : ℕ => (n : ZMod q)) (fun _ _ => mem_univ _) ?_ ?_
    (fun _ _ => rfl)).trans (MulChar.sum_eq_zero_of_ne_one hχ)
  · intro a ha b hb hab
    simp only [coe_range, Set.mem_Iio] at ha hb
    have := congrArg ZMod.val hab
    rwa [ZMod.val_cast_of_lt ha, ZMod.val_cast_of_lt hb] at this
  · intro a _
    exact ⟨a.val, by simpa using ZMod.val_lt a, ZMod.natCast_zmod_val a⟩

/-- Periodicity: complete blocks of length `q` contribute nothing. -/
lemma sum_range_char_periodic (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (k r : ℕ) :
    ∑ n ∈ range (q * k + r), χ n = ∑ n ∈ range r, χ n := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e : q * (k + 1) + r = q + (q * k + r) := by ring
    rw [e, sum_range_add, sum_range_char_eq_zero χ hχ, zero_add, ← ih]
    refine sum_congr rfl fun n _ => ?_
    have : ((q + n : ℕ) : ZMod q) = n := by simp
    rw [this]

/-- Partial sums of a nontrivial Dirichlet character are bounded by the modulus. -/
theorem norm_sum_char_le (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (N : ℕ) :
    ‖∑ n ∈ range N, χ n‖ ≤ q := by
  rw [← Nat.div_add_mod N q, sum_range_char_periodic χ hχ]
  calc ‖∑ n ∈ range (N % q), χ n‖ ≤ ∑ n ∈ range (N % q), ‖χ n‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ range (N % q), (1 : ℝ) :=
      sum_le_sum fun n _ => DirichletCharacter.norm_le_one χ _
    _ = ((N % q : ℕ) : ℝ) := by simp
    _ ≤ q := by exact_mod_cast (Nat.mod_lt N (NeZero.pos q)).le

/-- Discrete Abel summation (summation by parts). -/
lemma sum_mul_eq_abel (G f : ℕ → ℂ) (N : ℕ) :
    ∑ n ∈ range (N + 1), (G (n + 1) - G n) * f n
      = G (N + 1) * f N + ∑ n ∈ range N, G (n + 1) * (f n - f (n + 1)) - G 0 * f 0 := by
  induction N with
  | zero => simp only [zero_add, sum_range_one, sum_range_zero, add_zero]; ring
  | succ N ih => rw [sum_range_succ, ih, sum_range_succ]; ring

/-- The telescoping weights `1/(i+1) - 1/(i+2)`. -/
private noncomputable def dd (i : ℕ) : ℝ := 1 / ((i : ℝ) + 1) - 1 / ((i : ℝ) + 2)

private lemma dd_nonneg (i : ℕ) : 0 ≤ dd i := by
  unfold dd
  rw [sub_nonneg]
  exact one_div_le_one_div_of_le (by positivity) (by linarith)

private lemma sum_dd (M n : ℕ) :
    ∑ i ∈ range n, dd (i + M) = 1 / ((M : ℝ) + 1) - 1 / ((n : ℝ) + M + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih]
    unfold dd
    push_cast
    ring

private lemma hasSum_dd (M : ℕ) : HasSum (fun i => dd (i + M)) (1 / ((M : ℝ) + 1)) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun i => dd_nonneg _)]
  simp_rw [sum_dd]
  have h : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + M + 1)) Filter.atTop (𝓝 0) := by
    refine tendsto_const_nhds.div_atTop ?_
    exact (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds).atTop_add tendsto_const_nhds
  have h2 : Filter.Tendsto (fun n : ℕ => 1 / ((M : ℝ) + 1) - 1 / ((n : ℝ) + M + 1)) Filter.atTop
      (𝓝 (1 / ((M : ℝ) + 1) - 0)) := tendsto_const_nhds.sub h
  rwa [sub_zero] at h2

/-- `∑_{1 ≤ n ≤ y} χ(n)/n` converges, with rate `2q/y`. -/
theorem exists_limit_sum_char_div (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    ∃ ℓ : ℂ, ∀ y : ℝ, 1 ≤ y → ‖∑ n ∈ Icc 1 ⌊y⌋₊, χ n / n - ℓ‖ ≤ 2 * q / y := by
  obtain ⟨G, hG⟩ : ∃ G : ℕ → ℂ, ∀ k, G k = ∑ j ∈ range k, χ j := ⟨_, fun _ => rfl⟩
  have hGle : ∀ k, ‖G k‖ ≤ q := fun k => by rw [hG]; exact norm_sum_char_le χ hχ k
  have hGs : ∀ k, G (k + 1) = G k + χ k := fun k => by rw [hG, hG, sum_range_succ]
  obtain ⟨a, ha⟩ : ∃ a : ℕ → ℂ, ∀ i, a i = G (i + 2) * ((dd i : ℝ) : ℂ) := ⟨_, fun _ => rfl⟩
  -- Abel summation identity
  have habel : ∀ N : ℕ, ∑ n ∈ Icc 1 (N + 1), χ n / n
      = G (N + 2) / ((N : ℂ) + 1) + ∑ i ∈ range N, a i := by
    intro N
    induction N with
    | zero => simp [hG, sum_range_succ, char_apply_zero_eq_zero χ hχ]
    | succ N ih =>
      rw [sum_Icc_succ_top (by omega), ih, sum_range_succ,
        show N + 1 + 1 = N + 2 from rfl, show N + 1 + 2 = N + 2 + 1 from rfl, hGs (N + 2), ha N]
      unfold dd
      push_cast
      ring
  -- summability and tail bounds
  have hnorm_a : ∀ i, ‖a i‖ ≤ q * dd i := by
    intro i
    rw [ha i, norm_mul, Complex.norm_real, Real.norm_of_nonneg (dd_nonneg i)]
    exact mul_le_mul_of_nonneg_right (hGle _) (dd_nonneg i)
  have hsum_dd : Summable dd := by simpa using (hasSum_dd 0).summable
  have hsum_a : Summable a := Summable.of_norm_bounded (hsum_dd.mul_left (q : ℝ)) hnorm_a
  have htail : ∀ M : ℕ, ‖∑' i, a (i + M)‖ ≤ q / ((M : ℝ) + 1) := by
    intro M
    have h := (hasSum_dd M).mul_left (q : ℝ)
    rw [mul_one_div] at h
    exact tsum_of_norm_bounded h fun i => hnorm_a (i + M)
  refine ⟨∑' i, a i, fun y hy => ?_⟩
  obtain ⟨N, hN⟩ : ∃ N, ⌊y⌋₊ = N + 1 :=
    ⟨⌊y⌋₊ - 1, by have := (Nat.one_le_floor_iff y).mpr hy; omega⟩
  have hy' : y < (N : ℝ) + 2 := by
    have := Nat.lt_floor_add_one y
    rw [hN] at this
    push_cast at this
    linarith
  rw [hN, habel N, ← hsum_a.sum_add_tsum_nat_add (N + 1), sum_range_succ]
  have hkey : G (N + 2) / ((N : ℂ) + 1) + ∑ i ∈ range N, a i
      - (∑ i ∈ range N, a i + a N + ∑' i, a (i + (N + 1)))
      = G (N + 2) / ((N : ℂ) + 2) - ∑' i, a (i + (N + 1)) := by
    rw [ha N]
    unfold dd
    push_cast
    ring
  rw [hkey]
  have hN2 : ‖G (N + 2) / ((N : ℂ) + 2)‖ ≤ q / ((N : ℝ) + 2) := by
    rw [norm_div]
    have e : ((N : ℂ) + 2) = ((N + 2 : ℕ) : ℂ) := by simp
    have : ‖(N : ℂ) + 2‖ = (N : ℝ) + 2 := by rw [e, Complex.norm_natCast]; simp
    rw [this]
    exact div_le_div_of_nonneg_right (hGle _) (by positivity)
  have hT := htail (N + 1)
  push_cast at hT
  calc ‖G (N + 2) / ((N : ℂ) + 2) - ∑' i, a (i + (N + 1))‖
      ≤ ‖G (N + 2) / ((N : ℂ) + 2)‖ + ‖∑' i, a (i + (N + 1))‖ := norm_sub_le _ _
    _ ≤ q / ((N : ℝ) + 2) + q / ((N : ℝ) + 1 + 1) := add_le_add hN2 hT
    _ = 2 * q / ((N : ℝ) + 2) := by ring
    _ ≤ 2 * q / y := div_le_div_of_nonneg_left (by positivity) (by linarith) hy'.le

/-- The weights `log n / n`. -/
private noncomputable def gg (n : ℕ) : ℝ := Real.log n / n

private lemma gg_nonneg (n : ℕ) : 0 ≤ gg n :=
  div_nonneg (Real.log_natCast_nonneg n) (Nat.cast_nonneg n)

private lemma gg_le_one (n : ℕ) : gg n ≤ 1 := by
  unfold gg
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    rw [div_le_one hn']
    linarith [Real.log_le_sub_one_of_pos hn']

private lemma gg_succ_le (n : ℕ) (hn : 3 ≤ n) : gg (n + 1) ≤ gg n := by
  have h3 : rexp 1 ≤ 3 := Real.exp_one_lt_d9.le.trans (by norm_num)
  have hn' : rexp 1 ≤ (n : ℝ) := h3.trans (by exact_mod_cast hn)
  have hn1 : rexp 1 ≤ ((n + 1 : ℕ) : ℝ) := by push_cast; linarith
  have hle : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by push_cast; linarith
  have h := Real.log_div_self_antitoneOn (Set.mem_Ici.mpr hn') (Set.mem_Ici.mpr hn1) hle
  exact h

private lemma abs_gg_sub_le (n : ℕ) : |gg n - gg (n + 1)| ≤ 1 := by
  rw [abs_le]
  constructor <;> linarith [gg_nonneg n, gg_le_one n, gg_nonneg (n + 1), gg_le_one (n + 1)]

/-- Total variation of `log n / n` is bounded. -/
private lemma sum_abs_gg_sub_le (N : ℕ) :
    ∑ n ∈ range N, |gg n - gg (n + 1)| ≤ 4 - gg N := by
  induction N with
  | zero => norm_num [gg]
  | succ N ih =>
    rw [sum_range_succ]
    rcases lt_or_ge N 3 with hN | hN
    · have h1 : ∑ n ∈ range N, |gg n - gg (n + 1)| ≤ N := by
        calc _ ≤ ∑ n ∈ range N, (1 : ℝ) := sum_le_sum fun n _ => abs_gg_sub_le n
          _ = N := by simp
      have h2 : (N : ℝ) ≤ 2 := by exact_mod_cast (show N ≤ 2 by omega)
      linarith [abs_gg_sub_le N, gg_le_one (N + 1)]
    · rw [abs_of_nonneg (sub_nonneg.mpr (gg_succ_le N hN))]
      linarith

/-- `∑_{n ≤ N} χ(n) log n / n` is bounded. -/
theorem exists_bound_sum_char_log_div (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    ∃ C : ℝ, ∀ N : ℕ, ‖∑ n ∈ Icc 1 N, χ n * (log n / n : ℝ)‖ ≤ C := by
  obtain ⟨G, hG⟩ : ∃ G : ℕ → ℂ, ∀ k, G k = ∑ j ∈ range k, χ j := ⟨_, fun _ => rfl⟩
  have hGle : ∀ k, ‖G k‖ ≤ q := fun k => by rw [hG]; exact norm_sum_char_le χ hχ k
  have hGs : ∀ k : ℕ, χ k = G (k + 1) - G k := fun k => by rw [hG, hG, sum_range_succ]; ring
  have hG0 : G 0 = 0 := by rw [hG]; simp
  refine ⟨5 * q, fun N => ?_⟩
  show ‖∑ n ∈ Icc 1 N, χ n * ((gg n : ℝ) : ℂ)‖ ≤ 5 * q
  have hIcc : ∑ n ∈ Icc 1 N, χ n * ((gg n : ℝ) : ℂ)
      = ∑ n ∈ range (N + 1), χ n * ((gg n : ℝ) : ℂ) := by
    rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot (show 0 < N + 1 by omega), zero_add,
      Ico_add_one_right_eq_Icc]
    simp [gg]
  have hsum : ∑ n ∈ range (N + 1), χ n * ((gg n : ℝ) : ℂ)
      = ∑ n ∈ range (N + 1), (G (n + 1) - G n) * ((gg n : ℝ) : ℂ) :=
    sum_congr rfl fun n _ => by rw [hGs n]
  have habel := sum_mul_eq_abel G (fun n => ((gg n : ℝ) : ℂ)) N
  rw [hG0, zero_mul, sub_zero] at habel
  rw [hIcc, hsum, habel]
  have h1 : ‖G (N + 1) * ((gg N : ℝ) : ℂ)‖ ≤ q * 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (gg_nonneg N)]
    exact mul_le_mul (hGle _) (gg_le_one N) (gg_nonneg N) (Nat.cast_nonneg q)
  have h2 : ‖∑ n ∈ range N, G (n + 1) * (((gg n : ℝ) : ℂ) - ((gg (n + 1) : ℝ) : ℂ))‖
      ≤ ∑ n ∈ range N, q * |gg n - gg (n + 1)| := by
    refine (norm_sum_le _ _).trans (sum_le_sum fun n _ => ?_)
    rw [norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hGle _) (abs_nonneg _)
  calc ‖G (N + 1) * ((gg N : ℝ) : ℂ)
        + ∑ n ∈ range N, G (n + 1) * (((gg n : ℝ) : ℂ) - ((gg (n + 1) : ℝ) : ℂ))‖
      ≤ ‖G (N + 1) * ((gg N : ℝ) : ℂ)‖
        + ‖∑ n ∈ range N, G (n + 1) * (((gg n : ℝ) : ℂ) - ((gg (n + 1) : ℝ) : ℂ))‖ :=
      norm_add_le _ _
    _ ≤ q * 1 + ∑ n ∈ range N, q * |gg n - gg (n + 1)| := add_le_add h1 h2
    _ = q * (1 + ∑ n ∈ range N, |gg n - gg (n + 1)|) := by rw [← mul_sum]; ring
    _ ≤ q * (1 + 4) := by
      gcongr
      linarith [sum_abs_gg_sub_le N, gg_nonneg N]
    _ = 5 * q := by ring

end Erdos727
