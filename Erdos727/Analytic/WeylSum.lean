import Mathlib

/-!
# Exponential sums with quadratic phases (Section 8)

We write `e x = exp(2πix)` and `dist₁ x` for the distance from `x` to the nearest integer.

* Geometric sums: `‖∑_{z<N} e(αz + β)‖ ≤ 1 / (2 dist₁ α)` when `α ∉ ℤ`, and `≤ N` always.
* Complete residue sums: `∑_{b<q} min(N, 1/(2 dist₁(b/q))) ≤ 2N + 2q (1 + log q)`.
* **Weyl's inequality** for a quadratic phase with rational leading coefficient `a/q`, `q` odd and
  `gcd(a, q) = 1`: squaring and differencing,
  `‖∑_{z<N} e(a(z₀+z)²/q + θ(z₀+z) + γ)‖² ≤ (2N/q + 1) (2N + 2q (1 + log q))`.
  This is the shape of (8.1) used in Section 9: `‖S‖ ≪ N/√q + √(q log q)` up to the
  harmless cross term.
-/

namespace Erdos727

open Finset Real

/-- `e(x) = exp(2π i x)`. -/
noncomputable def e (x : ℝ) : ℂ := Complex.exp (2 * π * Complex.I * x)

theorem e_add (x y : ℝ) : e (x + y) = e x * e y := by
  unfold e
  push_cast
  rw [mul_add, Complex.exp_add]

theorem e_zero : e 0 = 1 := by
  simp [e]

theorem e_int (n : ℤ) : e n = 1 := by
  unfold e
  rw [show 2 * (π : ℂ) * Complex.I * ((n : ℝ) : ℂ) = (n : ℂ) * (2 * π * Complex.I) by
    push_cast; ring]
  exact Complex.exp_int_mul_two_pi_mul_I n

theorem e_add_int (x : ℝ) (n : ℤ) : e (x + n) = e x := by
  rw [e_add, e_int, mul_one]

theorem norm_e (x : ℝ) : ‖e x‖ = 1 := by
  unfold e
  rw [show 2 * (π : ℂ) * Complex.I * (x : ℂ) = ((2 * π * x : ℝ) : ℂ) * Complex.I by
    push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

theorem e_neg (x : ℝ) : e (-x) = (starRingEnd ℂ) (e x) := by
  unfold e
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  push_cast
  ring

theorem e_nat_mul (x : ℝ) (n : ℕ) : e (x * n) = e x ^ n := by
  unfold e
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- `‖e α - 1‖ = 2 |sin (π α)|`. -/
theorem norm_e_sub_one (x : ℝ) : ‖e x - 1‖ = 2 * |sin (π * x)| := by
  unfold e
  rw [show 2 * (π : ℂ) * Complex.I * (x : ℂ) = Complex.I * ((2 * π * x : ℝ) : ℂ) by
    push_cast; ring, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, abs_mul,
    abs_two]
  congr 2
  ring_nf

/-- Distance to the nearest integer. -/
noncomputable def dist₁ (x : ℝ) : ℝ := |x - round x|

theorem dist₁_nonneg (x : ℝ) : 0 ≤ dist₁ x := by
  exact abs_nonneg _

theorem dist₁_le_half (x : ℝ) : dist₁ x ≤ 1 / 2 := by
  exact abs_sub_round x

theorem dist₁_add_int (x : ℝ) (n : ℤ) : dist₁ (x + n) = dist₁ x := by
  unfold dist₁
  rw [round_add_intCast]
  push_cast
  ring_nf

theorem dist₁_neg_le (x : ℝ) : dist₁ (-x) ≤ dist₁ x := by
  unfold dist₁
  calc |-x - round (-x)| ≤ |-x - ((-round x : ℤ) : ℝ)| := round_le _ _
    _ = |x - round x| := by
      push_cast
      rw [← abs_neg]
      congr 1
      ring

theorem dist₁_neg (x : ℝ) : dist₁ (-x) = dist₁ x := by
  refine le_antisymm (dist₁_neg_le x) ?_
  simpa using dist₁_neg_le (-x)

theorem dist₁_eq_zero_iff {x : ℝ} : dist₁ x = 0 ↔ ∃ n : ℤ, x = n := by
  constructor
  · intro h
    exact ⟨round x, by simpa [dist₁, abs_eq_zero, sub_eq_zero] using h⟩
  · rintro ⟨n, rfl⟩
    simp [dist₁, round_intCast]

theorem dist₁_le_abs (x : ℝ) : dist₁ x ≤ |x| := by
  unfold dist₁
  calc |x - round x| ≤ |x - ((0 : ℤ) : ℝ)| := round_le x 0
    _ = |x| := by simp

/-- A lower bound for `dist₁` in terms of the distances to `0` and `1`. -/
theorem min_le_dist₁ (x : ℝ) : min x (1 - x) ≤ dist₁ x := by
  unfold dist₁
  rcases le_or_gt (round x) 0 with h | h
  · have h' : ((round x : ℤ) : ℝ) ≤ 0 := by exact_mod_cast h
    calc min x (1 - x) ≤ x := min_le_left _ _
      _ ≤ x - round x := by linarith
      _ ≤ |x - round x| := le_abs_self _
  · have h' : (1 : ℝ) ≤ ((round x : ℤ) : ℝ) := by exact_mod_cast h
    calc min x (1 - x) ≤ 1 - x := min_le_right _ _
      _ ≤ -(x - round x) := by linarith
      _ ≤ |x - round x| := neg_le_abs _

/-- `|sin (π x)| ≥ 2 dist₁ x`. -/
theorem two_mul_dist₁_le_abs_sin (x : ℝ) : 2 * dist₁ x ≤ |sin (π * x)| := by
  have hx : x = (x - round x) + (round x : ℤ) := by ring
  have h1 : sin (π * x) = (-1) ^ (round x) * sin (π * (x - round x)) := by
    conv_lhs => rw [hx]
    rw [mul_add, mul_comm π ((round x : ℤ) : ℝ), Real.sin_add_int_mul_pi]
  rw [h1, abs_mul, abs_neg_one_zpow, one_mul]
  have hd : |x - round x| ≤ 1 / 2 := abs_sub_round x
  have hπ : |π * (x - round x)| ≤ π / 2 := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_pos]
  have := Real.mul_abs_le_abs_sin hπ
  rw [abs_mul, abs_of_pos Real.pi_pos] at this
  unfold dist₁
  calc 2 * |x - round x| = 2 / π * (π * |x - round x|) := by field_simp
    _ ≤ _ := this

/-- `‖e x - 1‖ ≥ 4 dist₁ x`. -/
theorem four_mul_dist₁_le_norm_e_sub_one (x : ℝ) : 4 * dist₁ x ≤ ‖e x - 1‖ := by
  rw [norm_e_sub_one]
  linarith [two_mul_dist₁_le_abs_sin x]

/-- For an integer `c` not divisible by `q > 0`, `dist₁ (c / q) ≥ 1 / q`. -/
theorem inv_le_dist₁_div {q : ℕ} (hq : 0 < q) {c : ℤ} (hc : ¬ (q : ℤ) ∣ c) :
    1 / (q : ℝ) ≤ dist₁ ((c : ℝ) / q) := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  set r := round ((c : ℝ) / q) with hr
  have hne : c - q * r ≠ 0 := by
    intro h
    apply hc
    exact ⟨r, by linarith⟩
  have h1 : (1 : ℝ) ≤ |((c - q * r : ℤ) : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hne
  have h2 : (c : ℝ) / q - r = ((c - q * r : ℤ) : ℝ) / q := by
    push_cast
    field_simp
  unfold dist₁
  rw [← hr, h2, abs_div, abs_of_pos hq']
  gcongr

/-- The trivial bound. -/
theorem norm_sum_e_le (α β : ℝ) (N : ℕ) : ‖∑ z ∈ range N, e (α * z + β)‖ ≤ N := by
  calc ‖∑ z ∈ range N, e (α * z + β)‖ ≤ ∑ z ∈ range N, ‖e (α * z + β)‖ := norm_sum_le _ _
    _ = N := by simp [norm_e]

/-- The geometric-sum bound `‖∑_{z<N} e(αz + β)‖ ≤ 1 / (2 dist₁ α)` for `α ∉ ℤ`. -/
theorem norm_sum_e_le_inv_dist₁ {α : ℝ} (hα : dist₁ α ≠ 0) (β : ℝ) (N : ℕ) :
    ‖∑ z ∈ range N, e (α * z + β)‖ ≤ 1 / (2 * dist₁ α) := by
  have hd : 0 < dist₁ α := lt_of_le_of_ne (dist₁_nonneg α) (Ne.symm hα)
  have hω : 0 < ‖e α - 1‖ := by linarith [four_mul_dist₁_le_norm_e_sub_one α]
  have hω1 : e α ≠ 1 := by
    intro h
    rw [h, sub_self, norm_zero] at hω
    exact lt_irrefl _ hω
  have hsum : ∑ z ∈ range N, e (α * z + β) = e β * ∑ z ∈ range N, (e α) ^ z := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [e_add, e_nat_mul, mul_comm]
  rw [hsum, norm_mul, norm_e, one_mul, geom_sum_eq hω1, norm_div]
  have hnum : ‖e α ^ N - 1‖ ≤ 2 := by
    calc ‖e α ^ N - 1‖ ≤ ‖e α ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, norm_e, one_pow, norm_one]; norm_num
  calc ‖e α ^ N - 1‖ / ‖e α - 1‖ ≤ 2 / (4 * dist₁ α) := by
        gcongr
        · exact four_mul_dist₁_le_norm_e_sub_one α
    _ = 1 / (2 * dist₁ α) := by field_simp; ring

/-- The bound `min N (1 / (2 dist₁ α))`, with the convention that the second entry is `N`
when `α ∈ ℤ`. -/
noncomputable def geomBound (N : ℕ) (α : ℝ) : ℝ :=
  if dist₁ α = 0 then N else min (N : ℝ) (1 / (2 * dist₁ α))

theorem norm_sum_e_le_geomBound (α β : ℝ) (N : ℕ) :
    ‖∑ z ∈ range N, e (α * z + β)‖ ≤ geomBound N α := by
  unfold geomBound
  split_ifs with h
  · exact norm_sum_e_le α β N
  · exact le_min (norm_sum_e_le α β N) (norm_sum_e_le_inv_dist₁ h β N)

theorem geomBound_le (N : ℕ) (α : ℝ) : geomBound N α ≤ N := by
  unfold geomBound
  split_ifs
  · exact le_rfl
  · exact min_le_left _ _

theorem geomBound_nonneg (N : ℕ) (α : ℝ) : 0 ≤ geomBound N α := by
  unfold geomBound
  split_ifs
  · exact Nat.cast_nonneg _
  · exact le_min (Nat.cast_nonneg _) (by
      have := dist₁_nonneg α
      positivity)

theorem geomBound_mono {N M : ℕ} (h : N ≤ M) (α : ℝ) : geomBound N α ≤ geomBound M α := by
  unfold geomBound
  have h' : (N : ℝ) ≤ M := by exact_mod_cast h
  split_ifs
  · exact h'
  · exact min_le_min_right _ h'

/-- If `dist₁ α ≥ d > 0` then `geomBound N α ≤ 1 / (2 d)`. -/
theorem geomBound_le_of_le {N : ℕ} {α d : ℝ} (hd : 0 < d) (h : d ≤ dist₁ α) :
    geomBound N α ≤ 1 / (2 * d) := by
  unfold geomBound
  have hne : dist₁ α ≠ 0 := by linarith
  rw [ite_eq_right hne]
  calc min (N : ℝ) (1 / (2 * dist₁ α)) ≤ 1 / (2 * dist₁ α) := min_le_right _ _
    _ ≤ 1 / (2 * d) := by gcongr

theorem geomBound_add_int (N : ℕ) (α : ℝ) (n : ℤ) : geomBound N (α + n) = geomBound N α := by
  unfold geomBound
  rw [dist₁_add_int]

theorem geomBound_neg (N : ℕ) (α : ℝ) : geomBound N (-α) = geomBound N α := by
  unfold geomBound
  rw [dist₁_neg]

/-- Rotating the summation index modulo `q`. -/
theorem sum_range_add_mod {q : ℕ} (hq : 0 < q) (F : ℕ → ℝ) (k : ℕ) :
    ∑ b ∈ range q, F ((b + k) % q) = ∑ b ∈ range q, F b := by
  have : NeZero q := ⟨hq.ne'⟩
  rw [Finset.sum_range, Finset.sum_range]
  exact Fintype.sum_equiv (Equiv.addRight (Fin.ofNat q k)) _ _ fun i => by
    simp [Fin.val_add, Nat.add_mod_mod]

/-- For `0 < x < 1`, `geomBound N x ≤ 1/(2x) + 1/(2(1-x))`. -/
theorem geomBound_le_of_mem_Ioo {N : ℕ} {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    geomBound N x ≤ 1 / (2 * x) + 1 / (2 * (1 - x)) := by
  have h1 : 0 < 1 - x := by linarith
  have hd : 0 < min x (1 - x) := lt_min hx0 h1
  have hA : 0 ≤ 1 / (2 * x) := div_nonneg zero_le_one (by linarith)
  have hB : 0 ≤ 1 / (2 * (1 - x)) := div_nonneg zero_le_one (by linarith)
  calc geomBound N x ≤ 1 / (2 * min x (1 - x)) := geomBound_le_of_le hd (min_le_dist₁ x)
    _ ≤ 1 / (2 * x) + 1 / (2 * (1 - x)) := by
      rcases min_choice x (1 - x) with h | h <;> rw [h] <;> linarith

/-- The auxiliary bound `N` for `m = 0` and `q / (2m)` otherwise. -/
noncomputable def harmTerm (N q m : ℕ) : ℝ := if m = 0 then N else (q : ℝ) / (2 * m)

theorem harmTerm_nonneg (N q m : ℕ) : 0 ≤ harmTerm N q m := by
  unfold harmTerm
  split_ifs <;> positivity

/-- The pointwise bound for `m < q` and `0 ≤ u < 1`. -/
theorem geomBound_div_le (N q : ℕ) (hq : 0 < q) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) {m : ℕ}
    (hm : m < q) :
    geomBound N (((m : ℝ) + u) / q) ≤ harmTerm N q m + harmTerm N q (q - 1 - m) := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  by_cases h0 : m = 0
  · have : harmTerm N q m = N := by simp [harmTerm, h0]
    linarith [geomBound_le N (((m : ℝ) + u) / q), harmTerm_nonneg N q (q - 1 - m)]
  by_cases h1 : q - 1 - m = 0
  · have : harmTerm N q (q - 1 - m) = N := by simp [harmTerm, h1]
    linarith [geomBound_le N (((m : ℝ) + u) / q), harmTerm_nonneg N q m]
  have hm1 : 1 ≤ m := Nat.pos_of_ne_zero h0
  have hm2 : m + 1 < q := by omega
  have hmr : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  have hmq : (m : ℝ) + 1 < q := by exact_mod_cast hm2
  have hcast : ((q - 1 - m : ℕ) : ℝ) = q - 1 - m := by
    rw [show q - 1 - m = q - (m + 1) by omega, Nat.cast_sub hm2.le]
    push_cast
    ring
  have hH1 : harmTerm N q m = q / (2 * m) := by simp [harmTerm, h0]
  have hH2 : harmTerm N q (q - 1 - m) = q / (2 * ((q : ℝ) - 1 - m)) := by
    rw [harmTerm, ite_eq_right h1, hcast]
  rw [hH1, hH2]
  set x := ((m : ℝ) + u) / q with hx
  have hqx : (q : ℝ) * x = m + u := by rw [hx]; field_simp
  have hx0 : 0 < x := div_pos (by linarith) hq'
  have hx1 : x < 1 := by rw [hx, div_lt_one hq']; linarith
  have h1x : 0 < 1 - x := by linarith
  calc geomBound N x ≤ 1 / (2 * x) + 1 / (2 * (1 - x)) := geomBound_le_of_mem_Ioo hx0 hx1
    _ ≤ q / (2 * m) + q / (2 * ((q : ℝ) - 1 - m)) := by
      gcongr ?_ + ?_
      · rw [le_div_iff₀ (by positivity), div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        linarith
      · rw [le_div_iff₀ (by linarith), div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        linarith

/-- The harmonic-sum bound `∑_{m<q} harmTerm N q m ≤ N + (q/2)(1 + log q)`. -/
theorem sum_harmTerm_le (N q : ℕ) (hq : 0 < q) :
    ∑ m ∈ range q, harmTerm N q m ≤ N + (q : ℝ) / 2 * (1 + log q) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hq.ne'
  rw [Finset.sum_range_succ']
  have h0 : harmTerm N (n + 1) 0 = N := by simp [harmTerm]
  have hs : ∑ i ∈ range n, harmTerm N (n + 1) (i + 1)
      = ((n + 1 : ℕ) : ℝ) / 2 * (harmonic n : ℝ) := by
    simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [harmTerm, Nat.succ_ne_zero, ite_false]
    rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv, mul_assoc]
  rw [h0, hs]
  have hlog : log (n : ℝ) ≤ log ((n + 1 : ℕ) : ℝ) := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp
    · exact Real.log_le_log (by exact_mod_cast hn) (by push_cast; linarith)
  have hh := harmonic_le_one_add_log n
  have hq' : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) / 2 := by positivity
  have h2 := mul_le_mul_of_nonneg_left hh hq'
  have h3 := mul_le_mul_of_nonneg_left (add_le_add_left hlog 1) hq'
  linarith

/-- Complete residue sums: `∑_{b<q} geomBound N (b/q + θ) ≤ 2N + 2q (1 + log q)`, uniformly in
the real shift `θ`.  (The points `b/q + θ` are `1/q`-spaced modulo `1`; at most two of them lie
within `1/q` of an integer, and the rest contribute a harmonic sum.) -/
theorem sum_geomBound_le (q : ℕ) (hq : 0 < q) (N : ℕ) (θ : ℝ) :
    ∑ b ∈ range q, geomBound N ((b : ℝ) / q + θ) ≤ 2 * N + 2 * q * (1 + log q) := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hqZ : (0 : ℤ) < q := by exact_mod_cast hq
  -- decompose `q θ = c + u` with `c = ⌊qθ⌋`, `u = fract (qθ)`
  set u : ℝ := Int.fract ((q : ℝ) * θ) with hu
  set c : ℤ := ⌊(q : ℝ) * θ⌋ with hc
  have hu0 : 0 ≤ u := Int.fract_nonneg _
  have hu1 : u < 1 := Int.fract_lt_one _
  have hθq : θ * q = c + u := by rw [hu, hc, Int.floor_add_fract, mul_comm]
  set k : ℕ := (c % q).toNat with hk
  have hk' : (k : ℤ) = c % q := Int.toNat_of_nonneg (Int.emod_nonneg _ hqZ.ne')
  have hc' : (c : ℝ) = q * ((c / q : ℤ) : ℝ) + k := by
    have h := Int.mul_ediv_add_emod c q
    rw [← hk'] at h
    exact_mod_cast h.symm
  -- each term is a `geomBound` at `((b + k) % q + u) / q`
  have hterm : ∀ b ∈ range q, geomBound N ((b : ℝ) / q + θ)
      = geomBound N (((((b + k) % q : ℕ) : ℝ) + u) / q) := by
    intro b _
    have h2 : (b : ℝ) + k = ((b + k) % q : ℕ) + q * (((b + k) / q : ℕ) : ℝ) := by
      have := Nat.mod_add_div (b + k) q
      exact_mod_cast this.symm
    rw [← geomBound_add_int N (((((b + k) % q : ℕ) : ℝ) + u) / q) ((((b + k) / q : ℕ) : ℤ) + c / q)]
    congr 1
    apply mul_right_cancel₀ hq'.ne'
    rw [add_mul, add_mul, div_mul_cancel₀ _ hq'.ne', div_mul_cancel₀ _ hq'.ne', hθq,
      Int.cast_add, Int.cast_natCast]
    linear_combination hc' + h2
  calc ∑ b ∈ range q, geomBound N ((b : ℝ) / q + θ)
      = ∑ b ∈ range q, geomBound N (((((b + k) % q : ℕ) : ℝ) + u) / q) :=
        Finset.sum_congr rfl hterm
    _ = ∑ m ∈ range q, geomBound N ((((m : ℕ) : ℝ) + u) / q) :=
        sum_range_add_mod hq (fun m => geomBound N ((((m : ℕ) : ℝ) + u) / q)) k
    _ ≤ ∑ m ∈ range q, (harmTerm N q m + harmTerm N q (q - 1 - m)) :=
        Finset.sum_le_sum fun m hm => geomBound_div_le N q hq hu0 hu1 (Finset.mem_range.mp hm)
    _ = 2 * ∑ m ∈ range q, harmTerm N q m := by
        rw [Finset.sum_add_distrib, Finset.sum_range_reflect (harmTerm N q) q]; ring
    _ ≤ 2 * (N + (q : ℝ) / 2 * (1 + log q)) := by
        gcongr; exact sum_harmTerm_le N q hq
    _ ≤ 2 * N + 2 * q * (1 + log q) := by
        have := Real.log_natCast_nonneg q
        nlinarith

/-- The quadratic phase `a x² / q + θ x + γ`. -/
noncomputable def quadPhase (a : ℤ) (q : ℕ) (θ γ x : ℝ) : ℝ := (a : ℝ) / q * x ^ 2 + θ * x + γ

/-- The inner sum after differencing: for an integer shift `h`,
`∑_{z ∈ Ico lo hi} e(P(z₀+z) - P(z₀+z+h))` is a geometric sum in `z` with ratio `e(-2ah/q)`,
hence bounded by `geomBound N (2ah/q)` when `hi ≤ N`. -/
theorem norm_sum_diff_le (a : ℤ) (q : ℕ) (θ γ : ℝ) (z₀ h : ℤ) {N lo hi : ℕ} (hhi : hi ≤ N) :
    ‖∑ z ∈ Ico lo hi, e (quadPhase a q θ γ ((z₀ : ℝ) + z)
        - quadPhase a q θ γ ((z₀ : ℝ) + z + h))‖
      ≤ geomBound N (2 * a * h / q) := by
  have hsum : ∑ z ∈ Ico lo hi, e (quadPhase a q θ γ ((z₀ : ℝ) + z)
        - quadPhase a q θ γ ((z₀ : ℝ) + z + h))
      = ∑ j ∈ range (hi - lo), e (-(2 * a * h / q) * j
          + (-(2 * a * h / q) * (z₀ + lo) - a / q * h ^ 2 - θ * h)) := by
    rw [Finset.sum_Ico_eq_sum_range]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    unfold quadPhase
    push_cast
    ring
  rw [hsum]
  calc ‖∑ j ∈ range (hi - lo), e (-(2 * a * h / q) * j
          + (-(2 * a * h / q) * (z₀ + lo) - a / q * h ^ 2 - θ * h))‖
      ≤ geomBound (hi - lo) (-(2 * a * h / q)) := norm_sum_e_le_geomBound _ _ _
    _ ≤ geomBound N (-(2 * a * h / q)) := geomBound_mono (by omega) _
    _ = geomBound N (2 * a * h / q) := geomBound_neg _ _

/-- A nonnegative `q`-periodic sequence: `∑_{k<L} G k ≤ (L/q + 1) ∑_{b<q} G b`. -/
theorem sum_range_le_of_periodic {q : ℕ} (hq : 0 < q) (G : ℕ → ℝ) (hG : ∀ k, 0 ≤ G k)
    (hper : ∀ k, G (k + q) = G k) (L : ℕ) :
    ∑ k ∈ range L, G k ≤ ((L : ℝ) / q + 1) * ∑ b ∈ range q, G b := by
  have hper' : ∀ t b, G (t * q + b) = G b := by
    intro t
    induction t with
    | zero => intro b; simp
    | succ t ih => intro b; rw [show (t + 1) * q + b = (t * q + b) + q by ring, hper, ih]
  have hblock : ∀ T : ℕ, ∑ k ∈ range (T * q), G k = T * ∑ b ∈ range q, G b := by
    intro T
    induction T with
    | zero => simp
    | succ T ih =>
      rw [add_mul, one_mul, Finset.sum_range_add, ih]
      push_cast
      rw [add_mul, one_mul]
      congr 1
      exact Finset.sum_congr rfl fun b _ => hper' T b
  have hS : 0 ≤ ∑ b ∈ range q, G b := Finset.sum_nonneg fun b _ => hG b
  have hLT : L ≤ (L / q + 1) * q := by
    have := Nat.lt_div_mul_add (a := L) hq
    rw [add_mul, one_mul]
    exact this.le
  have hT : (((L / q + 1 : ℕ)) : ℝ) ≤ (L : ℝ) / q + 1 := by
    have := (Nat.cast_div_le : ((L / q : ℕ) : ℝ) ≤ (L : ℝ) / q)
    push_cast
    linarith
  calc ∑ k ∈ range L, G k ≤ ∑ k ∈ range ((L / q + 1) * q), G k :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hLT) fun k _ _ => hG k
    _ = ((L / q + 1 : ℕ) : ℝ) * ∑ b ∈ range q, G b := hblock _
    _ ≤ ((L : ℝ) / q + 1) * ∑ b ∈ range q, G b := mul_le_mul_of_nonneg_right hT hS

/-- Summing a function of `(b : ZMod q)` over `b < q` is summing over `ZMod q`. -/
theorem sum_range_zmod {q : ℕ} [NeZero q] (g : ZMod q → ℝ) :
    ∑ b ∈ range q, g (b : ZMod q) = ∑ x : ZMod q, g x := by
  refine Finset.sum_nbij' (fun b => (b : ZMod q)) (fun x => x.val) (fun _ _ => Finset.mem_univ _)
    (fun x _ => Finset.mem_range.mpr (ZMod.val_lt x)) (fun b hb => ?_) (fun x _ => ?_)
    (fun _ _ => rfl)
  · exact ZMod.val_cast_of_lt (Finset.mem_range.mp hb)
  · exact ZMod.natCast_zmod_val x

/-- For a unit `c` of `ZMod q` and any `d`, `x ↦ c * (x - d)` permutes `ZMod q`. -/
theorem sum_zmod_mul_sub {q : ℕ} [NeZero q] (c u d : ZMod q) (huc : u * c = 1)
    (g : ZMod q → ℝ) :
    ∑ x : ZMod q, g (c * (x - d)) = ∑ x : ZMod q, g x := by
  refine Finset.sum_nbij' (fun x => c * (x - d)) (fun y => u * y + d)
    (fun _ _ => Finset.mem_univ _) (fun _ _ => Finset.mem_univ _) (fun x _ => ?_)
    (fun y _ => ?_) (fun _ _ => rfl)
  · linear_combination (x - d) * huc
  · linear_combination y * huc

/-- **Weyl's inequality for quadratic phases**: for `q` odd, `gcd(a, q) = 1`, any integer `z₀`
and reals `θ, γ`,
`‖∑_{z<N} e(a (z₀+z)² / q + θ (z₀+z) + γ)‖² ≤ (2N/q + 1) (2N + 2q (1 + log q))`. -/
theorem weyl_quadratic {q : ℕ} (hq : 0 < q) (hodd : Odd q) {a : ℤ} (ha : Int.gcd a q = 1)
    (θ γ : ℝ) (z₀ : ℤ) (N : ℕ) :
    ‖∑ z ∈ range N, e ((a : ℝ) / q * ((z₀ : ℝ) + z) ^ 2 + θ * ((z₀ : ℝ) + z) + γ)‖ ^ 2
      ≤ (2 * N / q + 1) * (2 * N + 2 * q * (1 + log q)) := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hlog : 0 ≤ log (q : ℝ) := Real.log_natCast_nonneg q
  have hR : 0 ≤ 2 * (N : ℝ) + 2 * q * (1 + log q) := by
    have : 0 ≤ 2 * (q : ℝ) * (1 + log q) := mul_nonneg (by positivity) (by linarith)
    have : 0 ≤ 2 * (N : ℝ) := by positivity
    linarith
  -- the trivial case `N = 0`
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    have h0 : ‖∑ z ∈ range 0, e ((a : ℝ) / q * ((z₀ : ℝ) + z) ^ 2 + θ * ((z₀ : ℝ) + z) + γ)‖ ^ 2
        = 0 := by simp
    rw [h0]
    exact mul_nonneg (by positivity) hR
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  show ‖∑ z ∈ range (M + 1), e (quadPhase a q θ γ ((z₀ : ℝ) + z))‖ ^ 2 ≤ _
  set S := ∑ z ∈ range (M + 1), e (quadPhase a q θ γ ((z₀ : ℝ) + z)) with hS
  -- Step 1: `‖S‖² = ‖S * conj S‖`
  have h1 : ‖S‖ ^ 2 = ‖S * (starRingEnd ℂ) S‖ := by
    rw [norm_mul, Complex.norm_conj, sq]
  -- Step 2: `S * conj S` as a double sum of `e(P(z₀+z) - P(z₀+z'))`
  have h2 : S * (starRingEnd ℂ) S = ∑ p ∈ range (M + 1) ×ˢ range (M + 1),
      e (quadPhase a q θ γ ((z₀ : ℝ) + p.1) - quadPhase a q θ γ ((z₀ : ℝ) + p.2)) := by
    rw [hS, map_sum, Finset.sum_mul_sum, Finset.sum_product]
    refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun z' _ => ?_
    dsimp only
    rw [sub_eq_add_neg, e_add, e_neg]
  -- Step 3: reindex by the difference `k = z' - z + M ∈ range (2M+1)`
  have h3 : ∑ p ∈ range (M + 1) ×ˢ range (M + 1),
      e (quadPhase a q θ γ ((z₀ : ℝ) + p.1) - quadPhase a q θ γ ((z₀ : ℝ) + p.2))
      = ∑ k ∈ range (2 * M + 1), ∑ z ∈ Ico (M - k) (min (M + 1) (2 * M + 1 - k)),
          e (quadPhase a q θ γ ((z₀ : ℝ) + z)
            - quadPhase a q θ γ ((z₀ : ℝ) + z + (((k : ℤ) - M : ℤ) : ℝ))) := by
    rw [Finset.sum_sigma']
    refine Finset.sum_nbij' (fun p : ℕ × ℕ => (⟨p.2 + M - p.1, p.1⟩ : (_ : ℕ) × ℕ))
      (fun x : (_ : ℕ) × ℕ => (x.2, x.2 + x.1 - M)) ?_ ?_ ?_ ?_ ?_
    · rintro ⟨z, z'⟩ hp
      simp only [Finset.mem_product, Finset.mem_range] at hp
      simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_Ico]
      omega
    · rintro ⟨k, z⟩ hx
      simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_Ico] at hx
      simp only [Finset.mem_product, Finset.mem_range]
      omega
    · rintro ⟨z, z'⟩ hp
      simp only [Finset.mem_product, Finset.mem_range] at hp
      simp only [Prod.mk.injEq, true_and]
      omega
    · rintro ⟨k, z⟩ hx
      simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_Ico] at hx
      simp only [Sigma.mk.injEq, heq_eq_eq, and_true]
      omega
    · rintro ⟨z, z'⟩ hp
      simp only [Finset.mem_product, Finset.mem_range] at hp
      dsimp only
      congr 1
      unfold quadPhase
      push_cast [Nat.cast_sub (by omega : z ≤ z' + M)]
      ring
  -- Step 4: each inner sum is a geometric sum
  have h4 : ∀ k ∈ range (2 * M + 1),
      ‖∑ z ∈ Ico (M - k) (min (M + 1) (2 * M + 1 - k)),
          e (quadPhase a q θ γ ((z₀ : ℝ) + z)
            - quadPhase a q θ γ ((z₀ : ℝ) + z + (((k : ℤ) - M : ℤ) : ℝ)))‖
        ≤ geomBound (M + 1) (2 * a * (((k : ℤ) - M : ℤ) : ℝ) / q) := fun k _ =>
    norm_sum_diff_le a q θ γ z₀ ((k : ℤ) - M) (min_le_left _ _)
  -- `G k := geomBound (M+1) (2a(k - M)/q)` is `q`-periodic
  set G : ℕ → ℝ := fun k => geomBound (M + 1) (2 * a * (((k : ℤ) - M : ℤ) : ℝ) / q) with hG
  have hGnn : ∀ k, 0 ≤ G k := fun k => geomBound_nonneg _ _
  have hGper : ∀ k, G (k + q) = G k := by
    intro k
    simp only [hG]
    rw [← geomBound_add_int (M + 1) (2 * a * (((k : ℤ) - M : ℤ) : ℝ) / q) (2 * a)]
    congr 1
    push_cast
    field_simp
    ring
  -- Step 5: `2a` is a unit mod `q`
  have : NeZero q := ⟨hq.ne'⟩
  have hunit : ∃ u : ZMod q, u * (2 * (a : ZMod q)) = 1 := by
    have hcop : IsCoprime (2 * a) (q : ℤ) := by
      refine IsCoprime.mul_left ?_ (Int.isCoprime_iff_gcd_eq_one.mpr ha)
      obtain ⟨m, hm⟩ := hodd
      exact ⟨-m, 1, by rw [hm]; push_cast; ring⟩
    obtain ⟨u, v, huv⟩ := hcop
    refine ⟨(u : ZMod q), ?_⟩
    have := congrArg (Int.cast : ℤ → ZMod q) huv
    push_cast at this
    rwa [ZMod.natCast_self, mul_zero, add_zero] at this
  -- reduce `G b` modulo `q`
  have hGres : ∀ b : ℕ, G b = geomBound (M + 1)
      ((((2 * (a : ZMod q)) * ((b : ZMod q) - (M : ZMod q))).val : ℝ) / q) := by
    intro b
    simp only [hG]
    obtain ⟨n, hn⟩ : ∃ n : ℤ, n = 2 * a * ((b : ℤ) - M) := ⟨_, rfl⟩
    have hcast : (2 * (a : ZMod q)) * ((b : ZMod q) - (M : ZMod q)) = (n : ZMod q) := by
      rw [hn]; push_cast; ring
    have hval : (((n : ZMod q).val : ℤ)) = n % q := ZMod.val_intCast n
    have hdecomp : (n : ℝ) = q * ((n / q : ℤ) : ℝ) + ((n : ZMod q).val : ℝ) := by
      have h := Int.mul_ediv_add_emod n q
      rw [← hval] at h
      exact_mod_cast h.symm
    rw [hcast]
    calc geomBound (M + 1) (2 * (a : ℝ) * (((b : ℤ) - M : ℤ) : ℝ) / q)
        = geomBound (M + 1) (((n : ZMod q).val : ℝ) / q + ((n / q : ℤ) : ℝ)) := by
          congr 1
          rw [show 2 * (a : ℝ) * (((b : ℤ) - M : ℤ) : ℝ) = (n : ℝ) by rw [hn]; push_cast; ring,
            hdecomp, add_div, mul_div_cancel_left₀ _ hq'.ne', add_comm]
      _ = geomBound (M + 1) (((n : ZMod q).val : ℝ) / q) := geomBound_add_int _ _ _
  -- Step 6: the complete residue sum
  have h5 : ∑ b ∈ range q, G b ≤ 2 * ((M + 1 : ℕ) : ℝ) + 2 * q * (1 + log q) := by
    obtain ⟨u, hu⟩ := hunit
    calc ∑ b ∈ range q, G b
        = ∑ b ∈ range q, (fun x : ZMod q => geomBound (M + 1) ((x.val : ℝ) / q))
            ((2 * (a : ZMod q)) * ((b : ZMod q) - (M : ZMod q))) :=
          Finset.sum_congr rfl fun b _ => hGres b
      _ = ∑ x : ZMod q, (fun x : ZMod q => geomBound (M + 1) ((x.val : ℝ) / q))
            ((2 * (a : ZMod q)) * (x - (M : ZMod q))) :=
          sum_range_zmod (fun x : ZMod q => (fun x : ZMod q => geomBound (M + 1) ((x.val : ℝ) / q))
            ((2 * (a : ZMod q)) * (x - (M : ZMod q))))
      _ = ∑ x : ZMod q, geomBound (M + 1) ((x.val : ℝ) / q) :=
          sum_zmod_mul_sub (2 * (a : ZMod q)) u (M : ZMod q) hu
            (fun x : ZMod q => geomBound (M + 1) ((x.val : ℝ) / q))
      _ = ∑ b ∈ range q, geomBound (M + 1) ((b : ℝ) / q + 0) := by
          rw [← sum_range_zmod (fun x : ZMod q => geomBound (M + 1) ((x.val : ℝ) / q))]
          refine Finset.sum_congr rfl fun b hb => ?_
          rw [ZMod.val_cast_of_lt (Finset.mem_range.mp hb), add_zero]
      _ ≤ _ := sum_geomBound_le q hq (M + 1) 0
  -- Step 7: assemble
  have hsum := sum_range_le_of_periodic hq G hGnn hGper (2 * M + 1)
  have hT : ((2 * M + 1 : ℕ) : ℝ) / q + 1 ≤ 2 * ((M + 1 : ℕ) : ℝ) / q + 1 := by
    gcongr
    push_cast
    linarith
  calc ‖S‖ ^ 2 = ‖∑ k ∈ range (2 * M + 1), ∑ z ∈ Ico (M - k) (min (M + 1) (2 * M + 1 - k)),
          e (quadPhase a q θ γ ((z₀ : ℝ) + z)
            - quadPhase a q θ γ ((z₀ : ℝ) + z + (((k : ℤ) - M : ℤ) : ℝ)))‖ := by
        rw [h1, h2, h3]
    _ ≤ ∑ k ∈ range (2 * M + 1), G k :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk => h4 k hk)
    _ ≤ (((2 * M + 1 : ℕ) : ℝ) / q + 1) * ∑ b ∈ range q, G b := hsum
    _ ≤ (2 * ((M + 1 : ℕ) : ℝ) / q + 1) * (2 * ((M + 1 : ℕ) : ℝ) + 2 * q * (1 + log q)) :=
        mul_le_mul hT h5 (Finset.sum_nonneg fun b _ => hGnn b) (by positivity)

end Erdos727
