import Erdos727.Ranges

/-!
# Large primes (Section 11)

For a prime `p > X^{1/2+η}` dividing `Lv i v`, write `Lv i v = p m`; then `m ≤ 2 Cb X / p
< 2 Cb X^{1/2-η}`, so `m / p → 0`.  Clearing denominators in `f = α_i L_i² + β_i L_i - j_i`
(`f_eq_L0`, …, `f_eq_L5` in `Polynomial.lean`) gives, for `i ≠ 2`, an integer identity

  `a (F v + j) = w (p m)² + u (p m)`   (`a = slope i`, `u ∈ ℤ`),

so with `w m² = a s + r`, `0 < r < a`: `a (F v - s p²) = r p² + u p m - a j`.  For `p` large
compared with `m`, this shows `F v mod p² = (r p² + u p m - a j) / a`, and level `2` carries
as soon as `2 r > a`.  Reducing `L_i = p m` modulo `a` gives `m ≡ b_i p⁻¹ (mod a)`, so whether
`2 r > a` depends only on the class of `p` modulo `a = slope i`: the *bad classes* are those with
`2 (w (b_i p⁻¹)² mod a) < a`.  Their proportions among the units are `1/6, 0, –, 1/3, 0, 1/3`
for `i = 0, 1, –, 3, 4, 5`; for `i = 2` (`L = t + 1`, `a = 1`) level `2` always carries.

Hence, for large `X`, `badSet X i p` is empty unless `p` lies in a bad class modulo `slope i`,
in which case it is a single residue class mod `p` and has at most `X/p + 1` elements.  Since
every `slope i` divides `210`, Mertens' theorem in progressions modulo `210` (`MertensAP 210`)
gives `∑ 1/p` over the bad primes in `(X^{1/2+η}, 2 Cb X]` as `(5/6) log (1/(1/2+η)) + o(1)
< (5/6) log 2 + o(1) < 0.5776 + o(1)`.

The endpoint terms `+1` are controlled by Chebyshev's bound `π(x) ≤ log 4 · x / log √x + √x`
(`Chebyshev.pi_le_log4_mul_div`), which gives `#(largeR X) = o(X)`.
-/

namespace Erdos727

open Finset Real Filter

/-! ### The level-2 carry criterion -/

/-- The leading coefficients `w_i` with `slope i * f = w_i L_i² + c_i L_i - slope i * shift i`. -/
def wcoef : Fin 6 → ℕ := ![6, 35, 210, 1, 14, 15]

/-- The uniform identity `a_i F v = w_i (Lv i v)² + c_i Lv i v - a_i j_i` (Section 11, (11.2)). -/
theorem slope_mul_F_eq (i : Fin 6) (v : ℕ) :
    (slope i : ℤ) * F v = wcoef i * (Lv i v) ^ 2 + c i * Lv i v - slope i * shift i := by
  unfold F Lv
  fin_cases i <;> simp [slope, icept, c, shift, wcoef, L, f] <;> ring

/-- If `a F = a s p² + N` with `0 ≤ N < a p²` and `a p² ≤ 2 N`, then level `2` carries. -/
theorem carry_of_decomp {p a F : ℕ} {s N : ℤ} (ha : 0 < a)
    (h : (a : ℤ) * F = a * s * (p : ℤ) ^ 2 + N) (_hN0 : 0 ≤ N) (hN1 : N < a * (p : ℤ) ^ 2)
    (hN2 : (a : ℤ) * (p : ℤ) ^ 2 ≤ 2 * N) : p ^ 2 ≤ 2 * (F % p ^ 2) := by
  have ha' : (0 : ℤ) < a := by exact_mod_cast ha
  -- `q := F - s p²` satisfies `a q = N`.
  set q : ℤ := (F : ℤ) - s * (p : ℤ) ^ 2 with hq
  have hqN : (a : ℤ) * q = N := by rw [hq]; linear_combination h
  have hq0 : 0 ≤ q := by
    by_contra hcon
    push Not at hcon
    nlinarith
  have hq1 : q < (p : ℤ) ^ 2 := by
    by_contra hcon
    push Not at hcon
    nlinarith
  have hq2 : (p : ℤ) ^ 2 ≤ 2 * q := by
    by_contra hcon
    push Not at hcon
    nlinarith
  have hmod : ((F % p ^ 2 : ℕ) : ℤ) = q := by
    rw [Int.natCast_mod, Nat.cast_pow]
    have : (F : ℤ) = q + (p : ℤ) ^ 2 * s := by rw [hq]; ring
    rw [this, Int.add_mul_emod_self_left, Int.emod_eq_of_lt hq0 hq1]
  have : ((p ^ 2 : ℕ) : ℤ) ≤ 2 * ((F % p ^ 2 : ℕ) : ℤ) := by
    rw [hmod]; push_cast; exact hq2
  exact_mod_cast this

/-- **Level-2 carry criterion** (`i ≠ 2`): if `a F = w (p m)² + u (p m) - a j` with
`|u| ≤ 41`, `a j ≤ 630`, `p ≥ 100 (m + 1)` and `2 ((w m²) mod a) > a`, then level `2` carries. -/
theorem carry_of_class {p a w j m F : ℕ} {u : ℤ} (ha : 0 < a) (hu : |u| ≤ 41)
    (haj : a * j ≤ 630) (hp : 100 * (m + 1) ≤ p)
    (h : (a : ℤ) * F = w * ((p : ℤ) * m) ^ 2 + u * ((p : ℤ) * m) - a * j)
    (hr : a < 2 * ((w * m ^ 2) % a)) : p ^ 2 ≤ 2 * (F % p ^ 2) := by
  set r : ℕ := (w * m ^ 2) % a with hr_def
  set s : ℕ := (w * m ^ 2) / a with hs_def
  have hdiv : w * m ^ 2 = a * s + r := (Nat.div_add_mod (w * m ^ 2) a).symm
  have hra : r < a := Nat.mod_lt _ ha
  have hdivZ : (w : ℤ) * (m : ℤ) ^ 2 = a * s + r := by exact_mod_cast hdiv
  have hraZ : (r : ℤ) < a := by exact_mod_cast hra
  have hrZ : (a : ℤ) < 2 * r := by exact_mod_cast hr
  have hajZ : (a : ℤ) * j ≤ 630 := by exact_mod_cast haj
  have hpZ : 100 * ((m : ℤ) + 1) ≤ p := by exact_mod_cast hp
  have hm0 : (0 : ℤ) ≤ m := by positivity
  have hu1 : -41 ≤ u := (abs_le.mp hu).1
  have hu2 : u ≤ 41 := (abs_le.mp hu).2
  -- `p² ≥ 100 p m + 100 p`, and `p ≥ 100`.
  have hp100 : (100 : ℤ) ≤ p := by linarith
  have hpp : 100 * (p : ℤ) * m + 100 * p ≤ (p : ℤ) ^ 2 := by nlinarith
  have hpm : (0 : ℤ) ≤ (p : ℤ) * m := by positivity
  refine carry_of_decomp (s := s) (N := r * (p : ℤ) ^ 2 + u * ((p : ℤ) * m) - a * j) ha ?_ ?_ ?_ ?_
  · rw [h]
    linear_combination ((p : ℤ) ^ 2) * hdivZ
  · nlinarith
  · nlinarith
  · nlinarith

/-- **Level-2 carry for `i = 2`**: `F = 210 (p m)² - 29 p m - 2` and level `2` always carries
for `p ≥ 100 (m + 1)`. -/
theorem carry_of_two {p m F : ℕ} (hp : 100 * (m + 1) ≤ p)
    (h : (F : ℤ) = 210 * ((p : ℤ) * m) ^ 2 - 29 * ((p : ℤ) * m) - 2) :
    p ^ 2 ≤ 2 * (F % p ^ 2) := by
  have hpZ : 100 * ((m : ℤ) + 1) ≤ p := by exact_mod_cast hp
  have hm0 : (0 : ℤ) ≤ m := by positivity
  have hp100 : (100 : ℤ) ≤ p := by linarith
  have hpp : 100 * (p : ℤ) * m + 100 * p ≤ (p : ℤ) ^ 2 := by nlinarith
  have hpm : (0 : ℤ) ≤ (p : ℤ) * m := by positivity
  refine carry_of_decomp (a := 1) (s := 210 * (m : ℤ) ^ 2 - 1)
    (N := (p : ℤ) ^ 2 - 29 * ((p : ℤ) * m) - 2) one_pos ?_ ?_ ?_ ?_
  · push_cast; rw [h]; ring
  · nlinarith
  · push_cast; nlinarith
  · push_cast; nlinarith

/-! ### The bad residue classes modulo `210` -/

/-- The bad classes of `p` modulo `210`, for each form `i` (empty for `i = 1, 2, 4`). -/
def badRes : Fin 6 → Finset ℕ :=
  ![{1, 29, 41, 71, 139, 169, 181, 209}, ∅, ∅,
    {1, 23, 29, 37, 41, 47, 71, 103, 107, 139, 163, 169, 173, 181, 187, 209}, ∅,
    {1, 13, 29, 41, 43, 71, 83, 97, 113, 127, 139, 167, 169, 181, 197, 209}]

theorem card_badRes_zero : #(badRes 0) = 8 := by decide
theorem card_badRes_three : #(badRes 3) = 16 := by decide
theorem card_badRes_five : #(badRes 5) = 16 := by decide

theorem badRes_one : badRes 1 = ∅ := rfl
theorem badRes_two : badRes 2 = ∅ := rfl
theorem badRes_four : badRes 4 = ∅ := rfl

/-- `8 + 0 + 0 + 16 + 0 + 16 = 40` bad classes in total. -/
theorem sum_card_badRes : ∑ i : Fin 6, #(badRes i) = 40 := by decide

theorem badRes_subset (i : Fin 6) : ∀ c ∈ badRes i, c < 210 ∧ Nat.Coprime c 210 := by
  fin_cases i <;> decide

set_option maxRecDepth 100000 in
/-- The finite residue check: for `i ≠ 2`, if `pc` is a unit modulo `210` and `mc` satisfies
`pc mc ≡ b_i (mod a_i)` and `2 ((w_i mc²) mod a_i) ≤ a_i`, then `pc ∈ badRes i`. -/
theorem residue_check_zero : ∀ pc ∈ range 210, Nat.gcd pc 210 = 1 → ∀ mc ∈ range 35,
    (pc * mc) % 35 = 36 % 35 → 2 * ((6 * mc ^ 2) % 35) ≤ 35 → pc ∈ badRes 0 := by
  decide

set_option maxRecDepth 100000 in
theorem residue_check_one : ∀ pc ∈ range 210, Nat.gcd pc 210 = 1 → ∀ mc ∈ range 6,
    (pc * mc) % 6 = 5 % 6 → 2 * ((35 * mc ^ 2) % 6) ≤ 6 → pc ∈ badRes 1 := by
  decide

set_option maxRecDepth 100000 in
theorem residue_check_three : ∀ pc ∈ range 210, Nat.gcd pc 210 = 1 → ∀ mc ∈ range 210,
    (pc * mc) % 210 = 181 % 210 → 2 * ((1 * mc ^ 2) % 210) ≤ 210 → pc ∈ badRes 3 := by
  decide

set_option maxRecDepth 100000 in
theorem residue_check_four : ∀ pc ∈ range 210, Nat.gcd pc 210 = 1 → ∀ mc ∈ range 15,
    (pc * mc) % 15 = 14 % 15 → 2 * ((14 * mc ^ 2) % 15) ≤ 15 → pc ∈ badRes 4 := by
  decide

set_option maxRecDepth 100000 in
theorem residue_check_five : ∀ pc ∈ range 210, Nat.gcd pc 210 = 1 → ∀ mc ∈ range 14,
    (pc * mc) % 14 = 13 % 14 → 2 * ((15 * mc ^ 2) % 14) ≤ 14 → pc ∈ badRes 5 := by
  decide

/-- The residue check, uniformly in `i ≠ 2`. -/
theorem residue_check (i : Fin 6) (hi : i ≠ 2) : ∀ pc ∈ range 210, Nat.gcd pc 210 = 1 →
    ∀ mc ∈ range (slope i), (pc * mc) % slope i = icept i % slope i →
    2 * ((wcoef i * mc ^ 2) % slope i) ≤ slope i → pc ∈ badRes i := by
  fin_cases i
  · exact residue_check_zero
  · exact residue_check_one
  · exact absurd rfl hi
  · exact residue_check_three
  · exact residue_check_four
  · exact residue_check_five

theorem slope_dvd_210 (i : Fin 6) : slope i ∣ 210 := by
  fin_cases i <;> decide

theorem slope_mul_shift_le (i : Fin 6) : slope i * shift i ≤ 630 := by
  fin_cases i <;> decide

theorem Lv_mod_slope (i : Fin 6) (v : ℕ) : Lv i v % slope i = icept i % slope i := by
  unfold Lv L
  exact Nat.mul_add_mod _ _ _

/-- **No second carry forces a bad class**: if `p > 1000` is prime, `Lv i v = p m`,
`100 (m + 1) ≤ p` and level `2` does not carry, then `p mod 210 ∈ badRes i`. -/
theorem mem_badRes_of_noCarry {p : ℕ} (hp : p.Prime) (hpY : Y < p) (i : Fin 6) {v m : ℕ}
    (hm : Lv i v = p * m) (hpm : 100 * (m + 1) ≤ p) (hnc : 2 * (F v % p ^ 2) < p ^ 2) :
    p % 210 ∈ badRes i := by
  have hmZ : (Lv i v : ℤ) = (p : ℤ) * m := by exact_mod_cast hm
  by_cases hi : i = 2
  · subst hi
    exfalso
    have h := slope_mul_F_eq 2 v
    rw [hmZ] at h
    have e1 : slope 2 = 1 := rfl
    have e2 : wcoef 2 = 210 := rfl
    have e3 : c 2 = -29 := rfl
    have e4 : shift 2 = 2 := rfl
    rw [e1, e2, e3, e4] at h
    push_cast at h
    have h' : (F v : ℤ) = 210 * ((p : ℤ) * m) ^ 2 - 29 * ((p : ℤ) * m) - 2 := by linarith
    have := carry_of_two hpm h'
    omega
  · have h := slope_mul_F_eq i v
    rw [hmZ] at h
    have hr : 2 * ((wcoef i * m ^ 2) % slope i) ≤ slope i := by
      by_contra hcon
      push Not at hcon
      have := carry_of_class (slope_pos i) (abs_c_le i) (slope_mul_shift_le i) hpm h hcon
      omega
    have hcop : Nat.Coprime p 210 := by
      rw [Nat.Prime.coprime_iff_not_dvd hp]
      intro hd
      have := Nat.le_of_dvd (by norm_num) hd
      unfold Y at hpY
      omega
    have hg : Nat.gcd (p % 210) 210 = 1 := by
      rw [← Nat.gcd_rec, Nat.gcd_comm]
      exact hcop
    have hmod1 : (p % 210 * (m % slope i)) % slope i = icept i % slope i := by
      have h1 : p % 210 * (m % slope i) ≡ p * m [MOD slope i] :=
        ((Nat.mod_modEq p 210).of_dvd (slope_dvd_210 i)).mul (Nat.mod_modEq m (slope i))
      rw [h1, ← hm, Lv_mod_slope]
    have hmod2 : 2 * ((wcoef i * (m % slope i) ^ 2) % slope i) ≤ slope i := by
      have h1 : wcoef i * (m % slope i) ^ 2 ≡ wcoef i * m ^ 2 [MOD slope i] :=
        ((Nat.mod_modEq m (slope i)).pow 2).mul_left (wcoef i)
      rw [h1]
      exact hr
    exact residue_check i hi (p % 210) (mem_range.mpr (Nat.mod_lt _ (by norm_num))) hg
      (m % slope i) (mem_range.mpr (Nat.mod_lt _ (slope_pos i))) hmod1 hmod2

/-! ### The bad sets at a large prime -/

theorem mem_largeR {X p : ℕ} : p ∈ largeR X ↔
    p.Prime ∧ Y < p ∧ p ≤ 2 * Cb * X ∧ (X : ℝ) ^ ((1 : ℝ) / 2 + η) < p := by
  unfold largeR
  rw [Finset.mem_filter, mem_primeRange]
  tauto

/-- `badSet X i p` lies in a single class modulo `p`, so it has at most `X / p + 1` elements. -/
theorem card_badSet_le_div_add_one {p : ℕ} (hp : p.Prime) (hpY : Y < p) (i : Fin 6) (X : ℕ) :
    (#(badSet X i p) : ℝ) ≤ X / p + 1 := by
  classical
  obtain ⟨r, -, hr⟩ := exists_root hp hpY i
  have hsub : badSet X i p ⊆ {v ∈ Ico X (X + X) | v % p = r} := by
    intro v hv
    unfold badSet at hv
    rw [Finset.mem_filter] at hv ⊢
    rw [two_mul] at hv
    exact ⟨hv.1, (hr v).mp hv.2.1⟩
  calc (#(badSet X i p) : ℝ) ≤ #{v ∈ Ico X (X + X) | v % p = r} := by
        exact_mod_cast card_le_card hsub
    _ ≤ X / p + 1 := card_filter_mod_eq_le_real hp.pos

/-- For `p² > 400 Cb X`, `badSet X i p` is empty unless `p mod 210` is a bad class. -/
theorem badSet_eq_empty_of_not_mem_badRes {p : ℕ} (hp : p.Prime) (hpY : Y < p) (i : Fin 6)
    {X : ℕ} (hX : 400 * Cb * X < p ^ 2) (hres : p % 210 ∉ badRes i) : badSet X i p = ∅ := by
  classical
  unfold badSet
  rw [Finset.filter_eq_empty_iff]
  rintro v hv ⟨hdvd, hnc⟩
  rw [Finset.mem_Ico] at hv
  obtain ⟨m, hm⟩ := hdvd
  have hv1 : 1 ≤ v := by omega
  have h1 : p * m ≤ Cb * v := hm ▸ Lv_le i hv1
  have h2 : Cb * v ≤ Cb * (2 * X) := Nat.mul_le_mul_left _ hv.2.le
  have h3 : p * (200 * m) < p * p := by nlinarith
  have h4 : 200 * m < p := Nat.lt_of_mul_lt_mul_left h3
  have hpm : 100 * (m + 1) ≤ p := by unfold Y at hpY; omega
  exact hres (mem_badRes_of_noCarry hp hpY i hm hpm (hnc 2 le_rfl))

/-- `p > X^{1/2+η}` and `X^{2η} ≥ 400 Cb` give `p² > 400 Cb X`. -/
theorem sq_gt_of_mem_largeR {X p : ℕ} (hX0 : 0 < X) (hη : (400 * Cb : ℝ) ≤ (X : ℝ) ^ (2 * η))
    (hp : (X : ℝ) ^ ((1 : ℝ) / 2 + η) < p) : 400 * Cb * X < p ^ 2 := by
  have hXr : (0 : ℝ) < X := by exact_mod_cast hX0
  have h1 : ((X : ℝ) ^ ((1 : ℝ) / 2 + η)) ^ 2 = X * (X : ℝ) ^ (2 * η) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hXr.le]
    rw [show ((1 : ℝ) / 2 + η) * ((2 : ℕ) : ℝ) = 1 + 2 * η by push_cast; ring]
    rw [Real.rpow_add hXr, Real.rpow_one]
  have h2 : (400 * Cb * X : ℝ) < (p : ℝ) ^ 2 := by
    calc (400 * Cb * X : ℝ) = X * (400 * Cb) := by ring
      _ ≤ X * (X : ℝ) ^ (2 * η) := by gcongr
      _ = ((X : ℝ) ^ ((1 : ℝ) / 2 + η)) ^ 2 := h1.symm
      _ < (p : ℝ) ^ 2 := by gcongr
  exact_mod_cast h2

/-- The per-form bound: `∑_p #(badSet X i p) ≤ X · #(badRes i) · ε + #(largeR X)`, provided each
bad class contributes at most `ε` to `∑ 1/p`. -/
theorem sum_form_le (i : Fin 6) {X : ℕ} (hX : ∀ p ∈ largeR X, 400 * Cb * X < p ^ 2) {ε : ℝ}
    (hε : ∀ c ∈ badRes i, ∑ p ∈ (largeR X).filter (fun p => p % 210 = c), (1 : ℝ) / p ≤ ε) :
    ∑ p ∈ largeR X, (#(badSet X i p) : ℝ) ≤ X * (#(badRes i) * ε) + #(largeR X) := by
  calc ∑ p ∈ largeR X, (#(badSet X i p) : ℝ)
      ≤ ∑ p ∈ largeR X, ((X : ℝ) * (if p % 210 ∈ badRes i then (1 : ℝ) / p else 0) + 1) := by
        refine sum_le_sum fun p hp => ?_
        obtain ⟨hpr, hpY, -, -⟩ := mem_largeR.mp hp
        split_ifs with h
        · rw [mul_one_div]
          exact card_badSet_le_div_add_one hpr hpY i X
        · rw [badSet_eq_empty_of_not_mem_badRes hpr hpY i (hX p hp) h]
          simp
    _ = X * ∑ p ∈ (largeR X).filter (fun p => p % 210 ∈ badRes i), (1 : ℝ) / p
          + #(largeR X) := by
        rw [sum_add_distrib, sum_const, nsmul_eq_mul, mul_one, ← mul_sum, sum_filter]
    _ = X * ∑ c ∈ badRes i, ∑ p ∈ ((largeR X).filter (fun p => p % 210 ∈ badRes i)).filter
          (fun p => p % 210 = c), (1 : ℝ) / p + #(largeR X) := by
        rw [sum_fiberwise_of_maps_to (fun p hp => (mem_filter.mp hp).2)]
    _ ≤ X * ∑ c ∈ badRes i, ε + #(largeR X) := by
        gcongr with c hc
        refine (sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)).trans (hε c hc)
        intro p hp
        simp only [mem_filter] at hp ⊢
        exact ⟨hp.1.1, hp.2⟩
    _ = X * (#(badRes i) * ε) + #(largeR X) := by rw [sum_const, nsmul_eq_mul]

/-! ### Counting the large primes -/

theorem card_primesLE_eq (n : ℕ) : #(Nat.primesLE n) = Nat.primeCounting n := by
  unfold Nat.primeCounting Nat.primeCounting'
  rw [Nat.count_eq_card_filter_range]
  rfl

/-- `6 #(largeR X) ≤ 0.016 X` for `X ≥ 2 Cb · 1500² + 4` with `log X ≥ 3000 Cb log 4`. -/
theorem card_largeR_le {X : ℕ} (hX : 2 * Cb * 1500 ^ 2 + 4 ≤ X)
    (hlog : 3000 * Cb * log 4 ≤ log X) : (6 * #(largeR X) : ℝ) ≤ (16 / 1000) * X := by
  have hCbN : 1 ≤ Cb := by unfold Cb; omega
  have hCb : (1 : ℝ) ≤ Cb := by exact_mod_cast hCbN
  have hX4 : 4 ≤ X := le_trans (Nat.le_add_left 4 _) hX
  have hXr : (4 : ℝ) ≤ X := by exact_mod_cast hX4
  have hX0 : (0 : ℝ) < X := by linarith
  have hXn : (X : ℝ) ≤ ((2 * Cb * X : ℕ) : ℝ) := by
    push_cast
    nlinarith
  have hn1 : (1 : ℝ) < ((2 * Cb * X : ℕ) : ℝ) := by linarith
  have hlogX : 0 < log X := Real.log_pos (by linarith)
  have hlogn : log X ≤ log ((2 * Cb * X : ℕ) : ℝ) := Real.log_le_log hX0 hXn
  have hlog4 : 0 < log 4 := Real.log_pos (by norm_num)
  have h1 : #(largeR X) ≤ #(Nat.primesLE (2 * Cb * X)) := by
    apply card_le_card
    intro p hp
    obtain ⟨hpr, -, hle, -⟩ := mem_largeR.mp hp
    exact Nat.mem_primesLE.mpr ⟨hle, hpr⟩
  have h2 := Chebyshev.pi_le_log4_mul_div hn1
  rw [Nat.floor_natCast, ← card_primesLE_eq, Real.log_sqrt (by positivity)] at h2
  have hA : log 4 * ((2 * Cb * X : ℕ) : ℝ) / (log ((2 * Cb * X : ℕ) : ℝ) / 2) ≤ X / 750 := by
    rw [div_le_iff₀ (by linarith)]
    have := mul_le_mul_of_nonneg_left (hlog.trans hlogn) (by positivity : (0 : ℝ) ≤ X / 1500)
    push_cast at this ⊢
    nlinarith
  have hB : √((2 * Cb * X : ℕ) : ℝ) ≤ X / 1500 := by
    have hXr' : (2 * Cb * 1500 ^ 2 + 4 : ℝ) ≤ X := by exact_mod_cast hX
    have h3 : (((2 * Cb * X : ℕ) : ℝ)) ≤ ((X : ℝ) / 1500) ^ 2 := by
      push_cast
      have e : ((X : ℝ) / 1500) ^ 2 = X * X / 1500 ^ 2 := by ring
      rw [e, le_div_iff₀ (by norm_num)]
      have : (2 * Cb * 1500 ^ 2 : ℝ) * X ≤ X * X :=
        mul_le_mul_of_nonneg_right (by linarith) hX0.le
      nlinarith
    calc √((2 * Cb * X : ℕ) : ℝ) ≤ √(((X : ℝ) / 1500) ^ 2) := Real.sqrt_le_sqrt h3
      _ = X / 1500 := Real.sqrt_sq (by positivity)
  have h1r : (#(largeR X) : ℝ) ≤ #(Nat.primesLE (2 * Cb * X)) := by exact_mod_cast h1
  linarith

/-! ### The Mertens sums over the bad classes -/

/-- The prime harmonic sum over `p ≤ x`, `p ≡ c (mod 210)`. -/
noncomputable def Sc (c : ℕ) (x : ℝ) : ℝ :=
  ∑ p ∈ (Nat.primesLE ⌊x⌋₊).filter (fun p : ℕ => (p : ZMod 210) = (c : ZMod 210)), (1 : ℝ) / p

theorem totient_210 : Nat.totient 210 = 48 := by decide

/-- `MertensAP 210`, with constants chosen for every class. -/
theorem mertensAP_classes (hM : MertensAP 210) : ∃ B C : ℕ → ℝ, ∀ c : ℕ, Nat.Coprime c 210 →
    ∀ x : ℝ, 2 ≤ x → |Sc c x - (48 : ℝ)⁻¹ * log (log x) - B c| ≤ C c / log x := by
  have h : ∀ c : ℕ, ∃ B C : ℝ, Nat.Coprime c 210 → ∀ x : ℝ, 2 ≤ x →
      |Sc c x - (48 : ℝ)⁻¹ * log (log x) - B| ≤ C / log x := by
    intro c
    by_cases hc : Nat.Coprime c 210
    · obtain ⟨B, C, h⟩ := hM (c : ZMod 210) ((ZMod.isUnit_iff_coprime c 210).mpr hc)
      refine ⟨B, C, fun _ x hx => ?_⟩
      have := h x hx
      simp only [totient_210, Nat.cast_ofNat] at this
      exact this
    · exact ⟨0, 0, fun h => absurd h hc⟩
  choose B C hBC using h
  exact ⟨B, C, hBC⟩

/-- A sum of `1/p` over primes `y₁ < p ≤ y₂` in the class `c` is at most `Sc c y₂ - Sc c y₁`. -/
theorem sum_class_le_sub {c : ℕ} {y₁ y₂ : ℝ} (h0 : 0 ≤ y₁) (h12 : y₁ ≤ y₂) (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime ∧ y₁ < p ∧ (p : ℝ) ≤ y₂ ∧ (p : ZMod 210) = (c : ZMod 210)) :
    ∑ p ∈ s, (1 : ℝ) / p ≤ Sc c y₂ - Sc c y₁ := by
  unfold Sc
  have h02 : 0 ≤ y₂ := h0.trans h12
  have hsplit := (sum_filter_add_sum_filter_not
    ((Nat.primesLE ⌊y₂⌋₊).filter (fun p : ℕ => (p : ZMod 210) = (c : ZMod 210)))
    (fun p : ℕ => (p : ℝ) ≤ y₁) (fun p : ℕ => (1 : ℝ) / p))
  have hT1 : ((Nat.primesLE ⌊y₂⌋₊).filter (fun p : ℕ => (p : ZMod 210) = (c : ZMod 210))).filter
      (fun p : ℕ => (p : ℝ) ≤ y₁) =
      (Nat.primesLE ⌊y₁⌋₊).filter (fun p : ℕ => (p : ZMod 210) = (c : ZMod 210)) := by
    ext p
    simp only [mem_filter, Nat.mem_primesLE, Nat.le_floor_iff h0, Nat.le_floor_iff h02]
    constructor
    · rintro ⟨⟨⟨-, hp⟩, hc⟩, h1⟩
      exact ⟨⟨h1, hp⟩, hc⟩
    · rintro ⟨⟨h1, hp⟩, hc⟩
      exact ⟨⟨⟨h1.trans h12, hp⟩, hc⟩, h1⟩
  have hsub : s ⊆ ((Nat.primesLE ⌊y₂⌋₊).filter
      (fun p : ℕ => (p : ZMod 210) = (c : ZMod 210))).filter (fun p : ℕ => ¬ (p : ℝ) ≤ y₁) := by
    intro p hp
    obtain ⟨hpr, h1, h2, hc⟩ := hs p hp
    simp only [mem_filter, Nat.mem_primesLE, Nat.le_floor_iff h02]
    exact ⟨⟨⟨h2, hpr⟩, hc⟩, not_le.mpr h1⟩
  have hle := sum_le_sum_of_subset_of_nonneg hsub
    (fun p _ _ => by positivity : ∀ p ∈ _, p ∉ s → (0 : ℝ) ≤ 1 / p)
  rw [hT1] at hsplit
  linarith

/-- The Mertens estimate for the difference `Sc c y₂ - Sc c y₁`. -/
theorem class_sum_le {c : ℕ} {B C K : ℝ} (hCK : |C| ≤ K)
    (h : ∀ x : ℝ, 2 ≤ x → |Sc c x - (48 : ℝ)⁻¹ * log (log x) - B| ≤ C / log x)
    {y₁ y₂ : ℝ} (hy₁ : 2 ≤ y₁) (hy₁₂ : y₁ ≤ y₂) :
    Sc c y₂ - Sc c y₁ ≤ (48 : ℝ)⁻¹ * (log (log y₂) - log (log y₁)) + 2 * K / log y₁ := by
  have hl1 : 0 < log y₁ := Real.log_pos (by linarith)
  have hl2 : log y₁ ≤ log y₂ := Real.log_le_log (by linarith) hy₁₂
  have hK0 : 0 ≤ K := (abs_nonneg C).trans hCK
  have h1 := abs_le.mp (h y₁ hy₁)
  have h2 := abs_le.mp (h y₂ (hy₁.trans hy₁₂))
  have hC1 : C / log y₁ ≤ K / log y₁ :=
    div_le_div_of_nonneg_right ((le_abs_self C).trans hCK) hl1.le
  have hC2 : C / log y₂ ≤ K / log y₁ := by
    calc C / log y₂ ≤ K / log y₂ :=
          div_le_div_of_nonneg_right ((le_abs_self C).trans hCK) (by linarith)
      _ ≤ K / log y₁ := div_le_div_of_nonneg_left hK0 hl1 hl2
  have : 2 * K / log y₁ = K / log y₁ + K / log y₁ := by ring
  linarith [h1.1, h1.2, h2.1, h2.2]

/-- `log log (K X) - log log (X^{1/2+η}) ≤ log 2 + 1/1000` once `log K ≤ log X / 1000`. -/
theorem loglog_diff_le {X K : ℝ} (hX : 1 < X) (hK : 1 ≤ K)
    (hKX : log K ≤ (1 / 1000) * log X) :
    log (log (K * X)) - log (log (X ^ ((1 : ℝ) / 2 + η))) ≤ log 2 + 1 / 1000 := by
  have hX0 : 0 < X := by linarith
  have hlogX : 0 < log X := Real.log_pos hX
  have hlogK : 0 ≤ log K := Real.log_nonneg hK
  have e1 : log (K * X) = log K + log X := Real.log_mul (by positivity) (by positivity)
  have e2 : log (X ^ ((1 : ℝ) / 2 + η)) = ((1 : ℝ) / 2 + η) * log X := Real.log_rpow hX0 _
  have hy : 0 < log (X ^ ((1 : ℝ) / 2 + η)) := by rw [e2]; unfold η; positivity
  have hkey : log (K * X) ≤ (2 + 2 / 1000) * log (X ^ ((1 : ℝ) / 2 + η)) := by
    rw [e1, e2]; unfold η; nlinarith
  have h3 : log (log (K * X)) ≤ log ((2 + 2 / 1000) * log (X ^ ((1 : ℝ) / 2 + η))) :=
    Real.log_le_log (by rw [e1]; linarith) hkey
  rw [Real.log_mul (by norm_num) hy.ne'] at h3
  have h4 : log (2 + 2 / 1000) ≤ log 2 + 1 / 1000 := by
    have e : (2 + 2 / 1000 : ℝ) = 2 * (1 + 1 / 1000) := by norm_num
    rw [e, Real.log_mul (by norm_num) (by norm_num)]
    have := Real.log_le_sub_one_of_pos (x := 1 + 1 / 1000) (by norm_num)
    linarith
  linarith

/-! ### Conclusion -/

/-- **Section 11**: large primes, conditional on Mertens' theorem in progressions mod `210`. -/
theorem large_bound (hM : MertensAP 210) : ∀ᶠ X : ℕ in atTop,
    (∑ i, ∑ p ∈ largeR X, #(badSet X i p) : ℝ) ≤ (60 / 100) * X := by
  obtain ⟨B, C, hBC⟩ := mertensAP_classes hM
  -- a uniform bound for the finitely many error constants
  set K : ℝ := ∑ c ∈ range 210, |C c| with hK
  have hKc : ∀ c < 210, |C c| ≤ K := fun c hc =>
    single_le_sum (f := fun c => |C c|) (fun _ _ => abs_nonneg _) (mem_range.mpr hc)
  have hK0 : 0 ≤ K := sum_nonneg (fun _ _ => abs_nonneg _)
  have hCbN : 1 ≤ Cb := by unfold Cb; omega
  have hCb : (1 : ℝ) ≤ Cb := by exact_mod_cast hCbN
  -- the eventual conditions on `X`
  have ev1 : ∀ᶠ X : ℕ in atTop, (400 * Cb : ℝ) ≤ (X : ℝ) ^ (2 * η) :=
    ((tendsto_rpow_atTop (by unfold η; norm_num)).comp
      tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  have ev2 : ∀ᶠ X : ℕ in atTop,
      max (1000 * log (2 * Cb)) (max (40000 * K) (3000 * Cb * log 4)) ≤ log (X : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  have ev3 : ∀ᶠ X : ℕ in atTop, 2 * Cb * 1500 ^ 2 + 4 ≤ X := eventually_ge_atTop _
  filter_upwards [ev1, ev2, ev3] with X hX1 hX2 hX3
  have hX1' : (400 * Cb : ℝ) ≤ (X : ℝ) ^ (2 * η) := hX1
  have hX2' : max (1000 * log (2 * Cb)) (max (40000 * K) (3000 * Cb * log 4)) ≤ log (X : ℝ) :=
    hX2
  have hX4 : 4 ≤ X := le_trans (Nat.le_add_left 4 _) hX3
  have hX0 : 0 < X := by omega
  have hXr4 : (4 : ℝ) ≤ X := by exact_mod_cast hX4
  have hXr1 : (1 : ℝ) < X := by linarith
  have hlogX : 0 < log X := Real.log_pos hXr1
  -- the endpoints `y₁ = X^{1/2+η}` and `y₂ = 2 Cb X`
  have hy₁ : (2 : ℝ) ≤ (X : ℝ) ^ ((1 : ℝ) / 2 + η) := by
    calc (2 : ℝ) = √4 := by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      _ ≤ √X := Real.sqrt_le_sqrt hXr4
      _ = (X : ℝ) ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow X
      _ ≤ (X : ℝ) ^ ((1 : ℝ) / 2 + η) :=
          Real.rpow_le_rpow_of_exponent_le hXr1.le (by unfold η; norm_num)
  have hy₁₂ : (X : ℝ) ^ ((1 : ℝ) / 2 + η) ≤ 2 * Cb * X := by
    calc (X : ℝ) ^ ((1 : ℝ) / 2 + η) ≤ (X : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hXr1.le (by unfold η; norm_num)
      _ = X := Real.rpow_one _
      _ ≤ 2 * Cb * X := by nlinarith
  have hlogy₁ : log ((X : ℝ) ^ ((1 : ℝ) / 2 + η)) = ((1 : ℝ) / 2 + η) * log X :=
    Real.log_rpow (by positivity) _
  have hlogy₁pos : 0 < log ((X : ℝ) ^ ((1 : ℝ) / 2 + η)) := by
    rw [hlogy₁]; unfold η; positivity
  -- the contribution of a single bad class
  have hclass : ∀ c, c < 210 → Nat.Coprime c 210 →
      ∑ p ∈ (largeR X).filter (fun p => p % 210 = c), (1 : ℝ) / p ≤ 146 / 10000 := by
    intro c hc hcop
    have hs : ∀ p ∈ (largeR X).filter (fun p => p % 210 = c),
        p.Prime ∧ (X : ℝ) ^ ((1 : ℝ) / 2 + η) < p ∧ (p : ℝ) ≤ 2 * Cb * X ∧
          (p : ZMod 210) = (c : ZMod 210) := by
      intro p hp
      rw [mem_filter, mem_largeR] at hp
      obtain ⟨⟨hpr, -, hple, hpgt⟩, hpc⟩ := hp
      refine ⟨hpr, hpgt, by exact_mod_cast hple, ?_⟩
      rw [← ZMod.natCast_mod p 210, hpc]
    have hA : log (log (2 * Cb * X)) - log (log ((X : ℝ) ^ ((1 : ℝ) / 2 + η))) ≤
        log 2 + 1 / 1000 := by
      apply loglog_diff_le hXr1 (by linarith)
      have := le_trans (le_max_left _ _) hX2'
      linarith
    have hB : 2 * K / log ((X : ℝ) ^ ((1 : ℝ) / 2 + η)) ≤ 1 / 10000 := by
      rw [div_le_iff₀ hlogy₁pos, hlogy₁]
      have := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hX2')
      unfold η
      nlinarith
    calc ∑ p ∈ (largeR X).filter (fun p => p % 210 = c), (1 : ℝ) / p
        ≤ Sc c (2 * Cb * X) - Sc c ((X : ℝ) ^ ((1 : ℝ) / 2 + η)) :=
          sum_class_le_sub (by positivity) hy₁₂ _ hs
      _ ≤ (48 : ℝ)⁻¹ * (log (log (2 * Cb * X)) - log (log ((X : ℝ) ^ ((1 : ℝ) / 2 + η))))
            + 2 * K / log ((X : ℝ) ^ ((1 : ℝ) / 2 + η)) :=
          class_sum_le (hKc c hc) (hBC c hcop) hy₁ hy₁₂
      _ ≤ (48 : ℝ)⁻¹ * (log 2 + 1 / 1000) + 1 / 10000 := by
          have : (0 : ℝ) ≤ (48 : ℝ)⁻¹ := by norm_num
          nlinarith
      _ ≤ 146 / 10000 := by linarith [Real.log_two_lt_d9]
  -- the per-form bounds
  have hform : ∀ i : Fin 6, ∑ p ∈ largeR X, (#(badSet X i p) : ℝ) ≤
      X * (#(badRes i) * (146 / 10000)) + #(largeR X) := by
    intro i
    apply sum_form_le i
    · intro p hp
      exact sq_gt_of_mem_largeR hX0 hX1' (mem_largeR.mp hp).2.2.2
    · intro c hc
      exact hclass c (badRes_subset i c hc).1 (badRes_subset i c hc).2
  -- the endpoint terms
  have hcard : (6 * #(largeR X) : ℝ) ≤ (16 / 1000) * X :=
    card_largeR_le hX3 (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hX2'))
  have hsum : ∑ i : Fin 6, (#(badRes i) : ℝ) = 40 := by exact_mod_cast sum_card_badRes
  calc (∑ i, ∑ p ∈ largeR X, #(badSet X i p) : ℝ)
      ≤ ∑ i : Fin 6, ((X : ℝ) * (#(badRes i) * (146 / 10000)) + #(largeR X)) :=
        sum_le_sum fun i _ => hform i
    _ = (X : ℝ) * ((∑ i : Fin 6, (#(badRes i) : ℝ)) * (146 / 10000)) + 6 * #(largeR X) := by
        rw [sum_add_distrib, ← mul_sum, ← sum_mul, sum_const, card_univ, Fintype.card_fin,
          nsmul_eq_mul]
        push_cast
        ring
    _ = (X : ℝ) * (40 * (146 / 10000)) + 6 * #(largeR X) := by rw [hsum]
    _ ≤ (60 / 100) * X := by linarith

end Erdos727
