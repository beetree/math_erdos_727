import Erdos727.Analytic.CharacterMertens

/-!
# Mertens' theorems in arithmetic progressions (steps 6–7 of `CharacterSums`)
-/

namespace Erdos727

open Finset Real

variable {q : ℕ} [NeZero q]

/-! ### Orthogonality bookkeeping -/

/-- Orthogonality: for a unit `a`, the indicator of `p ≡ a (mod q)` is `φ(q)⁻¹ ∑_χ χ(a)⁻¹ χ(p)`. -/
lemma indicator_eq_sum_char_inv_mul_char (a : ZMod q) (ha : IsUnit a) (p : ℕ) :
    (if (p : ZMod q) = a then (Nat.totient q : ℂ) else 0)
      = ∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * χ p := by
  rw [DirichletCharacter.sum_char_inv_mul_char_eq ℂ ha (p : ZMod q)]
  by_cases h : (p : ZMod q) = a
  · simp [h]
  · simp [h, Ne.symm h]

/-- The principal character picks out the primes coprime to `q`. -/
lemma sum_one_char_prime_log_div (N : ℕ) :
    ∑ p ∈ Nat.primesLE N, (1 : DirichletCharacter ℂ q) p * ((log p / p : ℝ) : ℂ)
      = ((∑ p ∈ (Nat.primesLE N).filter (fun p : ℕ => IsUnit (p : ZMod q)), log p / p : ℝ) : ℂ) := by
  rw [sum_filter, Complex.ofReal_sum]
  refine sum_congr rfl fun p _ => ?_
  by_cases h : IsUnit (p : ZMod q)
  · simp only [h, ↓reduceIte]
    rw [MulChar.one_apply h, one_mul]
  · simp only [h, ↓reduceIte]
    rw [MulChar.map_nonunit _ h, zero_mul, Complex.ofReal_zero]

/-- `φ(q) ∑_{p ≤ N, p ≡ a} log p / p = ∑_χ χ(a)⁻¹ ∑_{p ≤ N} χ(p) log p / p`. -/
lemma totient_mul_sum_AP_eq_sum_char (a : ZMod q) (ha : IsUnit a) (N : ℕ) :
    (Nat.totient q : ℂ) *
        ((∑ p ∈ (Nat.primesLE N).filter (fun p : ℕ => (p : ZMod q) = a), log p / p : ℝ) : ℂ)
      = ∑ χ : DirichletCharacter ℂ q,
          χ a⁻¹ * ∑ p ∈ Nat.primesLE N, χ p * ((log p / p : ℝ) : ℂ) := by
  simp_rw [mul_sum]
  rw [sum_comm, sum_filter, Complex.ofReal_sum, mul_sum]
  refine sum_congr rfl fun p _ => ?_
  simp only [← mul_assoc]
  rw [← sum_mul, ← indicator_eq_sum_char_inv_mul_char a ha p]
  split_ifs <;> simp

/-- **Mertens' first theorem in arithmetic progressions.** -/
theorem mertens_first_AP (a : ZMod q) (ha : IsUnit a) :
    ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
      |∑ p ∈ (Nat.primesLE N).filter (fun p : ℕ => (p : ZMod q) = a), log p / p
        - (Nat.totient q : ℝ)⁻¹ * log N| ≤ C := by
  classical
  have hφ : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  -- a bound for every nonprincipal character
  have hb : ∀ χ : DirichletCharacter ℂ q, ∃ C : ℝ, χ ≠ 1 →
      ∀ N : ℕ, ‖∑ p ∈ Nat.primesLE N, χ p * ((log p / p : ℝ) : ℂ)‖ ≤ C := by
    intro χ
    by_cases h : χ = 1
    · exact ⟨0, fun h' => absurd h h'⟩
    · obtain ⟨C, hC⟩ := exists_bound_sum_char_prime_log_div χ h
      exact ⟨C, fun _ => hC⟩
  choose Cf hCf using hb
  set D : ℝ := ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).erase 1, Cf χ with hD
  set K : ℝ := ∑ p ∈ q.primeFactors, log p / p with hK
  refine ⟨(Nat.totient q : ℝ)⁻¹ * (D + (3 + K)), fun N hN => ?_⟩
  -- Step 1: the complex identity, with the principal character split off
  have hid := totient_mul_sum_AP_eq_sum_char a ha N
  rw [← Finset.add_sum_erase _ _ (mem_univ (1 : DirichletCharacter ℂ q)),
    sum_one_char_prime_log_div N] at hid
  have h1a : (1 : DirichletCharacter ℂ q) a⁻¹ = 1 := by
    apply MulChar.one_apply
    exact IsUnit.of_mul_eq_one a ((ZMod.inv_mul_eq_one_of_isUnit ha a).mpr rfl)
  rw [h1a, one_mul] at hid
  -- Step 2: the nonprincipal characters contribute `O(1)`
  have hR : ‖∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).erase 1,
      χ a⁻¹ * ∑ p ∈ Nat.primesLE N, χ p * ((log p / p : ℝ) : ℂ)‖ ≤ D := by
    refine (norm_sum_le _ _).trans (sum_le_sum fun χ hχ => ?_)
    rw [norm_mul]
    have hχ1 : χ ≠ 1 := (mem_erase.mp hχ).1
    calc ‖χ a⁻¹‖ * ‖∑ p ∈ Nat.primesLE N, χ p * ((log p / p : ℝ) : ℂ)‖
        ≤ 1 * Cf χ := mul_le_mul (DirichletCharacter.norm_le_one χ _) (hCf χ hχ1 N)
          (norm_nonneg _) zero_le_one
      _ = Cf χ := one_mul _
  -- Step 3: back to real numbers
  set S : ℝ := ∑ p ∈ (Nat.primesLE N).filter (fun p : ℕ => (p : ZMod q) = a), log p / p with hS
  set U : ℝ := ∑ p ∈ (Nat.primesLE N).filter (fun p : ℕ => IsUnit (p : ZMod q)), log p / p
    with hU
  have hSU : |(Nat.totient q : ℝ) * S - U| ≤ D := by
    have : (((Nat.totient q : ℝ) * S - U : ℝ) : ℂ)
        = ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).erase 1,
            χ a⁻¹ * ∑ p ∈ Nat.primesLE N, χ p * ((log p / p : ℝ) : ℂ) := by
      rw [Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_natCast, hid]
      ring
    rw [← Real.norm_eq_abs, ← Complex.norm_real, this]
    exact hR
  -- Step 4: the principal character gives `log N + O(1)`
  have hUlog : |U - log N| ≤ 3 + K := by
    have hsplit := sum_filter_add_sum_filter_not (Nat.primesLE N)
      (fun p : ℕ => IsUnit (p : ZMod q)) (fun p : ℕ => log p / p)
    have hV0 : 0 ≤ ∑ p ∈ (Nat.primesLE N).filter (fun p : ℕ => ¬ IsUnit (p : ZMod q)),
        log p / p := sum_nonneg fun p _ => by positivity
    have hVK : ∑ p ∈ (Nat.primesLE N).filter (fun p : ℕ => ¬ IsUnit (p : ZMod q)),
        log p / p ≤ K := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro p hp
        rw [mem_filter, Nat.mem_primesLE, ZMod.isUnit_iff_coprime] at hp
        rw [Nat.mem_primeFactors]
        exact ⟨hp.1.2, hp.1.2.dvd_iff_not_coprime.mpr hp.2, NeZero.ne q⟩
      · intro p _ _
        positivity
    have h3 := Mertens.abs_sum_prime_log_div_sub_log_le_nat hN
    rw [abs_le] at h3 ⊢
    constructor <;> linarith
  -- Step 5: combine
  have hrw : S - (Nat.totient q : ℝ)⁻¹ * log N
      = (Nat.totient q : ℝ)⁻¹ * (((Nat.totient q : ℝ) * S - U) + (U - log N)) := by
    rw [sub_add_sub_cancel, mul_sub, ← mul_assoc, inv_mul_cancel₀ hφ.ne', one_mul]
  rw [hrw, abs_mul, abs_of_pos (inv_pos.mpr hφ)]
  exact mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (add_le_add hSU hUlog))
    (inv_pos.mpr hφ).le

/-! ### The character-restricted prime weight -/

/-- The bare form of the prime weight restricted to the progression `a (mod q)`, scaled by
`φ(q)` so that its partial sums are `log N + O(1)`. -/
noncomputable def apWeightFun (q : ℕ) (a : ZMod q) : ℕ → ℝ :=
  fun n ↦ if n.Prime ∧ (n : ZMod q) = a then (Nat.totient q : ℝ) * (log n / n) else 0

omit [NeZero q] in
lemma sum_apWeightFun_eq (a : ZMod q) (N : ℕ) :
    ∑ n ∈ Ioc 0 N, apWeightFun q a n
      = (Nat.totient q : ℝ) *
          ∑ p ∈ (Nat.primesLE N).filter (fun p : ℕ => (p : ZMod q) = a), log p / p := by
  rw [mul_sum, sum_filter, Nat.primesLE_eq_filter_Ioc_zero, sum_filter]
  refine sum_congr rfl fun n _ => ?_
  unfold apWeightFun
  by_cases hn : n.Prime <;> by_cases ha : (n : ZMod q) = a <;> simp [hn, ha]

omit [NeZero q] in
lemma sum_inv_log_mul_apWeightFun_eq (a : ZMod q) (N : ℕ) :
    ∑ n ∈ Ioc 0 N, (log n)⁻¹ * apWeightFun q a n
      = (Nat.totient q : ℝ) *
          ∑ p ∈ (Nat.primesLE N).filter (fun p : ℕ => (p : ZMod q) = a), (1 : ℝ) / p := by
  rw [mul_sum, sum_filter, Nat.primesLE_eq_filter_Ioc_zero, sum_filter]
  refine sum_congr rfl fun n _ => ?_
  unfold apWeightFun
  by_cases hn : n.Prime
  · by_cases ha : (n : ZMod q) = a
    · simp only [hn, ha, and_self, ↓reduceIte]
      have hl : log n ≠ 0 := hn.log_pos.ne'
      have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne_zero
      field_simp
    · simp [hn, ha]
  · simp [hn]

/-- The two-sided `O(1)` bound `∑_{n ≤ x} f_a n - log x` for real `x ≥ 1`, from the natural-number
bound of `mertens_first_AP`. -/
lemma apWeightFun_err_bounds (a : ZMod q) (C : ℝ)
    (hC : ∀ N : ℕ, 1 ≤ N →
      |∑ p ∈ (Nat.primesLE N).filter (fun p : ℕ => (p : ZMod q) = a), log p / p
        - (Nat.totient q : ℝ)⁻¹ * log N| ≤ C) {x : ℝ} (hx : 1 ≤ x) :
    -((Nat.totient q : ℝ) * C) - log 2 ≤ ∑ n ∈ Ioc 0 ⌊x⌋₊, apWeightFun q a n - log x ∧
      ∑ n ∈ Ioc 0 ⌊x⌋₊, apWeightFun q a n - log x ≤ (Nat.totient q : ℝ) * C := by
  have hφ : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  have hN : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by simpa using hx)
  have hNx : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hxN : x < ⌊x⌋₊ + 1 := Nat.lt_floor_add_one x
  have hN1 : (1 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast hN
  have h := hC ⌊x⌋₊ hN
  rw [sum_apWeightFun_eq]
  set S : ℝ := ∑ p ∈ (Nat.primesLE ⌊x⌋₊).filter (fun p : ℕ => (p : ZMod q) = a), log p / p
    with hS
  have h' : |(Nat.totient q : ℝ) * S - log ⌊x⌋₊| ≤ (Nat.totient q : ℝ) * C := by
    have : (Nat.totient q : ℝ) * S - log ⌊x⌋₊
        = (Nat.totient q : ℝ) * (S - (Nat.totient q : ℝ)⁻¹ * log ⌊x⌋₊) := by
      rw [mul_sub, ← mul_assoc, mul_inv_cancel₀ hφ.ne', one_mul]
    rw [this, abs_mul, abs_of_pos hφ]
    exact mul_le_mul_of_nonneg_left h hφ.le
  have hlog1 : log ⌊x⌋₊ ≤ log x := Real.log_le_log (by linarith) hNx
  have hlog2 : log x ≤ log 2 + log ⌊x⌋₊ := by
    rw [← Real.log_mul (by norm_num) (by linarith)]
    exact Real.log_le_log (by linarith) (by linarith)
  rw [abs_le] at h'
  constructor <;> linarith

/-- The prime weight restricted to the progression `a (mod q)` (scaled by `φ(q)`), as a
`Mertens.Weight`, given a bound `C` for Mertens' first theorem in the progression. -/
@[reducible]
noncomputable def apWeight (q : ℕ) [NeZero q] (a : ZMod q) (C : ℝ)
    (hC : ∀ N : ℕ, 1 ≤ N →
      |∑ p ∈ (Nat.primesLE N).filter (fun p : ℕ => (p : ZMod q) = a), log p / p
        - (Nat.totient q : ℝ)⁻¹ * log N| ≤ C) : Mertens.Weight := {
  toFun := apWeightFun q a
  map_zero' := by simp [apWeightFun]
  map_one' := by simp [apWeightFun]
  lowerBound := -((Nat.totient q : ℝ) * C) - log 2
  upperBound := (Nat.totient q : ℝ) * C
  le_first' x hx := (apWeightFun_err_bounds a C hC hx).1
  first_le' x hx := (apWeightFun_err_bounds a C hC hx).2
  C₀ := Nat.totient q
  toFun_bound n := by
    unfold apWeightFun
    split_ifs
    · rw [abs_of_nonneg (by positivity), mul_div_assoc]
    · rw [abs_zero]; positivity
}

/-- **Mertens' second theorem in arithmetic progressions**, with `O(1/log x)` error. -/
theorem mertensAP_of_neZero (q : ℕ) [NeZero q] : MertensAP q := by
  intro a ha
  obtain ⟨C, hC⟩ := mertens_first_AP a ha
  have hφ : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  refine ⟨Mertens.Weight.M (f := apWeight q a C hC) / Nat.totient q,
    Mertens.Weight.C₂ (f := apWeight q a C hC) / Nat.totient q, fun x hx => ?_⟩
  have h : |∑ n ∈ Ioc 0 ⌊x⌋₊, (log n)⁻¹ * apWeightFun q a n - log (log x)
      - Mertens.Weight.M (f := apWeight q a C hC)|
        ≤ Mertens.Weight.C₂ (f := apWeight q a C hC) / log x :=
    Mertens.Weight.sum_div_log_sub_sub_bound (f := apWeight q a C hC) hx
  rw [sum_inv_log_mul_apWeightFun_eq] at h
  set Sx : ℝ := ∑ p ∈ (Nat.primesLE ⌊x⌋₊).filter (fun p : ℕ => (p : ZMod q) = a), (1 : ℝ) / p
    with hSx
  set M := Mertens.Weight.M (f := apWeight q a C hC) with hM
  set C₂ := Mertens.Weight.C₂ (f := apWeight q a C hC) with hC₂
  have hrw : Sx - (Nat.totient q : ℝ)⁻¹ * log (log x) - M / Nat.totient q
      = (Nat.totient q : ℝ)⁻¹ * ((Nat.totient q : ℝ) * Sx - log (log x) - M) := by
    field_simp
  rw [hrw, abs_mul, abs_of_pos (inv_pos.mpr hφ)]
  calc (Nat.totient q : ℝ)⁻¹ * |(Nat.totient q : ℝ) * Sx - log (log x) - M|
      ≤ (Nat.totient q : ℝ)⁻¹ * (C₂ / log x) :=
        mul_le_mul_of_nonneg_left h (inv_pos.mpr hφ).le
    _ = C₂ / Nat.totient q / log x := by ring

end Erdos727
