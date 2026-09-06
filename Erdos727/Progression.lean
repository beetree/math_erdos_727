import Erdos727.SmallPrimes
import Erdos727.Count

/-!
# The progression `F v = f (t₀ + Q v)` and its linear factors (end of Section 4)

* `F v = f (t₀ + Q v)` and `Lv i v = L i (t₀ + Q v)`.
* Size bounds: `Lv i v ≤ Cb * v` and `F v ≤ Cf * v ^ 2` for `v ≥ 1`; `v ^ 2 ≤ F v`.
* For a prime `p > 1000`, `slope i * Q` is a unit mod `p`, so `p ∣ Lv i v` is a single
  residue class `v ≡ root p i (mod p)`.
* First carry: `p ∣ Lv i v` forces `F v ≡ -shift i (mod p)`, so level `1` carries.
* Injectivity: on the root class, `F v ≡ F v' (mod p^ℓ)` forces `v ≡ v' (mod p^ℓ)`, because
  `F v - F v' = (v - v') (D (v + v') + E)` and `D (v + v') + E ≡ Q f'(t) ≢ 0 (mod p)`.
* Without repeated factors, `v_p (A (F v)) ≤ 1` for `p > 1000`.
-/

namespace Erdos727

open Finset

/-- `F v = f (t₀ + Q v)`. -/
noncomputable def F (v : ℕ) : ℕ := f (t₀ + Q * v)

/-- `Lv i v = L i (t₀ + Q v)`. -/
noncomputable def Lv (i : Fin 6) (v : ℕ) : ℕ := L i (t₀ + Q * v)

/-- Leading coefficient `D = 210 Q²` of `F`. -/
noncomputable def D : ℕ := 210 * Q ^ 2

/-- Linear coefficient `E = Q f'(t₀)` of `F`. -/
noncomputable def E : ℕ := Q * fderiv t₀

/-- Constant term `G = f t₀` of `F`. -/
noncomputable def G : ℕ := f t₀

/-- A constant with `Lv i v ≤ Cb * v` for `v ≥ 1`. -/
noncomputable def Cb : ℕ := 210 * (t₀ + Q) + 181

/-- A constant with `F v ≤ Cf * v ^ 2` for `v ≥ 1`. -/
noncomputable def Cf : ℕ := 210 * (t₀ + Q) ^ 2 + 391 * (t₀ + Q) + 179

theorem F_eq (v : ℕ) : F v = D * v ^ 2 + E * v + G := by
  unfold F D E G f fderiv; ring

theorem A_F (v : ℕ) : A (F v) = ∏ i, Lv i v := by
  unfold F Lv; exact A_f _

theorem Lv_pos (i : Fin 6) (v : ℕ) : 0 < Lv i v := L_pos i _

/-- Auxiliary: every slope is at most `210`. -/
theorem slope_le_210 (i : Fin 6) : slope i ≤ 210 := by
  fin_cases i <;> simp [slope]

/-- Auxiliary: every intercept is at most `181`. -/
theorem icept_le_181 (i : Fin 6) : icept i ≤ 181 := by
  fin_cases i <;> simp [icept]

theorem Lv_le (i : Fin 6) {v : ℕ} (hv : 1 ≤ v) : Lv i v ≤ Cb * v := by
  unfold Lv L Cb
  have h1 := slope_le_210 i
  have h2 := icept_le_181 i
  calc slope i * (t₀ + Q * v) + icept i ≤ 210 * (t₀ + Q * v) + 181 :=
        Nat.add_le_add (Nat.mul_le_mul_right _ h1) h2
    _ ≤ (210 * (t₀ + Q) + 181) * v := by nlinarith

theorem F_le {v : ℕ} (hv : 1 ≤ v) : F v ≤ Cf * v ^ 2 := by
  unfold F f Cf
  have h : t₀ + Q * v ≤ (t₀ + Q) * v := by nlinarith
  have h2 : (t₀ + Q * v) ^ 2 ≤ ((t₀ + Q) * v) ^ 2 := Nat.pow_le_pow_left h 2
  have h3 : v ≤ v ^ 2 := by nlinarith
  have h4 : (t₀ + Q) * v ≤ (t₀ + Q) * v ^ 2 := Nat.mul_le_mul_left _ h3
  rw [mul_pow] at h2
  nlinarith

theorem sq_le_F (v : ℕ) : v ^ 2 ≤ F v := by
  unfold F f
  have hQ := Q_pos
  have h : v ≤ t₀ + Q * v := by nlinarith
  have h2 : v ^ 2 ≤ (t₀ + Q * v) ^ 2 := Nat.pow_le_pow_left h 2
  nlinarith

/-- Auxiliary: `f` is strictly monotone. -/
theorem f_strictMono : StrictMono f := by
  intro a b hab
  unfold f
  nlinarith [Nat.mul_le_mul hab.le hab.le]

theorem F_strictMono : StrictMono F := by
  intro a b hab
  unfold F
  apply f_strictMono
  have := Q_pos
  nlinarith

/-- `Lv i v ∣ F v + shift i`. -/
theorem Lv_dvd_F_add_shift (i : Fin 6) (v : ℕ) : Lv i v ∣ F v + shift i := by
  unfold Lv F; exact L_dvd_f_add_shift i _

/-- `p ∤ slope i * Q` for primes `p > 1000`. -/
theorem not_dvd_slope_mul_Q {p : ℕ} (hp : p.Prime) (hpY : Y < p) (i : Fin 6) :
    ¬ p ∣ slope i * Q := by
  intro h
  unfold Y at hpY
  rcases (Nat.Prime.dvd_mul hp).mp h with h | h
  · have := prime_dvd_slope_le i hp h
    omega
  · have := prime_dvd_Q_le hp h
    unfold Y at this
    omega

/-- For a prime `p > 1000`, `p ∣ Lv i v` is a single residue class modulo `p`. -/
theorem exists_root {p : ℕ} (hp : p.Prime) (hpY : Y < p) (i : Fin 6) :
    ∃ r, r < p ∧ ∀ v, p ∣ Lv i v ↔ v % p = r := by
  have := Fact.mk hp
  have hu : (slope i : ZMod p) * (Q : ZMod p) ≠ 0 := by
    have h := not_dvd_slope_mul_Q hp hpY i
    rw [← ZMod.natCast_eq_zero_iff] at h
    push_cast at h
    exact h
  have hinv : (slope i : ZMod p) * (Q : ZMod p) * ((slope i : ZMod p) * (Q : ZMod p))⁻¹ = 1 :=
    mul_inv_cancel₀ hu
  set r : ZMod p := -((icept i : ZMod p) + (slope i : ZMod p) * (t₀ : ZMod p)) *
    ((slope i : ZMod p) * (Q : ZMod p))⁻¹ with hr
  refine ⟨r.val, ZMod.val_lt r, fun v => ?_⟩
  have key : (Lv i v : ZMod p) = (slope i : ZMod p) * (Q : ZMod p) * ((v : ZMod p) - r) := by
    unfold Lv L
    push_cast
    rw [hr]
    linear_combination (-((icept i : ZMod p) + (slope i : ZMod p) * (t₀ : ZMod p))) * hinv
  constructor
  · intro hdvd
    have h0 : (Lv i v : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
    rw [key, mul_eq_zero, sub_eq_zero] at h0
    rcases h0 with h0 | h0
    · exact absurd h0 hu
    · rw [← ZMod.val_natCast, h0]
  · intro hv
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    rw [key]
    have : (v : ZMod p) = r := by
      rw [← ZMod.natCast_mod v p, hv, ZMod.natCast_zmod_val]
    rw [this, sub_self, mul_zero]

/-- `F v % p = p - shift i` when `p ∣ Lv i v` and `p > 3`. -/
theorem F_mod_eq {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (i : Fin 6) {v : ℕ} (h : p ∣ Lv i v) :
    F v % p = p - shift i := by
  have hd : p ∣ F v + shift i := dvd_trans h (Lv_dvd_F_add_shift i v)
  have hs3 := shift_le_three i
  have hs0 := shift_pos i
  obtain ⟨k, hk⟩ := hd
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := by
    refine ⟨k - 1, ?_⟩
    rcases k with _ | k
    · omega
    · omega
  have hF : F v = p * k' + (p - shift i) := by
    rw [mul_add, mul_one] at hk
    omega
  rw [hF, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]

/-- **First carry**: if a prime `p > 6` divides `Lv i v`, then `F v ≡ -shift i (mod p)` and
level `1` carries. -/
theorem first_carry {p : ℕ} (hp : p.Prime) (hp6 : 6 < p) (i : Fin 6) {v : ℕ}
    (h : p ∣ Lv i v) : p ≤ 2 * (F v % p) := by
  rw [F_mod_eq hp (by omega) i h]
  have := shift_le_three i
  omega

/-- `D (v + v') + E ≡ Q f'(t₀ + Q v) (mod p)` whenever `v ≡ v' (mod p)`; in particular it is a
unit modulo any prime `p > 1000` dividing `Lv i v`. -/
theorem not_dvd_D_add_E {p : ℕ} (hp : p.Prime) (hpY : Y < p) (i : Fin 6) {v v' : ℕ}
    (hv : p ∣ Lv i v) (hvv' : v ≡ v' [MOD p]) : ¬ p ∣ D * (v + v') + E := by
  have h1 : D * (v + v') + E ≡ D * (v + v) + E [MOD p] :=
    ((hvv'.symm.add_left v).mul_left D).add_right E
  have h2 : D * (v + v) + E = Q * fderiv (t₀ + Q * v) := by unfold D E fderiv; ring
  rw [h2] at h1
  intro hd
  have hd' : p ∣ Q * fderiv (t₀ + Q * v) := (Nat.ModEq.dvd_iff h1 (dvd_refl p)).mp hd
  unfold Y at hpY
  rcases (Nat.Prime.dvd_mul hp).mp hd' with h | h
  · have := prime_dvd_Q_le hp h
    unfold Y at this
    omega
  · exact not_dvd_fderiv hp (by omega) i hv h

/-- **Injectivity on the root class**: for a prime `p > 1000` with `p ∣ Lv i v` and
`p ∣ Lv i v'`, `F v ≡ F v' (mod p^ℓ)` implies `v ≡ v' (mod p^ℓ)`. -/
theorem modEq_of_F_modEq {p : ℕ} (hp : p.Prime) (hpY : Y < p) (i : Fin 6) {v v' ℓ : ℕ}
    (hv : p ∣ Lv i v) (hv' : p ∣ Lv i v') (h : F v ≡ F v' [MOD p ^ ℓ]) : v ≡ v' [MOD p ^ ℓ] := by
  obtain ⟨r, -, hr⟩ := exists_root hp hpY i
  have hvv' : v ≡ v' [MOD p] := by
    unfold Nat.ModEq
    rw [(hr v).mp hv, (hr v').mp hv']
  have hnd := not_dvd_D_add_E hp hpY i hv hvv'
  have hcop : IsCoprime ((p ^ ℓ : ℕ) : ℤ) ((D * (v + v') + E : ℕ) : ℤ) :=
    Nat.Coprime.isCoprime (Nat.Coprime.pow_left ℓ ((Nat.Prime.coprime_iff_not_dvd hp).mpr hnd))
  have hdiff : ((F v' : ℕ) : ℤ) - (F v : ℕ) = ((v' : ℤ) - v) * ((D * (v + v') + E : ℕ) : ℤ) := by
    rw [F_eq, F_eq]; push_cast; ring
  have hdvd := Nat.modEq_iff_dvd.mp h
  rw [hdiff] at hdvd
  exact Nat.modEq_iff_dvd.mpr (hcop.dvd_of_dvd_mul_right hdvd)

/-- **Section 5**: without repeated prime factors, `v_p (A (F v)) ≤ 1` for `p > 1000`, and
`v_p (A (F v)) = 1` exactly when `p` divides some `Lv i v`. -/
theorem factorization_A_F_le_one {p : ℕ} (hp : p.Prime) (hpY : Y < p) {v : ℕ}
    (hsq : ∀ i, ¬ p ^ 2 ∣ Lv i v) : (A (F v)).factorization p ≤ 1 := by
  rw [A_F, Nat.factorization_prod (fun i _ => (Lv_pos i v).ne'), Finsupp.finsetSum_apply]
  have hle : ∀ i, (Lv i v).factorization p ≤ 1 := by
    intro i
    by_contra hcon
    push Not at hcon
    exact hsq i ((hp.pow_dvd_iff_le_factorization (Lv_pos i v).ne').mpr hcon)
  by_cases hex : ∃ i, p ∣ Lv i v
  · obtain ⟨i₀, hi₀⟩ := hex
    unfold Y at hpY
    rw [Finset.sum_eq_single i₀]
    · exact hle i₀
    · intro j _ hj
      apply Nat.factorization_eq_zero_of_not_dvd
      intro hj'
      exact hj (eq_of_prime_dvd_two_forms hp (by omega) hj' hi₀)
    · intro h
      exact absurd (Finset.mem_univ i₀) h
  · push Not at hex
    rw [Finset.sum_eq_zero (fun i _ => Nat.factorization_eq_zero_of_not_dvd (hex i))]
    exact zero_le_one

theorem factorization_A_F_eq_zero {p : ℕ} (hp : p.Prime) (hpY : Y < p) {v : ℕ}
    (h : ∀ i, ¬ p ∣ Lv i v) : (A (F v)).factorization p = 0 := by
  rw [A_F, Nat.factorization_prod (fun i _ => (Lv_pos i v).ne'), Finsupp.finsetSum_apply]
  exact Finset.sum_eq_zero (fun i _ => Nat.factorization_eq_zero_of_not_dvd (h i))

/-- **Reduction of Section 5**: `F v` is good as soon as, for every prime `p > 1000` and every
form `i` with `p ∣ Lv i v`, we have `p² ∤ Lv i v` and a second carry. -/
theorem good_F_of {v : ℕ}
    (hsq : ∀ i p, p.Prime → Y < p → p ∣ Lv i v → ¬ p ^ 2 ∣ Lv i v)
    (hcar : ∀ i p, p.Prime → Y < p → p ∣ Lv i v → 2 ≤ carry p (F v)) : Good (F v) := by
  rw [good_iff]
  intro p hp
  by_cases hpY : p ≤ Y
  · unfold F
    exact small_primes_good v p hp hpY
  · push Not at hpY
    by_cases hex : ∃ i, p ∣ Lv i v
    · obtain ⟨i, hi⟩ := hex
      have hsq' : ∀ j, ¬ p ^ 2 ∣ Lv j v := fun j hj =>
        hsq j p hp hpY (dvd_trans (dvd_pow_self p two_ne_zero) hj) hj
      have h1 := factorization_A_F_le_one hp hpY hsq'
      have h2 := hcar i p hp hpY hi
      omega
    · push Not at hex
      rw [factorization_A_F_eq_zero hp hpY hex]
      simp

/-- Contrapositive form used for counting: a bad `v` exhibits a prime `p > 1000` and a form
`i` with `p ∣ Lv i v`, and either `p² ∣ Lv i v` or no level `h ≥ 2` carries. -/
theorem exists_bad_prime_of_not_good {v : ℕ} (h : ¬ Good (F v)) :
    ∃ i p, p.Prime ∧ Y < p ∧ p ∣ Lv i v ∧
      (p ^ 2 ∣ Lv i v ∨ ∀ h, 2 ≤ h → 2 * (F v % p ^ h) < p ^ h) := by
  by_contra hcon
  push Not at hcon
  refine h (good_F_of ?_ ?_)
  · intro i p hp hpY hi
    exact (hcon i p hp hpY hi).1
  · intro i p hp hpY hi
    obtain ⟨-, hh, hh2, hcar⟩ := hcon i p hp hpY hi
    by_contra hlt
    push Not at hlt
    have hp6 : 6 < p := by unfold Y at hpY; omega
    have := not_carry_of_lt_two hp (first_carry hp hp6 i hi) hlt hh hh2
    omega

end Erdos727
