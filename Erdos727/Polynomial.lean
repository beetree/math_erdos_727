import Erdos727.Defs

/-!
# The six linear factors (Section 3) and the exact identities of Section 11

* `f t + 1 = (35t+36)(6t+5)`, `f t + 2 = (t+1)(210t+181)`, `f t + 3 = (15t+14)(14t+13)`.
* `A (f t) = ∏ i, L i t`.
* A prime `p > 41` divides at most one of the six forms at a given `t`.
* The derivative `f'(t) = 420 t + 391` is congruent to `c i ∈ {±41, ±29, ±1}` modulo any
  prime `p ∤ slope i` dividing `L i t`.
* The identities `f = α_i L_i² + β_i L_i - j_i`, cleared of denominators.
-/

namespace Erdos727

open Finset

/-- The derivative `f'(t) = 420 t + 391`. -/
def fderiv (t : ℕ) : ℕ := 420 * t + 391

/-- The value of `f'` on the root class of `L i`. -/
def c : Fin 6 → ℤ := ![-41, 41, -29, 29, -1, 1]

/-! ### Evaluation lemmas for the six forms -/

theorem L_zero (t : ℕ) : L 0 t = 35 * t + 36 := rfl
theorem L_one (t : ℕ) : L 1 t = 6 * t + 5 := rfl
theorem L_two (t : ℕ) : L 2 t = t + 1 := by
  show 1 * t + 1 = t + 1
  ring
theorem L_three (t : ℕ) : L 3 t = 210 * t + 181 := rfl
theorem L_four (t : ℕ) : L 4 t = 15 * t + 14 := rfl
theorem L_five (t : ℕ) : L 5 t = 14 * t + 13 := rfl

theorem slope_pos (i : Fin 6) : 0 < slope i := by
  fin_cases i <;> decide

theorem icept_pos (i : Fin 6) : 0 < icept i := by
  fin_cases i <;> decide

theorem shift_pos (i : Fin 6) : 0 < shift i := by
  fin_cases i <;> decide

theorem shift_le_three (i : Fin 6) : shift i ≤ 3 := by
  fin_cases i <;> decide

theorem L_pos (i : Fin 6) (t : ℕ) : 0 < L i t := by
  unfold L
  have := icept_pos i
  omega

theorem coprime_slope_icept (i : Fin 6) : Nat.Coprime (slope i) (icept i) := by
  fin_cases i <;> decide

/-- Every prime factor of a slope is at most `7`. -/
theorem prime_dvd_slope_le (i : Fin 6) {p : ℕ} (hp : p.Prime) (h : p ∣ slope i) : p ≤ 7 := by
  have h210 : p ∣ 2 * 3 * 5 * 7 := h.trans (by fin_cases i <;> decide)
  rcases (Nat.Prime.dvd_mul hp).mp h210 with h' | h'
  · rcases (Nat.Prime.dvd_mul hp).mp h' with h' | h'
    · rcases (Nat.Prime.dvd_mul hp).mp h' with h' | h'
      · exact (Nat.le_of_dvd (by norm_num) h').trans (by norm_num)
      · exact (Nat.le_of_dvd (by norm_num) h').trans (by norm_num)
    · exact (Nat.le_of_dvd (by norm_num) h').trans (by norm_num)
  · exact Nat.le_of_dvd (by norm_num) h'

theorem f_add_one (t : ℕ) : f t + 1 = L 0 t * L 1 t := by
  rw [L_zero, L_one]; unfold f; ring

theorem f_add_two (t : ℕ) : f t + 2 = L 2 t * L 3 t := by
  rw [L_two, L_three]; unfold f; ring

theorem f_add_three (t : ℕ) : f t + 3 = L 4 t * L 5 t := by
  rw [L_four, L_five]; unfold f; ring

/-- `A (f t) = ∏ i, L i t`. -/
theorem A_f (t : ℕ) : A (f t) = ∏ i, L i t := by
  rw [Fin.prod_univ_six, L_zero, L_one, L_two, L_three, L_four, L_five]
  unfold A f
  ring

/-- `L i t ∣ f t + shift i`. -/
theorem L_dvd_f_add_shift (i : Fin 6) (t : ℕ) : L i t ∣ f t + shift i := by
  fin_cases i
  · exact Dvd.intro _ (f_add_one t).symm
  · exact Dvd.intro_left _ (f_add_one t).symm
  · exact Dvd.intro _ (f_add_two t).symm
  · exact Dvd.intro_left _ (f_add_two t).symm
  · exact Dvd.intro _ (f_add_three t).symm
  · exact Dvd.intro_left _ (f_add_three t).symm

/-- `f t + shift i = L i t * L (partner i) t`; the partner of `2j` is `2j+1`. -/
theorem f_add_shift_eq (i : Fin 6) (t : ℕ) :
    f t + shift i = L i t * L (if i.val % 2 = 0 then i + 1 else i - 1) t := by
  fin_cases i
  · exact f_add_one t
  · exact (f_add_one t).trans (mul_comm _ _)
  · exact f_add_two t
  · exact (f_add_two t).trans (mul_comm _ _)
  · exact f_add_three t
  · exact (f_add_three t).trans (mul_comm _ _)

/-- Auxiliary: if `p > 41` divides `x` and `y` and `a * x = b * y + r` with `0 < r ≤ 41`,
contradiction. -/
theorem aux_two_forms {p : ℕ} (_hp : p.Prime) (h41 : 41 < p) (a b r : ℕ) {x y : ℕ}
    (hx : p ∣ x) (hy : p ∣ y) (hr0 : 0 < r) (hr : r ≤ 41) (h : a * x = b * y + r) : False := by
  have h1 : p ∣ a * x := dvd_mul_of_dvd_right hx a
  have h2 : p ∣ b * y := dvd_mul_of_dvd_right hy b
  rw [h] at h1
  have h3 : p ∣ r := (Nat.dvd_add_right h2).mp h1
  have := Nat.le_of_dvd hr0 h3
  omega

/-- **Section 3**: a prime `p > 41` divides at most one of the six forms at a given `t`. -/
theorem eq_of_prime_dvd_two_forms {p : ℕ} (hp : p.Prime) (h41 : 41 < p) {i j : Fin 6}
    {t : ℕ} (hi : p ∣ L i t) (hj : p ∣ L j t) : i = j := by
  have key : ∀ (a b r : ℕ) {x y : ℕ}, p ∣ x → p ∣ y → 0 < r → r ≤ 41 →
      a * x = b * y + r → False := fun a b r _ _ hx hy hr0 hr h =>
    aux_two_forms hp h41 a b r hx hy hr0 hr h
  fin_cases i <;> fin_cases j
  -- i = 0
  · rfl
  · exact (key 6 35 41 (x := L 0 t) (y := L 1 t) hi hj (by norm_num) (by norm_num)
      (by rw [L_zero, L_one]; ring)).elim
  · exact (key 1 35 1 (x := L 0 t) (y := L 2 t) hi hj (by norm_num) (by norm_num)
      (by rw [L_zero, L_two]; ring)).elim
  · exact (key 6 1 35 (x := L 0 t) (y := L 3 t) hi hj (by norm_num) (by norm_num)
      (by rw [L_zero, L_three]; ring)).elim
  · exact (key 3 7 10 (x := L 0 t) (y := L 4 t) hi hj (by norm_num) (by norm_num)
      (by rw [L_zero, L_four]; ring)).elim
  · exact (key 2 5 7 (x := L 0 t) (y := L 5 t) hi hj (by norm_num) (by norm_num)
      (by rw [L_zero, L_five]; ring)).elim
  -- i = 1
  · exact (key 6 35 41 (x := L 0 t) (y := L 1 t) hj hi (by norm_num) (by norm_num)
      (by rw [L_zero, L_one]; ring)).elim
  · rfl
  · exact (key 6 1 1 (x := L 2 t) (y := L 1 t) hj hi (by norm_num) (by norm_num)
      (by rw [L_two, L_one]; ring)).elim
  · exact (key 1 35 6 (x := L 3 t) (y := L 1 t) hj hi (by norm_num) (by norm_num)
      (by rw [L_three, L_one]; ring)).elim
  · exact (key 2 5 3 (x := L 4 t) (y := L 1 t) hj hi (by norm_num) (by norm_num)
      (by rw [L_four, L_one]; ring)).elim
  · exact (key 3 7 4 (x := L 5 t) (y := L 1 t) hj hi (by norm_num) (by norm_num)
      (by rw [L_five, L_one]; ring)).elim
  -- i = 2
  · exact (key 1 35 1 (x := L 0 t) (y := L 2 t) hj hi (by norm_num) (by norm_num)
      (by rw [L_zero, L_two]; ring)).elim
  · exact (key 6 1 1 (x := L 2 t) (y := L 1 t) hi hj (by norm_num) (by norm_num)
      (by rw [L_two, L_one]; ring)).elim
  · rfl
  · exact (key 210 1 29 (x := L 2 t) (y := L 3 t) hi hj (by norm_num) (by norm_num)
      (by rw [L_two, L_three]; ring)).elim
  · exact (key 15 1 1 (x := L 2 t) (y := L 4 t) hi hj (by norm_num) (by norm_num)
      (by rw [L_two, L_four]; ring)).elim
  · exact (key 14 1 1 (x := L 2 t) (y := L 5 t) hi hj (by norm_num) (by norm_num)
      (by rw [L_two, L_five]; ring)).elim
  -- i = 3
  · exact (key 6 1 35 (x := L 0 t) (y := L 3 t) hj hi (by norm_num) (by norm_num)
      (by rw [L_zero, L_three]; ring)).elim
  · exact (key 1 35 6 (x := L 3 t) (y := L 1 t) hi hj (by norm_num) (by norm_num)
      (by rw [L_three, L_one]; ring)).elim
  · exact (key 210 1 29 (x := L 2 t) (y := L 3 t) hj hi (by norm_num) (by norm_num)
      (by rw [L_two, L_three]; ring)).elim
  · rfl
  · exact (key 14 1 15 (x := L 4 t) (y := L 3 t) hj hi (by norm_num) (by norm_num)
      (by rw [L_four, L_three]; ring)).elim
  · exact (key 15 1 14 (x := L 5 t) (y := L 3 t) hj hi (by norm_num) (by norm_num)
      (by rw [L_five, L_three]; ring)).elim
  -- i = 4
  · exact (key 3 7 10 (x := L 0 t) (y := L 4 t) hj hi (by norm_num) (by norm_num)
      (by rw [L_zero, L_four]; ring)).elim
  · exact (key 2 5 3 (x := L 4 t) (y := L 1 t) hi hj (by norm_num) (by norm_num)
      (by rw [L_four, L_one]; ring)).elim
  · exact (key 15 1 1 (x := L 2 t) (y := L 4 t) hj hi (by norm_num) (by norm_num)
      (by rw [L_two, L_four]; ring)).elim
  · exact (key 14 1 15 (x := L 4 t) (y := L 3 t) hi hj (by norm_num) (by norm_num)
      (by rw [L_four, L_three]; ring)).elim
  · rfl
  · exact (key 14 15 1 (x := L 4 t) (y := L 5 t) hi hj (by norm_num) (by norm_num)
      (by rw [L_four, L_five]; ring)).elim
  -- i = 5
  · exact (key 2 5 7 (x := L 0 t) (y := L 5 t) hj hi (by norm_num) (by norm_num)
      (by rw [L_zero, L_five]; ring)).elim
  · exact (key 3 7 4 (x := L 5 t) (y := L 1 t) hi hj (by norm_num) (by norm_num)
      (by rw [L_five, L_one]; ring)).elim
  · exact (key 14 1 1 (x := L 2 t) (y := L 5 t) hj hi (by norm_num) (by norm_num)
      (by rw [L_two, L_five]; ring)).elim
  · exact (key 15 1 14 (x := L 5 t) (y := L 3 t) hi hj (by norm_num) (by norm_num)
      (by rw [L_five, L_three]; ring)).elim
  · exact (key 14 15 1 (x := L 4 t) (y := L 5 t) hj hi (by norm_num) (by norm_num)
      (by rw [L_four, L_five]; ring)).elim
  · rfl

/-- `slope i * f'(t) = 420 * L i t + slope i * c i` as integers. -/
theorem slope_mul_fderiv (i : Fin 6) (t : ℕ) :
    (slope i : ℤ) * fderiv t = 420 * L i t + slope i * c i := by
  fin_cases i <;> simp [slope, icept, c, fderiv, L] <;> ring

/-- `|c i| ≤ 41`, so `c i` is a unit modulo any prime `p > 41`. -/
theorem abs_c_le (i : Fin 6) : |c i| ≤ 41 := by
  fin_cases i <;> decide

theorem c_ne_zero (i : Fin 6) : c i ≠ 0 := by
  fin_cases i <;> decide

/-- If `p ∤ slope i`, `p ∣ L i t` and `p` is prime, then `f'(t) ≡ c i (mod p)`. -/
theorem fderiv_modEq_c {p : ℕ} (hp : p.Prime) (i : Fin 6) {t : ℕ} (hs : ¬ p ∣ slope i)
    (h : p ∣ L i t) : (fderiv t : ZMod p) = c i := by
  have := Fact.mk hp
  have h1 : (L i t : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr h
  have h2 : (slope i : ZMod p) ≠ 0 := fun h0 => hs ((ZMod.natCast_eq_zero_iff _ _).mp h0)
  have h3 := congrArg (Int.cast : ℤ → ZMod p) (slope_mul_fderiv i t)
  push_cast at h3
  rw [h1, mul_zero, zero_add] at h3
  exact mul_left_cancel₀ h2 h3

/-- Hence `p ∤ f'(t)` for primes `p > 41` dividing `L i t`. -/
theorem not_dvd_fderiv {p : ℕ} (hp : p.Prime) (h41 : 41 < p) (i : Fin 6) {t : ℕ}
    (h : p ∣ L i t) : ¬ p ∣ fderiv t := by
  intro hd
  have := Fact.mk hp
  have hs : ¬ p ∣ slope i := fun hs => by
    have := prime_dvd_slope_le i hp hs
    omega
  have h1 := fderiv_modEq_c hp i hs h
  have h2 : (fderiv t : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hd
  rw [h2] at h1
  have h3 : (p : ℤ) ∣ c i := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h1.symm
  have h4 : (p : ℤ) ∣ |c i| := (dvd_abs _ _).mpr h3
  have h5 : (p : ℤ) ≤ |c i| := Int.le_of_dvd (abs_pos.mpr (c_ne_zero i)) h4
  have h6 := abs_c_le i
  omega

/-! ### Section 11 identities, denominators cleared -/

theorem f_eq_L0 (t : ℕ) : 35 * (f t + 1) + 41 * L 0 t = 6 * L 0 t ^ 2 := by
  rw [L_zero]; unfold f; ring

theorem f_eq_L1 (t : ℕ) : 6 * (f t + 1) = 35 * L 1 t ^ 2 + 41 * L 1 t := by
  rw [L_one]; unfold f; ring

theorem f_eq_L2 (t : ℕ) : (f t + 2) + 29 * L 2 t = 210 * L 2 t ^ 2 := by
  rw [L_two]; unfold f; ring

theorem f_eq_L3 (t : ℕ) : 210 * (f t + 2) = L 3 t ^ 2 + 29 * L 3 t := by
  rw [L_three]; unfold f; ring

theorem f_eq_L4 (t : ℕ) : 15 * (f t + 3) + L 4 t = 14 * L 4 t ^ 2 := by
  rw [L_four]; unfold f; ring

theorem f_eq_L5 (t : ℕ) : 14 * (f t + 3) = 15 * L 5 t ^ 2 + L 5 t := by
  rw [L_five]; unfold f; ring

end Erdos727
