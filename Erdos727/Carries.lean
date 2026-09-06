import Erdos727.Defs

/-!
# Carries and the factorial divisibility criterion (Section 2)

`carry p n = v_p (binom(2n,n))` counts the levels `i ≥ 1` with `p^i ≤ 2 (n mod p^i)`,
i.e. the carries when `n` is added to itself in base `p` (Kummer's theorem, available in
Mathlib as `Nat.factorization_choose'`).  The target `((n+3)!)² ∣ (2n)!` is equivalent to
`A n ^ 2 ∣ binom(2n,n)`, i.e. to `2 v_p(A n) ≤ carry p n` for every prime `p`.
-/

namespace Erdos727

open Finset

/-- Kummer's theorem in the form used throughout: `carry p n` is the number of levels
`1 ≤ i < b` at which doubling `n` produces a carry, for any `b > log_p (2n)`. -/
theorem carry_eq_card {p n b : ℕ} (hp : p.Prime) (hb : Nat.log p (2 * n) < b) :
    carry p n = #{i ∈ Ico 1 b | p ^ i ≤ 2 * (n % p ^ i)} := by
  unfold carry
  have h2n : (2 * n).choose n = (n + n).choose n := by rw [two_mul]
  rw [Nat.centralBinom_eq_two_mul_choose, h2n,
    Nat.factorization_choose' hp (by rwa [← two_mul])]
  congr 1
  apply Finset.filter_congr
  intro i _
  rw [two_mul]

/-- Any finite set of carrying levels gives a lower bound on `carry p n`. -/
theorem card_le_carry {p n : ℕ} (hp : p.Prime) (s : Finset ℕ)
    (hs : ∀ i ∈ s, 1 ≤ i ∧ p ^ i ≤ 2 * (n % p ^ i)) : #s ≤ carry p n := by
  rw [carry_eq_card hp (Nat.lt_succ_self (Nat.log p (2 * n)))]
  apply Finset.card_le_card
  intro i hi
  obtain ⟨h1, h2⟩ := hs i hi
  rw [Finset.mem_filter, Finset.mem_Ico]
  refine ⟨⟨h1, ?_⟩, h2⟩
  have hle : p ^ i ≤ 2 * n := le_trans h2 (Nat.mul_le_mul_left 2 (Nat.mod_le n _))
  exact Nat.lt_succ_of_le (Nat.le_log_of_pow_le hp.one_lt hle)

/-- A single carrying level gives `1 ≤ carry p n`. -/
theorem one_le_carry {p n i : ℕ} (hp : p.Prime) (hi : 1 ≤ i) (h : p ^ i ≤ 2 * (n % p ^ i)) :
    1 ≤ carry p n := by
  have := card_le_carry hp {i} (by
    intro j hj
    rw [Finset.mem_singleton] at hj
    subst hj
    exact ⟨hi, h⟩)
  simpa using this

/-- Two distinct carrying levels give `2 ≤ carry p n`. -/
theorem two_le_carry {p n i j : ℕ} (hp : p.Prime) (hi : 1 ≤ i) (hj : 1 ≤ j) (hij : i ≠ j)
    (h₁ : p ^ i ≤ 2 * (n % p ^ i)) (h₂ : p ^ j ≤ 2 * (n % p ^ j)) : 2 ≤ carry p n := by
  have := card_le_carry hp {i, j} (by
    intro k hk
    rw [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl
    · exact ⟨hi, h₁⟩
    · exact ⟨hj, h₂⟩)
  rwa [Finset.card_pair hij] at this

/-- If level `1` carries but `carry p n < 2`, then no level `i ≥ 2` carries. -/
theorem not_carry_of_lt_two {p n : ℕ} (hp : p.Prime) (h1 : p ≤ 2 * (n % p))
    (h : carry p n < 2) : ∀ i, 2 ≤ i → 2 * (n % p ^ i) < p ^ i := by
  intro i hi
  by_contra hcon
  rw [not_lt] at hcon
  have h1' : p ^ 1 ≤ 2 * (n % p ^ 1) := by simpa using h1
  have := two_le_carry hp (le_refl 1) (by omega) (by omega : 1 ≠ i) h1' hcon
  omega

/-- A block of `k - b` consecutive carrying levels `b+1, …, k`, read off from `n mod p^k`. -/
theorem carry_ge_of_block {p n b k r : ℕ} (hp : p.Prime) (hbk : b ≤ k) (hr : n % p ^ k = r)
    (hblock : ∀ h, b < h → h ≤ k → p ^ h ≤ 2 * (r % p ^ h)) : k - b ≤ carry p n := by
  have := card_le_carry hp (Finset.Ioc b k) (by
    intro h hh
    rw [Finset.mem_Ioc] at hh
    refine ⟨by omega, ?_⟩
    have := hblock h hh.1 hh.2
    rwa [← hr, Nat.mod_mod_of_dvd n (Nat.pow_dvd_pow p hh.2)] at this)
  rwa [Nat.card_Ioc] at this

/-- `(n+3)! = A n * n!`. -/
theorem factorial_add_three (n : ℕ) : (n + 3).factorial = A n * n.factorial := by
  simp only [Nat.factorial_succ, A]
  ring

/-- `(2n)! = binom(2n,n) * n! * n!`. -/
theorem factorial_two_mul (n : ℕ) :
    (2 * n).factorial = Nat.centralBinom n * n.factorial * n.factorial := by
  have h := Nat.choose_mul_factorial_mul_factorial (show n ≤ 2 * n by omega)
  rw [show 2 * n - n = n by omega] at h
  rw [Nat.centralBinom_eq_two_mul_choose]
  exact h.symm

/-- The target property is equivalent to `A n ^ 2 ∣ binom(2n, n)`. -/
theorem good_iff_sq_dvd_centralBinom (n : ℕ) : Good n ↔ A n ^ 2 ∣ Nat.centralBinom n := by
  unfold Good
  rw [factorial_add_three, factorial_two_mul]
  have hne : n.factorial * n.factorial ≠ 0 :=
    mul_ne_zero (Nat.factorial_ne_zero n) (Nat.factorial_ne_zero n)
  have e1 : (A n * n.factorial) ^ 2 = A n ^ 2 * (n.factorial * n.factorial) := by ring
  have e2 : Nat.centralBinom n * n.factorial * n.factorial
      = Nat.centralBinom n * (n.factorial * n.factorial) := by ring
  rw [e1, e2, mul_dvd_mul_iff_right hne]

/-- **Section 2, (2.3)**: the target property is equivalent to the carry inequalities at
every prime. -/
theorem good_iff (n : ℕ) :
    Good n ↔ ∀ p, p.Prime → 2 * (A n).factorization p ≤ carry p n := by
  rw [good_iff_sq_dvd_centralBinom]
  have hA : A n ^ 2 ≠ 0 := pow_ne_zero _ (by unfold A; positivity)
  rw [← Nat.factorization_le_iff_dvd hA (Nat.centralBinom_ne_zero n), Nat.factorization_pow,
    Finsupp.le_def]
  unfold carry
  constructor
  · intro h p _
    simpa using h p
  · intro h p
    by_cases hp : p.Prime
    · simpa using h p hp
    · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

/-- If `n ≡ m [MOD p^b]` and `v_p(m) < b` (with `m ≠ 0`) then `v_p(n) = v_p(m)`. -/
theorem factorization_eq_of_modEq {p b n m : ℕ} (hp : p.Prime) (hm : m ≠ 0)
    (hmb : m.factorization p < b) (h : n ≡ m [MOD p ^ b]) :
    n.factorization p = m.factorization p := by
  have h1 : p ^ m.factorization p ∣ m := Nat.ordProj_dvd m p
  have h2 : ¬ p ^ (m.factorization p + 1) ∣ m := Nat.pow_succ_factorization_not_dvd hm hp
  have d1 : p ^ m.factorization p ∣ p ^ b := Nat.pow_dvd_pow p hmb.le
  have d2 : p ^ (m.factorization p + 1) ∣ p ^ b := Nat.pow_dvd_pow p hmb
  have h1' : p ^ m.factorization p ∣ n := (h.dvd_iff d1).mpr h1
  have h2' : ¬ p ^ (m.factorization p + 1) ∣ n := fun hd => h2 ((h.dvd_iff d2).mp hd)
  have hn : n ≠ 0 := by
    rintro rfl
    exact h2' (dvd_zero _)
  rw [hp.pow_dvd_iff_le_factorization hn] at h1' h2'
  omega

end Erdos727
