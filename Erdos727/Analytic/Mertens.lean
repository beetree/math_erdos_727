import Erdos727.Analytic.MertensSource
import Mathlib

/-!
# Prime harmonic sums (Section 6)

* `mertens_second`: Mertens' second theorem with an `O(1/log x)` error term, from the vendored
  `MertensSource` (`Mertens.sum_prime_inv_sub_sub_bound`).
* `sum_inv_prime_block`: the block sums `∑_{x^{1/b} < p ≤ x^{1/a}} 1/p ≤ log (b/a) + C b / log x`,
  the form of (6.3) used in Sections 7, 9 and 10.
* `MertensAP q`: Mertens' second theorem in arithmetic progressions modulo `q`, the analytic
  input (6.4) used in Section 11.  It is stated as a proposition and threaded as a hypothesis;
  see `Erdos727/Analytic/MertensAP.lean` for its status.
-/

namespace Erdos727

open Finset Real

/-- **Mertens' second theorem** with error `O(1/log x)`. -/
theorem mertens_second : ∃ M C : ℝ, ∀ x : ℝ, 2 ≤ x →
    |∑ p ∈ Nat.primesLE ⌊x⌋₊, (1 : ℝ) / p - log (log x) - M| ≤ C / log x :=
  ⟨Mertens.Weight.prime.M, log 4 + 3, fun _ hx => Mertens.sum_prime_inv_sub_sub_bound hx⟩

/-- The primes `x^{1/b} < p ≤ x^{1/a}`. -/
noncomputable def primeBlock (x a b : ℝ) : Finset ℕ :=
  (Nat.primesLE ⌊x ^ (1 / a)⌋₊).filter fun p => x ^ (1 / b) < p

/-- The block sum is the difference of two prime harmonic sums. -/
lemma sum_primeBlock_eq (x a b : ℝ) (hab : x ^ (1 / b) ≤ x ^ (1 / a)) :
    ∑ p ∈ primeBlock x a b, (1 : ℝ) / p =
      ∑ p ∈ Nat.primesLE ⌊x ^ (1 / a)⌋₊, (1 : ℝ) / p
        - ∑ p ∈ Nat.primesLE ⌊x ^ (1 / b)⌋₊, (1 : ℝ) / p := by
  rw [eq_sub_iff_add_eq, primeBlock]
  by_cases hb0 : 0 ≤ x ^ (1 / b)
  · have ha0 : 0 ≤ x ^ (1 / a) := hb0.trans hab
    have : Nat.primesLE ⌊x ^ (1 / b)⌋₊ =
        (Nat.primesLE ⌊x ^ (1 / a)⌋₊).filter fun p : ℕ => ¬ x ^ (1 / b) < (p : ℝ) := by
      ext p
      simp only [Nat.mem_primesLE, Finset.mem_filter, not_lt, Nat.le_floor_iff hb0,
        Nat.le_floor_iff ha0]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨⟨h1.trans hab, h2⟩, h1⟩
      · rintro ⟨⟨_, h2⟩, h1⟩
        exact ⟨h1, h2⟩
    rw [this, Finset.sum_filter_add_sum_filter_not]
  · push Not at hb0
    have hfloor : ⌊x ^ (1 / b)⌋₊ = 0 := Nat.floor_of_nonpos hb0.le
    have : (Nat.primesLE ⌊x ^ (1 / a)⌋₊).filter (fun p : ℕ => x ^ (1 / b) < (p : ℝ)) =
        Nat.primesLE ⌊x ^ (1 / a)⌋₊ := by
      apply Finset.filter_true_of_mem
      intro p hp
      have := (Nat.mem_primesLE.mp hp).2.pos
      calc x ^ (1 / b) < 0 := hb0
        _ ≤ p := by exact_mod_cast this.le
    rw [this, hfloor]
    simp [Nat.primesLE_zero]

/-- **Block sums (6.3)**: for `1 ≤ a ≤ b` with `x^{1/b} ≥ 2`,
`∑_{x^{1/b} < p ≤ x^{1/a}} 1/p ≤ log (b / a) + C b / log x`. -/
theorem sum_inv_prime_block : ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 2 ≤ x → ∀ a b : ℝ, 1 ≤ a → a ≤ b →
    2 ≤ x ^ (1 / b) → ∑ p ∈ primeBlock x a b, (1 : ℝ) / p ≤ log (b / a) + C * b / log x := by
  obtain ⟨M, C, hMC⟩ := mertens_second
  refine ⟨2 * max C 0, by positivity, ?_⟩
  intro x hx a b ha hab hy₁
  have hx0 : 0 < x := by linarith
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have hy12 : x ^ (1 / b) ≤ x ^ (1 / a) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (one_div_le_one_div_of_le ha0 hab)
  have hy₂ : 2 ≤ x ^ (1 / a) := hy₁.trans hy12
  have hlogx : 0 < log x := Real.log_pos (by linarith)
  have h1 := hMC _ hy₁
  have h2 := hMC _ hy₂
  rw [abs_le] at h1 h2
  rw [sum_primeBlock_eq x a b hy12]
  rw [Real.log_rpow hx0] at h1 h2
  have hll : log (1 / a * log x) - log (1 / b * log x) = log (b / a) := by
    rw [Real.log_mul (by positivity) hlogx.ne', Real.log_mul (by positivity) hlogx.ne',
      Real.log_div hb0.ne' ha0.ne', one_div, one_div, Real.log_inv, Real.log_inv]
    ring
  have hC : C ≤ max C 0 := le_max_left _ _
  have hC0 : 0 ≤ max C 0 := le_max_right _ _
  have hd1 : C / (1 / a * log x) ≤ max C 0 * b / log x := by
    have : C / (1 / a * log x) = C * a / log x := by field_simp
    rw [this]
    refine div_le_div_of_nonneg_right ?_ hlogx.le
    nlinarith
  have hd2 : C / (1 / b * log x) ≤ max C 0 * b / log x := by
    have : C / (1 / b * log x) = C * b / log x := by field_simp
    rw [this]
    exact div_le_div_of_nonneg_right (by nlinarith) hlogx.le
  have : 2 * max C 0 * b / log x = max C 0 * b / log x + max C 0 * b / log x := by ring
  rw [this]
  linarith

/-- **Mertens' second theorem in arithmetic progressions** modulo `q` with error `O(1/log x)`:
for every unit `a` modulo `q`, `∑_{p ≤ x, p ≡ a (q)} 1/p = φ(q)⁻¹ log log x + B + O(1/log x)`. -/
def MertensAP (q : ℕ) : Prop := ∀ a : ZMod q, IsUnit a → ∃ B C : ℝ, ∀ x : ℝ, 2 ≤ x →
    |∑ p ∈ (Nat.primesLE ⌊x⌋₊).filter (fun p : ℕ => (p : ZMod q) = a), (1 : ℝ) / p
      - (Nat.totient q : ℝ)⁻¹ * log (log x) - B| ≤ C / log x

end Erdos727
