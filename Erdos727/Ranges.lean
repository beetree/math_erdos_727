import Erdos727.Failure
import Erdos727.Analytic.Mertens

/-!
# The four prime ranges and their counting bounds (Sections 5, 7, 9–11)

The primes of `primeRange X` are split into
* `smallR X`: `1000 < p ≤ X^{1/20}` (Section 7),
* `mediumR X`: `X^{1/20} < p ≤ X^{1/2 + η}` (Sections 9 and 10),
* `largeR X`: `p > X^{1/2 + η}` (Section 11),
while the square events (Section 5) are counted over the whole range.  The bounds themselves are
proved in `Erdos727/Range/Square.lean`, `Small.lean`, `Medium.lean`, `Large.lean`.  The limiting
proportions in the manuscript are `0.006`, `< 0.01`, `< 3/8 + 0.01`, and `< 7/12`; we use the
slacker constants `0.01`, `0.02`, `0.35`, `0.60`, whose sum `0.98 < 1` suffices.
-/

namespace Erdos727

open Finset Real Filter

/-- The exponent margin `η = 10⁻⁶` of Sections 9–11. -/
noncomputable def η : ℝ := 1 / 1000000

/-- Primes `1000 < p ≤ X^{1/20}`. -/
noncomputable def smallR (X : ℕ) : Finset ℕ :=
  (primeRange X).filter fun p => (p : ℝ) ≤ (X : ℝ) ^ ((1 : ℝ) / 20)

/-- Primes `X^{1/20} < p ≤ X^{1/2 + η}`. -/
noncomputable def mediumR (X : ℕ) : Finset ℕ :=
  (primeRange X).filter fun p => (X : ℝ) ^ ((1 : ℝ) / 20) < p ∧ (p : ℝ) ≤ (X : ℝ) ^ ((1 : ℝ) / 2 + η)

/-- Primes `p > X^{1/2 + η}` (and `p ≤ 2 Cb X`). -/
noncomputable def largeR (X : ℕ) : Finset ℕ :=
  (primeRange X).filter fun p => (X : ℝ) ^ ((1 : ℝ) / 2 + η) < p

theorem sum_badSet_split (X : ℕ) (i : Fin 6) :
    ∑ p ∈ primeRange X, #(badSet X i p) =
      ∑ p ∈ smallR X, #(badSet X i p) + ∑ p ∈ mediumR X, #(badSet X i p)
        + ∑ p ∈ largeR X, #(badSet X i p) := by
  have hAB : (X : ℝ) ^ ((1 : ℝ) / 20) ≤ (X : ℝ) ^ ((1 : ℝ) / 2 + η) := by
    rcases Nat.eq_zero_or_pos X with hX | hX
    · subst hX
      simp only [Nat.cast_zero]
      rw [Real.zero_rpow (by norm_num), Real.zero_rpow (by unfold η; norm_num)]
    · apply Real.rpow_le_rpow_of_exponent_le
      · exact_mod_cast hX
      · unfold η; norm_num
  have h1 : mediumR X = ((primeRange X).filter fun p : ℕ => ¬ (p : ℝ) ≤ (X : ℝ) ^ ((1 : ℝ) / 20)).filter
      fun p : ℕ => (p : ℝ) ≤ (X : ℝ) ^ ((1 : ℝ) / 2 + η) := by
    unfold mediumR
    rw [Finset.filter_filter]
    apply Finset.filter_congr
    intro p _
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨not_le.mpr h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨not_le.mp h1, h2⟩
  have h2 : largeR X = ((primeRange X).filter fun p : ℕ => ¬ (p : ℝ) ≤ (X : ℝ) ^ ((1 : ℝ) / 20)).filter
      fun p : ℕ => ¬ (p : ℝ) ≤ (X : ℝ) ^ ((1 : ℝ) / 2 + η) := by
    unfold largeR
    rw [Finset.filter_filter]
    apply Finset.filter_congr
    intro p _
    constructor
    · intro h
      exact ⟨not_le.mpr (lt_of_le_of_lt hAB h), not_le.mpr h⟩
    · rintro ⟨-, h⟩
      exact not_le.mp h
  rw [h1, h2, add_assoc, Finset.sum_filter_add_sum_filter_not, smallR,
    Finset.sum_filter_add_sum_filter_not]

end Erdos727
