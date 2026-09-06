import Erdos727.Analytic.LFunctionLink

/-!
# Mertens' first theorem twisted by a nontrivial character (steps 4–5 of `CharacterSums`)
-/

namespace Erdos727

open Finset Real

variable {q : ℕ} [NeZero q]

/-- `∑_{d ≤ N} χ(d) Λ(d) / d` is bounded; this uses `L(1, χ) ≠ 0`. -/
theorem exists_bound_sum_char_vonMangoldt_div (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    ∃ C : ℝ, ∀ N : ℕ, ‖∑ d ∈ Icc 1 N, χ d * (ArithmeticFunction.vonMangoldt d / d : ℝ)‖ ≤ C := by
  sorry

/-- **Mertens' first theorem twisted by a nontrivial character.** -/
theorem exists_bound_sum_char_prime_log_div (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    ∃ C : ℝ, ∀ N : ℕ, ‖∑ p ∈ Nat.primesLE N, χ p * (log p / p : ℝ)‖ ≤ C := by
  sorry

end Erdos727
